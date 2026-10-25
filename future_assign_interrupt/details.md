# future_assign_interrupt: the defect and the fix

A correctness fix, not a capability: without it Isabelle silently converts an asynchronous
interrupt into `exception Option`, which surfaces as an intermittent, traceless failure in
code that runs under `Timeout.apply` or cancels future groups.

## The defect

`src/Pure/Concurrent/future.ML`, `assign_result`:

```sml
val _ =
  (case Exn.capture_body (fn () => Single_Assignment.assign result res) of
    Exn.Exn (exn as Fail _) => …      (*only Fail is re-raised*)
  | _ => ());                          (*everything else is dropped — including an interrupt*)
val ok =
  (case the (Single_Assignment.peek result) of …   (*unassigned → the → Option*)
```

The code after the `case` assumes the result is assigned. That holds when
`assign` returns, and the `Fail` branch (duplicate assignment) re-raises. But a
third case exists and was silently dropped:

1. A future group is cancelled, or a `Timeout.apply` deadline fires, and an
   **asynchronous interrupt** is delivered to the working thread.
2. It lands in an interruptible part of `Single_Assignment.assign` before the
   assignment. The state mutation itself sits in an inner `uninterruptible_body`
   and cannot be interrupted; what can is the code around it that runs with the
   caller's interrupt attributes, for example the prologue after
   `Multithreading.synchronized`'s `run e` has restored them and before that body
   is entered.
3. `Exn.capture_body` catches the interrupt, and `| _ => ()` throws it away.
   `capture_body` also consumes the thread's break flag, so the interrupt is now
   gone in both of its representations.
4. `the (Single_Assignment.peek result)` then meets a result that was never
   assigned, and raises `exception Option` at `General/basics.ML:84`.

A real interrupt has become a bogus `Option`, at a site that names neither.

## Which call paths can hit the defect

Only those that assign on the **caller's own thread**, with the caller's
interrupt attributes:

| entry point | exposed? |
|---|---|
| `Future.value`, `Future.value_result` | **yes** |
| `Future.map` on an already-finished future | **yes** (takes the `value_result` fast path) |
| `Future.cond_forks` when `Future.enabled ()` is false (one thread, or `parallel_limit` reached) | **yes** |
| `Future.fork` / `forks` | no: the worker thread runs with `interrupts = false` |
| `Future.fulfill_result` | no: wrapped in `Thread_Attributes.no_interrupts` |

Pure itself takes those paths from hot code: `Lazy.force`
(`Concurrent/lazy.ML:109,112,151`), promise fulfilment (`thm.ML:1184,2048`), and
proof-term construction (`proofterm.ML:258,363,480`). So the defect is reachable
from an ordinary simplifier call, not only from code that touches futures
directly.

## The fix

```sml
  | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else ()
  | Exn.Res _ => ());
```

Re-raise the interrupt, so the code below runs only when the assignment actually
happened. This lands at the single point all four callers of `assign_result`
pass through (`future_job`, `value_result`, `promise_name`, `fulfill_result`),
which is why no call site needs its own guard.

### Both interrupt forms, not just the proper one

The fix tests `Exn.is_interrupt`, **not** the `Exn.is_interrupt_proper` used a
few lines above. `Exn.capture_body` is `Isabelle_Thread`'s shadowing version
(`isabelle_thread.ML:160-165`, with the helpers shown at 152-155), which
normalises what it catches:

```sml
fun make_interrupt break = if break then Exn.Interrupt_Break else Exn.Interrupt_Breakdown;
fun check_interrupt exn =
  if Exn.is_interrupt_raw exn then make_interrupt (reset_interrupt ()) else exn;
fun capture f x = Res (f x) handle e => Exn (check_interrupt e);
```

So a raw `Thread.Thread.Interrupt` never reaches this `case`. It arrives as
`Interrupt_Break`, or, when the thread's break flag had already been consumed,
as `Interrupt_Breakdown`. And `is_interrupt_proper` is `raw orelse break`
(`exn.ML:116`): it **misses `Interrupt_Breakdown`**, while `is_interrupt` covers
both (`exn.ML:117`). Either form can mean that the assignment did not happen, so
both must be re-raised. The author's logs of this defect carried 239
`Interrupt_Breakdown` records against 11 `Option` events, so the form the narrower
predicate misses is not a corner case.

`Exn.reraise` rather than a bare `raise`: a bare one overwrites Poly/ML's raise
location and truncates the frame trace.

Note that `promise_name` (`future.ML:652` before the fix) already handles
`assign_result` raising an interrupt, so re-raising is within the existing
contract rather than a new obligation on callers.

### Why not re-raise everything

An earlier draft re-raised every non-`Fail` exception. `assign` can only raise
`Fail` or an interrupt, so the two forms behave the same. Both also re-raise an
interrupt that arrives in the brief window *after* the assignment has succeeded
(the inner `uninterruptible_body` restores the caller's interrupt attributes in
`with_attributes`, `thread_attributes.ML`, before its `Exn.release`), where the
old code carried on. The shipped form names the interrupt, which is the case
that was broken.

## Evidence

Diagnosed 2026-09-08 with a probe in `assign_result` that changed no semantics: it
recorded what had been dropped and still raised the same `Option`:

```
future_probe.log     10:37:34.941  assign_result UNASSIGNED swallowed=INTERRUPT
event_log/exception  10:37:35.232  exn="Option"  raised=Concurrent/future.ML:450
```

(`future.ML:450` is the line of the `the` call in the probed copy of `future.ML`;
in the release it is line 432.) Before the fix, a proof-replay workload hit this
within 9 minutes of starting. The wider "re-raise everything" draft was run
first: 15 consecutive passes (about 3 h 40 min) clean. The shipped form is
behaviourally identical on this path (only `Fail` and an interrupt can reach the
branch).

## Upstream

Not reported yet; Isabelle2024's `assign_result` has the same code. Worth
reporting together with the design question this fix does **not** settle: after
the re-raise the result variable is still unassigned, so a later
`Single_Assignment.await` on it would block forever. On the exposed paths no
caller can reach it: they all go through `value_result`, which raises before it
returns the future. The previous behaviour left the variable unassigned too, so
this is not a regression, but the thorough fix would assign
`Isabelle_Thread.interrupt_exn` as the result before propagating. That would
change Isabelle's concurrency semantics, so it is upstream's call.
