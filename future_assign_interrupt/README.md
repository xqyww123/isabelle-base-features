# future_assign_interrupt

In Isabelle2025-2, when a timeout (`Timeout.apply`) or the cancelling of a future interrupts
running code at the wrong moment, the interrupt can turn into `exception Option` and is itself
lost. This feature fixes that: a timeout or a cancellation no longer shows up as `exception Option`.

You need it if code that runs under timeouts, or cancels futures, fails now and then with

```
exception Option raised (line 84 of "General/basics.ML")
```

and nothing in your own code explains it.

Other feature packages build on this one, so it may have come in as a dependency.
[`details.md`](https://github.com/xqyww123/isabelle-base-features/blob/main/future_assign_interrupt/details.md)
explains the defect and the fix.
