# expose_foreign: how it works

## What Isabelle2025-2 does

`src/Pure/ML/ml_name_space.ML` names four structures to hide from ML code:

```ml
val hidden_structures = ["CInterface", "Foreign", "RunCall", "Signal"];
```

Three of them exist in Poly/ML 5.9.2, the version Isabelle2025-2 ships: `Foreign` (Poly/ML's
foreign function interface, the FFI), `RunCall` (low-level access to ML values and memory) and
`Signal` (process signal handlers). `CInterface`, Poly/ML's old FFI, is no longer in Poly/ML, so
its name in the list changes nothing.

`src/Pure/ML_Bootstrap.thy` (line 25) runs
`List.app ML_Name_Space.forget_structure ML_Name_Space.hidden_structures`, which calls
`PolyML.Compiler.forgetStructure` on the global name space while Pure is bootstrapping. The
removal is baked into the `Pure` heap, so every session inherits it, and any ML file touching the
FFI fails to compile, with errors such as

```
Structure (Foreign) has not been declared
Structure (Memory) has not been declared in structure Foreign
```

There is no supported alternative: Poly/ML's FFI is `Foreign`. Isabelle2024 had
`hidden_structures = []`.

## What the feature changes

It removes `CInterface`, `Foreign` and `RunCall` from the list, leaving

```ml
val hidden_structures = ["Signal"];
```

`Signal` stays hidden: letting theory ML install process signal handlers is a bad idea. `RunCall`
cannot be left out either: it is how ML code reads raw words out of an ML value without copying,
which code that hands large ML data to a C library wants, so exposing only `Foreign` would not be
enough for such code.

The list feeds three other places, and all change with it:

- `ML_Bootstrap.thy` (lines 12-15) re-declares each listed structure inside the theory
  `ML_Bootstrap`'s own ML environment before line 25 forgets them globally; with the shorter list
  it re-declares only `Signal`.
- `ML_Bootstrap.thy` (line 25) forgets exactly the names still in the list, so `Foreign` and
  `RunCall` survive into the `Pure` heap.
- `bootstrap_structures = [...] @ hidden_structures`, and `sml_structure` is everything *not* in
  `bootstrap_structures`; dropping the names from `hidden_structures` therefore puts `Foreign` and
  `RunCall` back into the `SML` environment too, where Isabelle2024 had them.

## Consequences

Exposing the FFI means theory ML can call arbitrary native code, read and write raw memory
(`RunCall.loadWord`, `RunCall.storeWord`) and give any value any type (`RunCall.unsafeCast`), so
nothing stops it from forging a `thm`. Isabelle2024 permitted the same, but it is a guard rail
removed: only sessions that need `Foreign` should exercise it.
