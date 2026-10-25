# expose_foreign

Isabelle2025-2 hides the Poly/ML structures `Foreign` (calling C libraries) and `RunCall`
(low-level memory access) from ML code; Isabelle2024 did not. This feature makes them reachable
again.

You need it if Isabelle2025-2 rejects your ML code with an ML error that says

```
Structure (Foreign) has not been declared
```

or the same for `RunCall`. With them, ML code in a theory can call C code and read and write raw
memory, which Isabelle2025-2 otherwise prevents.

Other feature packages build on this one, so it may have come in as a dependency.
[`details.md`](https://github.com/xqyww123/isabelle-base-features/blob/main/expose_foreign/details.md)
explains how it works.
