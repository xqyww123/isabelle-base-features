# isabelle-base-features

The base of the Isabelle feature-package chain for
[isabelle-patch-control](https://github.com/xqyww123/isabelle_patch_control): fixes to
Isabelle's sources that every other feature package builds on.

| Directory | conda package | The fix |
|---|---|---|
| [`expose_foreign/`](expose_foreign/) | `isabelle-expose-foreign` | Isabelle2025-2 hides Poly/ML's `Foreign`, `CInterface` and `RunCall` structures, so ML code cannot call C libraries; this makes them reachable again. |
| [`future_assign_interrupt/`](future_assign_interrupt/) | `isabelle-future-assign-interrupt` | An interrupt from a timeout or a cancelled future can show up as a misleading `exception Option`; with this it stays an interrupt. |

Each directory's `README.md` explains its fix. The README of isabelle-patch-control says how to
install feature packages, and its [`RELEASE.md`](https://github.com/xqyww123/isabelle_patch_control/blob/main/RELEASE.md)
how to release one.
