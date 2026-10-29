# fast_abbrev_printing: the cause and the fix

A speed fix, not a capability: with it Isabelle prints exactly the same text, sooner.

## The cause

When Isabelle prints a term, its `uncheck` phase runs `Proof_Context.contract_abbrevs`
(`src/Pure/Isar/proof_context.ML`), which turns every subterm that is the expansion of an
abbreviation back into the abbreviation. It uses the context's reverted abbreviations: the rules
from an abbreviation's expansion back to the abbreviation, kept per print mode in `Consts`. For
each subterm it retrieves candidates among them and tries them in order with `Pattern.match_rew`;
the first that matches is used. Isabelle2025-2 retrieves by unification (`Item_Net.retrieve`; the
matching retrieval would be `Item_Net.retrieve_matching`):

```sml
val nets = Consts.revert_abbrevs consts (print_mode_value () @ [""]);
val rew = Option.map #1 oo Pattern.match_rew thy;
fun match_abbrev t = get_first (fn net => get_first (rew t) (Item_Net.retrieve net t)) nets;
```

The reverted abbreviations sit in an `Item_Net` over Pure's discrimination net `Net`, which keys
every λ-abstraction as a wildcard, and unification retrieval treats a λ-abstraction in the subterm
as a wildcard too. So at every λ-abstraction of the printed term every reverted abbreviation is a
candidate. In a locale context every constant defined in a locale is a local abbreviation, once for
each instance of that locale in scope, so such a context holds thousands of reverted abbreviations:
2,544 in the default print mode in the locale `Simple_Network_Impl_nat_ceiling_start_state` of the
AFP entry Munta_Model_Checker. Contracting each of 1,259 statements there once visits 203,502
subterms, 10,738 of them λ-abstractions, and retrieves 27.4 million candidates for 5,022 matches.
In the five AFP locale contexts measured, contraction took more than 90% of the printing time.

Isabelle2024 retrieved by matching unless the subterm could beta-eta contract; Isabelle2025
retrieves by unification for every subterm. Matching retrieval on `Net` misses candidates at a
subterm that could beta-eta contract; iNet's matching retrieval normalises the subterm and misses
none.

## The fix

- `src/Pure/improved_net.ML` (new): iNet, the improved discrimination net of
  [Performant_Isabelle_ML](https://github.com/xqyww123/Performant_Isabelle_ML)
  (`library/improved_net.ML` at commit 637990c, byte for byte), whose matching retrieval
  discriminates λ-abstractions by their bodies. Its header lists how it differs from `Net` and
  states the retrieval contract.
- `src/Pure/item_net.ML`: `Item_Net` becomes a functor of the net, its body unchanged.
  `structure Item_Net = Item_Net(Net)` is the stock structure; `structure Item_iNet =
  Item_Net(iNet)` is new.
- `src/Pure/consts.ML`: the reverted abbreviations of each print mode are kept in an `Item_iNet`.
  The new `Consts.retrieve_abbrevs`, with the name and type of Isabelle2024's, returns a
  subterm's matching candidates, mode by mode in the order given. `Consts.revert_abbrevs` keeps
  its type and returns copies as `Item_Net`s with the same content, for its other caller in the
  distribution (`src/HOL/Library/Time_Commands.ML`) and any other code.
- `src/Pure/Isar/proof_context.ML`: `contract_abbrevs` retrieves through
  `Consts.retrieve_abbrevs`.
- `src/Pure/ROOT.ML`: loads `improved_net.ML` after `envir.ML` (iNet normalises with `Envir`) and
  moves `item_net.ML` after it (`Item_iNet` needs iNet).

## Why the printed text does not change

`contract_abbrevs` uses the first candidate that `Pattern.match_rew` accepts. The stock and the
patched retrieval both return every candidate it accepts, in the same order:

- the stock one, because unification retrieval returns every candidate that could match;
- the patched one, because `Pattern.match_rew` accepts only a subterm that is beta-eta equal to an
  instance of the candidate's pattern, and iNet's matching retrieval returns every such candidate;
- in the same order, because `Item_Net` and `Item_iNet` are the same code run through the same
  operations with the same equality, both nets decide membership and deletion alike (each finds an
  item through its own pattern), and both retrievals sort by the items' serial numbers.

Either retrieval may also return candidates that the other does not; `Pattern.match_rew` rejects
them. So the first accepted candidate, the contracted term and the printed text are the stock
ones.

## Tests

`tests/ROOT` describes the four test sessions. Their golden files, recorded on Isabelle without
this patch, match byte for byte on the patched one; at each of the 3.3 million subterms the
contraction visits in them, the stock and the patched retrieval give the same accepted candidates
in the same order; and each of eight one-line mutations of the patch's code outside iNet, and four
of iNet's internals, makes them fail.

## What it costs

- Declaring a constant or an abbreviation in a locale context with many reverted abbreviations is
  a little slower: the declaration merges the context's reverted abbreviations with the theory's,
  and iNet answers the merge's membership checks more slowly where patterns hold λ-abstractions.
  One merge in the Munta_Model_Checker context above took 81 ms instead of 13 ms; in the other
  contexts measured, at most 9 ms more by the minimum of seven runs (one context varied too much
  to tell).
- Opening such a context, estimated by the time to insert its own reverted abbreviations: 93 ms
  more in that context, whose opening takes 31.6 s; at most 5 ms more in the other contexts
  measured.
- `Consts.revert_abbrevs` builds its copies anew on every call: at most 15 ms per print mode in
  that context.
- Heap images: Pure +0.35%, HOL +0.71%, HOL-Algebra +2.27%.

## What it adds to Pure

`iNet` (signature `INET`), the functor `Item_Net`, `Item_iNet` and `Consts.retrieve_abbrevs` are
new names of Pure; code that uses them needs this package. ML that uses iNet should keep loading
Performant_Isabelle_ML: on an Isabelle with this package such code also compiles when it does not
load Performant_Isabelle_ML, because Pure has its own copy of iNet, and it then fails on an
Isabelle without this package.

## Measurements

Contraction in AFP locale contexts on stock Isabelle2025-2, with an `Item_iNet` built in ML beside
a stock `Item_Net` of the same content; 1,259–1,430 statements each, wall ms, one run each:

| locale (AFP entry) | stock | patched |
|---|---|---|
| `Simple_Network_Impl_nat_ceiling_start_state` (Munta_Model_Checker) | 16,553 | 475 |
| `grounded_superposition_calculus` (Superposition_Calculus) | 2,365 | 93 |
| `Simulation_Invariants` (Timed_Automata, opened in Munta_Certificate_Checker) | 1,784 | 78 |
| `composite_equivalence_of_bicategories` (Bicategory) | 1,915 | 115 |
| `padic_fields` (Padic_Field) | 1,481 | 134 |

Contraction on the patched Isabelle, every named fact of each context, minimum of five runs (wall
ms); stock is the stock unification retrieval over the copies that `Consts.revert_abbrevs`
returns, run beside the patched one:

| context | statements | stock | patched |
|---|---|---|---|
| HOL-Algebra's theories | 7,792 | 2,048 | 364 |
| `UnivPoly.UP_pre_univ_prop` | 4,778 | 1,863 | 204 |
| `Fields.linordered_field` | 2,810 | 326 | 100 |
| `Ring.ring` | 1,378 | 429 | 81 |
| `Orderings.linorder` | 696 | 130 | 24 |
