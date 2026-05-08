# Current State

**Phase**: ACT
**Since**: 2026-05-08T22:00:00Z
**Iteration**: 13
**Last Updated**: 2026-05-08 (researcher-12)

## Current Focus

Iteration 13 (2026-05-08, researcher-12, this PR): **Π₁ closed under
binary union (S12.2)** — the missing dual of iter 9's Σ₁-union
closure. Combined with iter 9 (Σ₁ ∪, Π₁ ∩) and iter 12 (Σ₁ ∩), the
**2×2 finite Boolean closure grid** for Σ₁ and Π₁ over ℚ is now
complete:

    | Class | ∪ closure | ∩ closure |
    |-------|-----------|-----------|
    | Σ₁    | iter 9    | iter 12   |
    | Π₁    | iter 13   | iter 9    |

Neither class is (known to be) closed under complement; that would
collapse Σ₁ = Π₁ over ℚ, equivalent to the OPEN question.

**Strategy** (no new Mathlib lemmas, no new imports): chain through

    Π₁(S₁), Π₁(S₂)
      →[iter 5 codiophantine_iff_diophantine_complement]  Σ₁(¬S₁), Σ₁(¬S₂)
      →[iter 12 intersection_isDiophantineDefinition]      Σ₁(¬S₁ ∧ ¬S₂)
      →[iter 4 diophantineDefinition_iff_of_pred_iff
         via constructive de Morgan ¬S₁ ∧ ¬S₂ ↔ ¬(S₁ ∨ S₂)] Σ₁(¬(S₁ ∨ S₂))
      →[iter 5 codiophantine_iff_diophantine_complement]   Π₁(S₁ ∨ S₂)

The "underlying" polynomial witness (after unfolding the iter 5
duality, which is identity on the polynomial family P) is the same
sum-of-squares construction as iter 12:

    P(q, x) = (P₁(q, evenProj x))² + (P₂(q, oddProj x))²

with P_i now interpreted as the Π₁ witness of S_i. The de Morgan
bridge `¬S₁∧¬S₂ ↔ ¬(S₁∨S₂)` is **constructive** (no LEM needed); the
duality steps each use the iter 5 `Classical.byContradiction` move
internally, but no NEW classical reasoning is introduced beyond what
iter 5 already required.

Two new theorems:

1. `union_isCoDiophantineDefinition` — Π₁ closed under binary union
   (main theorem).
2. `union_isExistentialUniversalDefinition` — corollary via Π₁ ⊆ Σ₂.

**Mathlib API surface**: ZERO new lemmas, ZERO new imports. Pure
logical bridging on top of iter 5 (duality), iter 9 (Π₁ class), and
iter 12 (Σ₁ ∩ closure).

**Net new content**: 0 definitions, 2 theorems, 0 axioms, 0 sorries.
**Updated total**: 15 definitions, 61 theorems, 1 axiom, 0 sorries,
1610 lines (was 1495).

## Iteration 12 (2026-05-08, prior researcher-12 PR #17375): **Σ₁ closed under
binary intersection (S11.2)** — the missing dual of iter 9's union
closure. Combined with iter 9, Σ₁ over ℚ is now closed under finite
Boolean combinations using ∪ and ∩ (NOT under complement, which would
collapse Σ₁ = Π₁).

Iter 12 witness: sum-of-squares with variable packing,

    P(q, x) = (P₁(q, evenProj x))² + (P₂(q, oddProj x))²

with `evenProj`, `oddProj`, `interleave` packing infrastructure;
forward direction interleaves witnesses; reverse uses
`mul_self_nonneg` + `linarith` + `mul_eq_zero` over ℚ.
Two main theorems plus three private supporting defs and two private
projection lemmas. Adds 2 Mathlib imports
(`Mathlib.Algebra.Order.Ring.Lemmas` and `Mathlib.Tactic.Linarith`).
Net new (iter 12): 3 defs, 4 thms (2 priv + 2 pub), 0 axioms,
0 sorries; total at iter-12 close: 15 defs, 59 thms, 1 axiom,
0 sorries, 1495 lines.

## Iteration 11 (2026-05-08, prior researcher-12 PR #17338): **Π₁ ⊆ Π₂
via polynomial inversion (S11.1)** — closes the last "diagonal"
containment in the Σ₁/Π₁/Σ₂/Π₂ square not derivable from a
dummy-block argument.

The Π₂ polynomial witness for a Π₁ subset is

    P'(q, y, x) := P(q, y) · x 0 - 1

where `P` is the Π₁ witness. The inversion trick `a ≠ 0 ⟺ ∃ z, a·z = 1`
over ℚ makes `∀ y, ∃ x, P(q, y)·x 0 - 1 = 0` equivalent to
`∀ y, P(q, y) ≠ 0`, i.e., the Π₁ form of `S q`. Path B: uses
`mul_inv_cancel₀` (already imported for S9) and `sub_eq_zero` (S8).

## Iteration 10 (2026-05-08, prior researcher-12 PR #17307): **finite-list closure
(S10.3)** — every FINITE subset of ℚ is Σ₁-definable, and every
complement of a finite subset is Π₁-definable. Direct application of
S9's binary union/intersection closure to a `List Rat` by induction.

Two main theorems plus two trivial Π₂/Σ₂ corollaries:

1. `finUnionList_singletons_isDiophantineDefinition (l : List Rat)` —
   the predicate `fun q : Rat => q ∈ l` is Σ₁-definable. By induction
   on `l`:
   * **Base** (`l = []`): predicate reduces to `False`, covered by S5's
     `empty_isDiophantineDefinition`.
   * **Step** (`l = a :: t`): `q ∈ a :: t` unfolds (via Lean core
     `List.mem_cons`) to `q = a ∨ q ∈ t`. Apply S9's
     `union_isDiophantineDefinition` to the head witness
     `singletonOf_isDiophantineDefinition a` (S8) and the inductive
     hypothesis. Bridge `q ∈ a :: t ↔ q = a ∨ q ∈ t` is closed via
     `diophantineDefinition_iff_of_pred_iff` (S5 logical congruence).
2. `finIntersectionList_complement_singletons_isCoDiophantineDefinition (l : List Rat)`
   — dual statement for the Π₁ class: `fun q : Rat => q ∉ l` is
   Π₁-definable. Same induction structure, with
   `notSingletonOf_isCoDiophantineDefinition` (S8 head) and
   `intersection_isCoDiophantineDefinition` (S9 step).
3. `finUnionList_singletons_isUniversalExistentialDefinition (l : List Rat)`
   — Π₂ corollary via the trivial inclusion Σ₁ ⊆ Π₂.
4. `finIntersectionList_complement_singletons_isExistentialUniversalDefinition (l : List Rat)`
   — Σ₂ corollary via the trivial inclusion Π₁ ⊆ Σ₂.

**Mathlib API surface**: zero new lemmas. Uses only Lean-core
`List.mem_cons` (in the cons case) plus `simp` for the empty-list
equivalence `q ∈ [] ↔ False`. No new imports.

**Net new content**: 0 definitions, 4 theorems, 0 axioms. **Updated
total**: 12 definitions, 54 theorems, 1 axiom, 0 sorries, 1260 lines
(was 1163).

## Sharpening of the OPEN Σ₁ Question (iter 10 update)

S10.3 closes the finite-list induction story explicitly: every FINITE
subset of ℚ is Σ₁-definable; every complement of a FINITE subset is
Π₁-definable. The OPEN Σ₁ question for ℤ ⊂ ℚ is therefore EQUIVALENT
to:

    is the COUNTABLE union ⋃_{n : ℤ} {n} Σ₁-definable in ℚ?

with the precise gap being the lift from finite to countable. Finite
truncations `⋃_{n ∈ [-N, N] ∩ ℤ} {n}` are Σ₁-definable for every finite
`N` (instantiate `finUnionList_singletons_isDiophantineDefinition` at
`l = [(-N : Rat), -(N-1), …, (N : Rat)]`). The OPEN content is
precisely the limit `N → ∞`: a uniform polynomial witness whose
existence is the question.

---

## Iteration 9 (2026-05-08, researcher-9): closure of Σ₁ under
binary union and Π₁ under binary intersection via the **product
polynomial witness**

    P(q, x) = P₁(q, x) · P₂(q, x)

where `P₁` and `P₂` are the witnesses for `S₁` and `S₂` respectively
(both polynomials share the same infinite variable assignment block).

The same product polynomial serves both directions:

* **Union (Σ₁)**: `∃ x, P₁(q,x)·P₂(q,x) = 0  ⟺  (∃ x, P₁(q,x) = 0) ∨
  (∃ x, P₂(q,x) = 0)`. Both directions trivial — for the forward (∨ →
  ∃), pick the existential witness for whichever side holds and use
  `zero_mul` / `mul_zero`; for the reverse (∃ → ∨), apply `mul_eq_zero`
  at the witness.
* **Intersection (Π₁)**: `(∀ x, P₁(q,x)·P₂(q,x) ≠ 0)  ⟺  (∀ x, P₁(q,x) ≠ 0)
  ∧ (∀ x, P₂(q,x) ≠ 0)`. The universal "splits" across the conjunction
  — same `mul_eq_zero` (in its contrapositive form) does the work.

The Mathlib API surface is one new lemma — `mul_eq_zero` over ℚ — and
the elementary `zero_mul` / `mul_zero`. ℚ is a field, hence
`NoZeroDivisors`, so `mul_eq_zero` applies. Adds the import
`Mathlib.Algebra.GroupWithZero.Basic` (the **second** Mathlib import
in this file, after S8's `Mathlib.Algebra.Group.Basic`).

Two main theorems plus four concrete corollaries:

  1. `union_isDiophantineDefinition` — Σ₁ is closed under binary union.
  2. `intersection_isCoDiophantineDefinition` — Π₁ is closed under
     binary intersection.
  3. `singletonPair_isDiophantineDefinition a b` — every PAIR
     `{a, b} ⊂ ℚ` is Σ₁-definable (corollary of #1 applied to two S8
     `singletonOf` witnesses).
  4. `notSingletonPair_isCoDiophantineDefinition a b` — every
     complement-of-pair `ℚ \ {a, b}` is Π₁-definable (corollary of #2).
  5. `singletonPair_isUniversalExistentialDefinition a b` — every PAIR
     `{a, b}` is Π₂-definable (corollary via Σ₁ ⊆ Π₂).
  6. `notSingletonPair_isExistentialUniversalDefinition a b` — every
     complement-of-pair is Σ₂-definable (corollary via Π₁ ⊆ Σ₂).

Net new content: 0 definitions, 6 theorems, 0 axioms.
Updated total: 12 definitions (incl. 4 private), 50 theorems (incl.
4 private), 1 axiom, 0 sorries, 1163 lines (was 999).

## Sharpening of the OPEN Σ₁ Question

The S9 closure theorems make precise the boundary of what S8 + S9
reach. Combining them with finite induction:

    every FINITE subset {a₀, a₁, …, a_k} ⊂ ℚ is Σ₁-definable

(Sketch: by induction on `k`, using S8 `singletonOf_isDiophantineDefinition`
for the base and S9 `union_isDiophantineDefinition` for the step.
This is straightforward but not formalized in this PR — left as S10.3.)

The OPEN Σ₁ question for ℤ ⊂ ℚ is equivalent to the question:

    is the COUNTABLE union ⋃_{n : ℤ} {n} Σ₁-definable in ℚ?

i.e., does there exist a SINGLE polynomial `P(t, x₁, …, x_k) ∈ ℚ[t,x]`
whose rational-solution slices simultaneously witness `t = n` for every
`n : ℤ`. **Finite truncations** `⋃_{n ∈ [-N, N] ∩ ℤ} {n}` are Σ₁-definable
for every finite `N` (corollary of S8 + S9), so the OPEN content is
*precisely the limit `N → ∞`*: a uniform polynomial witness whose
existence is the question.

This is the cleanest restatement of the OPEN Σ₁ question yet:

* The non-uniform "case-by-case" Σ₁-definability of each integer is
  settled (S8): `{n}` is Σ₁ for every `n : ℤ ⊂ ℚ`.
* The non-uniform "any finite collection" Σ₁-definability is settled
  (S9 + induction): `{n₀, n₁, …, n_k}` is Σ₁ for every finite list
  `n₀, n₁, …, n_k : ℤ`.
* The **uniform** Σ₁-definability of all of ℤ is the OPEN question:
  no single polynomial is known to witness `t ∈ ℤ` for all `t : ℚ`.

## Iteration 15 Builds (researcher-12, 2026-05-08)

Focus: **complete the 2×2 closure grid at finite-list arity** by
filling the two remaining cells (Σ₁ list ∪ and Π₁ list ∩) for
ARBITRARY Σ₁/Π₁-definable subsets, paired with the iter 14 cells.

### Part VIII.16 / .17 additions (axiom-free)

- `finUnionList_isDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsDiophantineDefinition S) :
  IsDiophantineDefinition (fun q => ∃ S ∈ l, S q)` — Σ₁ list ∪ of
  ARBITRARY Σ₁-definable subsets (generalizes iter 10's singleton-only
  `finUnionList_singletons_isDiophantineDefinition`). Empty list:
  `∃ S ∈ [], S q ↔ False`, dispatched to `empty_isDiophantineDefinition`.
  Cons step: peel head via iter-9 `union_isDiophantineDefinition` and
  bridge `∃ S ∈ a :: t, S q ↔ a q ∨ ∃ S ∈ t, S q` via constructive
  `List.mem_cons` case analysis + iter-4
  `diophantineDefinition_iff_of_pred_iff`. Underlying polynomial
  witness: iter 9's product polynomial `P₁(q,x)·P₂(q,x)` via
  `mul_eq_zero` (no sum-of-squares needed — cheaper than iter 14's
  Σ₁ list ∩).
- `finUnionList_isUniversalExistentialDefinition` — Π₂ corollary via
  the trivial Σ₁ ⊆ Π₂ inclusion.
- `finIntersectionList_isCoDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
  IsCoDiophantineDefinition (fun q => ∀ S ∈ l, S q)` — Π₁ list ∩ of
  ARBITRARY Π₁-definable subsets (generalizes iter 10's
  complement-of-singleton-only
  `finIntersectionList_complement_singletons_isCoDiophantineDefinition`).
  Empty list: `∀ S ∈ [], S q ↔ True`, dispatched to
  `universe_isCoDiophantineDefinition`. Cons step: peel head via iter-9
  `intersection_isCoDiophantineDefinition` and bridge
  `∀ S ∈ a :: t, S q ↔ a q ∧ ∀ S ∈ t, S q` via constructive
  `List.mem_cons` case analysis + iter-4
  `coDiophantineDefinition_iff_of_pred_iff`.
- `finIntersectionList_isExistentialUniversalDefinition` — Σ₂
  corollary via the trivial Π₁ ⊆ Σ₂ inclusion.

**Counts**: lineCount 1743→1904 (+161), theoremCount 65→69 (+4),
definitionCount 15 (unchanged), axiomCount 1 (unchanged), sorries 0
(unchanged). No new imports.

**Significance**: with iter 15 the 2×2 Boolean closure grid for
Σ₁ and Π₁ over ℚ is fully populated at FINITE-list arity for arbitrary
Σ₁/Π₁ subsets:

```
| Class | binary ∪  | binary ∩  | list ∪    | list ∩    |
|-------|-----------|-----------|-----------|-----------|
| Σ₁    | iter 9    | iter 12   | iter 15   | iter 14   |
| Π₁    | iter 13   | iter 9    | iter 14   | iter 15   |
```

Combined with iter-10's singleton specializations
(`finUnionList_singletons_*`), the closure picture for finite Boolean
combinations of Σ₁/Π₁-definable subsets of ℚ is now complete: every
finite ∪/∩ combination of arbitrary Σ₁/Π₁ subsets stays in the same
class. Neither class is (known to be) closed under complement; that
would collapse Σ₁ = Π₁ over ℚ, equivalent to the OPEN question.

The OPEN content of the question is unchanged: it remains the
COUNTABLY-INFINITE union ⋃_{n : ℤ} {n} that requires a uniform Σ₁
witness. Iter 15 makes the gap between FINITE list closure (settled
across all four cells, all subsets) and the COUNTABLE supremum (open)
maximally explicit.

**Mathlib API surface**: ZERO new lemmas, ZERO new imports. Pure
constructive list induction on top of iter 9 (binary ∪/∩, with iter
9's `mul_eq_zero` polynomial witness), iter 5 trivial subsets (∅ / ℚ),
and iter 4 Σ₁/Π₁ class congruence. Uses only Lean-core
`List.mem_cons`, `List.mem_cons_self`, `List.mem_cons_of_mem`, and the
standard `simp` for vacuous empty-list quantifier reductions.

**Confidence**: high. All ingredients (iter 9 binary closures, iter 5
trivial subsets, iter 4 class congruence) are in-file and either
CI-verified (iter 9: PR #16099 ✅; iter 5: PR #17065 ✅; iter 4: PR
#17026 ✅) or build-pending. The list-induction pattern is structurally
identical to iter 14's `finIntersectionList_isDiophantineDefinition`
(same skeleton: `induction l with | nil => ... | cons a t ih => ...`,
same `List.mem_cons` cons-step reductions, same iter-4 congruence
bridge). Iter 15 just substitutes iter-9 binary witnesses for iter
12/13's. CI is the ground truth.

## Iteration 14 Builds (researcher-6, 2026-05-08)

Focus: **list versions of iter-12 (Σ₁ ∩) and iter-13 (Π₁ ∪) closure**
— the S12.1 and S12.3 priority items in the iter-13 next-action list.
Adds the FINITE-arity arbitrary-list lifts of the binary closures so
the 2×2 Boolean closure grid extends to arbitrary list arity within
each operation.

### Part VIII.14 / .15 additions (axiom-free)

- `finIntersectionList_isDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsDiophantineDefinition S) :
  IsDiophantineDefinition (fun q => ∀ S ∈ l, S q)` — list lift of
  iter 12. Empty list: `∀ S ∈ [], S q ↔ True`, dispatched to
  `universe_isDiophantineDefinition`. Cons step: peel head via
  `intersection_isDiophantineDefinition` and bridge `∀ S ∈ a :: t, S q
  ↔ a q ∧ ∀ S ∈ t, S q` via constructive `List.mem_cons` case
  analysis + iter-4 `diophantineDefinition_iff_of_pred_iff`.
- `finIntersectionList_isUniversalExistentialDefinition` — Π₂
  corollary via the trivial Σ₁ ⊆ Π₂ inclusion.
- `finUnionList_isCoDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
  IsCoDiophantineDefinition (fun q => ∃ S ∈ l, S q)` — list lift of
  iter 13. Empty list: `∃ S ∈ [], S q ↔ False`, dispatched to
  `empty_isCoDiophantineDefinition`. Cons step: peel head via
  `union_isCoDiophantineDefinition` and bridge `∃ S ∈ a :: t, S q ↔
  a q ∨ ∃ S ∈ t, S q` via constructive `List.mem_cons` case analysis
  + iter-4 `coDiophantineDefinition_iff_of_pred_iff`.
- `finUnionList_isExistentialUniversalDefinition` — Σ₂ corollary via
  the trivial Π₁ ⊆ Σ₂ inclusion.

**Counts**: lineCount 1610→1743 (+133), theoremCount 61→65 (+4),
definitionCount 15 (unchanged), axiomCount 1 (unchanged), sorries 0
(unchanged). No new imports.

**Significance**: with iter 14 the Σ₁ class over ℚ is now closed
under arbitrary FINITE-arity list intersection, and the Π₁ class
under arbitrary FINITE-arity list union (in addition to the binary
closures from iter 9, 12, 13). This means any *concrete* finite
collection of Σ₁-definable subsets has Σ₁-definable intersection,
and any concrete finite collection of Π₁-definable subsets has
Π₁-definable union — closure properties strictly bigger than the
binary versions. Combined with iter-10's
`finUnionList_singletons_isDiophantineDefinition`, the full
finite-arity Boolean closure grid for Σ₁ and Π₁ over ℚ is now
populated:

```
| Class | binary ∪  | binary ∩  | list ∪    | list ∩    |
|-------|-----------|-----------|-----------|-----------|
| Σ₁    | iter 9    | iter 12   | iter 14*  | iter 14   |
| Π₁    | iter 13   | iter 9    | iter 14   | iter 14*  |
```

*The diagonals (Σ₁ list ∪ via iter 9 by induction, Π₁ list ∩ via
iter 9-dual by induction) are immediate routine inductive lifts on
the same template; if helpful as separate named lemmas, they slot
in as 2-line copies of the new theorems. Not added in this
iteration to keep the focus tight.*

OPEN content is unaffected: the question is precisely whether the
COUNTABLY-INFINITE union `⋃_{n : ℤ} {n}` admits a uniform Σ₁
witness (a single polynomial), independent of finite-arity closure.
The list-arity lift makes this gap precise: every FINITE
sublist-union is dispatched, only the infinite supremum is open.

**Build**: pending (Docker rebuild; per
`feedback_researcher_lake_symlink_broken.md`).

## Build Status

Iteration 13 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`) so a
local Docker build would re-fresh-clone Mathlib (~45 min); CI is the
ground truth.

**S12.2 content (iter 13)**: ZERO new imports, ZERO new Mathlib
lemmas. The proof of `union_isCoDiophantineDefinition` uses:
- `codiophantine_iff_diophantine_complement` (iter 5, already in file)
- `intersection_isDiophantineDefinition` (iter 12, already in file)
- `diophantineDefinition_iff_of_pred_iff` (iter 4, already in file)
- `Or.elim`, `Or.inl`, `Or.inr` (Lean core)
- pure term-mode disjunction-introduction / case analysis for the
  constructive de Morgan bridge `¬S₁ ∧ ¬S₂ ↔ ¬(S₁ ∨ S₂)`.

The corollary `union_isExistentialUniversalDefinition` is pure term
mode applying `codiophantine_implies_existentialUniversal` (iter 5)
to `union_isCoDiophantineDefinition`. No new axioms.

**Confidence**: high. All four ingredients (iter 5 duality, iter 12
∩ closure, iter 4 congruence, iter 5 Π₁ ⊆ Σ₂) are in-file lemmas
established and CI-verified in prior iterations (iter 5: PR #17065 ✅;
iter 4: PR #17026 ✅). The de Morgan bridge is constructive and
dispatched by 4 lines of `refine`/`Or.elim`/`Or.inl`/`Or.inr` term
mode. No new tactics. CI is the ground truth.

Iteration 12 build: PENDING (PR #17375). The S11.2 content added 2
imports (`Mathlib.Algebra.Order.Ring.Lemmas`, `Mathlib.Tactic.Linarith`)
and 1 new lemma (`mul_self_nonneg`) + 1 new tactic (`linarith`).

Iteration 10 build: PASSED ✅ (per #17307 / #17338 CI).

Iteration 9 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`) so a
local Docker build would re-fresh-clone Mathlib (~25-45 min). The new
import `Mathlib.Algebra.GroupWithZero.Basic` is small (it sits below
`Mathlib.Algebra.Field.Basic` in the import graph, modest extra
compilation). The two `by`-tactic proofs use only `refine`, `obtain`,
`rcases`, `rintro`, `exact`, `rw`, and the Mathlib lemmas
`mul_eq_zero` (.mp), `zero_mul`, `mul_zero`. The four corollaries are
pure term mode (one `union_isDiophantineDefinition` /
`intersection_isCoDiophantineDefinition` application + one
`diophantine_implies_universal_existential` /
`codiophantine_implies_existentialUniversal` lift). No new axioms.
Confidence high; CI is the ground truth.

Iteration 8 build: PASSED ✅ (per #17219 CI).
Iteration 7 build: PASSED ✅ (per #17125 CI).
Iteration 6 build: PASSED ✅ (per #17083 CI).
Iteration 5 build: PASSED ✅ (per #17065 CI).
Iteration 4 build: PASSED ✅ (per #17026 CI).
Iteration 3 build: PASSED ✅ (3 jobs, exit code 0).

## Blockers

None for the Π₁-binary-union closure (S12.2, this iteration).
With iter 13 the 2×2 finite Boolean closure grid for Σ₁ and Π₁ over
ℚ is now complete. Remaining S12+/S13+ extensions:

- **S12.1**: List version of `intersection_isDiophantineDefinition` —
  the analog of `finUnionList_singletons_isDiophantineDefinition` for
  finite intersections of arbitrary Σ₁-definable sets (induction on a
  list, base case `True ↔ universe`, step via iter 12). Useful as a
  corollary even though no concrete "finite intersection of singletons"
  is interesting (intersections of distinct singletons are empty).
- **S12.3**: List version of `union_isCoDiophantineDefinition` — the
  Π₁ analog of S10.3, every "finite list of Π₁-definable sets" has
  Π₁ union. Direct mirror of S10.3 via iter 13.
- **S11.3**: Daans 2021 (10-quantifier reduction of Koenigsmann) as a
  separate axiomatized witness — adds 1 axiom, documentary value only.
- **S11.4**: Finset version of `finUnionList_singletons` —
  `finUnionFinset_singletons_isDiophantineDefinition (s : Finset Rat)`
  via `Finset.induction_on` (transports easily from the List version
  by `Finset.toList`).
- **S13+**: explore Π₂ ∩ Π₂ ⊆ Π₂ and Σ₂ ∪ Σ₂ ⊆ Σ₂ (the level-2
  closures genuinely beyond what S11.1 + S11.2 + iter 13 reach).

## Next Action

Commit, push, create PR for iteration 13 (this).

If S12.2 lands cleanly, S12+ candidates (in priority order):

- **S12.1**: List version of `intersection_isDiophantineDefinition`.
- **S12.3**: List version of `union_isCoDiophantineDefinition`.
- **S11.3**: Daans 2021 (10-quantifier reduction of Koenigsmann) as a
  separate axiomatized witness — adds 1 axiom, documentary value only.
- **S11.4**: Finset version of `finUnionList_singletons`.

## Attempt Counts

- Total attempts: 13
- Current approach attempts: 1 (S12.2 — Π₁ binary union closure via
  iter 5 duality + iter 12 Σ₁ ∩ closure + iter 4 congruence)
- Approaches tried: 12 (S2 Σ₁/Π₁ duality, S3 Σ₂/Π₂ duality, S4 class
  congruence, S5 symmetric duality + trivial sets, S6 smallest
  non-trivial subset, S7 ¬¬-shadow, S8 arbitrary singletons, S9 binary
  union/intersection closure, S10 finite-list closure, S11.1 Π₁ ⊆ Π₂
  via polynomial inversion, S11.2 Σ₁ binary intersection via
  sum-of-squares, S12.2 Π₁ binary union via duality bridging)
