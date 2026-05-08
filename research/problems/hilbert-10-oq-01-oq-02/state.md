# Current State

**Phase**: ACT
**Since**: 2026-05-08T20:30:00Z
**Iteration**: 12
**Last Updated**: 2026-05-08 (researcher-12)

## Current Focus

Iteration 12 (2026-05-08, researcher-12, this PR): **Σ₁ closed under
binary intersection (S11.2)** — the missing dual of iter 9's union
closure. Combined with iter 9, Σ₁ over ℚ is now closed under finite
Boolean combinations using ∪ and ∩ (NOT under complement, which would
collapse Σ₁ = Π₁).

**Witness** (sum-of-squares with variable packing):

    P(q, x) = (P₁(q, evenProj x))² + (P₂(q, oddProj x))²

where `evenProj x n = x (2*n)` and `oddProj x n = x (2*n+1)`. The two
polynomial constraints can simultaneously be witnessed by a single
`x : Nat → Rat` because they "see" disjoint slots of the variable
assignment. The forward direction interleaves witnesses for `S₁` and
`S₂` into a single `x = interleave x₁ x₂`; the reverse direction
splits a vanishing sum-of-squares into two vanishing squares (using
`mul_self_nonneg` over the LinearOrderedField ℚ + `linarith`) and
then individually into two zero polynomial values (`mul_eq_zero` over
ℚ as a NoZeroDivisors structure).

Two new theorems plus three private supporting structures:

1. `intersection_isDiophantineDefinition` — Σ₁ closed under binary
   intersection (main theorem).
2. `intersection_isUniversalExistentialDefinition` — corollary via Σ₁ ⊆ Π₂.

Private supporting:
- `private def evenProj`, `private def oddProj`, `private def interleave`
  — variable-packing infrastructure on `Nat → Rat` assignments.
- `private theorem evenProj_interleave`, `private theorem oddProj_interleave`
  — the section/inverse identities, pure Nat arithmetic via `omega`.

**Mathlib API surface**: 1 new lemma (`mul_self_nonneg`) and 1 new
tactic (`linarith`). Adds 2 imports:
- `Mathlib.Algebra.Order.Ring.Lemmas` (for `mul_self_nonneg`)
- `Mathlib.Tactic.Linarith` (for `linarith`)

**Net new content**: 3 definitions (private), 4 theorems (2 private +
2 public), 0 axioms, 0 sorries. **Updated total**: 15 definitions,
59 theorems, 1 axiom, 0 sorries, 1495 lines (was 1321).

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

## Build Status

Iteration 12 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`) so a
local Docker build would re-fresh-clone Mathlib (~45 min). The S11.2
content adds 2 imports:
- `Mathlib.Algebra.Order.Ring.Lemmas` (for `mul_self_nonneg : 0 ≤ a*a`
  in any LinearOrderedRing — ℚ is a LinearOrderedField so the instance
  applies).
- `Mathlib.Tactic.Linarith` (for `linarith` to discharge
  `a*a + b*b = 0 ∧ 0 ≤ a*a ∧ 0 ≤ b*b → a*a = 0 ∧ b*b = 0`).

The proof of `intersection_isDiophantineDefinition` uses:
- `mul_self_nonneg` (new)
- `linarith` (new)
- `mul_eq_zero` (already imported via S9)
- `ring` (Mathlib core via existing imports)
- `omega` (Lean core, no Mathlib needed) for the projection lemmas
  `evenProj_interleave` and `oddProj_interleave`.
- `if_pos` / `if_neg` (Lean core).
- `set ... with` (Lean core for variable abbreviation).

The corollary `intersection_isUniversalExistentialDefinition` is pure
term mode applying `diophantine_implies_universal_existential` to
`intersection_isDiophantineDefinition`. No new axioms.

**Confidence**: high. The Nat-arithmetic facts `(2*n) % 2 = 0`,
`(2*n) / 2 = n`, `(2*n+1) % 2 = 1`, `(2*n+1) / 2 = n` are all standard
and discharged by `omega`. The Mathlib lemma surfaces are a
one-line use each. CI is the ground truth.

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

None for the binary-intersection closure (S11.2, this iteration).
Remaining S11/12+ extensions:

- **S12.1**: List version of `intersection_isDiophantineDefinition` —
  the analog of `finUnionList_singletons_isDiophantineDefinition` for
  finite intersections of arbitrary Σ₁-definable sets (induction on a
  list, base case `True ↔ universe`, step via S11.2). Direct mirror of
  S10.3 but for the intersection direction. Useful as a corollary even
  though no concrete "finite intersection of singletons" is interesting
  (intersections of distinct singletons are empty).
- **S12.2**: De Morgan dualization — combine S11.2 with the Σ₁/Π₁
  duality and classical de Morgan to derive `union_isCoDiophantineDefinition`
  (Π₁ closed under binary union). Requires `not_and_or` or
  `Classical.em` reasoning. The witness can also be constructed
  directly as a sum-of-squares of complement witnesses, making this
  axiom-free up to classical excluded middle (already in scope from
  iter 7's `doubleNeg` lemmas).
- **S11.3**: Daans 2021 (10-quantifier reduction of Koenigsmann) as a
  separate axiomatized witness — adds 1 axiom, documentary value only.
- **S11.4**: Finset version of `finUnionList_singletons` —
  `finUnionFinset_singletons_isDiophantineDefinition (s : Finset Rat)`
  via `Finset.induction_on` (transports easily from the List version
  by `Finset.toList`).

## Next Action

Commit, push, create PR for iteration 12 (this).

If S11.2 lands cleanly, S12+ candidates (in priority order):

- **S12.1**: List version of `intersection_isDiophantineDefinition`.
- **S12.2**: De Morgan dualization to derive `union_isCoDiophantineDefinition`
  (Π₁ closed under binary union).
- **S11.3**: Daans 2021 (10-quantifier reduction of Koenigsmann) as a
  separate axiomatized witness — adds 1 axiom, documentary value only.
- **S11.4**: Finset version of `finUnionList_singletons`.

## Attempt Counts

- Total attempts: 12
- Current approach attempts: 1 (S11.2 — Σ₁ binary intersection closure
  via sum-of-squares + interleave)
- Approaches tried: 11 (S2 Σ₁/Π₁ duality, S3 Σ₂/Π₂ duality, S4 class
  congruence, S5 symmetric duality + trivial sets, S6 smallest
  non-trivial subset, S7 ¬¬-shadow, S8 arbitrary singletons, S9 binary
  union/intersection closure, S10 finite-list closure, S11.1 Π₁ ⊆ Π₂
  via polynomial inversion, S11.2 Σ₁ binary intersection via
  sum-of-squares)
