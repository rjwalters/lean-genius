# Current State

**Phase**: ACT
**Since**: 2026-05-08T18:30:00Z
**Iteration**: 9
**Last Updated**: 2026-05-08 (researcher-9)

## Current Focus

Iteration 9 (2026-05-08, researcher-9, this PR): **closure of Σ₁ under
binary union and Π₁ under binary intersection** via the **product
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

None for the binary-union / binary-intersection story. S10+ extensions:

- **S10.1**: Π₁ ⊆ Π₂ via the polynomial-inversion trick `a ≠ 0 ⟺ ∃ z, a·z = 1`
  — needs `Rat` field arithmetic (`mul_inv`, `mul_inv_cancel` from
  Mathlib's field library).
- **S10.2**: Σ₁ closure under binary INTERSECTION via sum-of-squares
  witness `P(q, x, y) = P₁(q, x)² + P₂(q, y)²`. Requires:
  (a) `a² + b² = 0 ↔ a = 0 ∧ b = 0` over an ordered field (Mathlib has
  this via `add_sq_eq_zero_iff_of_nonneg` and friends);
  (b) a packing-trick to use disjoint variable indices for `x` and `y`,
  since the SAME variable assignment block won't work for intersection
  (where we need both factors to vanish at the SAME polynomial value).
- **S10.3**: `finUnion_singletons_isDiophantineDefinition` — by induction
  on a finite list of rationals (extending S9's binary pair to `k`-tuple),
  every FINITE subset of ℚ is Σ₁-definable. Makes precise the
  uniform/non-uniform boundary discussed above.

## Next Action

Commit, push, create PR for iteration 9 (this).

If S9 lands cleanly, S10+ candidates (in priority order):

- **S10.1**: Π₁ ⊆ Π₂ via polynomial inversion (`a ≠ 0 ⟺ ∃ z, a·z = 1`).
- **S10.2**: Σ₁ closure under finite INTERSECTION via sum-of-squares.
- **S10.3**: `finUnion_singletons_isDiophantineDefinition` — every
  finite subset of ℚ is Σ₁-definable (corollary of S8 + S9 by induction).
- **S10.4**: Daans 2021 (10-quantifier reduction of Koenigsmann) as a
  separate axiomatized witness — adds 1 axiom, documentary value only.

## Attempt Counts

- Total attempts: 9
- Current approach attempts: 1 (S9 — binary union/intersection closure)
- Approaches tried: 8 (S2 Σ₁/Π₁ duality, S3 Σ₂/Π₂ duality, S4 class
  congruence, S5 symmetric duality + trivial sets, S6 smallest
  non-trivial subset, S7 ¬¬-shadow, S8 arbitrary singletons, S9 binary
  union/intersection closure)
