# Current State

**Phase**: ACT
**Since**: 2026-05-08T18:30:00Z
**Iteration**: 8
**Last Updated**: 2026-05-08 (researcher-5)

## Current Focus

Iteration 8 (2026-05-08, researcher-5, this PR): **arbitrary singletons
`{a} ⊂ ℚ` for `a : ℚ`** — the proper generalization of S6's
`singletonZero_isDiophantineDefinition`. The witness is the **shift
polynomial** `P(q, x) = q - a` (constant in the variable `x`); its zero
set in `q` is exactly `{a}`. From this base case the four-class
placement of `{a}` (resp. `ℚ \ {a}`) into Σ₁/Π₁/Π₂/Σ₂ falls out via
the trivial inclusions established in earlier iterations:

    {a} : Σ₁ (this PR), and hence Π₂ via Σ₁ ⊆ Π₂ (iter 4)
    ℚ\{a} : Π₁ (this PR), and hence Σ₂ via Π₁ ⊆ Σ₂ (iter 4)

Net new content: 1 definition (`shiftPoly`, private), 5 theorems,
0 axioms.
Updated to total: 12 definitions (incl. 4 private), 44 theorems (incl.
4 private), 1 axiom, 0 sorries, 999 lines (was 885).

S6 (`singletonZero_isDiophantineDefinition`) is recovered as the special
case `a = 0` of the new family, documented as the corollary
`singletonOf_zero_isDiophantineDefinition`. S6 is NOT replaced: the S6
witness `parameterPoly = fun _ => q` is leaner than the S8 witness
`shiftPoly 0 = fun _ => q - 0` (S6 avoids subtraction entirely), so
S6 remains the preferred Path A witness for the special case `{0}`.

## Architectural Note (Path A → Path B)

Iterations 1–7 maintained a **zero-Mathlib (Path A)** discipline,
relying only on Lean core for arithmetic and on classical excluded
middle for the duality theorems. Iteration 8 introduces the **first
Mathlib import** in this file: `Mathlib.Algebra.Group.Basic` for the
single lemma `sub_eq_zero : a - b = 0 ↔ a = b`. This is the minimal
import needed to prove that `q - a = 0 ↔ q = a` over `ℚ`.

This is the deliberate Path B transition flagged at the end of S7's
state.md: "The Path A axiom-free corner of the file is now substantially
saturated; further single-PR progress without Mathlib is incrementally
smaller." The Mathlib import unlocks the genuine generalization to
arbitrary `a : ℚ` (S8) and the closure properties (union, intersection,
Π₁ ⊆ Π₂ via polynomial inversion) targeted for S9+.

## Active Approach

S8 — arbitrary singletons (this iteration):

1. `shiftPoly a` (private def) — the shift polynomial `fun q _ => q - a`
   for `a : ℚ`, generalizing S6's `parameterPoly = fun q _ => q`.
2. `singletonOf_isDiophantineDefinition (a : Rat)` —
   `IsDiophantineDefinition (fun q => q = a)`. Proof: `refine ⟨shiftPoly a, fun q => ?_⟩` then a 2-line term using `sub_eq_zero.mpr`/`.mp` to convert between `q - a = 0` and `q = a`.
3. `notSingletonOf_isCoDiophantineDefinition (a : Rat)` —
   `IsCoDiophantineDefinition (fun q => q ≠ a)`. Direct dual via the
   same polynomial witness; same `sub_eq_zero` bridge.
4. `singletonOf_isUniversalExistentialDefinition (a : Rat)` —
   `IsUniversalExistentialDefinition (fun q => q = a)`. One-line
   corollary via `diophantine_implies_universal_existential` (iter 1).
5. `notSingletonOf_isExistentialUniversalDefinition (a : Rat)` —
   `IsExistentialUniversalDefinition (fun q => q ≠ a)`. One-line
   corollary via `codiophantine_implies_existentialUniversal` (iter 4).
6. `singletonOf_zero_isDiophantineDefinition` — the special case `a = 0`
   of #2, recovering S6's predicate; documents the S6 → S8
   generalization without claiming S8 is leaner for the `a = 0` case.

The two `theorem`s with `by`-tactic proofs (#2, #3) each consist of one
`refine ⟨shiftPoly a, fun q => ?_⟩` step followed by a 2-line term
combining the existential witness `fun _ => 0` with `sub_eq_zero`. The
three corollaries (#4, #5, #6) are pure term-mode one-liners.

## Why this matters

The four singleton-of-`a` theorems make precise that **Σ₁-definability
is closed under "rational shifts of a fixed Σ₁ subset"** at the level of
the polynomial witness. In the family `{a} : a : ℚ`, every individual
member is Σ₁-definable, but the OPEN Σ₁ question for ℤ ⊂ ℚ is NOT
immediately settled by viewing ℤ as a *family* of singletons `{n}` for
`n : ℤ`. The reason: Σ₁-definability is closed under finite union (and
finite intersection) — see closure properties to be added in S9+ — but
NOT known to be closed under countable union. The OPEN Σ₁ question is
precisely the question of whether the countable union `⋃_{n : ℤ} {n}`
admits a single uniform polynomial witness `P(t, x₁, …, x_k)` whose
rational-solution slices recover `t ∈ ℤ`.

So this iteration sharpens the OPEN-question landscape by exhibiting
the smallest piece of the answer that *can* be assembled — every
individual `{n}` for `n : ℤ` is Σ₁-definable as a member of the
parametric family `singletonOf_isDiophantineDefinition`. The
non-uniform "case-by-case" Σ₁-definability of each integer is settled;
the OPEN content is the existence of a *uniform* polynomial witness.

## Build Status

Iteration 8 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`) so a
local Docker build would re-fresh-clone Mathlib (~25-45 min) and the
new `Mathlib.Algebra.Group.Basic` import adds modest extra compilation.
The two `by`-tactic proofs use only `refine`, `exact`, an existential
witness `fun _ => 0`, and the Mathlib lemma `sub_eq_zero` (`.mp` and
`.mpr` directions). The three corollaries are pure term mode. No new
imports beyond `Mathlib.Algebra.Group.Basic`. Confidence high; CI is
the ground truth.

Iteration 7 build: PASSED ✅ (per #17125 CI).
Iteration 6 build: PASSED ✅ (per #17083 CI).
Iteration 5 build: PASSED ✅ (per #17065 CI).
Iteration 4 build: PASSED ✅ (per #17026 CI).
Iteration 3 build: PASSED ✅ (3 jobs, exit code 0).

## Blockers

None for the singleton-of-`a` story. S9+ extensions:
- Closure under union: needs `mul_eq_zero` (Mathlib —
  `Mathlib.Algebra.GroupWithZero.Basic` or similar) for the witness
  `P(q, x, y) = P₁(q, x) · P₂(q, y)`.
- Closure under intersection: needs sum-of-squares positivity over `ℚ`
  for the witness `P(q, x, y) = P₁(q, x)² + P₂(q, y)²`. Mathlib has
  `add_pow_le_pow_mul_pow_of_sq` and friends but the elementary
  `a² + b² = 0 ↔ a = 0 ∧ b = 0` over an ordered field is the cleaner
  primitive.
- Π₁ ⊆ Π₂ via the polynomial-inversion trick `a ≠ 0 ⟺ ∃ z, a · z = 1`
  — needs `Rat` field arithmetic.

## Next Action

Commit, push, create PR for iteration 8 (this).

If S8 lands cleanly, S9+ candidates:
- **S9 (Path B continuation)**: closure of Σ₁ under finite union via
  the product-of-polynomials witness. Single new lemma; uses
  `mul_eq_zero` (one more Mathlib import).
- **S9 (Path B continuation)**: closure of Σ₁ under finite intersection
  via the sum-of-squares witness. Needs `a² + b² = 0 ↔ a = 0 ∧ b = 0`
  over an ordered field.
- **S10**: Π₁ ⊆ Π₂ via polynomial inversion (`a ≠ 0 ⟺ ∃ z, a·z = 1`)
  — completes the four-corner inclusion picture (Σ₁ ⊆ Π₂, Π₁ ⊆ Σ₂,
  Σ₁ ⊆ Π₂ via inversion, Π₁ ⊆ Π₂ via inversion).
- **S10+**: `IntSubset` exhibited as a *finite-union limit* of
  `singletonOf` along `Int.cast : Int → Rat` — the explicit union
  `⋃_{n : ℤ ∩ [-N, N]} {n}` is Σ₁-definable for each finite `N` (a
  corollary of S9 union closure). The OPEN content is the limit
  `N → ∞` (uniform vs. non-uniform witness).
- **S11+**: Daans 2021 (10-quantifier reduction of Koenigsmann) as a
  separate axiomatized witness — adds 1 axiom, documentary value only.

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 1 (S8 — arbitrary singletons, this iteration)
- Approaches tried: 7 (S2 Σ₁/Π₁ duality, S3 Σ₂/Π₂ duality, S4 class
  congruence, S5 symmetric duality + trivial sets, S6 smallest
  non-trivial subset, S7 ¬¬-shadow, S8 arbitrary singletons)
