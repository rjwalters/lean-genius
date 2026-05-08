# Current State

**Phase**: ACT
**Since**: 2026-05-08T03:30:00Z
**Iteration**: 2

## Current Focus

Adding the Σ₁/Π₁ duality layer to the existing Σ₁ vs Π₂ framework. The
file already encodes Σ₁ (open) vs Π₂ (Koenigsmann 2016, axiomatized) on
ℤ ⊂ ℚ. The narrative claims "Σ₁ ⟺ ¬(Π₁ for the complement)" but did not
formalize it. Closing that gap with axiom-free additions.

## Active Approach

S2 — Π₁ definability + classical duality:

1. Define `IsCoDiophantineDefinition` (Π₁, purely universal definability).
2. Define `NotIntSubset = ℚ \ ℤ` as a predicate.
3. Prove `diophantine_iff_codiophantine_complement` — the general Σ₁/Π₁
   duality theorem (one classical step on the Π₁ → Σ₁ direction via
   `Classical.byContradiction`).
4. Specialize to ℤ as `integers_diophantine_iff_complement_codiophantine`.
5. Re-export the OQ-01 conditionals (H10/ℚ-undecidability, Mazur) against
   the new Π₁(ℚ\ℤ) predicate — pure logical consequences, no new axioms.

Net new content: 2 definitions, 4 theorems, 0 new axioms.

## Build Status

Docker build: PENDING (running) — file uses Lean core only, no mathlib;
fast build expected.

First attempt failed because `by_contra` in Lean core requires `Decidable`
(this file has no mathlib import). Fixed by switching to explicit
`Classical.byContradiction` with type ascription on the negated
hypotheses (forces beta reduction of `(fun q => ¬ S q) q ↔ ¬ S q`).

## Blockers

None.

## Next Action

Verify the Docker build passes; commit, push, create PR.

If Σ₁/Π₁ duality lands cleanly, S3 candidates:
- Σ₁ × Π₁ closure properties (under finite union/intersection) for the
  Diophantine sets of ℚ.
- Π₁ ⊆ Π₂ via the `a ≠ 0 ⟺ ∃ z, a·z = 1` polynomial-inversion trick
  (cleaner once we have a `Field`-like API; would require minor
  arithmetic lemmas about ℚ).
- Daans 2021 (10-quantifier reduction) as a separate axiomatized witness
  refining `koenigsmann_2016_universal` — would add 1 new axiom but
  improve quantitative content; defer until Σ₁/Π₁ lands.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (build fix from `by_contra` to
  `Classical.byContradiction`)
- Approaches tried: 1 (S2 — Σ₁/Π₁ duality)
