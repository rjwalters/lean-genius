# Research State: minkowski-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-07T20:08:05Z
**Last Updated**: 2026-05-08
**Iteration**: 5

## Current Focus

**Both `minkowski_from_blichfeldt` sorries are CLOSED** (PR #16744,
Session 4). The previous state.md text "Closing the two sorries" was
stale — verification via
`grep -nE "(^|[ \t]):= by sorry|[ \t]sorry$" proofs/Proofs/MinkowskiTheoremOQ04.lean`
returns 0 actual sorry tokens (the only "sorry" hit is the file
docstring's "sorry-free" claim).

Remaining work: **eliminate the two measure-theory axioms**:
- `blichfeldt_volume_partition` — provable via Mathlib's
  `IsAddFundamentalDomain.lintegral_eq_tsum''` applied to
  `Set.indicator s (fun _ => (1 : ℝ≥0∞))`. Estimated 50-80 lines.
- `blichfeldt_general` — covering-count averaging argument;
  substantially harder. Estimated 150-300 lines.

## Active Approach (next session)

### Proof template for `blichfeldt_volume_partition`

Mathlib API reference (verified in
`proofs/.lake/packages/mathlib/Mathlib/MeasureTheory/Group/FundamentalDomain.lean:241`):

```
@[to_additive] lemma IsFundamentalDomain.lintegral_eq_tsum''
    (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g • x) ∂μ
```

Via `to_additive`, `IsAddFundamentalDomain.lintegral_eq_tsum''` gives
`∑' g : G, ∫⁻ x in s, f (g +ᵥ x) ∂μ`.

Sketch:
1. `Countable (stdLattice n).toAddSubgroup` instance (already done in
   `blichfeldt_disj_bound` lines 93-96 — copy verbatim).
2. Apply `(stdLattice_isAddFundamentalDomain n).lintegral_eq_tsum''` to
   `f = s.indicator (fun _ => (1 : ℝ≥0∞))`.
3. LHS reduces to `volume s` via `MeasureTheory.lintegral_indicator h_meas`
   plus the trivial `∫⁻ x, (1 : ℝ≥0∞) ∂(volume.restrict s) = volume s`.
4. For each summand, the integrand `s.indicator 1 (g +ᵥ x)` equals
   `((g +ᵥ ·) ⁻¹' s).indicator 1 x` (case-split on `g +ᵥ x ∈ s`;
   uses `Set.mem_preimage` and the if-then-else unfolding of
   `Set.indicator`).
5. `∫⁻ x in F, A.indicator 1 x ∂μ = volume (F ∩ A)` via
   `MeasureTheory.lintegral_indicator h_pre_meas`.
   Get `h_pre_meas := h_g_meas h_meas` where
   `h_g_meas := (measurable_const_vadd g : Measurable (g +ᵥ ·))`
   (Mathlib has `MeasurableVAdd L.toAddSubgroup E` for ℤ-lattices
   per `Mathlib/Algebra/Module/ZLattice/Covolume.lean:85`).
6. Show `F ∩ ((g +ᵥ ·) ⁻¹' s) = {z ∈ F | z + (g : Fin n → ℝ) ∈ s}` by
   `Set.ext` plus `add_comm` (since `g +ᵥ z = (g : ...) + z` and
   `(g : ...) + z = z + (g : ...)` for ℝⁿ).

Risk points:
- Step 4: definitional unfolding of `(g +ᵥ x ∈ s)` may need explicit
  `show`; the indicator composition is definitionally clean but Lean's
  elaborator may need help.
- Step 6: depending on the AddSubgroup vadd instance, `g +ᵥ z` vs
  `(g : Fin n → ℝ) + z` may or may not be `rfl`. Spot-check
  `(g +ᵥ z : Fin n → ℝ) = (g : Fin n → ℝ) + z` is provable before
  relying on it. If not `rfl`, look for `AddSubmonoidClass.coe_vadd`
  or instance unfolding.

### Proof sketch for `blichfeldt_general`

For vol(S) > k, the covering count `c(z) := #{v ∈ ℤⁿ | z + v ∈ S}`
satisfies ∫_F c dz = vol(S) > k. By averaging (`∫_F c ≥ (k+1) · vol(F)`
contradiction with ∫_F c ≤ k · vol(F) if c(z) ≤ k for all z), ∃ z ∈ F
with c(z) ≥ k+1. Yields k+1 lattice elements v₁,...,v_{k+1} with
z + vᵢ ∈ S, giving k+1 ℤⁿ-congruent points.

Mathlib infrastructure needed:
- `tsum_eq_lintegral_of_indicator` (or similar) to express c(z) as a
  tsum of indicators.
- `MeasureTheory.lintegral_const_mul` for the constant-multiple
  averaging step.
- A "support of c is non-empty above k" argument — may need hand-rolled
  lemma if not in Mathlib.

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1
- Approaches tried:
  - S1-S3 (Phase scaffolding, 2026-05-06/07)
  - S4 (researcher-?): closed both sorries via preimage-rewrite +
    addHaar_smul (PR #16744)
  - S5 (researcher-11, 2026-05-08): state.md reconciliation,
    Mathlib-API mapping for the two remaining axioms

## Blockers

None for `blichfeldt_volume_partition` — the path is well-mapped above
and the Mathlib infrastructure (`MeasurableVAdd`,
`IsAddFundamentalDomain.lintegral_eq_tsum''`) is verified to exist.

`blichfeldt_general` is substantially harder; the averaging argument
requires several measure-theoretic identities that may need hand-rolled
lemmas if not in Mathlib.

## Next Action

**Session 6**: Eliminate `blichfeldt_volume_partition` axiom following
the template above. ~50-80 lines. The cleanup of stale state.md text
was done in Session 5 (this iteration); the actual axiom-elimination
work remains.

## Iteration 5 Builds (researcher-11, 2026-05-08)

Focus: state-of-the-world reconciliation + Mathlib API mapping for
the remaining axioms.

Verified the previous state.md text was stale: `minkowski_from_blichfeldt`
sorries were closed by PR #16744 (S4), but state.md still said "Closing
the two sorries". Updated:
- Phase: kept ACT
- Iteration: 4 → 5
- Current focus: now reflects "0 sorries, 2 axioms remain"
- Active approach: detailed proof template for
  `blichfeldt_volume_partition` with verified Mathlib API references
  (`IsAddFundamentalDomain.lintegral_eq_tsum''`,
  `MeasurableVAdd L.toAddSubgroup E`)
- Risk points / spot-check guidance documented for the next session

No new theorems added in this iteration. The substantive work is
deferred to S6 (and beyond) per the documented plan.

**Counts**: lineCount 293, theoremCount 5, axiomCount 2, sorries 0
(all unchanged from PR #16744).
