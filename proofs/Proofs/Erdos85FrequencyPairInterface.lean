import Proofs.Erdos85FrequencyPairProjector
import Proofs.Erdos85ProjectedMultiplicityParity
import Proofs.Erdos85SquareTrace

/-!
# Frequency-pair bridge: trace as a projected-multiplicity Fourier sum

This interface file states the frequency-pair trace identity in the exact
vocabulary of the projected diagonal-anchor multiplicity machinery:

* `trace T = 2 * H(ζ)`, where
  `H(ζ) = ∑ s : ZMod p, projectedMultiplicity (ZMod.castHom hdvd _) m s * ζ^s`
  is the prime Fourier transform of the mod-`p` projection of the
  diagonal-anchor weight `m`, and `T` is the restriction of the (labeled)
  adjacency matrix to the `μ = ζ + ζ⁻¹` eigenspace of the defect operator;

* the **square branch**: when `κ - μ = s²` with `s ≠ 0`, the square-trace
  projector argument makes `H(ζ)` an integral multiple of `s`, hence
  `H(ζ)² ` an integral square times `κ - μ`;

* the **vanishing branch**: if the trace is zero then `H(ζ) = 0`, the
  hypothesis consumed by the prime Fourier uniformity terminal.

The remaining graph-specific inputs are precisely: the transported matrix
equation `M² = κ•1 + J - D`, commutation, symmetry, translation
invariance of diagonal blocks (`Erdos85FrequencyPairGraphBlocks`), and
the identification of `∑ c, M (0,c) (t,c)` with the ℕ-valued
diagonal-anchor multiplicity.
-/

namespace Erdos85

noncomputable section

variable {K : Type*} [Field K] {C : Type*} [Fintype C] [DecidableEq C]
  {r p : ℕ} [NeZero r] [NeZero p]

theorem pow_eq_one_of_dvd_of_pow_eq_one {ζ : K} (hdvd : p ∣ r)
    (hζp : ζ ^ p = 1) : ζ ^ r = 1 := by
  obtain ⟨q, rfl⟩ := hdvd
  rw [pow_mul, hζp, one_pow]

/-- **Trace equals twice the projected Fourier transform.**  The trace of
the restricted adjacency operator on the `ζ/ζ⁻¹` frequency-pair space is
twice the prime Fourier transform of the projected diagonal-anchor
multiplicity.  No residual normalization by `r` or `p` remains, and the
identity is symmetric in `ζ ↔ ζ⁻¹`, so it is independent of every cycle
orientation choice. -/
theorem trace_defectEigenspaceRestrict_eq_two_mul_projected_fourier
    {M : Matrix (ZMod r × C) (ZMod r × C) K}
    (hcomm : M * cycleDefectMatrix K C r = cycleDefectMatrix K C r * M)
    (hdiag : ∀ (c : C) (x y : ZMod r),
      M (x + 1, c) (y + 1, c) = M (x, c) (y, c))
    (hsymm : M.IsSymm)
    (hrOdd : Odd r) (hdvd : p ∣ r)
    {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1) (hr0 : (r : K) ≠ 0)
    (m : ZMod r → ℕ)
    (hm : ∀ t : ZMod r, (∑ c : C, M (0, c) (t, c)) = (m t : K)) :
    LinearMap.trace K
        (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
        (defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹)) =
      2 * ∑ s : ZMod p,
        ((projectedMultiplicity (ZMod.castHom hdvd (ZMod p)) m s : ℕ) : K) *
          ζ ^ s.val := by
  have hζr : ζ ^ r = 1 := pow_eq_one_of_dvd_of_pow_eq_one hdvd hζp
  rw [trace_defectEigenspaceRestrict hcomm hdiag hsymm hrOdd hζr hζsq hr0,
    sum_mul_cyclePow_eq_fiberwise hdvd hζp]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [projectedMultiplicity, projectionFiber, Nat.cast_sum]
  exact Finset.sum_congr rfl fun t _ ↦ hm t

/-- **Square branch.**  If `κ - μ = s²` is a nonzero square, the
frequency-pair space has even dimension and the square-trace projector
argument forces the projected Fourier transform to be an integral
multiple of `s`. -/
theorem projected_fourier_eq_int_mul_of_sq [CharZero K]
    {M : Matrix (ZMod r × C) (ZMod r × C) K} {κ : K}
    (hcomm : M * cycleDefectMatrix K C r = cycleDefectMatrix K C r * M)
    (hsqM : M * M = κ • (1 : Matrix (ZMod r × C) (ZMod r × C) K) +
      (Matrix.of fun _ _ : ZMod r × C ↦ (1 : K)) - cycleDefectMatrix K C r)
    (hdiag : ∀ (c : C) (x y : ZMod r),
      M (x + 1, c) (y + 1, c) = M (x, c) (y, c))
    (hsymm : M.IsSymm)
    (hrOdd : Odd r) (hdvd : p ∣ r)
    {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1)
    {s : K} (hs : s ≠ 0) (hκ : κ - (ζ + ζ⁻¹) = s * s)
    (m : ZMod r → ℕ)
    (hm : ∀ t : ZMod r, (∑ c : C, M (0, c) (t, c)) = (m t : K)) :
    ∃ u : ℤ,
      ∑ y : ZMod p,
        ((projectedMultiplicity (ZMod.castHom hdvd (ZMod p)) m y : ℕ) : K) *
          ζ ^ y.val = (u : K) * s := by
  have hζr : ζ ^ r = 1 := pow_eq_one_of_dvd_of_pow_eq_one hdvd hζp
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  have hr0 : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hTsq := defectEigenspaceRestrict_sq_ones hcomm hsqM hζr hζ1
  rw [hκ] at hTsq
  have heven : Even (Module.finrank K
      (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))) :=
    even_finrank_defectEigenspace hrOdd hζr hζsq
  obtain ⟨u, hu⟩ := LinearMap.exists_int_trace_eq_two_mul_of_sq_eq_sq
    (defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹)) s hs hTsq heven
  have htr := trace_defectEigenspaceRestrict_eq_two_mul_projected_fourier
    hcomm hdiag hsymm hrOdd hdvd hζp hζsq hr0 m hm
  refine ⟨u, ?_⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [← htr, hu]
  ring

/-- Squaring the square branch: `H(ζ)²` is an integral square times
`κ - μ`.  This is the exact input shape of the mod-4 obstruction files. -/
theorem projected_fourier_sq_eq_int_sq_mul [CharZero K]
    {M : Matrix (ZMod r × C) (ZMod r × C) K} {κ : K}
    (hcomm : M * cycleDefectMatrix K C r = cycleDefectMatrix K C r * M)
    (hsqM : M * M = κ • (1 : Matrix (ZMod r × C) (ZMod r × C) K) +
      (Matrix.of fun _ _ : ZMod r × C ↦ (1 : K)) - cycleDefectMatrix K C r)
    (hdiag : ∀ (c : C) (x y : ZMod r),
      M (x + 1, c) (y + 1, c) = M (x, c) (y, c))
    (hsymm : M.IsSymm)
    (hrOdd : Odd r) (hdvd : p ∣ r)
    {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1)
    {s : K} (hs : s ≠ 0) (hκ : κ - (ζ + ζ⁻¹) = s * s)
    (m : ZMod r → ℕ)
    (hm : ∀ t : ZMod r, (∑ c : C, M (0, c) (t, c)) = (m t : K)) :
    ∃ u : ℤ,
      (∑ y : ZMod p,
        ((projectedMultiplicity (ZMod.castHom hdvd (ZMod p)) m y : ℕ) : K) *
          ζ ^ y.val) ^ 2 = (u : K) ^ 2 * (κ - (ζ + ζ⁻¹)) := by
  obtain ⟨u, hu⟩ := projected_fourier_eq_int_mul_of_sq hcomm hsqM hdiag
    hsymm hrOdd hdvd hζp hζsq hs hκ m hm
  refine ⟨u, ?_⟩
  rw [hu, hκ]
  ring

/-- **Vanishing branch.**  If the frequency-pair trace vanishes, so does
the projected Fourier transform — the hypothesis consumed by the prime
Fourier uniformity terminal `false_of_prime_anchor_fourier_zero`. -/
theorem projected_fourier_eq_zero_of_trace_eq_zero [CharZero K]
    {M : Matrix (ZMod r × C) (ZMod r × C) K}
    (hcomm : M * cycleDefectMatrix K C r = cycleDefectMatrix K C r * M)
    (hdiag : ∀ (c : C) (x y : ZMod r),
      M (x + 1, c) (y + 1, c) = M (x, c) (y, c))
    (hsymm : M.IsSymm)
    (hrOdd : Odd r) (hdvd : p ∣ r)
    {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1)
    (m : ZMod r → ℕ)
    (hm : ∀ t : ZMod r, (∑ c : C, M (0, c) (t, c)) = (m t : K))
    (htrace0 : LinearMap.trace K
      (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
      (defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹)) = 0) :
    ∑ y : ZMod p,
      ((projectedMultiplicity (ZMod.castHom hdvd (ZMod p)) m y : ℕ) : K) *
        ζ ^ y.val = 0 := by
  have hr0 : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have htr := trace_defectEigenspaceRestrict_eq_two_mul_projected_fourier
    hcomm hdiag hsymm hrOdd hdvd hζp hζsq hr0 m hm
  rw [htrace0] at htr
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  exact (mul_eq_zero.mp htr.symm).resolve_left h2

end

end Erdos85
