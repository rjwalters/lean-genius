import Proofs.Erdos85FrequencyPairMixed

/-!
# The mixed projector trace without diagonal translation invariance

At even defect-cycle lengths, a diagonal adjacency block commuting with the
cycle matrix can contain reflection (Hankel) terms and need not be circulant.
The trace against the frequency-pair projector still has an exact formula,
but its component contribution retains the projector normalization `1 / ℓ c`.
This file exposes that formula explicitly; it is the normalization checkpoint
needed by any length-agnostic parity argument.
-/

namespace Erdos85

noncomputable section

open Matrix

variable {K : Type*} [Field K]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ}

/-- **General mixed trace formula.**  No translation-invariance or parity
hypothesis is used.  Each selected component contributes its complete
two-variable diagonal-block sum, multiplied by the genuine factor
`(ℓ c)⁻¹`. -/
theorem trace_mul_mixedFreqProjector_general
    {M : Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K}
    {ζ : K} :
    Matrix.trace (M * mixedFreqProjector p ζ ℓ) =
      ∑ c : C, if p ∣ ℓ c then
        ((ℓ c : K))⁻¹ *
          ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
            M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
      else 0 := by
  classical
  have hentry : ∀ (c : C) (i : ZMod (ℓ c)),
      (M * mixedFreqProjector p ζ ℓ) ⟨c, i⟩ ⟨c, i⟩ =
        if p ∣ ℓ c then
          ((ℓ c : K))⁻¹ * ∑ k : ZMod (ℓ c),
            M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
        else 0 := by
    intro c i
    rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single c]
    · by_cases hdvd : p ∣ ℓ c
      · rw [if_pos hdvd, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [mixedFreqProjector, Matrix.blockDiagonal'_apply_eq,
          if_pos hdvd, Matrix.smul_apply, Matrix.circulant_apply,
          smul_eq_mul]
        ring
      · rw [if_neg hdvd]
        apply Finset.sum_eq_zero
        intro k _
        rw [mixedFreqProjector, Matrix.blockDiagonal'_apply_eq,
          if_neg hdvd]
        simp
    · intro e _ hne
      apply Finset.sum_eq_zero
      intro k _
      rw [mixedFreqProjector, Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ c) h
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_congr rfl fun i _ ↦ hentry c i]
  by_cases hdvd : p ∣ ℓ c
  · simp only [if_pos hdvd, ← Finset.mul_sum]
  · simp [hdvd]

/-- In the absence of a further divisibility theorem, the component trace
normalization cannot be discarded: it is exactly inverse cycle length. -/
theorem trace_mul_mixedFreqProjector_general_component
    {M : Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K}
    {ζ : K} (c : C) (hdvd : p ∣ ℓ c) :
    (if p ∣ ℓ c then
      ((ℓ c : K))⁻¹ *
        ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
    else 0) =
      ((ℓ c : K))⁻¹ *
        ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i) := by
  rw [if_pos hdvd]

end

end Erdos85
