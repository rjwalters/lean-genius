import Proofs.Erdos85FrequencyPairProjector
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Mixed-length frequency-pair projector

The frequency-pair bridge generalized to a defect two-factor whose cycles
have arbitrary, possibly distinct, lengths `ℓ c`.  For a primitive `p`-th
root of unity `ζ`, the `μ = ζ + ζ⁻¹` eigenspace of the block-diagonal
defect operator is supported exactly on the components whose length is
divisible by `p`:

* on a component with `p ∣ ℓ c` the cyclic two-term recurrence has the
  two-dimensional solution space spanned by the `ζ` and `ζ⁻¹` Fourier
  vectors, exactly as in the equal-length case;
* on a component with `p ∤ ℓ c` any recurrence solution fails
  `ℓ c`-periodicity unless it vanishes, so the eigenspace is zero there.

Consequently the mixed frequency-pair projector — block diagonal, equal
to the scaled pair circulant on divisible components and zero elsewhere —
has the eigenspace as its exact range, the eigenspace has the even
dimension `2 · #{c | p ∣ ℓ c}`, and the trace of the restricted operator
is twice a prime Fourier sum of anchor weights collected over the
divisible components only.

No common-length hypothesis appears anywhere, and no parity condition on
the individual lengths is needed at this operator level: the
cross-frequency sums vanish by a geometric-sum argument at `ζ²`, which is
again a nontrivial `p`-th root of unity.
-/

namespace Erdos85

noncomputable section

open Matrix

/-! ## Length-parity-free convolution identities -/

section EvenFreeSums

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

theorem cyclePow_two_mul {ζ : K} (hζn : ζ ^ n = 1) (j : ZMod n) :
    cyclePow ζ (2 * j) = cyclePow (ζ ^ 2) j := by
  have h2 : (2 * j : ZMod n) = ((2 * j.val : ℕ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_rightInverse j]
  rw [h2, cyclePow_natCast hζn, cyclePow, pow_mul]

theorem sum_cyclePow_two_mul_add_eq_zero_of_sq {ζ : K}
    (hζn : ζ ^ n = 1) (hζsq : ζ ^ 2 ≠ 1) (a : ZMod n) :
    ∑ t : ZMod n, cyclePow ζ (2 * t + a) = 0 := by
  have hsq_n : (ζ ^ 2) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]
  have hterm : ∀ t : ZMod n,
      cyclePow ζ (2 * t + a) = cyclePow (ζ ^ 2) t * cyclePow ζ a := by
    intro t
    rw [cyclePow_add hζn, cyclePow_two_mul hζn]
  rw [Finset.sum_congr rfl fun t _ ↦ hterm t, ← Finset.sum_mul,
    sum_cyclePow_eq_zero hsq_n hζsq, zero_mul]

theorem circulant_cyclePow_mulVec_neg_of_sq {ζ : K}
    (hζn : ζ ^ n = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.circulant (cyclePow ζ) *ᵥ
      (fun s : ZMod n ↦ cyclePow ζ (-s)) = 0 := by
  funext t
  have hterm : ∀ s : ZMod n, cyclePow ζ (t - s) * cyclePow ζ (-s) =
      cyclePow ζ (2 * (-s) + t) := fun s ↦ by
    rw [← cyclePow_add hζn]
    exact congrArg (cyclePow ζ) (by ring)
  have hneg : ∑ s : ZMod n, cyclePow ζ (2 * (-s) + t) =
      ∑ s : ZMod n, cyclePow ζ (2 * s + t) :=
    Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ fun s ↦ rfl
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm,
    Pi.zero_apply]
  rw [hneg, sum_cyclePow_two_mul_add_eq_zero_of_sq hζn hζsq]

theorem circulant_neg_mulVec_cyclePow_of_sq {ζ : K}
    (hζn : ζ ^ n = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.circulant (fun s : ZMod n ↦ cyclePow ζ (-s)) *ᵥ
      (cyclePow ζ : ZMod n → K) = 0 := by
  funext t
  have hterm : ∀ s : ZMod n, cyclePow ζ (-(t - s)) * cyclePow ζ s =
      cyclePow ζ (2 * s + -t) := fun s ↦ by
    rw [← cyclePow_add hζn]
    exact congrArg (cyclePow ζ) (by ring)
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm,
    Pi.zero_apply]
  rw [sum_cyclePow_two_mul_add_eq_zero_of_sq hζn hζsq]

theorem circulant_freqPairKernel_mulVec_freqPairKernel_of_sq {ζ : K}
    (hζn : ζ ^ n = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.circulant (freqPairKernel ζ) *ᵥ
      (freqPairKernel ζ : ZMod n → K) = (n : K) • freqPairKernel ζ := by
  rw [freqPairKernel_eq, Matrix.circulant_add, Matrix.add_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_add,
    circulant_cyclePow_mulVec_cyclePow hζn,
    circulant_cyclePow_mulVec_neg_of_sq hζn hζsq,
    circulant_neg_mulVec_cyclePow_of_sq hζn hζsq,
    circulant_neg_mulVec_neg hζn, smul_add]
  abel

theorem circulant_freqPairKernel_mulVec_cyclePow_of_sq {ζ : K}
    (hζn : ζ ^ n = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.circulant (freqPairKernel ζ) *ᵥ (cyclePow ζ : ZMod n → K) =
      (n : K) • cyclePow ζ := by
  rw [freqPairKernel_eq, Matrix.circulant_add, Matrix.add_mulVec,
    circulant_cyclePow_mulVec_cyclePow hζn,
    circulant_neg_mulVec_cyclePow_of_sq hζn hζsq, add_zero]

theorem circulant_freqPairKernel_mulVec_negCyclePow_of_sq {ζ : K}
    (hζn : ζ ^ n = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.circulant (freqPairKernel ζ) *ᵥ
      (fun s : ZMod n ↦ cyclePow ζ (-s)) =
      (n : K) • fun s : ZMod n ↦ cyclePow ζ (-s) := by
  rw [freqPairKernel_eq, Matrix.circulant_add, Matrix.add_mulVec,
    circulant_cyclePow_mulVec_neg_of_sq hζn hζsq,
    circulant_neg_mulVec_neg hζn, zero_add]

/-- Entrywise action of one circulant defect block. -/
theorem circulant_defectKernel_mulVec_apply (w : ZMod n → K) (t : ZMod n) :
    (Matrix.circulant (defectKernel K n) *ᵥ w) t =
      w (t - 1) + w (t + 1) := by
  have hentry : ∀ k : ZMod n,
      Matrix.circulant (defectKernel K n) t k * w k =
        (if k = t - 1 then w k else 0) +
          (if k = t + 1 then w k else 0) := by
    intro k
    have h1 : (t - k = 1) = (k = t - 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    have h2 : (t - k = -1) = (k = t + 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    rw [Matrix.circulant_apply, defectKernel]
    simp only [h1, h2, add_mul, ite_mul, one_mul, zero_mul]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun k _ ↦ hentry k, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (t - 1) fun k ↦ w k,
    Finset.sum_ite_eq' Finset.univ (t + 1) fun k ↦ w k]
  simp

end EvenFreeSums

/-! ## The cyclic two-term recurrence at a single modulus -/

section Recurrence

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

theorem sub_inv_ne_zero_of_sq_ne_one {ζ : K} (hζ0 : ζ ≠ 0)
    (hζsq : ζ ^ 2 ≠ 1) : ζ - ζ⁻¹ ≠ 0 := by
  intro h
  apply hζsq
  have hinv : ζ = ζ⁻¹ := sub_eq_zero.mp h
  calc ζ ^ 2 = ζ * ζ := sq ζ
    _ = ζ * ζ⁻¹ := congrArg (fun w ↦ ζ * w) hinv
    _ = 1 := mul_inv_cancel₀ hζ0

/-- Natural-index form of any solution of the cyclic recurrence. -/
theorem cycle_recurrence_nat {ζ : K} (hζ0 : ζ ≠ 0) (hζsq : ζ ^ 2 ≠ 1)
    {v : ZMod n → K}
    (hrec : ∀ t : ZMod n, v (t - 1) + v (t + 1) = (ζ + ζ⁻¹) * v t) :
    ∃ a b : K, ∀ j : ℕ,
      v ((j : ℕ) : ZMod n) = a * ζ ^ j + b * ζ⁻¹ ^ j := by
  have hz : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  have hden : ζ - ζ⁻¹ ≠ 0 := sub_inv_ne_zero_of_sq_ne_one hζ0 hζsq
  have hden2 : ζ ^ 2 - 1 ≠ 0 := fun h ↦ hζsq (by linear_combination h)
  set a : K := (v 1 - ζ⁻¹ * v 0) / (ζ - ζ⁻¹) with haDef
  set b : K := (ζ * v 0 - v 1) / (ζ - ζ⁻¹) with hbDef
  refine ⟨a, b, ?_⟩
  have hpair : ∀ j : ℕ,
      v ((j : ℕ) : ZMod n) = a * ζ ^ j + b * ζ⁻¹ ^ j ∧
        v (((j + 1 : ℕ) : ZMod n)) =
          a * ζ ^ (j + 1) + b * ζ⁻¹ ^ (j + 1) := by
    intro j
    induction j with
    | zero =>
      constructor
      · rw [Nat.cast_zero, pow_zero, pow_zero, mul_one, mul_one, haDef,
          hbDef]
        field_simp
        ring
      · rw [Nat.cast_one, pow_one, pow_one, haDef, hbDef]
        field_simp
        ring
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hstep := hrec (((j + 1 : ℕ) : ZMod n))
      have hc1 : ((j + 1 : ℕ) : ZMod n) - 1 = ((j : ℕ) : ZMod n) := by
        push_cast
        ring
      have hc2 : ((j + 1 : ℕ) : ZMod n) + 1 =
          ((j + 1 + 1 : ℕ) : ZMod n) := by
        push_cast
        ring
      rw [hc1, hc2, ih.1, ih.2] at hstep
      have hsolve : v (((j + 1 + 1 : ℕ) : ZMod n)) =
          (ζ + ζ⁻¹) * (a * ζ ^ (j + 1) + b * ζ⁻¹ ^ (j + 1)) -
            (a * ζ ^ j + b * ζ⁻¹ ^ j) :=
        eq_sub_of_add_eq' hstep
      rw [hsolve]
      linear_combination (a * ζ ^ j + b * ζ⁻¹ ^ j) * hz
  exact fun j ↦ (hpair j).1

/-- On a modulus where `ζ^n = 1`, recurrence solutions are Fourier
pairs. -/
theorem cycle_recurrence_eq_fourier {ζ : K} (hζn : ζ ^ n = 1)
    (hζsq : ζ ^ 2 ≠ 1) {v : ZMod n → K}
    (hrec : ∀ t : ZMod n, v (t - 1) + v (t + 1) = (ζ + ζ⁻¹) * v t) :
    ∃ a b : K, ∀ t : ZMod n,
      v t = a * cyclePow ζ t + b * cyclePow ζ (-t) := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζn
  obtain ⟨a, b, hab⟩ := cycle_recurrence_nat hζ0 hζsq hrec
  refine ⟨a, b, fun t ↦ ?_⟩
  have h := hab t.val
  rw [ZMod.natCast_rightInverse t] at h
  rw [h, cyclePow_neg hζn, cyclePow, ← inv_pow]

/-- **Off-frequency vanishing.**  On a modulus where `ζ^n ≠ 1`, the only
`n`-periodic recurrence solution is zero. -/
theorem cycle_recurrence_eq_zero {ζ : K} (hζ0 : ζ ≠ 0)
    (hζsq : ζ ^ 2 ≠ 1) (hζn : ζ ^ n ≠ 1) {v : ZMod n → K}
    (hrec : ∀ t : ZMod n, v (t - 1) + v (t + 1) = (ζ + ζ⁻¹) * v t) :
    v = 0 := by
  have hden : ζ - ζ⁻¹ ≠ 0 := sub_inv_ne_zero_of_sq_ne_one hζ0 hζsq
  obtain ⟨a, b, hab⟩ := cycle_recurrence_nat hζ0 hζsq hrec
  have h0 := hab 0
  have h1 := hab 1
  have hn := hab n
  have hn1 := hab (n + 1)
  rw [Nat.cast_zero, pow_zero, pow_zero, mul_one, mul_one] at h0
  rw [Nat.cast_one, pow_one, pow_one] at h1
  rw [ZMod.natCast_self] at hn
  rw [show (((n + 1 : ℕ)) : ZMod n) = 1 by
    push_cast [ZMod.natCast_self]
    ring] at hn1
  have heq1 : a * ζ ^ n + b * ζ⁻¹ ^ n = a + b := by
    rw [← hn, h0]
  have heq2 : a * ζ ^ (n + 1) + b * ζ⁻¹ ^ (n + 1) = a * ζ + b * ζ⁻¹ := by
    rw [← hn1, h1]
  have hAB1 : a * (ζ ^ n - 1) + b * (ζ⁻¹ ^ n - 1) = 0 := by
    linear_combination heq1
  have hAB2 : a * (ζ ^ n - 1) * ζ + b * (ζ⁻¹ ^ n - 1) * ζ⁻¹ = 0 := by
    linear_combination heq2
  have hB : b * (ζ⁻¹ ^ n - 1) * (ζ⁻¹ - ζ) = 0 := by
    linear_combination hAB2 - ζ * hAB1
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hB with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · rw [sub_eq_zero, inv_pow] at h'
        exact absurd (inv_eq_one.mp h') hζn
    · exact absurd (by linear_combination -h : ζ - ζ⁻¹ = 0) hden
  have ha0 : a = 0 := by
    rw [hb0, zero_mul, add_zero] at hAB1
    rcases mul_eq_zero.mp hAB1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hζn
  funext t
  have h := hab t.val
  rw [ZMod.natCast_rightInverse t, ha0, hb0] at h
  simpa using h

end Recurrence

/-! ## The mixed-length defect operator and frequency-pair projector -/

section Mixed

variable {K : Type*} [Field K] {C : Type*} [Fintype C] [DecidableEq C]
  {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ}

/-- Block-diagonal defect operator of a mixed-length cycle system. -/
def mixedDefectMatrix (K : Type*) [Field K] (ℓ : C → ℕ)
    [∀ c, NeZero (ℓ c)] :
    Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K :=
  Matrix.blockDiagonal' fun c ↦ Matrix.circulant (defectKernel K (ℓ c))

/-- The mixed frequency-pair projector: the scaled pair circulant on the
components of length divisible by `p`, zero elsewhere. -/
def mixedFreqProjector (p : ℕ) (ζ : K) (ℓ : C → ℕ) [∀ c, NeZero (ℓ c)] :
    Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K :=
  Matrix.blockDiagonal' fun c ↦
    if p ∣ ℓ c then
      ((ℓ c : K))⁻¹ • Matrix.circulant (freqPairKernel ζ)
    else 0

/-- Block-diagonal matrices act cycle by cycle on vectors. -/
theorem blockDiagonal'_mulVec_apply
    (M : ∀ c : C, Matrix (ZMod (ℓ c)) (ZMod (ℓ c)) K)
    (v : (Σ c : C, ZMod (ℓ c)) → K) (c : C) (t : ZMod (ℓ c)) :
    (Matrix.blockDiagonal' M *ᵥ v) ⟨c, t⟩ =
      (M c *ᵥ fun k ↦ v ⟨c, k⟩) t := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single c]
  · exact Finset.sum_congr rfl fun k _ ↦ by
      rw [Matrix.blockDiagonal'_apply_eq]
  · intro c' _ hne
    apply Finset.sum_eq_zero
    intro k _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hne), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- Constant scalars pass through mixed block-diagonal families. -/
theorem blockDiagonal'_smul_blocks (x : K)
    (M : ∀ c : C, Matrix (ZMod (ℓ c)) (ZMod (ℓ c)) K) :
    (Matrix.blockDiagonal' fun c ↦ x • M c) =
      x • Matrix.blockDiagonal' M := by
  ext ⟨c, i⟩ ⟨c', j⟩
  by_cases h : c = c'
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h, Matrix.smul_apply]

theorem mixedDefectMatrix_mulVec_apply
    (v : (Σ c : C, ZMod (ℓ c)) → K) (c : C) (t : ZMod (ℓ c)) :
    (mixedDefectMatrix K ℓ *ᵥ v) ⟨c, t⟩ =
      v ⟨c, t - 1⟩ + v ⟨c, t + 1⟩ := by
  rw [mixedDefectMatrix, blockDiagonal'_mulVec_apply,
    circulant_defectKernel_mulVec_apply]

/-- Membership in the mixed frequency eigenspace is the per-component
cyclic recurrence. -/
theorem mem_defectEigenspace_mixed_iff {μ : K}
    {v : (Σ c : C, ZMod (ℓ c)) → K} :
    v ∈ defectEigenspace (mixedDefectMatrix K ℓ) μ ↔
      ∀ (c : C) (t : ZMod (ℓ c)),
        v ⟨c, t - 1⟩ + v ⟨c, t + 1⟩ = μ * v ⟨c, t⟩ := by
  rw [mem_defectEigenspace_iff]
  constructor
  · intro h c t
    have := congrFun h ⟨c, t⟩
    rw [mixedDefectMatrix_mulVec_apply] at this
    simpa using this
  · intro h
    funext x
    obtain ⟨c, t⟩ := x
    rw [mixedDefectMatrix_mulVec_apply]
    simpa using h c t

theorem mixedFreqProjector_mul_self [CharZero K] {ζ : K}
    (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1) :
    mixedFreqProjector p ζ ℓ * mixedFreqProjector p ζ ℓ =
      mixedFreqProjector p ζ ℓ := by
  rw [mixedFreqProjector, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext c
  by_cases hdvd : p ∣ ℓ c
  · rw [if_pos hdvd]
    have hζn : ζ ^ ℓ c = 1 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, pow_mul, hζp, one_pow]
    have hn0 : ((ℓ c : K)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (ℓ c))
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.circulant_mul,
      circulant_freqPairKernel_mulVec_freqPairKernel_of_sq hζn hζsq,
      Matrix.circulant_smul, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ hn0, mul_one]
  · rw [if_neg hdvd, mul_zero]

theorem mixedDefect_mul_freqProjector {ζ : K} (hζp : ζ ^ p = 1) :
    mixedDefectMatrix K ℓ * mixedFreqProjector p ζ ℓ =
      (ζ + ζ⁻¹) • mixedFreqProjector p ζ ℓ := by
  rw [mixedDefectMatrix, mixedFreqProjector, ← Matrix.blockDiagonal'_mul,
    ← blockDiagonal'_smul_blocks]
  congr 1
  funext c
  by_cases hdvd : p ∣ ℓ c
  · rw [if_pos hdvd]
    have hζn : ζ ^ ℓ c = 1 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, pow_mul, hζp, one_pow]
    rw [Matrix.mul_smul, Matrix.circulant_mul,
      circulant_defectKernel_mulVec_freqPairKernel hζn,
      Matrix.circulant_smul, smul_smul, smul_smul, mul_comm]
  · rw [if_neg hdvd, mul_zero, smul_zero]

theorem mixedFreqProjector_mul_defect {ζ : K} (hζp : ζ ^ p = 1) :
    mixedFreqProjector p ζ ℓ * mixedDefectMatrix K ℓ =
      (ζ + ζ⁻¹) • mixedFreqProjector p ζ ℓ := by
  rw [mixedDefectMatrix, mixedFreqProjector, ← Matrix.blockDiagonal'_mul,
    ← blockDiagonal'_smul_blocks]
  congr 1
  funext c
  by_cases hdvd : p ∣ ℓ c
  · rw [if_pos hdvd]
    have hζn : ζ ^ ℓ c = 1 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, pow_mul, hζp, one_pow]
    rw [Matrix.smul_mul, Matrix.circulant_mul_comm, Matrix.circulant_mul,
      circulant_defectKernel_mulVec_freqPairKernel hζn,
      Matrix.circulant_smul, smul_smul, smul_smul, mul_comm]
  · rw [if_neg hdvd, zero_mul, smul_zero]

/-- Column sums of the mixed defect operator are two. -/
theorem ones_mul_mixedDefectMatrix :
    (Matrix.of fun _ _ : Σ c : C, ZMod (ℓ c) ↦ (1 : K)) *
        mixedDefectMatrix K ℓ =
      (2 : K) • Matrix.of fun _ _ : Σ c : C, ZMod (ℓ c) ↦ (1 : K) := by
  ext x z
  obtain ⟨e, j⟩ := z
  rw [Matrix.mul_apply]
  have hentry : ∀ z : Σ c : C, ZMod (ℓ c),
      (Matrix.of fun _ _ : Σ c : C, ZMod (ℓ c) ↦ (1 : K)) x z *
          mixedDefectMatrix K ℓ z ⟨e, j⟩ =
        (if z = ⟨e, j - 1⟩ then 1 else 0) +
          (if z = ⟨e, j + 1⟩ then 1 else 0) := by
    rintro ⟨f, k⟩
    rw [Matrix.of_apply, one_mul, mixedDefectMatrix]
    by_cases hf : f = e
    · subst hf
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.circulant_apply,
        defectKernel]
      have h1 : (k - j = 1) = ((⟨f, k⟩ : Σ c : C, ZMod (ℓ c)) = ⟨f, j + 1⟩) := by
        apply propext
        rw [Sigma.mk.inj_iff]
        simp only [heq_eq_eq, true_and]
        exact ⟨fun h ↦ by linear_combination h,
          fun h ↦ by linear_combination h⟩
      have h2 : (k - j = -1) =
          ((⟨f, k⟩ : Σ c : C, ZMod (ℓ c)) = ⟨f, j - 1⟩) := by
        apply propext
        rw [Sigma.mk.inj_iff]
        simp only [heq_eq_eq, true_and]
        exact ⟨fun h ↦ by linear_combination h,
          fun h ↦ by linear_combination h⟩
      simp only [h1, h2]
      exact add_comm _ _
    · have hne1 : (⟨f, k⟩ : Σ c : C, ZMod (ℓ c)) ≠ ⟨e, j - 1⟩ := by
        intro h
        exact hf (congrArg Sigma.fst h)
      have hne2 : (⟨f, k⟩ : Σ c : C, ZMod (ℓ c)) ≠ ⟨e, j + 1⟩ := by
        intro h
        exact hf (congrArg Sigma.fst h)
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hf, if_neg hne1,
        if_neg hne2, add_zero]
  rw [Finset.sum_congr rfl fun z _ ↦ hentry z, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (⟨e, j - 1⟩ : Σ c : C, ZMod (ℓ c)),
    Finset.sum_ite_eq' Finset.univ (⟨e, j + 1⟩ : Σ c : C, ZMod (ℓ c))]
  simp only [Finset.mem_univ, if_true, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, mul_one]
  norm_num

/-- The trace of the mixed projector counts the divisible components
twice. -/
theorem trace_mixedFreqProjector [CharZero K] {ζ : K} :
    Matrix.trace (mixedFreqProjector p ζ ℓ) =
      2 * ((Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card : K) := by
  classical
  have htrbd := Matrix.trace_blockDiagonal'
    (fun c : C ↦ if p ∣ ℓ c then
      ((ℓ c : K))⁻¹ • Matrix.circulant (freqPairKernel (r := ℓ c) ζ)
      else (0 : Matrix (ZMod (ℓ c)) (ZMod (ℓ c)) K))
  rw [mixedFreqProjector, htrbd]
  have hblock : ∀ c : C,
      Matrix.trace (if p ∣ ℓ c then
          ((ℓ c : K))⁻¹ • Matrix.circulant (freqPairKernel (r := ℓ c) ζ)
        else (0 : Matrix (ZMod (ℓ c)) (ZMod (ℓ c)) K)) =
        if p ∣ ℓ c then (2 : K) else 0 := by
    intro c
    by_cases hdvd : p ∣ ℓ c
    · rw [if_pos hdvd, if_pos hdvd, Matrix.trace_smul]
      have hn0 : ((ℓ c : K)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (NeZero.ne (ℓ c))
      have hdiag : ∀ i : ZMod (ℓ c),
          Matrix.circulant (freqPairKernel (r := ℓ c) ζ) i i = 2 :=
        fun i ↦ by
          rw [Matrix.circulant_apply, sub_self, freqPairKernel, neg_zero,
            cyclePow_zero]
          norm_num
      have htr : Matrix.trace
          (Matrix.circulant (freqPairKernel (r := ℓ c) ζ)) =
          (ℓ c : K) * 2 := by
        rw [Matrix.trace]
        simp only [Matrix.diag_apply, hdiag, Finset.sum_const,
          Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [htr, smul_eq_mul, inv_mul_cancel_left₀ hn0]
    · rw [if_neg hdvd, if_neg hdvd, Matrix.trace_zero]
  rw [Finset.sum_congr rfl fun c _ ↦ hblock c, Finset.sum_ite,
    Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    mul_comm]

/-- **Fixed points.**  Every `μ = ζ + ζ⁻¹` eigenvector of the mixed
defect operator is fixed by the mixed projector: on divisible components
it is a Fourier pair, and on the remaining components it vanishes. -/
theorem mixedFreqProjector_mulVec_of_mem [CharZero K]
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {v : (Σ c : C, ZMod (ℓ c)) → K}
    (hv : v ∈ defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹)) :
    mixedFreqProjector p ζ ℓ *ᵥ v = v := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζsq : ζ ^ 2 ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : p ≠ 0)] at hζp
    exact zero_ne_one hζp
  have hrec := mem_defectEigenspace_mixed_iff.mp hv
  funext x
  obtain ⟨c, t⟩ := x
  rw [mixedFreqProjector, blockDiagonal'_mulVec_apply]
  by_cases hdvd : p ∣ ℓ c
  · rw [if_pos hdvd]
    have hζn : ζ ^ ℓ c = 1 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, pow_mul, hζp, one_pow]
    have hn0 : ((ℓ c : K)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (ℓ c))
    obtain ⟨a, b, hu⟩ :=
      cycle_recurrence_eq_fourier (v := fun k ↦ v ⟨c, k⟩) hζn hζsq
        fun s ↦ hrec c s
    rw [Matrix.smul_mulVec, Pi.smul_apply]
    have hufun : (fun k : ZMod (ℓ c) ↦ v ⟨c, k⟩) =
        a • (cyclePow ζ : ZMod (ℓ c) → K) +
          b • fun k : ZMod (ℓ c) ↦ cyclePow ζ (-k) := by
      funext k
      simp [hu k]
    rw [hufun, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      circulant_freqPairKernel_mulVec_cyclePow_of_sq hζn hζsq,
      circulant_freqPairKernel_mulVec_negCyclePow_of_sq hζn hζsq]
    have hval : (a • ((ℓ c : K) • (cyclePow ζ : ZMod (ℓ c) → K)) +
        b • ((ℓ c : K) • fun s : ZMod (ℓ c) ↦ cyclePow ζ (-s))) t =
        (ℓ c : K) * (a * cyclePow ζ t + b * cyclePow ζ (-t)) := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hval, smul_eq_mul, inv_mul_cancel_left₀ hn0]
    exact (hu t).symm
  · rw [if_neg hdvd]
    have hζn : ζ ^ ℓ c ≠ 1 := fun h ↦ hdvd (hζ.dvd_of_pow_eq_one _ h)
    have hv0 := cycle_recurrence_eq_zero (v := fun k ↦ v ⟨c, k⟩) hζ0 hζsq
      hζn fun s ↦ hrec c s
    rw [Matrix.zero_mulVec, Pi.zero_apply]
    exact (congrFun hv0 t).symm

/-- The range of the mixed projector lies in the frequency eigenspace. -/
theorem mixedFreqProjector_mulVec_mem {ζ : K} (hζp : ζ ^ p = 1)
    (v : (Σ c : C, ZMod (ℓ c)) → K) :
    mixedFreqProjector p ζ ℓ *ᵥ v ∈
      defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹) := by
  rw [mem_defectEigenspace_iff, Matrix.mulVec_mulVec,
    mixedDefect_mul_freqProjector hζp, Matrix.smul_mulVec]

/-- **The mixed frequency-pair space.**  The `μ = ζ + ζ⁻¹` eigenspace of
the mixed defect operator is exactly the range of the mixed projector. -/
theorem defectEigenspace_eq_range_mixedFreqProjector [CharZero K]
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹) =
      LinearMap.range (Matrix.toLin' (mixedFreqProjector p ζ ℓ)) := by
  apply le_antisymm
  · intro v hv
    exact ⟨v, by
      rw [Matrix.toLin'_apply,
        mixedFreqProjector_mulVec_of_mem hp hp2 hζ hv]⟩
  · rintro v ⟨w, rfl⟩
    rw [Matrix.toLin'_apply]
    exact mixedFreqProjector_mulVec_mem hζ.pow_eq_one w

/-- **Even dimension without equal lengths.**  The mixed frequency-pair
eigenspace has dimension twice the number of components whose length `p`
divides. -/
theorem finrank_defectEigenspace_mixed [CharZero K]
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Module.finrank K
        (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹)) =
      2 * (Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card := by
  classical
  have hζsq : ζ ^ 2 ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2
  have hidem : IsIdempotentElem
      (Matrix.toLin' (mixedFreqProjector p ζ ℓ)) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      mixedFreqProjector_mul_self hζ.pow_eq_one hζsq]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [Matrix.trace_toLin'_eq, trace_mixedFreqProjector,
    ← defectEigenspace_eq_range_mixedFreqProjector hp hp2 hζ] at htr
  have hcast : ((2 * (Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card : ℕ) :
      K) = ((Module.finrank K
        (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹)) : ℕ) : K) := by
    push_cast
    exact htr
  exact (Nat.cast_injective hcast).symm

theorem even_finrank_defectEigenspace_mixed [CharZero K]
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Even (Module.finrank K
      (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))) := by
  rw [finrank_defectEigenspace_mixed hp hp2 hζ, two_mul]
  exact ⟨_, rfl⟩

/-! ### The mixed trace identity -/

/-- Translation invariance of one diagonal cycle block propagates to
arbitrary shifts. -/
theorem mixed_diag_block_apply_eq_zero_row
    {M : Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K} {c : C}
    (hdiag : ∀ x y : ZMod (ℓ c),
      M ⟨c, x + 1⟩ ⟨c, y + 1⟩ = M ⟨c, x⟩ ⟨c, y⟩)
    (x y : ZMod (ℓ c)) : M ⟨c, x⟩ ⟨c, y⟩ = M ⟨c, 0⟩ ⟨c, y - x⟩ := by
  have hn : ∀ (m : ℕ) (x y : ZMod (ℓ c)),
      M ⟨c, x + (m : ZMod (ℓ c))⟩ ⟨c, y + (m : ZMod (ℓ c))⟩ =
        M ⟨c, x⟩ ⟨c, y⟩ := by
    intro m
    induction m with
    | zero => intro x y; simp
    | succ m ih =>
      intro x y
      have hx : x + ((m + 1 : ℕ) : ZMod (ℓ c)) =
          (x + (m : ZMod (ℓ c))) + 1 := by
        push_cast
        ring
      have hy : y + ((m + 1 : ℕ) : ZMod (ℓ c)) =
          (y + (m : ZMod (ℓ c))) + 1 := by
        push_cast
        ring
      rw [hx, hy, hdiag, ih]
  have hx := hn (-x).val x y
  rw [ZMod.natCast_rightInverse (-x), add_neg_cancel,
    ← sub_eq_add_neg] at hx
  exact hx.symm

/-- **Mixed trace against the projector.**  Only the divisible components
contribute, each through its own diagonal-anchor Fourier sum, and each
block normalization `1/ℓ c` cancels against its own cycle length. -/
theorem trace_mul_mixedFreqProjector [CharZero K]
    {M : Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K}
    (hdiag : ∀ c : C, p ∣ ℓ c → ∀ x y : ZMod (ℓ c),
      M ⟨c, x + 1⟩ ⟨c, y + 1⟩ = M ⟨c, x⟩ ⟨c, y⟩)
    (hsymm : M.IsSymm) {ζ : K} :
    Matrix.trace (M * mixedFreqProjector p ζ ℓ) =
      2 * ∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c,
        ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t := by
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
  have htrace : Matrix.trace (M * mixedFreqProjector p ζ ℓ) =
      ∑ c : C, if p ∣ ℓ c then
        ((ℓ c : K))⁻¹ * ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
      else 0 := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_congr rfl fun i _ ↦ hentry c i]
    by_cases hdvd : p ∣ ℓ c
    · simp only [if_pos hdvd, ← Finset.mul_sum]
    · simp [hdvd]
  rw [htrace]
  have hblock : ∀ c : C, p ∣ ℓ c →
      ((ℓ c : K))⁻¹ * ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i) =
        2 * ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t := by
    intro c hdvd
    have hn0 : ((ℓ c : K)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (ℓ c))
    have hre : ∀ i : ZMod (ℓ c),
        ∑ k : ZMod (ℓ c), M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i) =
          ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * freqPairKernel ζ t := by
      intro i
      refine Fintype.sum_equiv (Equiv.subRight i) _ _ fun k ↦ ?_
      rw [Equiv.subRight_apply,
        mixed_diag_block_apply_eq_zero_row (hdiag c hdvd) i k]
    rw [Finset.sum_congr rfl fun i _ ↦ hre i, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, inv_mul_cancel_left₀ hn0]
    have hcollect : ∀ t : ZMod (ℓ c),
        M ⟨c, 0⟩ ⟨c, t⟩ * freqPairKernel ζ t =
          M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t +
            M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ (-t) := by
      intro t
      rw [freqPairKernel, mul_add]
    rw [Finset.sum_congr rfl fun t _ ↦ hcollect t, Finset.sum_add_distrib]
    have heven : ∀ t : ZMod (ℓ c),
        M ⟨c, 0⟩ ⟨c, -t⟩ = M ⟨c, 0⟩ ⟨c, t⟩ := by
      intro t
      have h1 : M ⟨c, t⟩ ⟨c, 0⟩ = M ⟨c, 0⟩ ⟨c, -t⟩ := by
        rw [mixed_diag_block_apply_eq_zero_row (hdiag c hdvd) t 0,
          zero_sub]
      have h2 : M ⟨c, t⟩ ⟨c, 0⟩ = M ⟨c, 0⟩ ⟨c, t⟩ :=
        hsymm.apply ⟨c, 0⟩ ⟨c, t⟩
      rw [← h1, h2]
    have hneg : ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ (-t) =
        ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t := by
      have hswap : ∑ t : ZMod (ℓ c),
          M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ (-t) =
          ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, -t⟩ * cyclePow ζ t := by
        refine Fintype.sum_equiv (Equiv.neg (ZMod (ℓ c))) _ _ fun t ↦ ?_
        rw [Equiv.neg_apply, neg_neg]
      rw [hswap]
      exact Finset.sum_congr rfl fun t _ ↦ by rw [heven t]
    rw [hneg, two_mul]
  have hstep : ∀ c : C,
      (if p ∣ ℓ c then
        ((ℓ c : K))⁻¹ * ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
      else 0) =
        if p ∣ ℓ c then
          2 * ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t
        else 0 := by
    intro c
    by_cases hdvd : p ∣ ℓ c
    · rw [if_pos hdvd, if_pos hdvd, hblock c hdvd]
    · rw [if_neg hdvd, if_neg hdvd]
  rw [Finset.sum_congr rfl fun c _ ↦ hstep c, ← Finset.sum_filter,
    Finset.mul_sum]

/-- **The mixed frequency-pair trace identity.**  The trace of the
restricted operator on the mixed `μ = ζ + ζ⁻¹` eigenspace equals twice
the prime Fourier transform of the anchor weights of the divisible
components, fibered through each component's own reduction to `ZMod p`. -/
theorem trace_defectEigenspaceRestrict_mixed [CharZero K]
    {M : Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K}
    (hcomm : M * mixedDefectMatrix K ℓ = mixedDefectMatrix K ℓ * M)
    (hdiag : ∀ c : C, p ∣ ℓ c → ∀ x y : ZMod (ℓ c),
      M ⟨c, x + 1⟩ ⟨c, y + 1⟩ = M ⟨c, x⟩ ⟨c, y⟩)
    (hsymm : M.IsSymm)
    (hp : p.Prime) (hp2 : 2 < p) [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    LinearMap.trace K
        (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))
        (defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹)) =
      2 * ∑ s : ZMod p,
        (∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c,
          ∑ t ∈ Finset.univ.filter
            (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s),
            M ⟨c, 0⟩ ⟨c, t⟩) * ζ ^ s.val := by
  classical
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζsq : ζ ^ 2 ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2
  set P := mixedFreqProjector p ζ ℓ with hP
  set N := P * (M * P) with hN
  have hforall : ∀ x : (Σ c : C, ZMod (ℓ c)) → K, Matrix.toLin' N x ∈
      defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹) := by
    intro x
    rw [Matrix.toLin'_apply, hN, ← Matrix.mulVec_mulVec]
    exact mixedFreqProjector_mulVec_mem hζp _
  have hrestrict :
      (Matrix.toLin' N).restrict (fun x _ ↦ hforall x) =
        defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹) := by
    refine LinearMap.ext fun v ↦ Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, defectEigenspaceRestrict_coe,
      Matrix.toLin'_apply, hN, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec,
      mixedFreqProjector_mulVec_of_mem hp hp2 hζ v.2,
      mixedFreqProjector_mulVec_of_mem hp hp2 hζ
        (mulVec_mem_defectEigenspace hcomm v.2)]
  have htr := LinearMap.trace_restrict_eq_of_forall_mem
    (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))
    (Matrix.toLin' N) hforall (fun x _ ↦ hforall x)
  rw [hrestrict] at htr
  rw [htr, Matrix.trace_toLin'_eq, hN, hP, Matrix.trace_mul_comm,
    Matrix.mul_assoc, mixedFreqProjector_mul_self hζp hζsq,
    trace_mul_mixedFreqProjector hdiag hsymm]
  congr 1
  have hfiber : ∀ c : C, p ∣ ℓ c →
      ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t =
        ∑ s : ZMod p,
          (∑ t ∈ Finset.univ.filter
            (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s),
            M ⟨c, 0⟩ ⟨c, t⟩) * ζ ^ s.val := by
    intro c hdvd
    haveI : NeZero (ℓ c) := inferInstance
    rw [sum_mul_cyclePow_eq_fiberwise hdvd hζp
      (fun t ↦ M ⟨c, 0⟩ ⟨c, t⟩)]
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    apply Finset.sum_congr ?_ fun t _ ↦ rfl
    apply Finset.filter_congr
    intro t _
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  rw [Finset.sum_congr rfl fun c hc ↦
    hfiber c (Finset.mem_filter.mp hc).2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]

end Mixed

end

end Erdos85
