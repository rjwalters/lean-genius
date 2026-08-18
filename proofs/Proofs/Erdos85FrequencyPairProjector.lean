import Proofs.Erdos85FrequencyPairEigenspace
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.PID

/-!
# Frequency-pair projector on labeled equal cycles

The second-order defect two-factor of the equal-cycle extremal graph is a
disjoint union of cycles of one common length `r`, presented here in
labeled coordinates: the vertex type is `ZMod r × C` for a cycle index
type `C`, and the defect operator is the block-diagonal matrix whose
blocks are the circulant `±1`-step matrices.

For `ζ` with `ζ^r = 1` and `ζ² ≠ 1`, the `μ = ζ + ζ⁻¹` eigenspace of the
defect operator is described explicitly by the rank-two-per-cycle spectral
projector `P` with circulant kernel `(ζ^(x-y) + ζ^(y-x)) / r`:

* `P` is idempotent, commutes with the defect operator, and satisfies
  `D * P = μ • P`;
* every `μ`-eigenvector is fixed by `P` (a two-term recurrence argument),
  so the eigenspace is exactly the range of `P`;
* consequently the eigenspace has dimension `2 * #cycles` — in particular
  even, as required by the square-trace branch;
* for any symmetric matrix `M` commuting with the defect operator whose
  diagonal cycle blocks are translation invariant, the trace of the
  restriction of `M` to the eigenspace equals
  `2 * ∑ t, (∑ c, M (0,c) (t,c)) * ζ^t`,
  twice the Fourier transform of the diagonal-anchor weight — with no
  residual normalization by `r`;
* if moreover `p ∣ r` and `ζ^p = 1`, the Fourier sum regroups along the
  reduction `ZMod r → ZMod p` into a prime-frequency sum of projected
  multiplicities.

Everything is stated over an abstract field, so it applies verbatim to the
cyclotomic field used by the prime Fourier convolution files.
-/

namespace Erdos85

noncomputable section

open Matrix

/-! ## Cyclic powers of a root of unity -/

section CyclePow

variable {K : Type*} [Field K] {r : ℕ} [NeZero r]

/-- `ζ ^ t` for a cyclic exponent `t : ZMod r`. -/
def cyclePow (ζ : K) (t : ZMod r) : K := ζ ^ t.val

theorem pow_natMod_eq {ζ : K} {m : ℕ} (hζ : ζ ^ m = 1) (n : ℕ) :
    ζ ^ (n % m) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n m]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

omit [NeZero r] in
theorem cyclePow_natCast {ζ : K} (hζr : ζ ^ r = 1) (n : ℕ) :
    cyclePow ζ (n : ZMod r) = ζ ^ n := by
  rw [cyclePow, ZMod.val_natCast, pow_natMod_eq hζr]

omit [NeZero r] in
@[simp] theorem cyclePow_zero (ζ : K) : cyclePow ζ (0 : ZMod r) = 1 := by
  rw [cyclePow, ZMod.val_zero, pow_zero]

theorem cyclePow_add {ζ : K} (hζr : ζ ^ r = 1) (s t : ZMod r) :
    cyclePow ζ (s + t) = cyclePow ζ s * cyclePow ζ t := by
  have hs : ((s.val : ℕ) : ZMod r) = s := ZMod.natCast_rightInverse s
  have ht : ((t.val : ℕ) : ZMod r) = t := ZMod.natCast_rightInverse t
  rw [← hs, ← ht, ← Nat.cast_add, cyclePow_natCast hζr,
    cyclePow_natCast hζr, cyclePow_natCast hζr, pow_add]

theorem ne_zero_of_pow_eq_one {ζ : K} (hζr : ζ ^ r = 1) : ζ ≠ 0 := by
  intro h
  rw [h, zero_pow (NeZero.ne r)] at hζr
  exact zero_ne_one hζr

theorem cyclePow_one {ζ : K} (hζr : ζ ^ r = 1) :
    cyclePow ζ (1 : ZMod r) = ζ := by
  have h : ((1 : ℕ) : ZMod r) = (1 : ZMod r) := Nat.cast_one
  rw [← h, cyclePow_natCast hζr, pow_one]

theorem cyclePow_neg {ζ : K} (hζr : ζ ^ r = 1) (t : ZMod r) :
    cyclePow ζ (-t) = (cyclePow ζ t)⁻¹ := by
  have h : cyclePow ζ (-t) * cyclePow ζ t = 1 := by
    rw [← cyclePow_add hζr, neg_add_cancel, cyclePow_zero]
  exact eq_inv_of_mul_eq_one_left h

theorem cyclePow_add_one {ζ : K} (hζr : ζ ^ r = 1) (t : ZMod r) :
    cyclePow ζ (t + 1) = ζ * cyclePow ζ t := by
  rw [cyclePow_add hζr, cyclePow_one hζr, mul_comm]

theorem cyclePow_sub_one {ζ : K} (hζr : ζ ^ r = 1) (t : ZMod r) :
    cyclePow ζ (t - 1) = ζ⁻¹ * cyclePow ζ t := by
  rw [sub_eq_add_neg, add_comm, cyclePow_add hζr, cyclePow_neg hζr,
    cyclePow_one hζr]

/-- Geometric-sum vanishing over one full cycle. -/
theorem sum_cyclePow_eq_zero {ζ : K} (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    ∑ t : ZMod r, cyclePow ζ t = 0 := by
  have hshift : ∑ t : ZMod r, cyclePow ζ (t + 1) =
      ∑ t : ZMod r, cyclePow ζ t :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod r)) _ _ fun t ↦ rfl
  have hmul : ζ * ∑ t : ZMod r, cyclePow ζ t =
      ∑ t : ZMod r, cyclePow ζ t := by
    rw [Finset.mul_sum, ← hshift]
    exact Finset.sum_congr rfl fun t _ ↦ (cyclePow_add_one hζr t).symm
  have hfac : (ζ - 1) * ∑ t : ZMod r, cyclePow ζ t = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hζ1
  · exact h

/-- With `r` odd, doubling is a bijection of `ZMod r`, so the geometric sum
along any arithmetic progression of common difference two also vanishes. -/
theorem sum_cyclePow_two_mul_add_eq_zero (hrOdd : Odd r) {ζ : K}
    (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) (a : ZMod r) :
    ∑ t : ZMod r, cyclePow ζ (2 * t + a) = 0 := by
  have hunit : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
      (Nat.coprime_two_left.mpr hrOdd)
  have hbij : Function.Bijective (fun t : ZMod r ↦ 2 * t + a) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun s t hst ↦ ?_, rfl⟩
    simp only at hst
    exact hunit.mul_left_cancel (add_right_cancel hst)
  have h1 : ∑ t : ZMod r, cyclePow ζ (2 * t + a) =
      ∑ s : ZMod r, cyclePow ζ s :=
    Fintype.sum_bijective _ hbij _ _ fun t ↦ rfl
  rw [h1, sum_cyclePow_eq_zero hζr hζ1]

end CyclePow

/-! ## The labeled defect operator and the frequency-pair projector -/

section CycleMatrices

variable (K : Type*) [Field K] (C : Type*) [Fintype C] [DecidableEq C]
  (r : ℕ) [NeZero r]

/-- Kernel of one defect cycle block: unit steps in both directions. -/
def defectKernel : ZMod r → K := fun t ↦
  (if t = 1 then 1 else 0) + (if t = -1 then 1 else 0)

/-- The standard second-order defect operator on labeled equal cycles:
block diagonal with one circulant `±1`-step block per cycle. -/
def cycleDefectMatrix : Matrix (ZMod r × C) (ZMod r × C) K :=
  Matrix.blockDiagonal fun _ : C ↦ Matrix.circulant (defectKernel K r)

variable {K r} in
/-- The frequency-pair kernel `ζ^t + ζ^(-t)`. -/
def freqPairKernel (ζ : K) : ZMod r → K := fun t ↦
  cyclePow ζ t + cyclePow ζ (-t)

variable {K} in
/-- The frequency-pair spectral projector: block diagonal, of rank two on
every cycle, with circulant kernel `(ζ^(x-y) + ζ^(y-x)) / r`. -/
def freqPairProjector (ζ : K) : Matrix (ZMod r × C) (ZMod r × C) K :=
  (r : K)⁻¹ •
    Matrix.blockDiagonal fun _ : C ↦ Matrix.circulant (freqPairKernel ζ)

variable {K C r}

/-! ### Convolution identities for the kernels -/

theorem circulant_cyclePow_mulVec_cyclePow {ζ : K} (hζr : ζ ^ r = 1) :
    Matrix.circulant (cyclePow ζ) *ᵥ (cyclePow ζ : ZMod r → K) =
      (r : K) • cyclePow ζ := by
  funext t
  have hterm : ∀ s : ZMod r, cyclePow ζ (t - s) * cyclePow ζ s =
      cyclePow ζ t := fun s ↦ by
    rw [← cyclePow_add hζr, sub_add_cancel]
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Pi.smul_apply, smul_eq_mul]

theorem circulant_cyclePow_mulVec_neg (hrOdd : Odd r) {ζ : K}
    (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    Matrix.circulant (cyclePow ζ) *ᵥ
      (fun s : ZMod r ↦ cyclePow ζ (-s)) = 0 := by
  funext t
  have hterm : ∀ s : ZMod r, cyclePow ζ (t - s) * cyclePow ζ (-s) =
      cyclePow ζ (2 * (-s) + t) := fun s ↦ by
    rw [← cyclePow_add hζr]
    exact congrArg (cyclePow ζ) (by ring)
  have hneg : ∑ s : ZMod r, cyclePow ζ (2 * (-s) + t) =
      ∑ s : ZMod r, cyclePow ζ (2 * s + t) :=
    Fintype.sum_equiv (Equiv.neg (ZMod r)) _ _ fun s ↦ rfl
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm,
    Pi.zero_apply]
  rw [hneg, sum_cyclePow_two_mul_add_eq_zero hrOdd hζr hζ1]

theorem circulant_neg_mulVec_cyclePow (hrOdd : Odd r) {ζ : K}
    (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    Matrix.circulant (fun s : ZMod r ↦ cyclePow ζ (-s)) *ᵥ
      (cyclePow ζ : ZMod r → K) = 0 := by
  funext t
  have hterm : ∀ s : ZMod r, cyclePow ζ (-(t - s)) * cyclePow ζ s =
      cyclePow ζ (2 * s + -t) := fun s ↦ by
    rw [← cyclePow_add hζr]
    exact congrArg (cyclePow ζ) (by ring)
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm,
    Pi.zero_apply]
  rw [sum_cyclePow_two_mul_add_eq_zero hrOdd hζr hζ1]

theorem circulant_neg_mulVec_neg {ζ : K} (hζr : ζ ^ r = 1) :
    Matrix.circulant (fun s : ZMod r ↦ cyclePow ζ (-s)) *ᵥ
      (fun s : ZMod r ↦ cyclePow ζ (-s)) =
      (r : K) • fun s : ZMod r ↦ cyclePow ζ (-s) := by
  funext t
  have hterm : ∀ s : ZMod r, cyclePow ζ (-(t - s)) * cyclePow ζ (-s) =
      cyclePow ζ (-t) := fun s ↦ by
    rw [← cyclePow_add hζr]
    exact congrArg (cyclePow ζ) (by ring)
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Pi.smul_apply, smul_eq_mul]

theorem circulant_defectKernel_mulVec_cyclePow {ζ : K} (hζr : ζ ^ r = 1) :
    Matrix.circulant (defectKernel K r) *ᵥ (cyclePow ζ : ZMod r → K) =
      (ζ + ζ⁻¹) • cyclePow ζ := by
  funext t
  have hterm : ∀ s : ZMod r,
      defectKernel K r (t - s) * cyclePow ζ s =
        (if s = t - 1 then cyclePow ζ s else 0) +
          (if s = t + 1 then cyclePow ζ s else 0) := fun s ↦ by
    have h1 : (t - s = 1) = (s = t - 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    have h2 : (t - s = -1) = (s = t + 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    rw [defectKernel]
    simp only [h1, h2, add_mul, ite_mul, one_mul, zero_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (t - 1),
    Finset.sum_ite_eq' Finset.univ (t + 1)]
  simp only [Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
  rw [cyclePow_sub_one hζr, cyclePow_add_one hζr]
  ring

theorem circulant_defectKernel_mulVec_neg {ζ : K} (hζr : ζ ^ r = 1) :
    Matrix.circulant (defectKernel K r) *ᵥ
      (fun s : ZMod r ↦ cyclePow ζ (-s)) =
      (ζ + ζ⁻¹) • fun s : ZMod r ↦ cyclePow ζ (-s) := by
  funext t
  have hterm : ∀ s : ZMod r,
      defectKernel K r (t - s) * cyclePow ζ (-s) =
        (if s = t - 1 then cyclePow ζ (-s) else 0) +
          (if s = t + 1 then cyclePow ζ (-s) else 0) := fun s ↦ by
    have h1 : (t - s = 1) = (s = t - 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    have h2 : (t - s = -1) = (s = t + 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    rw [defectKernel]
    simp only [h1, h2, add_mul, ite_mul, one_mul, zero_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (t - 1),
    Finset.sum_ite_eq' Finset.univ (t + 1)]
  simp only [Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
  have hm : -(t - 1) = -t + 1 := by ring
  have hp : -(t + 1) = -t - 1 := by ring
  rw [hm, hp, cyclePow_sub_one hζr, cyclePow_add_one hζr]
  ring

omit [NeZero r] in
/-- The frequency-pair kernel splits as the two pure-frequency kernels. -/
theorem freqPairKernel_eq (ζ : K) :
    (freqPairKernel ζ : ZMod r → K) =
      cyclePow ζ + fun s : ZMod r ↦ cyclePow ζ (-s) := rfl

/-- Scalars pass through a constant block-diagonal family. -/
theorem blockDiagonal_const_smul (x : K)
    (M : Matrix (ZMod r) (ZMod r) K) :
    (Matrix.blockDiagonal fun _ : C ↦ x • M) =
      x • Matrix.blockDiagonal fun _ : C ↦ M :=
  Matrix.blockDiagonal_smul x fun _ ↦ M

theorem circulant_freqPairKernel_mulVec_freqPairKernel (hrOdd : Odd r)
    {ζ : K} (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    Matrix.circulant (freqPairKernel ζ) *ᵥ
      (freqPairKernel ζ : ZMod r → K) = (r : K) • freqPairKernel ζ := by
  rw [freqPairKernel_eq, circulant_add, add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_add, circulant_cyclePow_mulVec_cyclePow hζr,
    circulant_cyclePow_mulVec_neg hrOdd hζr hζ1,
    circulant_neg_mulVec_cyclePow hrOdd hζr hζ1,
    circulant_neg_mulVec_neg hζr, smul_add]
  abel

theorem circulant_defectKernel_mulVec_freqPairKernel {ζ : K}
    (hζr : ζ ^ r = 1) :
    Matrix.circulant (defectKernel K r) *ᵥ
      (freqPairKernel ζ : ZMod r → K) = (ζ + ζ⁻¹) • freqPairKernel ζ := by
  rw [freqPairKernel_eq, Matrix.mulVec_add,
    circulant_defectKernel_mulVec_cyclePow hζr,
    circulant_defectKernel_mulVec_neg hζr, smul_add]

/-! ### Projector identities -/

theorem freqPairProjector_mul_self (hrOdd : Odd r) {ζ : K}
    (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) (hr0 : (r : K) ≠ 0) :
    freqPairProjector C r ζ * freqPairProjector C r ζ =
      freqPairProjector C r ζ := by
  rw [freqPairProjector, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.blockDiagonal_mul]
  have hblock : (fun c : C ↦
      Matrix.circulant (freqPairKernel ζ) *
        Matrix.circulant (freqPairKernel ζ)) = fun _ : C ↦
      (r : K) • Matrix.circulant (freqPairKernel (r := r) ζ) := by
    funext c
    rw [Matrix.circulant_mul,
      circulant_freqPairKernel_mulVec_freqPairKernel hrOdd hζr hζ1,
      Matrix.circulant_smul]
  rw [hblock, blockDiagonal_const_smul, smul_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ hr0, mul_one]

theorem cycleDefectMatrix_mul_freqPairProjector {ζ : K} (hζr : ζ ^ r = 1) :
    cycleDefectMatrix K C r * freqPairProjector C r ζ =
      (ζ + ζ⁻¹) • freqPairProjector C r ζ := by
  rw [cycleDefectMatrix, freqPairProjector, Matrix.mul_smul,
    ← Matrix.blockDiagonal_mul]
  have hblock : (fun c : C ↦
      Matrix.circulant (defectKernel K r) *
        Matrix.circulant (freqPairKernel ζ)) = fun _ : C ↦
      (ζ + ζ⁻¹) • Matrix.circulant (freqPairKernel (r := r) ζ) := by
    funext c
    rw [Matrix.circulant_mul,
      circulant_defectKernel_mulVec_freqPairKernel hζr,
      Matrix.circulant_smul]
  rw [hblock, blockDiagonal_const_smul, smul_smul, smul_smul, mul_comm]

theorem freqPairProjector_mul_cycleDefectMatrix {ζ : K} (hζr : ζ ^ r = 1) :
    freqPairProjector C r ζ * cycleDefectMatrix K C r =
      (ζ + ζ⁻¹) • freqPairProjector C r ζ := by
  rw [freqPairProjector, cycleDefectMatrix, Matrix.smul_mul,
    ← Matrix.blockDiagonal_mul]
  have hblock : (fun c : C ↦
      Matrix.circulant (freqPairKernel ζ) *
        Matrix.circulant (defectKernel K r)) = fun _ : C ↦
      (ζ + ζ⁻¹) • Matrix.circulant (freqPairKernel (r := r) ζ) := by
    funext c
    rw [Matrix.circulant_mul_comm, Matrix.circulant_mul,
      circulant_defectKernel_mulVec_freqPairKernel hζr,
      Matrix.circulant_smul]
  rw [hblock, blockDiagonal_const_smul, smul_smul, mul_comm ((r : K)⁻¹),
    ← smul_smul]

/-- Column sums of the defect operator are two, in matrix form: the
all-ones matrix satisfies `J * D = 2 • J`. -/
theorem ones_mul_cycleDefectMatrix :
    (Matrix.of fun _ _ : ZMod r × C ↦ (1 : K)) * cycleDefectMatrix K C r =
      (2 : K) • Matrix.of fun _ _ : ZMod r × C ↦ (1 : K) := by
  ext x ⟨j, e⟩
  rw [Matrix.mul_apply]
  have hentry : ∀ z : ZMod r × C,
      (Matrix.of fun _ _ : ZMod r × C ↦ (1 : K)) x z *
          cycleDefectMatrix K C r z (j, e) =
        (if z = (j - 1, e) then 1 else 0) +
          (if z = (j + 1, e) then 1 else 0) := by
    rintro ⟨k, f⟩
    rw [Matrix.of_apply, one_mul, cycleDefectMatrix,
      Matrix.blockDiagonal_apply]
    by_cases hf : f = e
    · subst hf
      have h1 : (k - j = 1) = ((k, f) = (j + 1, f)) := by
        apply propext
        rw [Prod.mk.injEq]
        exact ⟨fun h ↦ ⟨by linear_combination h, rfl⟩,
          fun h ↦ by linear_combination h.1⟩
      have h2 : (k - j = -1) = ((k, f) = (j - 1, f)) := by
        apply propext
        rw [Prod.mk.injEq]
        exact ⟨fun h ↦ ⟨by linear_combination h, rfl⟩,
          fun h ↦ by linear_combination h.1⟩
      simp only [Matrix.circulant_apply, defectKernel, h1, h2, if_true]
      exact add_comm _ _
    · have hne1 : ¬((k, f) = (j - 1, e)) := by
        simp [Prod.ext_iff, hf]
      have hne2 : ¬((k, f) = (j + 1, e)) := by
        simp [Prod.ext_iff, hf]
      simp [hf, hne1, hne2]
  rw [Finset.sum_congr rfl fun z _ ↦ hentry z, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ ((j - 1, e) : ZMod r × C),
    Finset.sum_ite_eq' Finset.univ ((j + 1, e) : ZMod r × C)]
  simp only [Finset.mem_univ, if_true, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, mul_one]
  norm_num

/-- The trace of the frequency-pair projector is twice the number of
cycles. -/
theorem trace_freqPairProjector {ζ : K} (hr0 : (r : K) ≠ 0) :
    Matrix.trace (freqPairProjector C r ζ) = 2 * Fintype.card C := by
  rw [freqPairProjector, Matrix.trace_smul, Matrix.trace_blockDiagonal]
  have hblock : ∀ c : C,
      Matrix.trace (Matrix.circulant (freqPairKernel (r := r) ζ)) =
        (r : K) * 2 := by
    intro c
    have hdiag : ∀ i : ZMod r,
        Matrix.circulant (freqPairKernel (r := r) ζ) i i = 2 := fun i ↦ by
      rw [Matrix.circulant_apply, sub_self, freqPairKernel, neg_zero,
        cyclePow_zero]
      norm_num
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, hdiag, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun c _ ↦ hblock c, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  field_simp

end CycleMatrices

/-! ## The eigenspace is exactly the range of the projector -/

section Eigenspace

variable {K : Type*} [Field K] {C : Type*} [Fintype C] [DecidableEq C]
  {r : ℕ} [NeZero r]

/-- Splitting the pair kernel through the outer circulant factor. -/
theorem circulant_freqPairKernel_mulVec_cyclePow (hrOdd : Odd r) {ζ : K}
    (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    Matrix.circulant (freqPairKernel ζ) *ᵥ (cyclePow ζ : ZMod r → K) =
      (r : K) • cyclePow ζ := by
  rw [freqPairKernel_eq, Matrix.circulant_add, Matrix.add_mulVec,
    circulant_cyclePow_mulVec_cyclePow hζr,
    circulant_neg_mulVec_cyclePow hrOdd hζr hζ1, add_zero]

theorem circulant_freqPairKernel_mulVec_negCyclePow (hrOdd : Odd r) {ζ : K}
    (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    Matrix.circulant (freqPairKernel ζ) *ᵥ
      (fun s : ZMod r ↦ cyclePow ζ (-s)) =
      (r : K) • fun s : ZMod r ↦ cyclePow ζ (-s) := by
  rw [freqPairKernel_eq, Matrix.circulant_add, Matrix.add_mulVec,
    circulant_cyclePow_mulVec_neg hrOdd hζr hζ1,
    circulant_neg_mulVec_neg hζr, zero_add]

/-- A block-diagonal circulant acts cycle by cycle. -/
theorem blockDiagonal_circulant_mulVec_apply (w : ZMod r → K)
    (v : ZMod r × C → K) (t : ZMod r) (c : C) :
    (Matrix.blockDiagonal (fun _ : C ↦ Matrix.circulant w) *ᵥ v) (t, c) =
      (Matrix.circulant w *ᵥ fun k : ZMod r ↦ v (k, c)) t := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  have hentry : ∀ f : C,
      Matrix.blockDiagonal (fun _ : C ↦ Matrix.circulant w) (t, c) (k, f) *
          v (k, f) =
        if c = f then Matrix.circulant w t k * v (k, f) else 0 := by
    intro f
    rw [Matrix.blockDiagonal_apply]
    by_cases h : c = f <;> simp [h]
  rw [Finset.sum_congr rfl fun f _ ↦ hentry f,
    Finset.sum_ite_eq Finset.univ c fun f ↦ Matrix.circulant w t k * v (k, f)]
  simp

/-- Entrywise action of the labeled defect operator: unit steps in both
directions along the own cycle. -/
theorem cycleDefectMatrix_mulVec_apply (v : ZMod r × C → K) (t : ZMod r)
    (c : C) :
    (cycleDefectMatrix K C r *ᵥ v) (t, c) = v (t - 1, c) + v (t + 1, c) := by
  rw [cycleDefectMatrix, blockDiagonal_circulant_mulVec_apply]
  have hentry : ∀ k : ZMod r,
      Matrix.circulant (defectKernel K r) t k * v (k, c) =
        (if k = t - 1 then v (k, c) else 0) +
          (if k = t + 1 then v (k, c) else 0) := by
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
    Finset.sum_ite_eq' Finset.univ (t - 1) fun k ↦ v (k, c),
    Finset.sum_ite_eq' Finset.univ (t + 1) fun k ↦ v (k, c)]
  simp

/-- Membership in the frequency eigenspace is the cyclic two-term
recurrence. -/
theorem mem_defectEigenspace_cycleDefect_iff {μ : K}
    {v : ZMod r × C → K} :
    v ∈ defectEigenspace (cycleDefectMatrix K C r) μ ↔
      ∀ (c : C) (t : ZMod r),
        v (t - 1, c) + v (t + 1, c) = μ * v (t, c) := by
  rw [mem_defectEigenspace_iff]
  constructor
  · intro h c t
    have := congrFun h (t, c)
    rw [cycleDefectMatrix_mulVec_apply] at this
    simpa using this
  · intro h
    funext x
    obtain ⟨t, c⟩ := x
    rw [cycleDefectMatrix_mulVec_apply]
    simpa using h c t

/-- The frequency pair `μ = ζ + ζ⁻¹` is never the trivial column-sum
eigenvalue `2` when `ζ ≠ 1`. -/
theorem zeta_add_inv_ne_two {ζ : K} (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    ζ + ζ⁻¹ ≠ 2 := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζr
  intro h
  have hz : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  have hfac : (ζ - 1) * (ζ - 1) = 0 := by linear_combination ζ * h - hz
  exact hζ1 (sub_eq_zero.mp (mul_self_eq_zero.mp hfac))

/-- **Recurrence solution.**  On each cycle, a `μ = ζ + ζ⁻¹` eigenvector is
an explicit combination of the `ζ` and `ζ⁻¹` Fourier vectors. -/
theorem eigenvector_eq_fourier_pair_on_cycle {ζ : K}
    (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1)
    {v : ZMod r × C → K}
    (hv : v ∈ defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
    (c : C) :
    ∃ a b : K, ∀ s : ZMod r,
      v (s, c) = a * cyclePow ζ s + b * cyclePow ζ (-s) := by
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζr
  have hz : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  have hden : ζ - ζ⁻¹ ≠ 0 := by
    intro h
    apply hζsq
    have hinv : ζ = ζ⁻¹ := sub_eq_zero.mp h
    calc ζ ^ 2 = ζ * ζ := sq ζ
      _ = ζ * ζ⁻¹ := congrArg (fun w ↦ ζ * w) hinv
      _ = 1 := hz
  have hden2 : ζ ^ 2 - 1 ≠ 0 := fun h ↦ hζsq (by linear_combination h)
  have hrec := mem_defectEigenspace_cycleDefect_iff.mp hv
  refine ⟨(v (1, c) - ζ⁻¹ * v (0, c)) / (ζ - ζ⁻¹),
    (ζ * v (0, c) - v (1, c)) / (ζ - ζ⁻¹), ?_⟩
  set a : K := (v (1, c) - ζ⁻¹ * v (0, c)) / (ζ - ζ⁻¹) with haDef
  set b : K := (ζ * v (0, c) - v (1, c)) / (ζ - ζ⁻¹) with hbDef
  have hnat : ∀ n : ℕ,
      v (((n : ℕ) : ZMod r), c) = a * ζ ^ n + b * ζ⁻¹ ^ n ∧
        v (((n + 1 : ℕ) : ZMod r), c) =
          a * ζ ^ (n + 1) + b * ζ⁻¹ ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      constructor
      · rw [Nat.cast_zero, pow_zero, pow_zero, mul_one, mul_one, haDef,
          hbDef]
        field_simp
        ring
      · rw [Nat.cast_one, pow_one, pow_one, haDef, hbDef]
        field_simp
        ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hstep := hrec c (((n + 1 : ℕ) : ZMod r))
      have hc1 : ((n + 1 : ℕ) : ZMod r) - 1 = ((n : ℕ) : ZMod r) := by
        push_cast
        ring
      have hc2 : ((n + 1 : ℕ) : ZMod r) + 1 = ((n + 1 + 1 : ℕ) : ZMod r) := by
        push_cast
        ring
      rw [hc1, hc2, ih.1, ih.2] at hstep
      have hsolve : v (((n + 1 + 1 : ℕ) : ZMod r), c) =
          (ζ + ζ⁻¹) * (a * ζ ^ (n + 1) + b * ζ⁻¹ ^ (n + 1)) -
            (a * ζ ^ n + b * ζ⁻¹ ^ n) :=
        eq_sub_of_add_eq' hstep
      rw [hsolve]
      linear_combination (a * ζ ^ n + b * ζ⁻¹ ^ n) * hz
  intro s
  have h := (hnat s.val).1
  rw [ZMod.natCast_rightInverse s] at h
  rw [h, cyclePow_neg hζr, cyclePow, ← inv_pow]

/-- **Fixed-point property.**  Every `μ = ζ + ζ⁻¹` eigenvector of the
labeled defect operator is fixed by the frequency-pair projector. -/
theorem freqPairProjector_mulVec_of_mem (hrOdd : Odd r) {ζ : K}
    (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1) (hr0 : (r : K) ≠ 0)
    {v : ZMod r × C → K}
    (hv : v ∈ defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹)) :
    freqPairProjector C r ζ *ᵥ v = v := by
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  funext x
  obtain ⟨t, c⟩ := x
  obtain ⟨a, b, hu⟩ := eigenvector_eq_fourier_pair_on_cycle hζr hζsq hv c
  rw [freqPairProjector, Matrix.smul_mulVec, Pi.smul_apply,
    blockDiagonal_circulant_mulVec_apply]
  have hufun : (fun k : ZMod r ↦ v (k, c)) =
      a • (cyclePow ζ : ZMod r → K) +
        b • fun k : ZMod r ↦ cyclePow ζ (-k) := by
    funext k
    simp [hu k]
  rw [hufun, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    circulant_freqPairKernel_mulVec_cyclePow hrOdd hζr hζ1,
    circulant_freqPairKernel_mulVec_negCyclePow hrOdd hζr hζ1]
  have hval : (a • ((r : K) • (cyclePow ζ : ZMod r → K)) +
      b • ((r : K) • fun s : ZMod r ↦ cyclePow ζ (-s))) t =
      (r : K) * (a * cyclePow ζ t + b * cyclePow ζ (-t)) := by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hval, smul_eq_mul, inv_mul_cancel_left₀ hr0, hu t]

/-- The range of the projector lies in the frequency eigenspace. -/
theorem freqPairProjector_mulVec_mem {ζ : K} (hζr : ζ ^ r = 1)
    (v : ZMod r × C → K) :
    freqPairProjector C r ζ *ᵥ v ∈
      defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹) := by
  rw [mem_defectEigenspace_iff, Matrix.mulVec_mulVec,
    cycleDefectMatrix_mul_freqPairProjector hζr, Matrix.smul_mulVec]

/-- **The frequency-pair space.**  The `μ = ζ + ζ⁻¹` eigenspace of the
labeled defect operator is exactly the range of the frequency-pair
projector. -/
theorem defectEigenspace_eq_range_freqPairProjector (hrOdd : Odd r)
    {ζ : K} (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1) (hr0 : (r : K) ≠ 0) :
    defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹) =
      LinearMap.range (Matrix.toLin' (freqPairProjector C r ζ)) := by
  apply le_antisymm
  · intro v hv
    exact ⟨v, by
      rw [Matrix.toLin'_apply,
        freqPairProjector_mulVec_of_mem hrOdd hζr hζsq hr0 hv]⟩
  · rintro v ⟨w, rfl⟩
    rw [Matrix.toLin'_apply]
    exact freqPairProjector_mulVec_mem hζr w

/-- **Even dimension.**  The frequency-pair eigenspace has dimension
exactly twice the number of cycles. -/
theorem finrank_defectEigenspace [CharZero K] (hrOdd : Odd r)
    {ζ : K} (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Module.finrank K
        (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹)) =
      2 * Fintype.card C := by
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  have hr0 : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hidem : IsIdempotentElem (Matrix.toLin' (freqPairProjector C r ζ)) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      freqPairProjector_mul_self hrOdd hζr hζ1 hr0]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [Matrix.trace_toLin'_eq, trace_freqPairProjector hr0,
    ← defectEigenspace_eq_range_freqPairProjector hrOdd hζr hζsq hr0]
    at htr
  have hcast : ((2 * Fintype.card C : ℕ) : K) =
      ((Module.finrank K
        (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹)) : ℕ) : K) := by
    push_cast
    exact htr
  exact (Nat.cast_injective hcast).symm

/-- The evenness needed by the square-trace branch. -/
theorem even_finrank_defectEigenspace [CharZero K] (hrOdd : Odd r)
    {ζ : K} (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Even (Module.finrank K
      (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))) := by
  rw [finrank_defectEigenspace hrOdd hζr hζsq, two_mul]
  exact ⟨Fintype.card C, rfl⟩

end Eigenspace

/-! ## The trace identity -/

section Trace

variable {K : Type*} [Field K] {C : Type*} [Fintype C] [DecidableEq C]
  {r : ℕ} [NeZero r]

/-- Translation invariance of a diagonal cycle block propagates from unit
shifts to arbitrary shifts. -/
theorem diag_block_apply_eq_zero_row
    {M : Matrix (ZMod r × C) (ZMod r × C) K}
    (hdiag : ∀ (c : C) (x y : ZMod r),
      M (x + 1, c) (y + 1, c) = M (x, c) (y, c))
    (c : C) (x y : ZMod r) : M (x, c) (y, c) = M (0, c) (y - x, c) := by
  have hn : ∀ (n : ℕ) (x y : ZMod r),
      M (x + (n : ZMod r), c) (y + (n : ZMod r), c) = M (x, c) (y, c) := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      have hx : x + ((n + 1 : ℕ) : ZMod r) = (x + (n : ZMod r)) + 1 := by
        push_cast
        ring
      have hy : y + ((n + 1 : ℕ) : ZMod r) = (y + (n : ZMod r)) + 1 := by
        push_cast
        ring
      rw [hx, hy, hdiag, ih]
  have hx := hn (-x).val x y
  rw [ZMod.natCast_rightInverse (-x), add_neg_cancel,
    ← sub_eq_add_neg] at hx
  exact hx.symm

/-- **Trace against the projector.**  For a symmetric matrix whose diagonal
cycle blocks are translation invariant, the trace against the
frequency-pair projector is twice the Fourier transform of the
diagonal-anchor weight `t ↦ ∑ c, M (0,c) (t,c)`.  The normalization `1/r`
of the projector cancels exactly against the cycle length. -/
theorem trace_mul_freqPairProjector
    {M : Matrix (ZMod r × C) (ZMod r × C) K}
    (hdiag : ∀ (c : C) (x y : ZMod r),
      M (x + 1, c) (y + 1, c) = M (x, c) (y, c))
    (hsymm : M.IsSymm) {ζ : K} (hr0 : (r : K) ≠ 0) :
    Matrix.trace (M * freqPairProjector C r ζ) =
      2 * ∑ t : ZMod r, (∑ c : C, M (0, c) (t, c)) * cyclePow ζ t := by
  have hentry : ∀ (i : ZMod r) (c : C),
      (M * freqPairProjector C r ζ) (i, c) (i, c) =
        (r : K)⁻¹ * ∑ k : ZMod r,
          M (i, c) (k, c) * freqPairKernel ζ (k - i) := by
    intro i c
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hcol : ∀ f : C,
        M (i, c) (k, f) * freqPairProjector C r ζ (k, f) (i, c) =
          if c = f then
            (r : K)⁻¹ * (M (i, c) (k, f) * freqPairKernel ζ (k - i))
          else 0 := by
      intro f
      rw [freqPairProjector, Matrix.smul_apply, Matrix.blockDiagonal_apply]
      by_cases h : f = c
      · subst h
        simp only [Matrix.circulant_apply, smul_eq_mul, if_true]
        ring
      · have h' : ¬(c = f) := fun hcf ↦ h hcf.symm
        simp [h, h']
    rw [Finset.sum_congr rfl fun f _ ↦ hcol f,
      Finset.sum_ite_eq Finset.univ c
        fun f ↦ (r : K)⁻¹ * (M (i, c) (k, f) * freqPairKernel ζ (k - i))]
    simp
  have htrace : Matrix.trace (M * freqPairProjector C r ζ) =
      (r : K)⁻¹ * ∑ c : C, ∑ i : ZMod r, ∑ k : ZMod r,
        M (i, c) (k, c) * freqPairKernel ζ (k - i) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun c _ ↦ hentry i c]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  have hinner : ∀ c : C,
      ∑ i : ZMod r, ∑ k : ZMod r,
          M (i, c) (k, c) * freqPairKernel ζ (k - i) =
        (r : K) * ∑ t : ZMod r, M (0, c) (t, c) * freqPairKernel ζ t := by
    intro c
    have hre : ∀ i : ZMod r,
        ∑ k : ZMod r, M (i, c) (k, c) * freqPairKernel ζ (k - i) =
          ∑ t : ZMod r, M (0, c) (t, c) * freqPairKernel ζ t := by
      intro i
      refine Fintype.sum_equiv (Equiv.subRight i) _ _ fun k ↦ ?_
      rw [Equiv.subRight_apply, diag_block_apply_eq_zero_row hdiag c i k]
    rw [Finset.sum_congr rfl fun i _ ↦ hre i, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [htrace, Finset.sum_congr rfl fun c _ ↦ hinner c, ← Finset.mul_sum,
    inv_mul_cancel_left₀ hr0, Finset.sum_comm]
  have hcollect : ∀ t : ZMod r,
      ∑ c : C, M (0, c) (t, c) * freqPairKernel ζ t =
        (∑ c : C, M (0, c) (t, c)) * cyclePow ζ t +
          (∑ c : C, M (0, c) (t, c)) * cyclePow ζ (-t) := by
    intro t
    rw [← Finset.sum_mul, freqPairKernel, mul_add]
  rw [Finset.sum_congr rfl fun t _ ↦ hcollect t, Finset.sum_add_distrib]
  have heven : ∀ t : ZMod r,
      (∑ c : C, M (0, c) (-t, c)) = ∑ c : C, M (0, c) (t, c) := by
    intro t
    apply Finset.sum_congr rfl
    intro c _
    have h1 : M (t, c) (0, c) = M (0, c) (-t, c) := by
      rw [diag_block_apply_eq_zero_row hdiag c t 0, zero_sub]
    have h2 : M (t, c) (0, c) = M (0, c) (t, c) := hsymm.apply (0, c) (t, c)
    rw [← h1, h2]
  have hneg : ∑ t : ZMod r, (∑ c : C, M (0, c) (t, c)) * cyclePow ζ (-t) =
      ∑ t : ZMod r, (∑ c : C, M (0, c) (t, c)) * cyclePow ζ t := by
    have hswap : ∑ t : ZMod r,
        (∑ c : C, M (0, c) (t, c)) * cyclePow ζ (-t) =
        ∑ t : ZMod r, (∑ c : C, M (0, c) (-t, c)) * cyclePow ζ t := by
      refine Fintype.sum_equiv (Equiv.neg (ZMod r)) _ _ fun t ↦ ?_
      rw [Equiv.neg_apply, neg_neg]
    rw [hswap]
    exact Finset.sum_congr rfl fun t _ ↦ by rw [heven t]
  rw [hneg, two_mul]

/-- **The frequency-pair trace identity.**  For a symmetric matrix `M`
commuting with the labeled defect operator whose diagonal cycle blocks are
translation invariant, the trace of the restriction of `M` to the
`μ = ζ + ζ⁻¹` eigenspace is twice the Fourier transform, at `ζ`, of the
diagonal-anchor weight `t ↦ ∑ c, M (0,c) (t,c)`. -/
theorem trace_defectEigenspaceRestrict
    {M : Matrix (ZMod r × C) (ZMod r × C) K}
    (hcomm : M * cycleDefectMatrix K C r = cycleDefectMatrix K C r * M)
    (hdiag : ∀ (c : C) (x y : ZMod r),
      M (x + 1, c) (y + 1, c) = M (x, c) (y, c))
    (hsymm : M.IsSymm)
    (hrOdd : Odd r) {ζ : K} (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1)
    (hr0 : (r : K) ≠ 0) :
    LinearMap.trace K
        (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
        (defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹)) =
      2 * ∑ t : ZMod r, (∑ c : C, M (0, c) (t, c)) * cyclePow ζ t := by
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  set P := freqPairProjector C r ζ with hP
  set N := P * (M * P) with hN
  have hforall : ∀ x : ZMod r × C → K, Matrix.toLin' N x ∈
      defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹) := by
    intro x
    rw [Matrix.toLin'_apply, hN, ← Matrix.mulVec_mulVec]
    exact freqPairProjector_mulVec_mem hζr _
  have hrestrict :
      (Matrix.toLin' N).restrict (fun x _ ↦ hforall x) =
        defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹) := by
    refine LinearMap.ext fun v ↦ Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, defectEigenspaceRestrict_coe,
      Matrix.toLin'_apply, hN, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec,
      freqPairProjector_mulVec_of_mem hrOdd hζr hζsq hr0 v.2,
      freqPairProjector_mulVec_of_mem hrOdd hζr hζsq hr0
        (mulVec_mem_defectEigenspace hcomm v.2)]
  have htr := LinearMap.trace_restrict_eq_of_forall_mem
    (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
    (Matrix.toLin' N) hforall (fun x _ ↦ hforall x)
  rw [hrestrict] at htr
  rw [htr, Matrix.trace_toLin'_eq, hN, hP, Matrix.trace_mul_comm,
    Matrix.mul_assoc, freqPairProjector_mul_self hrOdd hζr hζ1 hr0]
  exact trace_mul_freqPairProjector hdiag hsymm hr0

/-- The square identity for the restriction, with the all-ones matrix in
the role of `J`: the hypotheses are exactly the transported even
second-order matrix equation and commutation. -/
theorem defectEigenspaceRestrict_sq_ones
    {M : Matrix (ZMod r × C) (ZMod r × C) K} {κ : K}
    (hcomm : M * cycleDefectMatrix K C r = cycleDefectMatrix K C r * M)
    (hsq : M * M = κ • (1 : Matrix (ZMod r × C) (ZMod r × C) K) +
      (Matrix.of fun _ _ : ZMod r × C ↦ (1 : K)) - cycleDefectMatrix K C r)
    {ζ : K} (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹) *
        defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹) =
      (κ - (ζ + ζ⁻¹)) • LinearMap.id :=
  defectEigenspaceRestrict_sq hcomm hsq ones_mul_cycleDefectMatrix
    (zeta_add_inv_ne_two hζr hζ1)

/-- **Projection to the prime frequency.**  When `p ∣ r` and `ζ^p = 1`,
the cyclic Fourier sum over `ZMod r` regroups along the reduction
`ZMod r → ZMod p` into the prime Fourier sum of the fiberwise-projected
weight. -/
theorem sum_mul_cyclePow_eq_fiberwise {p : ℕ} [NeZero p] (hdvd : p ∣ r)
    {ζ : K} (hζp : ζ ^ p = 1) (w : ZMod r → K) :
    ∑ t : ZMod r, w t * cyclePow ζ t =
      ∑ s : ZMod p,
        (∑ t ∈ Finset.univ.filter
          (fun t : ZMod r ↦ ZMod.castHom hdvd (ZMod p) t = s), w t) *
          ζ ^ s.val := by
  have hbridge : ∀ t : ZMod r,
      cyclePow ζ t = ζ ^ (ZMod.castHom hdvd (ZMod p) t).val := by
    intro t
    have h1 : ZMod.castHom hdvd (ZMod p) t = ((t.val : ℕ) : ZMod p) := by
      rw [ZMod.castHom_apply, ← ZMod.natCast_val]
    rw [cyclePow, h1, ZMod.val_natCast, pow_natMod_eq hζp]
  rw [← Finset.sum_fiberwise Finset.univ
    (fun t : ZMod r ↦ ZMod.castHom hdvd (ZMod p) t)
    (fun t : ZMod r ↦ w t * cyclePow ζ t)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hbridge t, (Finset.mem_filter.mp ht).2]

end Trace

end

end Erdos85
