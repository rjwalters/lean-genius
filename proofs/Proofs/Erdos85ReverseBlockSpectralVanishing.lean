import Proofs.Erdos85FrequencyPairMixed

/-!
# Reverse-oriented cycle blocks are spectrally invisible

A block matrix on `ZMod r` satisfying the *reverse* translation relation
`B (x+1) (y-1) = B x y` is constant along anti-diagonals: it is
determined by its zero row through `B x y = B 0 (x+y)`.  Against the
frequency-pair circulant kernel the trace of such a block vanishes for
*any* cycle length — even or odd — because both frequency modes see the
geometric sum `Σ_x ζ^(±2x)`, which dies whenever `ζ² ≠ 1`.

This is the denominator-free vanishing that lets the mixed spectral
trace formula drop the odd-length hypothesis: circulant-oriented
components contribute their integer anchored row weights, and
reverse-oriented components contribute exactly zero.
-/

namespace Erdos85

noncomputable section

open Matrix

variable {K : Type*} [Field K] {r : ℕ} [NeZero r]

/-- A reverse-oriented block is determined along anti-diagonals by its
zero row. -/
theorem reverse_block_apply_eq_zero_row {α : Type*}
    (B : Matrix (ZMod r) (ZMod r) α)
    (hrev : ∀ x y : ZMod r, B (x + 1) (y - 1) = B x y)
    (x y : ZMod r) : B x y = B 0 (x + y) := by
  have haux : ∀ (n : ℕ) (w : ZMod r),
      B (n : ZMod r) (w - (n : ZMod r)) = B 0 w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        have hstep := hrev (k : ZMod r) (w - (k : ZMod r))
        have hcast : ((k + 1 : ℕ) : ZMod r) = (k : ZMod r) + 1 := by
          push_cast
          ring
        rw [hcast, show w - ((k : ZMod r) + 1) =
          w - (k : ZMod r) - 1 from by ring, hstep]
        exact ih w
  have hx : ((x.val : ℕ) : ZMod r) = x := ZMod.natCast_rightInverse x
  have hmain := haux x.val (x + y)
  rw [hx, show x + y - x = y from by ring] at hmain
  exact hmain

/-- **Reverse blocks have zero spectral trace.**  A block satisfying the
reverse translation relation has vanishing trace against the
frequency-pair circulant kernel, for a cycle of any length: both
frequency modes reduce to the geometric sum `Σ ζ^(±2x) = 0`. -/
theorem trace_mul_circulant_freqPairKernel_eq_zero_of_reverse
    (B : Matrix (ZMod r) (ZMod r) K)
    (hrev : ∀ x y : ZMod r, B (x + 1) (y - 1) = B x y)
    {ζ : K} (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.trace (B * Matrix.circulant (freqPairKernel ζ)) = 0 := by
  have hBrow := reverse_block_apply_eq_zero_row B hrev
  have htrace : Matrix.trace (B * Matrix.circulant (freqPairKernel ζ)) =
      ∑ x : ZMod r, ∑ y : ZMod r, B x y * freqPairKernel ζ (y - x) := by
    rw [Matrix.trace]
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro y _
    rw [Matrix.circulant_apply]
  have hswap : ∀ x : ZMod r,
      (∑ y : ZMod r, B x y * freqPairKernel ζ (y - x)) =
      ∑ u : ZMod r, B 0 u * freqPairKernel ζ (u - 2 * x) := by
    intro x
    apply Fintype.sum_equiv (Equiv.addLeft x)
    intro y
    simp only [Equiv.coe_addLeft]
    rw [hBrow x y, show x + y - 2 * x = y - x from by ring]
  have hstep : (∑ x : ZMod r, ∑ y : ZMod r,
      B x y * freqPairKernel ζ (y - x)) =
      ∑ u : ZMod r, ∑ x : ZMod r,
        B 0 u * freqPairKernel ζ (u - 2 * x) := by
    calc
      (∑ x : ZMod r, ∑ y : ZMod r, B x y * freqPairKernel ζ (y - x)) =
          ∑ x : ZMod r, ∑ u : ZMod r,
            B 0 u * freqPairKernel ζ (u - 2 * x) :=
        Finset.sum_congr rfl fun x _ ↦ hswap x
      _ = ∑ u : ZMod r, ∑ x : ZMod r,
            B 0 u * freqPairKernel ζ (u - 2 * x) := Finset.sum_comm
  rw [htrace, hstep]
  apply Finset.sum_eq_zero
  intro u _
  have hsplit : ∀ x : ZMod r, freqPairKernel ζ (u - 2 * x) =
      cyclePow ζ (u - 2 * x) + cyclePow ζ (2 * x - u) := by
    intro x
    simp only [freqPairKernel]
    rw [show -(u - 2 * x) = 2 * x - u from by ring]
  have hker : (∑ x : ZMod r, freqPairKernel ζ (u - 2 * x)) = 0 := by
    rw [Finset.sum_congr rfl fun x _ ↦ hsplit x, Finset.sum_add_distrib]
    have h1 : (∑ x : ZMod r, cyclePow ζ (u - 2 * x)) = 0 := by
      have hneg : (∑ x : ZMod r, cyclePow ζ (u - 2 * x)) =
          ∑ x : ZMod r, cyclePow ζ (2 * x + u) := by
        apply Fintype.sum_equiv (Equiv.neg (ZMod r))
        intro x
        simp only [Equiv.neg_apply]
        rw [show 2 * (-x) + u = u - 2 * x from by ring]
      rw [hneg]
      exact sum_cyclePow_two_mul_add_eq_zero_of_sq hζr hζsq u
    have h2 : (∑ x : ZMod r, cyclePow ζ (2 * x - u)) = 0 := by
      have hcongr : (∑ x : ZMod r, cyclePow ζ (2 * x - u)) =
          ∑ x : ZMod r, cyclePow ζ (2 * x + (-u)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [show 2 * x + (-u) = 2 * x - u from by ring]
      rw [hcongr]
      exact sum_cyclePow_two_mul_add_eq_zero_of_sq hζr hζsq (-u)
    rw [h1, h2, add_zero]
  rw [← Finset.mul_sum, hker, mul_zero]

/-- Scaled form matching the mixed frequency projector's diagonal blocks:
the reverse block also kills the `1/r`-normalized circulant kernel. -/
theorem trace_mul_smul_circulant_freqPairKernel_eq_zero_of_reverse
    (B : Matrix (ZMod r) (ZMod r) K)
    (hrev : ∀ x y : ZMod r, B (x + 1) (y - 1) = B x y)
    {ζ : K} (hζr : ζ ^ r = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.trace (B * ((r : K)⁻¹ •
      Matrix.circulant (freqPairKernel ζ))) = 0 := by
  rw [Matrix.mul_smul, Matrix.trace_smul,
    trace_mul_circulant_freqPairKernel_eq_zero_of_reverse B hrev hζr hζsq,
    smul_zero]

end

end Erdos85
