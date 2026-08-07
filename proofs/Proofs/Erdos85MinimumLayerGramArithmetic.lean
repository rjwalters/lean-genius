import Mathlib

/-!
# Arithmetic aggregation of minimum-layer Gram identities

The graph-facing quotient Gram theorem is pairwise.  This file packages the
finite-sum conversion from those pairwise off-diagonal identities to the
single row-square identity consumed by the minimum-sector terminal.
-/

namespace Erdos85

/-- Summing a constant off-diagonal Gram identity over all ordered distinct
column pairs gives the aggregate row-square identity. -/
theorem sum_rowSquare_sub_sumSq_of_offDiagonal_gram
    {I : Type*} [DecidableEq I]
    (S : Finset I) (q : I → I → ℤ) (w : ℤ)
    (hgram : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' →
      (∑ f ∈ S, q f c * q f c') = w) :
    (∑ f ∈ S,
        ((∑ c ∈ S, q f c) ^ 2 - ∑ c ∈ S, (q f c) ^ 2)) =
      (S.card : ℤ) * ((S.card : ℤ) - 1) * w := by
  have hrow : ∀ f ∈ S,
      (∑ c ∈ S, q f c) ^ 2 - ∑ c ∈ S, (q f c) ^ 2 =
        ∑ c ∈ S, ∑ c' ∈ S.erase c, q f c * q f c' := by
    intro f hf
    have hsplit : ∀ c ∈ S,
        (∑ c' ∈ S, q f c * q f c') =
          q f c * q f c + ∑ c' ∈ S.erase c, q f c * q f c' := by
      intro c hc
      rw [← Finset.sum_erase_add _ _ hc]
      ring
    calc
      (∑ c ∈ S, q f c) ^ 2 - ∑ c ∈ S, (q f c) ^ 2 =
          (∑ c ∈ S, q f c) * (∑ c' ∈ S, q f c') -
            ∑ c ∈ S, q f c * q f c := by simp only [pow_two]
      _ = (∑ c ∈ S, ∑ c' ∈ S, q f c * q f c') -
            ∑ c ∈ S, q f c * q f c := by
        rw [Finset.sum_mul_sum]
      _ = (∑ c ∈ S,
              (q f c * q f c +
                ∑ c' ∈ S.erase c, q f c * q f c')) -
            ∑ c ∈ S, q f c * q f c := by
        congr 1
        apply Finset.sum_congr rfl
        intro c hc
        exact hsplit c hc
      _ = ∑ c ∈ S, ∑ c' ∈ S.erase c, q f c * q f c' := by
        rw [Finset.sum_add_distrib]
        ring
  calc
    (∑ f ∈ S,
        ((∑ c ∈ S, q f c) ^ 2 - ∑ c ∈ S, (q f c) ^ 2)) =
        ∑ f ∈ S, ∑ c ∈ S, ∑ c' ∈ S.erase c, q f c * q f c' := by
      apply Finset.sum_congr rfl
      intro f hf
      exact hrow f hf
    _ = ∑ c ∈ S, ∑ c' ∈ S.erase c, ∑ f ∈ S, q f c * q f c' := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]
    _ = ∑ c ∈ S, ∑ _c' ∈ S.erase c, w := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro c' hc'
      apply hgram c hc c'
      · exact Finset.mem_of_mem_erase hc'
      · exact (Finset.ne_of_mem_erase hc').symm
    _ = (S.card : ℤ) * ((S.card : ℤ) - 1) * w := by
      by_cases hS : S.card = 0
      · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hS
        simp [hEmpty]
      · have hpos : 0 < S.card := Nat.pos_of_ne_zero hS
        calc
          (∑ c ∈ S, ∑ _c' ∈ S.erase c, w) =
              ∑ _c ∈ S, ((S.card : ℤ) - 1) * w := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hc,
              Nat.cast_sub (by omega : 1 ≤ S.card)]
            norm_num
          _ = (S.card : ℤ) * ((S.card : ℤ) - 1) * w := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring

end Erdos85
