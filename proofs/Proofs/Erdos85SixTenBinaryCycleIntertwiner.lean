import Mathlib

/-!
# Binary intertwiners between cycles of orders six and ten

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

namespace Erdos85

theorem cycleIntertwiner_twoStep
    {r s : ℕ} [NeZero r] [NeZero s]
    (B : Matrix (ZMod r) (ZMod s) ℤ)
    (hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1))
    (x : ZMod r) (y : ZMod s) :
    B (x - 2) y + B (x + 2) y =
      B x (y - 2) + B x (y + 2) := by
  have hm := hinter (x - 1) y
  have hp := hinter (x + 1) y
  have hym := hinter x (y - 1)
  have hyp := hinter x (y + 1)
  have h0 := hinter x y
  ring_nf at hm hp hym hyp ⊢
  linear_combination hm + hp + hym + hyp

theorem cycleIntertwiner_threeStep
    {r s : ℕ} [NeZero r] [NeZero s]
    (B : Matrix (ZMod r) (ZMod s) ℤ)
    (hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1))
    (x : ZMod r) (y : ZMod s) :
    B (x - 3) y + B (x + 3) y =
      B x (y - 3) + B x (y + 3) := by
  have hm := hinter (x - 2) y
  have hp := hinter (x + 2) y
  have hym := cycleIntertwiner_twoStep B hinter x (y - 1)
  have hyp := cycleIntertwiner_twoStep B hinter x (y + 1)
  have h0 := hinter x y
  ring_nf at hm hp hym hyp h0 ⊢
  linear_combination hm + hp + hym + hyp - h0

/-- The order-six half-turn and binarity force every target row of a
`6 × 10` cycle intertwiner to be two-periodic. -/
theorem binary_sixTenCycleIntertwiner_row_twoPeriodic
    (B : Matrix (ZMod 6) (ZMod 10) ℤ)
    (hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1))
    (hbinary : ∀ x y, B x y = 0 ∨ B x y = 1) :
    ∀ x y, B x (y + 2) = B x y := by
  have hhalf (x : ZMod 6) (y : ZMod 10) :
      B x (y + 6) = B x y := by
    have h := cycleIntertwiner_threeStep B hinter x (y + 3)
    have hx : x - 3 = x + 3 := by
      rw [sub_eq_add_neg]
      congr 1
    rw [hx] at h
    ring_nf at h
    rcases hbinary x y with hy0 | hy1 <;>
      rcases hbinary x (y + 6) with hz0 | hz1 <;>
      rcases hbinary (x + 3) (y + 3) with hc0 | hc1 <;>
      ring_nf at * <;> omega
  intro x y
  have h1 := hhalf x y
  have h2 := hhalf x (y + 6)
  ring_nf at h1 h2 ⊢
  exact h2.trans h1

theorem zmodTen_binary_twoPeriodic_nonconstant_flip
    (f : ZMod 10 → ℤ)
    (hbinary : ∀ y, f y = 0 ∨ f y = 1)
    (hperiod : ∀ y, f (y + 2) = f y)
    (hnonconstant : ∃ y z, f y ≠ f z) :
    ∀ y, f (y + 1) = 1 - f y := by
  have h2 := hperiod 0
  have h3 := hperiod 1
  have h4 := hperiod 2
  have h5 := hperiod 3
  have h6 := hperiod 4
  have h7 := hperiod 5
  have h8 := hperiod 6
  have h9 := hperiod 7
  norm_num at h2 h3 h4 h5 h6 h7 h8 h9
  have values (y : ZMod 10) : f y = f 0 ∨ f y = f 1 := by
    have hy : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨
        y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 := by
      revert y
      decide
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at * <;> omega
  have hne : f 0 ≠ f 1 := by
    intro heq
    obtain ⟨y, z, hyz⟩ := hnonconstant
    rcases values y with hy | hy <;> rcases values z with hz | hz <;>
      apply hyz <;> omega
  have h01 : f 1 = 1 - f 0 := by
    rcases hbinary 0 with h00 | h01 <;>
      rcases hbinary 1 with h10 | h11 <;> omega
  intro y
  have h10 : f ((9 : ZMod 10) + 1) = f 0 := by
    congr 1
  have hy : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨
      y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 := by
    revert y
    decide
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at * <;> omega

/-- A binary `6 × 10` cycle intertwiner whose rows are nonconstant is one of
the two complementary checkerboards: moving one step in either coordinate
flips every entry. -/
theorem binary_sixTenCycleIntertwiner_checkerboard
    (B : Matrix (ZMod 6) (ZMod 10) ℤ)
    (hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1))
    (hbinary : ∀ x y, B x y = 0 ∨ B x y = 1)
    (hnonconstant : ∀ x, ∃ y z, B x y ≠ B x z) :
    (∀ x y, B x (y + 1) = 1 - B x y) ∧
      (∀ x y, B (x + 1) y = 1 - B x y) := by
  have hperiod :=
    binary_sixTenCycleIntertwiner_row_twoPeriodic B hinter hbinary
  have htarget (x : ZMod 6) :
      ∀ y, B x (y + 1) = 1 - B x y :=
    zmodTen_binary_twoPeriodic_nonconstant_flip
      (fun y ↦ B x y) (hbinary x) (hperiod x) (hnonconstant x)
  refine ⟨htarget, ?_⟩
  intro x y
  have hrec := hinter x y
  have hplus := htarget x y
  have hminus := htarget x (y - 1)
  have hsub : y - 1 + 1 = y := by ring
  rw [hsub] at hminus
  rcases hbinary (x - 1) y with hm0 | hm1 <;>
    rcases hbinary (x + 1) y with hp0 | hp1 <;> omega

/-- Quotient-ready form of the checkerboard classification.  Exact row
weight five automatically rules out a constant binary row. -/
theorem binary_sixTenCycleIntertwiner_sum_five_checkerboard
    (B : Matrix (ZMod 6) (ZMod 10) ℤ)
    (hinter : ∀ x y,
      B (x - 1) y + B (x + 1) y =
        B x (y + 1) + B x (y - 1))
    (hbinary : ∀ x y, B x y = 0 ∨ B x y = 1)
    (hrow : ∀ x, ∑ y, B x y = 5) :
    (∀ x y, B x (y + 1) = 1 - B x y) ∧
      (∀ x y, B (x + 1) y = 1 - B x y) := by
  apply binary_sixTenCycleIntertwiner_checkerboard B hinter hbinary
  intro x
  by_contra hconstant
  push Not at hconstant
  have hall (y : ZMod 10) : B x y = B x 0 := by
    exact hconstant y 0
  have hsum := hrow x
  rw [Finset.sum_congr rfl (fun y _ ↦ hall y)] at hsum
  rcases hbinary x 0 with hzero | hone <;> simp_all

end Erdos85

#print axioms Erdos85.binary_sixTenCycleIntertwiner_row_twoPeriodic
#print axioms Erdos85.zmodTen_binary_twoPeriodic_nonconstant_flip
#print axioms Erdos85.binary_sixTenCycleIntertwiner_checkerboard
#print axioms Erdos85.binary_sixTenCycleIntertwiner_sum_five_checkerboard
