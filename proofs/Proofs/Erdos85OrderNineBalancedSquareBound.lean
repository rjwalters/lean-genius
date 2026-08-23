import Proofs.Erdos85OddSquareOrderNineNearRegularCutArithmetic

/-! # Sharp balanced-square lower bound for 78 ordinary vertices -/

open Finset

namespace Erdos85

set_option maxHeartbeats 2000000

private theorem balancedSquare_point (a x : ℕ) :
    ((2 * a + 1 : ℕ) : ℤ) * x ≤
      (x : ℤ) ^ 2 + (a : ℤ) * (a + 1) := by
  push_cast
  by_cases hle : x ≤ a
  · have hleZ : (x : ℤ) ≤ a := by exact_mod_cast hle
    have hnonneg :
        0 ≤ ((a : ℤ) - x) * ((a : ℤ) + 1 - x) := by
      exact mul_nonneg (by omega) (by omega)
    have hid :
        (x : ℤ) ^ 2 + (a : ℤ) * ((a : ℤ) + 1) -
            (2 * (a : ℤ) + 1) * x =
          ((a : ℤ) - x) * ((a : ℤ) + 1 - x) := by ring
    omega
  · have hge : a + 1 ≤ x := by omega
    have hgeZ : (a : ℤ) + 1 ≤ x := by exact_mod_cast hge
    have hnonneg :
        0 ≤ ((x : ℤ) - a) * ((x : ℤ) - (a + 1)) := by
      exact mul_nonneg (by omega) (by omega)
    have hid :
        (x : ℤ) ^ 2 + (a : ℤ) * ((a : ℤ) + 1) -
            (2 * (a : ℤ) + 1) * x =
          ((x : ℤ) - a) * ((x : ℤ) - ((a : ℤ) + 1)) := by ring
    omega

private theorem balancedSquare_point_eq_iff (a x : ℕ) :
    ((2 * a + 1 : ℕ) : ℤ) * x =
        (x : ℤ) ^ 2 + (a : ℤ) * (a + 1) ↔
      x = a ∨ x = a + 1 := by
  have hid :
      (x : ℤ) ^ 2 + (a : ℤ) * (a + 1) -
          ((2 * a + 1 : ℕ) : ℤ) * x =
        ((x : ℤ) - a) * ((x : ℤ) - (a + 1)) := by
    push_cast
    ring
  constructor
  · intro h
    have hz : ((x : ℤ) - a) * ((x : ℤ) - (a + 1)) = 0 := by
      rw [← hid, h]
      ring
    rcases mul_eq_zero.mp hz with hz | hz
    · left
      exact_mod_cast (sub_eq_zero.mp hz)
    · right
      exact_mod_cast (sub_eq_zero.mp hz)
  · rintro (rfl | rfl) <;> push_cast <;> ring

/-- Type-generic form, used for the subtype of the 78 ordinary vertices. -/
theorem balancedSquareSum_le_sum_sq_of_card_78
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 78) (f : ι → ℕ) :
    orderNineBalancedSquareSum (∑ i, f i) ≤ ∑ i, (f i) ^ 2 := by
  let M := ∑ i, f i
  let a := M / 78
  let r := M % 78
  have hM : M = 78 * a + r := by
    dsimp only [a, r]
    omega
  have hr : r < 78 := by
    dsimp only [r]
    omega
  have hpoint : ∀ i : ι,
      ((2 * a + 1 : ℕ) : ℤ) * f i ≤
        (f i : ℤ) ^ 2 + (a : ℤ) * (a + 1) := by
    intro i
    exact balancedSquare_point a (f i)
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hpoint i
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hcard] at hsum
  rw [← Finset.mul_sum] at hsum
  have hgoalZ :
      (orderNineBalancedSquareSum M : ℤ) ≤
        ((∑ i, (f i) ^ 2 : ℕ) : ℤ) := by
    rw [show orderNineBalancedSquareSum M =
        (78 - r) * a ^ 2 + r * (a + 1) ^ 2 by rfl]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hr)]
    push_cast
    have hsumF : (∑ i, (f i : ℤ)) = (M : ℤ) := by simp [M]
    have hsumSq : (∑ i, (f i : ℤ) ^ 2) =
        ((∑ i, f i ^ 2 : ℕ) : ℤ) := by simp
    rw [hsumF, hsumSq] at hsum
    push_cast at hsum
    have hMZ : (M : ℤ) = 78 * (a : ℤ) + r := by exact_mod_cast hM
    have hid :
        ((78 : ℤ) - r) * (a : ℤ) ^ 2 +
            (r : ℤ) * ((a : ℤ) + 1) ^ 2 +
            78 * (a : ℤ) * ((a : ℤ) + 1) =
          (2 * (a : ℤ) + 1) * (M : ℤ) := by
      rw [hMZ]
      ring
    ring_nf at hsum hid ⊢
    linarith
  exact_mod_cast hgoalZ

/-- Among 78 natural numbers with fixed sum, the sum of squares is minimized
by the balanced quotient/remainder distribution. -/
theorem orderNineBalancedSquareSum_le_sum_sq (f : Fin 78 → ℕ) :
    orderNineBalancedSquareSum (∑ i, f i) ≤ ∑ i, (f i) ^ 2 := by
  exact balancedSquareSum_le_sum_sq_of_card_78 (by simp) f

/-- Equality in the balanced-square bound is rigid: every entry is one of
the two adjacent quotient values.  This is the equality interface used by
the q=9 articulation low-set arguments. -/
theorem balancedSquare_eq_iff_pointwise_of_card_78
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 78) (f : ι → ℕ)
    (heq : orderNineBalancedSquareSum (∑ i, f i) = ∑ i, (f i) ^ 2) :
    ∀ i, f i = (∑ j, f j) / 78 ∨ f i = (∑ j, f j) / 78 + 1 := by
  let M := ∑ i, f i
  let a := M / 78
  let r := M % 78
  have hM : M = 78 * a + r := by
    dsimp only [a, r]
    omega
  have hr : r < 78 := by
    dsimp only [r]
    omega
  have htotal :
      ∑ i, ((2 * a + 1 : ℕ) : ℤ) * f i =
        ∑ i, ((f i : ℤ) ^ 2 + (a : ℤ) * (a + 1)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [hcard, ← Finset.mul_sum]
    have hsumF : (∑ i, (f i : ℤ)) = (M : ℤ) := by simp [M]
    have hsumSq : (∑ i, (f i : ℤ) ^ 2) =
        ((∑ i, f i ^ 2 : ℕ) : ℤ) := by simp
    rw [hsumF, hsumSq, ← heq]
    have hbalancedCast : (orderNineBalancedSquareSum M : ℤ) =
        ((78 : ℤ) - r) * (a : ℤ) ^ 2 +
          (r : ℤ) * ((a : ℤ) + 1) ^ 2 := by
      rw [show orderNineBalancedSquareSum M =
          (78 - r) * a ^ 2 + r * (a + 1) ^ 2 by rfl]
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hr)]
      push_cast
      rfl
    rw [hbalancedCast]
    have hMZ : (M : ℤ) = 78 * (a : ℤ) + r := by exact_mod_cast hM
    rw [hMZ]
    push_cast
    ring
  intro i
  apply (balancedSquare_point_eq_iff a (f i)).mp
  have hle : ∀ j : ι,
      ((2 * a + 1 : ℕ) : ℤ) * f j ≤
        (f j : ℤ) ^ 2 + (a : ℤ) * (a + 1) :=
    fun j => balancedSquare_point a (f j)
  by_contra hne
  have hlt : ((2 * a + 1 : ℕ) : ℤ) * f i <
      (f i : ℤ) ^ 2 + (a : ℤ) * (a + 1) :=
    lt_of_le_of_ne (hle i) hne
  have hsumlt := Finset.sum_lt_sum
    (s := (Finset.univ : Finset ι))
    (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
  rw [htotal] at hsumlt
  exact lt_irrefl _ hsumlt

/-- In the equality case, the upper quotient value occurs exactly the
remainder number of times. -/
theorem balancedSquare_eq_upper_card_of_card_78
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 78) (f : ι → ℕ)
    (heq : orderNineBalancedSquareSum (∑ i, f i) = ∑ i, (f i) ^ 2) :
    (Finset.univ.filter fun i =>
      f i = (∑ j, f j) / 78 + 1).card = (∑ j, f j) % 78 := by
  let M := ∑ i, f i
  let a := M / 78
  let r := M % 78
  let Z := Finset.univ.filter fun i => f i = a + 1
  have hM : M = 78 * a + r := by
    dsimp only [a, r]
    omega
  have hpoint := balancedSquare_eq_iff_pointwise_of_card_78 hcard f heq
  have hf : ∀ i, f i = a + if i ∈ Z then 1 else 0 := by
    intro i
    have hi := hpoint i
    by_cases hiZ : i ∈ Z
    · have hiUpper : f i = a + 1 := (Finset.mem_filter.mp hiZ).2
      simp [hiZ, hiUpper]
    · have hiNotUpper : f i ≠ a + 1 := by
        intro hiUpper
        exact hiZ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiUpper⟩)
      have hiLower : f i = a := hi.resolve_right hiNotUpper
      simp [hiZ, hiLower]
  have hsum : M = 78 * a + Z.card := by
    calc
      M = ∑ i, f i := rfl
      _ = ∑ i, (a + if i ∈ Z then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hf i
      _ = 78 * a + Z.card := by
        rw [Finset.sum_add_distrib]
        simp [hcard, mul_comm]
  change Z.card = r
  omega

#print axioms orderNineBalancedSquareSum_le_sum_sq
#print axioms balancedSquareSum_le_sum_sq_of_card_78
#print axioms balancedSquare_eq_iff_pointwise_of_card_78
#print axioms balancedSquare_eq_upper_card_of_card_78

end Erdos85
