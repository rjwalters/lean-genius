import Proofs.Erdos85SquareOrderSectorProfile

/-! # Sharpening the odd square-order profile at q = 9

Node: B.3 / GAP B-CLASSIFY.  The exact first two high-incidence moments,
combined with the integer inequality `(k-2)(k-3) ≥ 0`, eliminate the last
scalar high-count candidate allowed by the coarse Cauchy bound.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every integer-valued incidence count contributes nonnegative excess about
the consecutive levels two and three. -/
theorem nat_two_three_excess_nonneg (k : ℕ) :
    (0 : ℤ) ≤ ((k : ℤ) - 2) * ((k : ℤ) - 3) := by
  by_cases hk : k ≤ 2
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  · exact mul_nonneg (by omega) (by omega)

/-- In a nonregular square-order profile at `q=9`, the high sector has at
most fifteen vertices.  The previous scalar polynomial alone permits the
spurious endpoint `h=17`; the integral two-level excess removes it. -/
theorem squareOrderNine_nonregular_high_card_le_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9) :
    (squareOrderHighVertices G 9).card ≤ 15 := by
  classical
  let H := squareOrderHighVertices G 9
  let k : V → ℕ := squareOrderHighIncidenceCount G 9
  let h := H.card
  have hfirstNat : (∑ x : V, k x) = 10 * h := by
    simpa only [k, h, H] using hp.first_moment
  have hsecondNat : (∑ x : V, (k x) ^ 2) = h * (h + 9) := by
    simpa only [k, h, H] using hp.second_moment
  have hfirst : (∑ x : V, (k x : ℤ)) = 10 * (h : ℤ) := by
    exact_mod_cast hfirstNat
  have hsecond : (∑ x : V, (k x : ℤ) ^ 2) =
      (h : ℤ) * ((h : ℤ) + 9) := by
    exact_mod_cast hsecondNat
  have hexcess : (0 : ℤ) ≤
      ∑ x : V, ((k x : ℤ) - 2) * ((k x : ℤ) - 3) := by
    apply Finset.sum_nonneg
    intro x _
    exact nat_two_three_excess_nonneg (k x)
  have hkzero {x : V} (hx : x ∈ H) : k x = 0 := by
    have hinter : G.neighborFinset x ∩ H = ∅ := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_inter.mp hy
        have hadj : G.Adj x y := (G.mem_neighborFinset x y).mp hy'.1
        exact False.elim (hp.high_independent hx hy'.2 hadj)
      · intro hy
        exact (by simpa using hy : False).elim
    simp [k, squareOrderHighIncidenceCount, H, hinter]
  have hhighSum :
      (∑ x ∈ H, ((k x : ℤ) - 2) * ((k x : ℤ) - 3)) =
        6 * (h : ℤ) := by
    calc
      _ = ∑ _x ∈ H, (6 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hkzero hx]
        norm_num
      _ = 6 * (h : ℤ) := by
        simp [h]
        ring
  have hhighLe : (6 : ℤ) * h ≤
      ∑ x : V, ((k x : ℤ) - 2) * ((k x : ℤ) - 3) := by
    rw [← hhighSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ H)
      (fun x _ _ => nat_two_three_excess_nonneg (k x))
  have hexpand :
      (∑ x : V, ((k x : ℤ) - 2) * ((k x : ℤ) - 3)) =
        (∑ x : V, (k x : ℤ) ^ 2) -
          5 * (∑ x : V, (k x : ℤ)) +
          6 * (Fintype.card V : ℤ) := by
    simp_rw [show ∀ x : V,
      ((k x : ℤ) - 2) * ((k x : ℤ) - 3) =
        (k x : ℤ) ^ 2 - 5 * (k x : ℤ) + 6 by
          intro x
          ring]
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    simp
    ring
  have hint : (0 : ℤ) ≤
      (h : ℤ) * ((h : ℤ) + 9) - 56 * (h : ℤ) + 486 := by
    rw [hexpand, hsecond, hfirst, hcard] at hhighLe
    norm_num at hhighLe
    ring_nf at hhighLe ⊢
    linarith
  have hpolyNat : h * h + 28 * h ≤ 729 := by
    simpa only [h, H] using hp.high_count_bound
  have hpoly : (h : ℤ) ^ 2 + 28 * (h : ℤ) ≤ 729 := by
    simp only [pow_two]
    exact_mod_cast hpolyNat
  have hle17 : h ≤ 17 := by
    by_contra hnot
    have h18 : (18 : ℤ) ≤ h := by omega
    have hmul : (0 : ℤ) ≤ (h : ℤ) * ((h : ℤ) - 18) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [hpoly, hmul]
  have hle15 : h ≤ 15 := by
    by_contra hnot
    have hcases : h = 16 ∨ h = 17 := by omega
    rcases hcases with h16 | h17
    · rw [h16] at hint
      norm_num at hint
    · rw [h17] at hint
      norm_num at hint
  simpa only [h, H] using hle15

/-- Handshake parity makes the high-sector cardinality odd at `q=9`. -/
theorem squareOrderNine_nonregular_high_card_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9) :
    Odd (squareOrderHighVertices G 9).card := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  rcases hp.high_parity with ⟨m, hm⟩
  rcases heven with ⟨n, hn⟩
  norm_num at hm
  omega

/-- Hence the scalar high-count classification at `q=9` consists of only
eight odd candidates. -/
theorem squareOrderNine_nonregular_high_card_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9) :
    let h := (squareOrderHighVertices G 9).card
    h = 1 ∨ h = 3 ∨ h = 5 ∨ h = 7 ∨ h = 9 ∨ h = 11 ∨ h = 13 ∨ h = 15 := by
  dsimp only
  have hpos : 0 < (squareOrderHighVertices G 9).card :=
    hp.high_nonempty.card_pos
  have hle := squareOrderNine_nonregular_high_card_le_fifteen
    G hcard hp
  rcases squareOrderNine_nonregular_high_card_odd G hp with ⟨k, hk⟩
  omega

end


end Erdos85

#print axioms Erdos85.nat_two_three_excess_nonneg
#print axioms Erdos85.squareOrderNine_nonregular_high_card_le_fifteen
#print axioms Erdos85.squareOrderNine_nonregular_high_card_odd
#print axioms Erdos85.squareOrderNine_nonregular_high_card_cases
