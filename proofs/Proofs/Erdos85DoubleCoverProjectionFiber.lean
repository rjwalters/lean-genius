import Proofs.Erdos85DoubleCoverOddCancellation
import Proofs.Erdos85ZModProjectionFiber

/-!
# Projection fibers on a cyclic double cover

For the residual `p`--`2p` configuration, reduction from the doubled
cycle to the base cycle has exactly the two deck lifts in each fiber.
Combining this with deck sparsity and the Sidon doubling criterion makes
every nonzero projected diagonal coefficient a Boolean ordered-difference
coefficient.  Only the zero fiber can carry an extra undetected bit.
-/

namespace Erdos85

noncomputable section

/-- The fiber of `ZMod (2p) → ZMod p` consists of the canonical lift and
its deck translate. -/
theorem doubleCover_projectionFiber_eq_pair
    {p : ℕ} [NeZero p] (t : ZMod p) :
    let hpdiv : p ∣ (2 : ℕ) * p := dvd_mul_left p 2
    projectionFiber (ZMod.castHom hpdiv (ZMod p)) t =
      {((t.val : ℕ) : ZMod (2 * p)),
        ((t.val + p : ℕ) : ZMod (2 * p))} := by
  classical
  dsimp only
  let hpdiv : p ∣ (2 : ℕ) * p := dvd_mul_left p 2
  let x : ZMod (2 * p) := (t.val : ℕ)
  let y : ZMod (2 * p) := (t.val + p : ℕ)
  have hpPos : 0 < p := NeZero.pos p
  have htx : t.val < p := ZMod.val_lt t
  have hxval : x.val = t.val := by
    dsimp only [x]
    rw [ZMod.val_cast_of_lt]
    omega
  have hyval : y.val = t.val + p := by
    dsimp only [y]
    rw [ZMod.val_cast_of_lt]
    omega
  have hxy : x ≠ y := by
    intro h
    have := congrArg ZMod.val h
    rw [hxval, hyval] at this
    omega
  have hxmem : x ∈ projectionFiber (ZMod.castHom hpdiv (ZMod p)) t := by
    simp only [projectionFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [x]
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hymem : y ∈ projectionFiber (ZMod.castHom hpdiv (ZMod p)) t := by
    simp only [projectionFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [y]
    rw [map_natCast, Nat.cast_add, ZMod.natCast_self, add_zero,
      ZMod.natCast_zmod_val]
  have hsub : ({x, y} : Finset (ZMod (2 * p))) ⊆
      projectionFiber (ZMod.castHom hpdiv (ZMod p)) t := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxmem
    · exact hymem
  have hfiberCard :
      (projectionFiber (ZMod.castHom hpdiv (ZMod p)) t).card = 2 := by
    rw [card_projectionFiber_zmod_castHom hpdiv t]
    simpa [Nat.mul_comm] using Nat.mul_div_right 2 hpPos
  have hpairCard : ({x, y} : Finset (ZMod (2 * p))).card = 2 := by
    rw [Finset.card_pair hxy]
  exact (Finset.eq_of_subset_of_card_le hsub (by
    rw [hpairCard, hfiberCard])).symm

/-- A deck-sparse set contains at most one element in every projection
fiber of the double cover. -/
theorem card_doubleCover_projectionFiber_inter_le_one
    {p : ℕ} [NeZero p]
    (A : Finset (ZMod (2 * p)))
    (hdeck : ∀ y ∈ A, y + (p : ZMod (2 * p)) ∉ A)
    (t : ZMod p) :
    let hpdiv : p ∣ (2 : ℕ) * p := dvd_mul_left p 2
    (A ∩ projectionFiber (ZMod.castHom hpdiv (ZMod p)) t).card ≤ 1 := by
  classical
  dsimp only
  let hpdiv : p ∣ (2 : ℕ) * p := dvd_mul_left p 2
  let x : ZMod (2 * p) := (t.val : ℕ)
  have hpair := doubleCover_projectionFiber_eq_pair t
  dsimp only at hpair
  rw [hpair]
  have hxp : x + (p : ZMod (2 * p)) =
      ((t.val + p : ℕ) : ZMod (2 * p)) := by
    dsimp only [x]
    push_cast
    ring
  rw [← hxp]
  change (A ∩ {x, x + (p : ZMod (2 * p))}).card ≤ 1
  by_cases hx : x ∈ A
  · have hnot := hdeck x hx
    simp [hx, hnot]
  · calc
      (A ∩ {x, x + (p : ZMod (2 * p))}).card ≤
          ({x + (p : ZMod (2 * p))} : Finset (ZMod (2 * p))).card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_inter, Finset.mem_insert,
          Finset.mem_singleton] at hz ⊢
        rcases hz.2 with rfl | hzx
        · exact (hx hz.1).elim
        · exact hzx
      _ = 1 := Finset.card_singleton _

/-- Away from zero, the projected diagonal count of a deck-sparse,
inverse-closed Sidon support is exactly the indicator of its doubled
ordered difference. -/
theorem card_doubleCover_projectedSupport_eq_indicator_ods
    {p : ℕ} [NeZero p]
    (A : Finset (ZMod (2 * p)))
    (hneg : negFinset A = A) (hsidon : IsOrderedSidon A)
    (hdeck : ∀ y ∈ A, y + (p : ZMod (2 * p)) ∉ A)
    (t : ZMod p) (ht : t ≠ 0) :
    let hpdiv : p ∣ (2 : ℕ) * p := dvd_mul_left p 2
    let x : ZMod (2 * p) := (t.val : ℕ)
    (A ∩ projectionFiber (ZMod.castHom hpdiv (ZMod p)) t).card =
      if 2 * x ∈ orderedDifferenceSet A then 1 else 0 := by
  classical
  dsimp only
  let hpdiv : p ∣ (2 : ℕ) * p := dvd_mul_left p 2
  let x : ZMod (2 * p) := (t.val : ℕ)
  have hpPos : 0 < p := NeZero.pos p
  have htx : t.val < p := ZMod.val_lt t
  have hpair := doubleCover_projectionFiber_eq_pair t
  dsimp only at hpair
  rw [hpair]
  have hxval : x.val = t.val := by
    dsimp only [x]
    exact ZMod.val_cast_of_lt (by omega)
  have hx0 : x ≠ 0 := by
    intro h
    apply ht
    apply ZMod.val_injective
    have := congrArg ZMod.val h
    simpa [hxval] using this
  have hxp : x + (p : ZMod (2 * p)) =
      ((t.val + p : ℕ) : ZMod (2 * p)) := by
    dsimp only [x]
    push_cast
    ring
  have hx2 : 2 * x ≠ 0 := by
    intro h
    rcases (two_mul_eq_zero_iff_eq_zero_or_halfTurn x).mp h with hzero | hhalf
    · exact hx0 hzero
    · have hval := congrArg ZMod.val hhalf
      rw [hxval, ZMod.val_cast_of_lt (by omega)] at hval
      omega
  rw [← hxp]
  change (A ∩ {x, x + (p : ZMod (2 * p))}).card =
    if 2 * x ∈ orderedDifferenceSet A then 1 else 0
  have hcriterion :=
    two_mul_mem_orderedDifferenceSet_iff_mem_or_halfTurn_mem
      A hneg hsidon x hx2
  by_cases hods : 2 * x ∈ orderedDifferenceSet A
  · rw [if_pos hods]
    rcases hcriterion.mp hods with hx | hxpA
    · have hnot := hdeck x hx
      simp [hx, hnot]
    · have hx : x ∉ A := by
        intro hx
        exact hdeck x hx hxpA
      simp [hx, hxpA]
  · rw [if_neg hods]
    have hneither : x ∉ A ∧ x + (p : ZMod (2 * p)) ∉ A := by
      exact not_or.mp (fun h ↦ hods (hcriterion.mpr h))
    simp [hneither.1, hneither.2]

end

end Erdos85
