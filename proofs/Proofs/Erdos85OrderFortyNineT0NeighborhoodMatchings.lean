import Proofs.Erdos85OrderFortyNineT0SupportFibers

/-!
# The first two `t = 0` support fibers are rooted perfect matchings

This specializes the Boolean terminal's partition law to high points zero
and one, producing the two canonical rooted coordinate systems used by the
cube generator.
-/

namespace Erdos85

noncomputable section

abbrev SevenHighT0Fiber (w : Fin 7) :=
  {x : Fin 49 // x ∈ sevenHighT0SupportFiber w}

def sevenHighT0FiberAdj (edges : BitVec 1176) (w : Fin 7)
    (x y : SevenHighT0Fiber w) : Bool :=
  orderFortyNineBitAdj edges x.1 y.1

theorem sevenHighT0Fiber_existsUnique_neighbor
    (edges : BitVec 1176)
    (h : orderFortyNineBooleanConstraints 7 sevenHighT0Masks edges)
    (w : Fin 7) (x : SevenHighT0Fiber w) :
    ∃! y : SevenHighT0Fiber w,
      sevenHighT0FiberAdj edges w x y = true := by
  rcases h with ⟨_, _, _, _, _, hpartition⟩
  have hxlow : 7 ≤ x.1.val :=
    sevenHighT0SupportFiber_isLow w x.2
  have hp := hpartition x.1 hxlow
    ⟨w.val, Nat.lt_trans w.isLt (by omega)⟩ w.isLt
  have heq :
      (Finset.univ.filter fun k =>
        orderFortyNineBitAdj edges x.1 k &&
          (orderFortyNineSupportMask sevenHighT0Masks k).getLsbD w.val) =
      (sevenHighT0SupportFiber w).filter fun k =>
        orderFortyNineBitAdj edges x.1 k = true := by
    ext k
    simp [sevenHighT0SupportFiber, Bool.and_eq_true, and_comm]
  rw [heq] at hp
  exact existsUnique_subtype_of_filter_card_eq_one
    (sevenHighT0SupportFiber w)
    (fun y => orderFortyNineBitAdj edges x.1 y) hp

theorem sevenHighT0_exists_rooted_fiber_matchings
    (edges : BitVec 1176)
    (h : orderFortyNineBooleanConstraints 7 sevenHighT0Masks edges) :
    ∃ e₀ : SevenHighT0Fiber 0 ≃ Fin 8,
      e₀ ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩ = 0 ∧
      (∀ x y, sevenHighT0FiberAdj edges 0 x y =
        decide (e₀ y = oneHighStandardMate (e₀ x))) ∧
    ∃ e₁ : SevenHighT0Fiber 1 ≃ Fin 8,
      e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0 ∧
      ∀ x y, sevenHighT0FiberAdj edges 1 x y =
        decide (e₁ y = oneHighStandardMate (e₁ x)) := by
  have hsymm : ∀ i j : Fin 49,
      orderFortyNineBitAdj edges i j = orderFortyNineBitAdj edges j i :=
    orderFortyNineBitAdj_comm edges
  have hloop : ∀ i : Fin 49, orderFortyNineBitAdj edges i i = false := by
    intro i
    simp [orderFortyNineBitAdj]
  obtain ⟨e₀, he₀root, he₀⟩ :=
    exists_equiv_finEight_canonical_matching_of_unique_rooted
      (by simpa [SevenHighT0Fiber] using sevenHighT0SupportFiber_card 0)
      (sevenHighT0FiberAdj edges 0)
      (fun x y => hsymm x.1 y.1)
      (fun x => hloop x.1)
      (sevenHighT0Fiber_existsUnique_neighbor edges h 0)
      ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩
  obtain ⟨e₁, he₁root, he₁⟩ :=
    exists_equiv_finEight_canonical_matching_of_unique_rooted
      (by simpa [SevenHighT0Fiber] using sevenHighT0SupportFiber_card 1)
      (sevenHighT0FiberAdj edges 1)
      (fun x y => hsymm x.1 y.1)
      (fun x => hloop x.1)
      (sevenHighT0Fiber_existsUnique_neighbor edges h 1)
      ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩
  exact ⟨e₀, he₀root, he₀, e₁, he₁root, he₁⟩

end

end Erdos85
