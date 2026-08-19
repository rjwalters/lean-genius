import Proofs.Erdos85ZModTenSameParityIntertwiner
import Proofs.Erdos85AntipodalCommutatorCut

/-! # Mixed-parity self-intertwiner obstruction on `C10` -/

namespace Erdos85

/-- The number of same-parity entries is independent of the row in a C10
self-intertwiner. -/
theorem zmodTen_selfIntertwiner_sameParity_card_eq
    (M : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hdiag : ∀ z, M z z = 0)
    (hinter : ∀ x y,
      M (x - 1) y + M (x + 1) y =
        M x (y + 1) + M x (y - 1))
    (x x' : ZMod 10) :
    ((Finset.univ : Finset (ZMod 10)).filter fun y =>
      ZModTenEvenOffset (y - x) ∧ M x y = 1).card =
    ((Finset.univ : Finset (ZMod 10)).filter fun y =>
      ZModTenEvenOffset (y - x') ∧ M x' y = 1).card := by
  classical
  let S := (Finset.univ : Finset (ZMod 10)).filter fun y =>
    ZModTenEvenOffset (y - x) ∧ M x y = 1
  let T := (Finset.univ : Finset (ZMod 10)).filter fun y =>
    ZModTenEvenOffset (y - x') ∧ M x' y = 1
  change S.card = T.card
  apply Finset.card_bij (fun y _ => y - x + x')
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [show (y - x + x') - x' = y - x by ring] using hy'.1
    · calc
        M x' (y - x + x') = M x y := by
          apply selfIntertwiner_eq_of_sub_eq_of_mem_range_two
            M hdiag hinter ?_ (by ring)
          rcases hy'.1 with h0 | h2 | h4 | h6 | h8
          · exact ⟨0, by rw [h0]; norm_num⟩
          · exact ⟨1, by rw [h2]; norm_num⟩
          · exact ⟨2, by rw [h4]; ring⟩
          · exact ⟨3, by rw [h6]; ring⟩
          · exact ⟨4, by rw [h8]; ring⟩
        _ = 1 := hy'.2
  · intro y₁ hy₁ y₂ hy₂ heq
    linear_combination heq
  · intro z hz
    refine ⟨z - x' + x, ?_, by ring⟩
    have hz' := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [show (z - x' + x) - x = z - x' by ring] using hz'.1
    · calc
        M x (z - x' + x) = M x' z := by
          apply selfIntertwiner_eq_of_sub_eq_of_mem_range_two
            M hdiag hinter ?_ (by ring)
          rcases hz'.1 with h0 | h2 | h4 | h6 | h8
          · exact ⟨0, by rw [h0]; norm_num⟩
          · exact ⟨1, by rw [h2]; norm_num⟩
          · exact ⟨2, by rw [h4]; ring⟩
          · exact ⟨3, by rw [h6]; ring⟩
          · exact ⟨4, by rw [h8]; ring⟩
        _ = 1 := hz'.2

/-- The total number of directed same-parity `1` entries of a C10
self-intertwiner is a multiple of ten. -/
theorem zmodTen_selfIntertwiner_sameParity_directed_card_eq_ten_mul
    (M : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hdiag : ∀ z, M z z = 0)
    (hinter : ∀ x y,
      M (x - 1) y + M (x + 1) y =
        M x (y + 1) + M x (y - 1)) :
    let E := (Finset.univ : Finset (ZMod 10 × ZMod 10)).filter fun p =>
      ZModTenEvenOffset (p.2 - p.1) ∧ M p.1 p.2 = 1
    (E.card : ℤ) = 10 *
      (((Finset.univ : Finset (ZMod 10)).filter fun y =>
        ZModTenEvenOffset y ∧ M 0 y = 1).card : ℤ) := by
  classical
  dsimp only
  rw [card_filter_univ_product_eq_sum_card_filter]
  have hrow (x : ZMod 10) :
      ((Finset.univ : Finset (ZMod 10)).filter fun y =>
        ZModTenEvenOffset (y - x) ∧ M x y = 1).card =
      ((Finset.univ : Finset (ZMod 10)).filter fun y =>
        ZModTenEvenOffset y ∧ M 0 y = 1).card := by
    simpa using zmodTen_selfIntertwiner_sameParity_card_eq M hdiag hinter x 0
  simp_rw [hrow]
  simp

/-- In particular a C10 self-intertwiner cannot have exactly four directed
same-parity entries (equivalently, exactly two undirected same-parity edges
when it is symmetric and loopless). -/
theorem zmodTen_selfIntertwiner_sameParity_directed_card_ne_four
    (M : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hdiag : ∀ z, M z z = 0)
    (hinter : ∀ x y,
      M (x - 1) y + M (x + 1) y =
        M x (y + 1) + M x (y - 1)) :
    ((Finset.univ : Finset (ZMod 10 × ZMod 10)).filter fun p =>
      ZModTenEvenOffset (p.2 - p.1) ∧ M p.1 p.2 = 1).card ≠ 4 := by
  intro hfour
  have hmul := zmodTen_selfIntertwiner_sameParity_directed_card_eq_ten_mul
    M hdiag hinter
  dsimp only at hmul
  rw [hfour] at hmul
  omega

end Erdos85

#print axioms Erdos85.zmodTen_selfIntertwiner_sameParity_card_eq
#print axioms Erdos85.zmodTen_selfIntertwiner_sameParity_directed_card_eq_ten_mul
#print axioms Erdos85.zmodTen_selfIntertwiner_sameParity_directed_card_ne_four
