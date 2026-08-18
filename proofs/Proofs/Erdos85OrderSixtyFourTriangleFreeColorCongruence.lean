import Proofs.Erdos85OrderSixtyFourTriangleFreeColorOrder
import Proofs.Erdos85OrderSixtyFourTriangleFreeEdgeNecessity
import Proofs.Erdos85EvenExcessOnePathSector

/-!
# The mixed triangle-free color has order one modulo three

In the all-size-sixteen stratum every triangle-free degree is zero or two.
The global cubic trace says the total triangle-free degree is two modulo six,
so the number of degree-two vertices is one modulo three.  This applies to
the live mixed sector without assuming an all-triangle-free component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The triangle-free colored support has cardinality `3k+1`. -/
theorem orderSixtyFour_allSixteen_triangleFreeColorOrder_eq_three_mul_add_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    ∃ k : ℕ,
      (Finset.univ.filter fun x : Fin 64 =>
        (triangleFreeEdgeGraph G).degree x = 2).card = 3 * k + 1 := by
  let T := triangleFreeEdgeGraph G
  let C := (Finset.univ.filter fun x : Fin 64 => T.degree x = 2).card
  have hdegree (x : Fin 64) : T.degree x = 0 ∨ T.degree x = 2 := by
    simpa [T] using
      orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two
        G hfree hreg hsize x
  have hsumNat : (∑ x : Fin 64, T.degree x) = 2 * C := by
    calc
      (∑ x : Fin 64, T.degree x) =
          ∑ x : Fin 64, if T.degree x = 2 then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        rcases hdegree x with hx0 | hx2
        · simp [hx0]
        · simp [hx2]
      _ = 2 * C := by
        rw [← Finset.sum_filter]
        simp [C, Nat.mul_comm]
  obtain ⟨z, hz⟩ :=
    orderSixtyFour_regular_sum_triangleFreeDegrees_eq_six_mul_add_two
      G hfree hreg
  have hcast : (∑ x : Fin 64, (T.degree x : ℤ)) =
      ((∑ x : Fin 64, T.degree x : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [hcast, hsumNat] at hz
  have hznonneg : 0 ≤ z := by omega
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hznonneg
  refine ⟨k, ?_⟩
  simpa [C, T] using (by omega : C = 3 * k + 1)

/-- Congruence form of the mixed-sector color-order constraint. -/
theorem orderSixtyFour_allSixteen_triangleFreeColorOrder_mod_three_eq_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card % 3 = 1 := by
  obtain ⟨k, hk⟩ :=
    orderSixtyFour_allSixteen_triangleFreeColorOrder_eq_three_mul_add_one
      G hfree hreg hsize
  rw [hk]
  omega

/-- In the all-size-sixteen stratum the mixed triangle-free color has at
least seven vertices.  Nonemptiness is forced globally, local degree-two
geometry supplies at least five, and the color-order congruence excludes
five and six. -/
theorem orderSixtyFour_allSixteen_seven_le_triangleFreeColorOrder
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    7 ≤ (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card := by
  let T := triangleFreeEdgeGraph G
  let S := Finset.univ.filter fun x : Fin 64 => T.degree x = 2
  have hdegree (x : Fin 64) : T.degree x = 0 ∨ T.degree x = 2 := by
    simpa [T] using
      orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two
        G hfree hreg hsize x
  obtain ⟨x, y, hxy⟩ :=
    orderSixtyFour_regular_exists_triangleFreeEdge G hfree hreg
  have hxdeg : T.degree x = 2 := by
    rcases hdegree x with hx0 | hx2
    · have hpos : 0 < T.degree x := by
        rw [← T.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨y, (T.mem_neighborFinset x y).mpr hxy⟩
      omega
    · exact hx2
  have hxcard : (T.neighborFinset x).card = 2 := by
    rw [T.card_neighborFinset_eq_degree, hxdeg]
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hxcard
  have hxa : T.Adj x a := (T.mem_neighborFinset x a).mp (by rw [hset]; simp)
  have hxb : T.Adj x b := (T.mem_neighborFinset x b).mp (by rw [hset]; simp)
  have hprop {u v : Fin 64} (huv : T.Adj u v) : T.degree v = 2 := by
    rcases hdegree v with hv0 | hv2
    · have hpos : 0 < T.degree v := by
        rw [← T.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨u, (T.mem_neighborFinset v u).mpr huv.symm⟩
      omega
    · exact hv2
  have hadeg : T.degree a = 2 := hprop hxa
  have hbdeg : T.degree b = 2 := hprop hxb
  obtain ⟨w, haw, hwx⟩ := exists_other_neighbor_of_degree_two T hadeg hxa.symm
  obtain ⟨u, hbu, hux⟩ := exists_other_neighbor_of_degree_two T hbdeg hxb.symm
  have hwdeg : T.degree w = 2 := hprop haw
  have hudeg : T.degree u = 2 := hprop hbu
  have hab_nadj : ¬ T.Adj a b := fun h =>
    triangleFreeEdgeGraph_not_triangle G hxa h hxb.symm
  have hxa' : x ≠ a := T.ne_of_adj hxa
  have hxb' : x ≠ b := T.ne_of_adj hxb
  have haw' : a ≠ w := T.ne_of_adj haw
  have hbu' : b ≠ u := T.ne_of_adj hbu
  have hwb : w ≠ b := by
    intro h
    rw [h] at haw
    exact hab_nadj haw
  have hua : u ≠ a := by
    intro h
    rw [h] at hbu
    exact hab_nadj hbu.symm
  have huw : u ≠ w := by
    intro h
    rw [h] at hbu
    exact triangleFreeEdgeGraph_not_four_cycle G hfree hxa haw hbu.symm
      hxb.symm hwx.symm hab hxa'.symm haw' hxb'.symm hwb.symm
  have hmemS : ∀ v : Fin 64, T.degree v = 2 → v ∈ S := fun v hv =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  have hsub : ({x, a, b, w, u} : Finset (Fin 64)) ⊆ S := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hxdeg
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hadeg
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hbdeg
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hwdeg
    · rw [Finset.mem_singleton.mp ht]
      exact hmemS _ hudeg
  have hw_notin : w ∉ ({u} : Finset (Fin 64)) := by
    simp only [Finset.mem_singleton]
    exact fun h => huw h.symm
  have c2 : ({w, u} : Finset (Fin 64)).card = 2 := by
    rw [Finset.card_insert_of_notMem hw_notin, Finset.card_singleton]
  have hb_notin : b ∉ ({w, u} : Finset (Fin 64)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hwb h.symm
    · exact hbu' h
  have c3 : ({b, w, u} : Finset (Fin 64)).card = 3 := by
    rw [Finset.card_insert_of_notMem hb_notin, c2]
  have ha_notin : a ∉ ({b, w, u} : Finset (Fin 64)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact hab h
    · exact haw' h
    · exact hua h.symm
  have c4 : ({a, b, w, u} : Finset (Fin 64)).card = 4 := by
    rw [Finset.card_insert_of_notMem ha_notin, c3]
  have hx_notin : x ∉ ({a, b, w, u} : Finset (Fin 64)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact hxa' h
    · exact hxb' h
    · exact hwx h.symm
    · exact hux h.symm
  have c5 : ({x, a, b, w, u} : Finset (Fin 64)).card = 5 := by
    rw [Finset.card_insert_of_notMem hx_notin, c4]
  have hfive : 5 ≤ S.card := by
    calc
      (5 : ℕ) = ({x, a, b, w, u} : Finset (Fin 64)).card := c5.symm
      _ ≤ S.card := Finset.card_le_card hsub
  have hmod : S.card % 3 = 1 := by
    simpa [S, T] using
      orderSixtyFour_allSixteen_triangleFreeColorOrder_mod_three_eq_one
        G hfree hreg hsize
  simpa [S, T] using (by omega : 7 ≤ S.card)

end

end Erdos85

#print axioms
  Erdos85.orderSixtyFour_allSixteen_triangleFreeColorOrder_eq_three_mul_add_one
#print axioms
  Erdos85.orderSixtyFour_allSixteen_triangleFreeColorOrder_mod_three_eq_one
#print axioms
  Erdos85.orderSixtyFour_allSixteen_seven_le_triangleFreeColorOrder
