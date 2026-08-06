import Proofs.Erdos85ExcessOneEvenCanonical

/-!
# The path sector at even-degree excess one is empty or large

At even degree and excess one the triangle-free color has local degree
zero or two, so the triangle-free edge graph `T` is a disjoint union of
cycles on the degree-two sector `S`.  A `T`-cycle of length three would
be a triangle of triangle-free edges (impossible), and one of length four
would be a `C₄` of the original graph (excluded by `C₄`-freeness).  Hence
every `T`-cycle has length at least five, and the degree-two sector is
either empty or has at least five vertices.

Combined with the landed trace identity `tr(AD) = 2|S|`, this quantizes
the first mixed moment: it vanishes or is at least ten.
-/

open SimpleGraph

namespace Erdos85

/-- In a two-regular vertex, any neighbor has a companion neighbor. -/
theorem exists_other_neighbor_of_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {v a : V}
    (hdeg : H.degree v = 2) (hadj : H.Adj v a) :
    ∃ b, H.Adj v b ∧ b ≠ a := by
  have hcard : (H.neighborFinset v).card = 2 := by
    rw [H.card_neighborFinset_eq_degree]
    exact hdeg
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hcard
  have hamem : a ∈ H.neighborFinset v := (H.mem_neighborFinset v a).mpr hadj
  rw [hset] at hamem
  rcases Finset.mem_insert.mp hamem with ha | ha
  · refine ⟨q, ?_, ?_⟩
    · refine (H.mem_neighborFinset v q).mp ?_
      rw [hset]
      simp
    · rw [ha]
      exact hpq.symm
  · have ha' : a = q := Finset.mem_singleton.mp ha
    refine ⟨p, ?_, ?_⟩
    · refine (H.mem_neighborFinset v p).mp ?_
      rw [hset]
      simp
    · rw [ha']
      exact hpq

/-- Endpoints of triangle-free edges lie in the degree-two color sector. -/
theorem excessOne_even_triangleFree_degree_eq_two_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) {x y : V}
    (hadj : (triangleFreeEdgeGraph G).Adj x y) :
    (triangleFreeEdgeGraph G).degree y = 2 := by
  rcases excessOne_even_triangleFree_degree_zero_or_two
      G hfree heven hreg hcard y with h0 | h2
  · exfalso
    have hmem : x ∈ (triangleFreeEdgeGraph G).neighborFinset y :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset y x).mpr hadj.symm
    have hzero : ((triangleFreeEdgeGraph G).neighborFinset y).card = 0 := by
      rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact h0
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hmem
    exact Finset.notMem_empty x hmem
  · exact h2

/-- **Path-sector quantization.**  At even degree and excess one the
degree-two triangle-free sector is empty or has at least five vertices:
the triangle-free edge graph is a disjoint union of cycles there, and
`C₄`-freeness forbids cycles of length three and four. -/
theorem excessOne_even_pathSector_card_eq_zero_or_five_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0 ∨
      5 ≤ (Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card := by
  by_cases hempty : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2) = ∅
  · left
    rw [hempty, Finset.card_empty]
  right
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hxdeg : (triangleFreeEdgeGraph G).degree x = 2 :=
    (Finset.mem_filter.mp hx).2
  have hxcard : ((triangleFreeEdgeGraph G).neighborFinset x).card = 2 := by
    rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
    exact hxdeg
  obtain ⟨y, z, hyz, hset⟩ := Finset.card_eq_two.mp hxcard
  have hxy : (triangleFreeEdgeGraph G).Adj x y := by
    refine ((triangleFreeEdgeGraph G).mem_neighborFinset x y).mp ?_
    rw [hset]
    simp
  have hxz : (triangleFreeEdgeGraph G).Adj x z := by
    refine ((triangleFreeEdgeGraph G).mem_neighborFinset x z).mp ?_
    rw [hset]
    simp
  have hydeg : (triangleFreeEdgeGraph G).degree y = 2 :=
    excessOne_even_triangleFree_degree_eq_two_of_adj
      G hfree heven hreg hcard hxy
  have hzdeg : (triangleFreeEdgeGraph G).degree z = 2 :=
    excessOne_even_triangleFree_degree_eq_two_of_adj
      G hfree heven hreg hcard hxz
  obtain ⟨w, hyw, hwx⟩ := exists_other_neighbor_of_degree_two
    (triangleFreeEdgeGraph G) hydeg hxy.symm
  obtain ⟨u, hzu, hux⟩ := exists_other_neighbor_of_degree_two
    (triangleFreeEdgeGraph G) hzdeg hxz.symm
  have hwdeg : (triangleFreeEdgeGraph G).degree w = 2 :=
    excessOne_even_triangleFree_degree_eq_two_of_adj
      G hfree heven hreg hcard hyw
  have hudeg : (triangleFreeEdgeGraph G).degree u = 2 :=
    excessOne_even_triangleFree_degree_eq_two_of_adj
      G hfree heven hreg hcard hzu
  have hyz_nadj : ¬ (triangleFreeEdgeGraph G).Adj y z := fun h =>
    triangleFreeEdgeGraph_not_triangle G hxy h hxz.symm
  have hxy' : x ≠ y := (triangleFreeEdgeGraph G).ne_of_adj hxy
  have hxz' : x ≠ z := (triangleFreeEdgeGraph G).ne_of_adj hxz
  have hyw' : y ≠ w := (triangleFreeEdgeGraph G).ne_of_adj hyw
  have hzu' : z ≠ u := (triangleFreeEdgeGraph G).ne_of_adj hzu
  have hwz : w ≠ z := by
    intro h
    rw [h] at hyw
    exact hyz_nadj hyw
  have huy : u ≠ y := by
    intro h
    rw [h] at hzu
    exact hyz_nadj hzu.symm
  have huw : u ≠ w := by
    intro h
    rw [h] at hzu
    exact triangleFreeEdgeGraph_not_four_cycle G hfree hxy hyw hzu.symm
      hxz.symm hwx.symm hyz hxy'.symm hyw' hxz'.symm hwz.symm
  have hmemS : ∀ v : V, (triangleFreeEdgeGraph G).degree v = 2 →
      v ∈ Finset.univ.filter (fun t : V =>
        (triangleFreeEdgeGraph G).degree t = 2) := fun v hv =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  have hsub : ({x, y, z, w, u} : Finset V) ⊆
      Finset.univ.filter (fun t : V =>
        (triangleFreeEdgeGraph G).degree t = 2) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hxdeg
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hydeg
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hzdeg
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hmemS _ hwdeg
    · rw [Finset.mem_singleton.mp ht]
      exact hmemS _ hudeg
  have hw_notin : w ∉ ({u} : Finset V) := by
    simp only [Finset.mem_singleton]
    exact fun h => huw h.symm
  have c2 : ({w, u} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem hw_notin, Finset.card_singleton]
  have hz_notin : z ∉ ({w, u} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hwz h.symm
    · exact hzu' h
  have c3 : ({z, w, u} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem hz_notin, c2]
  have hy_notin : y ∉ ({z, w, u} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact hyz h
    · exact hyw' h
    · exact huy h.symm
  have c4 : ({y, z, w, u} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem hy_notin, c3]
  have hx_notin : x ∉ ({y, z, w, u} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h | h)
    · exact hxy' h
    · exact hxz' h
    · exact hwx h.symm
    · exact hux h.symm
  have c5 : ({x, y, z, w, u} : Finset V).card = 5 := by
    rw [Finset.card_insert_of_notMem hx_notin, c4]
  calc
    (5 : ℕ) = ({x, y, z, w, u} : Finset V).card := c5.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Quantized first mixed moment.**  At even degree and excess one,
`tr(AD)` vanishes or is at least ten. -/
theorem trace_adjMatrix_mul_secondOrderDefect_eq_zero_or_ten_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) = 0 ∨
      10 ≤ Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) := by
  rw [trace_adjMatrix_mul_secondOrderDefect_even_excessOne
    G hfree heven hreg hcard]
  rcases excessOne_even_pathSector_card_eq_zero_or_five_le
      G hfree heven hreg hcard with h | h
  · left
    rw [h]
    simp
  · right
    have : (5 : ℤ) ≤ ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) := by
      exact_mod_cast h
    linarith

end Erdos85
