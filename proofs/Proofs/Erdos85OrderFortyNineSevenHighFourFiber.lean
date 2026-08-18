import Proofs.Erdos85OrderFortyNineSevenHighThreeFiber

/-!
# Fiber census for the four-block seven-high triple systems

There are exactly three linear four-triple systems on seven labeled points,
up to relabeling.  This file first certifies that finite classification and
then transports the graph fibers to the canonical SAT masks.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT4TripleSet (index : Nat) : Finset (Finset (Fin 7)) :=
  match index with
  | 0 => {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}}
  | 1 => {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}}
  | _ => {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 6}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fixed_first_four_linear_triples_canonical_packed
    (BCD : (SevenHighTriple × SevenHighTriple) × SevenHighTriple)
    (hfirstB : sevenHighFirstTriple ≠ BCD.1.1)
    (hfirstC : sevenHighFirstTriple ≠ BCD.1.2.1)
    (hfirstD : sevenHighFirstTriple ≠ BCD.2.1)
    (hBC : BCD.1.1 ≠ BCD.1.2) (hBD : BCD.1.1 ≠ BCD.2)
    (hCD : BCD.1.2 ≠ BCD.2)
    (hlinB : (sevenHighFirstTriple ∩ BCD.1.1).card ≤ 1)
    (hlinC : (sevenHighFirstTriple ∩ BCD.1.2.1).card ≤ 1)
    (hlinD : (sevenHighFirstTriple ∩ BCD.2.1).card ≤ 1)
    (hlinBC : (BCD.1.1.1 ∩ BCD.1.2.1).card ≤ 1)
    (hlinBD : (BCD.1.1.1 ∩ BCD.2.1).card ≤ 1)
    (hlinCD : (BCD.1.2.1 ∩ BCD.2.1).card ≤ 1) :
    ∃ index : Nat, index < 3 ∧ ∃ σ : Equiv.Perm (Fin 7),
      ({sevenHighFirstTriple.map σ.toEmbedding,
          BCD.1.1.1.map σ.toEmbedding, BCD.1.2.1.map σ.toEmbedding,
          BCD.2.1.map σ.toEmbedding} : Finset (Finset (Fin 7))) =
        sevenHighT4TripleSet index := by
  native_decide +revert

theorem fixed_first_four_linear_triples_canonical
    (B C D : SevenHighTriple)
    (hfirstB : sevenHighFirstTriple ≠ B.1)
    (hfirstC : sevenHighFirstTriple ≠ C.1)
    (hfirstD : sevenHighFirstTriple ≠ D.1)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hlinB : (sevenHighFirstTriple ∩ B.1).card ≤ 1)
    (hlinC : (sevenHighFirstTriple ∩ C.1).card ≤ 1)
    (hlinD : (sevenHighFirstTriple ∩ D.1).card ≤ 1)
    (hlinBC : (B.1 ∩ C.1).card ≤ 1)
    (hlinBD : (B.1 ∩ D.1).card ≤ 1)
    (hlinCD : (C.1 ∩ D.1).card ≤ 1) :
    ∃ index : Nat, index < 3 ∧ ∃ σ : Equiv.Perm (Fin 7),
      ({sevenHighFirstTriple.map σ.toEmbedding, B.1.map σ.toEmbedding,
          C.1.map σ.toEmbedding, D.1.map σ.toEmbedding} :
          Finset (Finset (Fin 7))) = sevenHighT4TripleSet index := by
  exact fixed_first_four_linear_triples_canonical_packed ((B, C), D)
    hfirstB hfirstC hfirstD hBC hBD hCD hlinB hlinC hlinD hlinBC hlinBD hlinCD

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem four_linear_triples_canonical
    (A B C D : SevenHighTriple)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hlinAB : (A.1 ∩ B.1).card ≤ 1)
    (hlinAC : (A.1 ∩ C.1).card ≤ 1)
    (hlinAD : (A.1 ∩ D.1).card ≤ 1)
    (hlinBC : (B.1 ∩ C.1).card ≤ 1)
    (hlinBD : (B.1 ∩ D.1).card ≤ 1)
    (hlinCD : (C.1 ∩ D.1).card ≤ 1) :
    ∃ index : Nat, index < 3 ∧ ∃ σ : Equiv.Perm (Fin 7),
      ({A.1.map σ.toEmbedding, B.1.map σ.toEmbedding,
          C.1.map σ.toEmbedding, D.1.map σ.toEmbedding} :
          Finset (Finset (Fin 7))) = sevenHighT4TripleSet index := by
  obtain ⟨a, b, c, hab, hac, hbc, hAform⟩ := Finset.card_eq_three.mp A.2
  let f : Fin 3 → Fin 7 := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  obtain ⟨σ0, hσ0⟩ := exists_perm7_send_to_initialSegment (by omega) f hf
  have hAσ0 : A.1.map σ0.toEmbedding = sevenHighFirstTriple := by
    rw [hAform]
    have h0 := hσ0 (0 : Fin 3)
    have h1 := hσ0 (1 : Fin 3)
    have h2 := hσ0 (2 : Fin 3)
    ext w
    fin_cases w <;> simp_all [f, sevenHighFirstTriple]
  let B0 : SevenHighTriple := ⟨B.1.map σ0.toEmbedding, by simp [B.2]⟩
  let C0 : SevenHighTriple := ⟨C.1.map σ0.toEmbedding, by simp [C.2]⟩
  let D0 : SevenHighTriple := ⟨D.1.map σ0.toEmbedding, by simp [D.2]⟩
  have first_ne (X : SevenHighTriple) (hAX : A ≠ X) :
      sevenHighFirstTriple ≠ (X.1.map σ0.toEmbedding) := by
    rw [← hAσ0]
    intro h
    apply hAX
    apply Subtype.ext
    exact Finset.map_injective σ0.toEmbedding h
  have mapped_ne (X Y : SevenHighTriple) (hXY : X ≠ Y) :
      (⟨X.1.map σ0.toEmbedding, by simp [X.2]⟩ : SevenHighTriple) ≠
        ⟨Y.1.map σ0.toEmbedding, by simp [Y.2]⟩ := by
    intro h
    apply hXY
    apply Subtype.ext
    exact Finset.map_injective σ0.toEmbedding (congrArg Subtype.val h)
  have mapped_lin (X Y : SevenHighTriple)
      (hXY : (X.1 ∩ Y.1).card ≤ 1) :
      (X.1.map σ0.toEmbedding ∩ Y.1.map σ0.toEmbedding).card ≤ 1 := by
    rw [← Finset.map_inter, Finset.card_map]
    exact hXY
  obtain ⟨index, hindex, τ, hτcanon⟩ :=
    fixed_first_four_linear_triples_canonical B0 C0 D0
      (first_ne B hAB) (first_ne C hAC) (first_ne D hAD)
      (mapped_ne B C hBC) (mapped_ne B D hBD) (mapped_ne C D hCD)
      (by rw [← hAσ0]; exact mapped_lin A B hlinAB)
      (by rw [← hAσ0]; exact mapped_lin A C hlinAC)
      (by rw [← hAσ0]; exact mapped_lin A D hlinAD)
      (mapped_lin B C hlinBC) (mapped_lin B D hlinBD)
      (mapped_lin C D hlinCD)
  refine ⟨index, hindex, σ0.trans τ, ?_⟩
  have hAcomp : A.1.map (σ0.trans τ).toEmbedding =
      sevenHighFirstTriple.map τ.toEmbedding := by
    rw [Equiv.trans_toEmbedding, ← Finset.map_map, hAσ0]
  rw [hAcomp]
  simpa [Finset.map_map, B0, C0, D0] using hτcanon

theorem sevenHigh_t4_exists_four_triple_supports
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfour : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ x y z u : Fin 49,
      x ≠ y ∧ x ≠ z ∧ x ≠ u ∧ y ≠ z ∧ y ≠ u ∧ z ≠ u ∧
      x ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G x).card = 3 ∧
      y ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G y).card = 3 ∧
      z ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G z).card = 3 ∧
      u ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G u).card = 3 ∧
      ∀ q : Fin 49,
        q ∈ orderFortyNineLowVertices G →
        (orderFortyNineHighSupport G q).card = 3 →
        q = x ∨ q = y ∨ q = z ∨ q = u := by
  let T := (orderFortyNineLowVertices G).filter fun q =>
    (orderFortyNineHighSupport G q).card = 3
  have hT : T.card = 4 := hfour
  obtain ⟨x, y, z, u, hxy, hxz, hxu, hyz, hyu, hzu, hTset⟩ :=
    Finset.card_eq_four.mp hT
  have hx := Finset.mem_filter.mp (by simp [T, hTset] : x ∈ T)
  have hy := Finset.mem_filter.mp (by simp [T, hTset] : y ∈ T)
  have hz := Finset.mem_filter.mp (by simp [T, hTset] : z ∈ T)
  have hu := Finset.mem_filter.mp (by simp [T, hTset] : u ∈ T)
  refine ⟨x, y, z, u, hxy, hxz, hxu, hyz, hyu, hzu,
    hx.1, hx.2, hy.1, hy.2, hz.1, hz.2, hu.1, hu.2, ?_⟩
  intro q hqLow hq3
  have hqT : q ∈ T := Finset.mem_filter.mpr ⟨hqLow, hq3⟩
  simpa [T, hTset] using hqT

theorem sevenHigh_t4_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hfour : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ index : Nat, index < 3 ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7,
      ∃ x y z u : Fin 49,
        ({sevenHighLabeledSupport G e x,
          sevenHighLabeledSupport G e y,
          sevenHighLabeledSupport G e z,
          sevenHighLabeledSupport G e u} : Finset (Finset (Fin 7))) =
            sevenHighT4TripleSet index ∧
        x ≠ y ∧ x ≠ z ∧ x ≠ u ∧ y ≠ z ∧ y ≠ u ∧ z ≠ u ∧
        ∀ q : Fin 49, (sevenHighLabeledSupport G e q).card = 3 →
          q = x ∨ q = y ∨ q = z ∨ q = u := by
  obtain ⟨x, y, z, u, hxy, hxz, hxu, hyz, hyu, hzu,
      hxLow, hx3, hyLow, hy3, hzLow, hz3, huLow, hu3, huniq⟩ :=
    sevenHigh_t4_exists_four_triple_supports G hfour
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  let A := sevenHighLabeledSupport G e0 x
  let B := sevenHighLabeledSupport G e0 y
  let C := sevenHighLabeledSupport G e0 z
  let D := sevenHighLabeledSupport G e0 u
  have hA : A.card = 3 := by rw [sevenHighLabeledSupport_card]; exact hx3
  have hB : B.card = 3 := by rw [sevenHighLabeledSupport_card]; exact hy3
  have hC : C.card = 3 := by rw [sevenHighLabeledSupport_card]; exact hz3
  have hD : D.card = 3 := by rw [sevenHighLabeledSupport_card]; exact hu3
  have support_ne {a b : Fin 49} (hab : a ≠ b)
      {P Q : Finset (Fin 7)}
      (hP : P = sevenHighLabeledSupport G e0 a)
      (hQ : Q = sevenHighLabeledSupport G e0 b)
      (hP3 : P.card = 3) : P ≠ Q := by
    subst P; subst Q
    intro h
    exact hab (sevenHighLabeledSupport_injective_of_two_le
      G hfree e0 (by omega) h)
  have support_lin {a b : Fin 49} (hab : a ≠ b) :
      (sevenHighLabeledSupport G e0 a ∩
        sevenHighLabeledSupport G e0 b).card ≤ 1 := by
    rw [sevenHighLabeledSupport_inter_card]
    exact orderFortyNine_card_inter_highSupport_le_one G hfree hab
  let A3 : SevenHighTriple := ⟨A, hA⟩
  let B3 : SevenHighTriple := ⟨B, hB⟩
  let C3 : SevenHighTriple := ⟨C, hC⟩
  let D3 : SevenHighTriple := ⟨D, hD⟩
  have subtype_ne {P Q : SevenHighTriple} (h : P.1 ≠ Q.1) : P ≠ Q := by
    intro heq; exact h (congrArg Subtype.val heq)
  obtain ⟨index, hindex, σ, hcanon⟩ := four_linear_triples_canonical
    A3 B3 C3 D3
    (subtype_ne (support_ne hxy rfl rfl hA))
    (subtype_ne (support_ne hxz rfl rfl hA))
    (subtype_ne (support_ne hxu rfl rfl hA))
    (subtype_ne (support_ne hyz rfl rfl hB))
    (subtype_ne (support_ne hyu rfl rfl hB))
    (subtype_ne (support_ne hzu rfl rfl hC))
    (support_lin hxy) (support_lin hxz) (support_lin hxu)
    (support_lin hyz) (support_lin hyu) (support_lin hzu)
  let e := e0.trans σ
  have heSupport (q : Fin 49) : sevenHighLabeledSupport G e q =
      (sevenHighLabeledSupport G e0 q).map σ.toEmbedding := by
    simp [sevenHighLabeledSupport, e, Finset.map_map]
  refine ⟨index, hindex, e, x, y, z, u, ?_, hxy, hxz, hxu,
    hyz, hyu, hzu, ?_⟩
  · rw [heSupport, heSupport, heSupport, heSupport]
    exact hcanon
  · intro q hq3
    have hqOrig3 : (orderFortyNineHighSupport G q).card = 3 := by
      rw [← sevenHighLabeledSupport_card G e q]
      exact hq3
    have hqLow : q ∈ orderFortyNineLowVertices G := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ q, ?_⟩
      intro hqHigh
      have hq0 := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hqHigh
      change (orderFortyNineHighSupport G q).card = 0 at hq0
      omega
    exact huniq q hqLow hqOrig3

theorem sevenHighT4TripleSet_member_card
    (index : Nat) (hindex : index < 3)
    {T : Finset (Fin 7)} (hT : T ∈ sevenHighT4TripleSet index) :
    T.card = 3 := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t4_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT4TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (w : Fin 7) :
    ((G.neighborFinset (e.symm w).1).filter fun q =>
      (orderFortyNineHighSupport G q).card = 3).card =
      ((sevenHighT4TripleSet index).filter fun T => w ∈ T).card := by
  let f : Fin 49 → Finset (Fin 7) := sevenHighLabeledSupport G e
  have hinj : Set.InjOn f ↑s := by
    intro a ha b hb hab
    exact sevenHighLabeledSupport_injective_of_two_le G hfree e
      (by have := hmember a ha; omega) hab
  have hgraphSet : ((G.neighborFinset (e.symm w).1).filter fun q =>
      (orderFortyNineHighSupport G q).card = 3) =
      s.filter fun q => w ∈ f q := by
    ext q
    constructor
    · intro hq
      have hq3 : (f q).card = 3 := by
        rw [sevenHighLabeledSupport_card]
        exact (Finset.mem_filter.mp hq).2
      refine Finset.mem_filter.mpr ⟨huniq q hq3, ?_⟩
      apply (mem_sevenHighLabeledSupport_iff G e q w).mpr
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
        (Finset.mem_filter.mp hq).1
    · intro hq
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_sevenHighLabeledSupport_iff G e q w).mp
            (Finset.mem_filter.mp hq).2
      · rw [← sevenHighLabeledSupport_card G e q]
        exact hmember q (Finset.mem_filter.mp hq).1
  rw [hgraphSet, ← hmap, Finset.filter_image]
  symm
  exact Finset.card_image_iff.mpr (hinj.mono (Finset.filter_subset _ _))

theorem sevenHigh_t4_singleton_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT4TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (w : Fin 7) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = {w}} =
      ((sevenHighT4TripleSet index).filter fun T => w ∈ T).card + 2 := by
  rw [sevenHigh_singleton_fiber_card_eq_local G e w]
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
      (Finset.mem_filter.mp (e.symm w).2).2
  dsimp only at hp
  rw [sevenHigh_t4_local_triple_card G hfree index hindex e s
    hmap hmember huniq w] at hp
  omega

theorem sevenHigh_t4_exists_triple_superset_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT4TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (P : Finset (Fin 7)) :
    (∃ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 ∧
      P ⊆ sevenHighLabeledSupport G e q) ↔
      ∃ T ∈ sevenHighT4TripleSet index, P ⊆ T := by
  constructor
  · rintro ⟨q, hq3, hPq⟩
    refine ⟨sevenHighLabeledSupport G e q, ?_, hPq⟩
    rw [← hmap]
    exact Finset.mem_image.mpr ⟨q, huniq q hq3, rfl⟩
  · rintro ⟨T, hT, hPT⟩
    rw [← hmap] at hT
    obtain ⟨q, hqs, hqT⟩ := Finset.mem_image.mp hT
    refine ⟨q, hmember q hqs, ?_⟩
    simpa [hqT] using hPT

theorem sevenHigh_t4_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT4TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (S : Finset (Fin 7)) (hS3 : S.card = 3) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = S} =
      if S ∈ sevenHighT4TripleSet index then 1 else 0 := by
  by_cases hS : S ∈ sevenHighT4TripleSet index
  · rw [if_pos hS]
    rw [← hmap] at hS
    obtain ⟨q, hqs, hqS⟩ := Finset.mem_image.mp hS
    have hone := sevenHighLabeledSupport_fiber_card_eq_one
      G hfree e q (by have := hmember q hqs; omega)
    simpa [hqS] using hone
  · rw [if_neg hS, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqEq := (Finset.mem_filter.mp hq).2
    apply hS
    rw [← hmap]
    exact Finset.mem_image.mpr ⟨q, huniq q (by simpa [hqEq] using hS3), hqEq⟩

def sevenHighT4KeyMultiplicity
    (index : Nat) (key : Option (Fin 7) × Finset (Fin 7)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 3
      else if key.2.card = 1 then
        ((sevenHighT4TripleSet index).filter fun T => key.2 ⊆ T).card + 2
      else if key.2.card = 2 then
        if ∃ T ∈ sevenHighT4TripleSet index, key.2 ⊆ T then 0 else 1
      else if key.2 ∈ sevenHighT4TripleSet index then 1 else 0

theorem sevenHigh_t4_mask_key_fiber_card
    (index : Nat) (hindex : index < 3)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {i : Fin 49 //
      sevenHighMaskAlignedKey
        (OrderFortyNineSevenHighCensus.representativeMasks 4 index) i = key} =
      sevenHighT4KeyMultiplicity index key := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t4_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (index : Nat)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT4TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (S : Finset (Fin 7))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2)
    (hcanonical : S ∉ sevenHighT4TripleSet index) :
    Fintype.card {q : Fin 49 //
      sevenHighGraphAlignedKey G e q = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hkey := (Finset.mem_filter.mp hq).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : sevenHighLabeledSupport G e q = S := by
    simpa [sevenHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hqNotHigh : q ∉ orderFortyNineHighVertices G := by
    intro hqHigh
    simp [sevenHighGraphAlignedKey, hqHigh] at hfirst
  have hq7 : G.degree q = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) q with hq7 | hq8
    · exact hq7
    · exact False.elim (hqNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, sevenHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hq7
  have hS3 : S.card = 3 := by omega
  apply hcanonical
  rw [← hmap]
  exact Finset.mem_image.mpr ⟨q, huniq q (by simpa [hsupp] using hS3), hsupp⟩

theorem sevenHigh_t4_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hfour : orderFortyNineHighIncidenceCount G 3 = 4)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (s : Finset (Fin 49))
    (hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT4TripleSet index)
    (hmember : ∀ q ∈ s, (sevenHighLabeledSupport G e q).card = 3)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {q : Fin 49 // sevenHighGraphAlignedKey G e q = key} =
      sevenHighT4KeyMultiplicity index key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [sevenHighT4KeyMultiplicity] using
          sevenHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [sevenHighT4KeyMultiplicity, hS0] using
          sevenHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        have hp := orderFortyNine_highIncidence_profile_of_seven_high
          G hfree hmin (Fintype.card_fin 49) hHigh
        dsimp only at hp
        have hn0 : orderFortyNineHighIncidenceCount G 0 = 3 := by omega
        simpa [sevenHighT4KeyMultiplicity, hn0] using
          sevenHigh_aligned_emptyLow_fiber_card G e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
            (by simp)]
          rw [sevenHigh_t4_singleton_fiber_card G hfree hmin hHigh
            index hindex e s hmap hmember huniq w]
          simp only [sevenHighT4KeyMultiplicity, Finset.card_singleton,
            ↓reduceIte]
          congr 2
          ext T
          simp
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
              (by simp)]
            rw [sevenHigh_pair_fiber_card G hfree hmin e a b hab]
            have hiff := sevenHigh_t4_exists_triple_superset_iff
              G index e s hmap hmember huniq {a, b}
            by_cases hex : ∃ q : Fin 49,
                (sevenHighLabeledSupport G e q).card = 3 ∧
                ({a, b} : Finset (Fin 7)) ⊆ sevenHighLabeledSupport G e q
            · have hrep := hiff.mp hex
              simp [sevenHighT4KeyMultiplicity, hab, hex, hrep]
            · have hrep := (not_congr hiff).mp hex
              simp [sevenHighT4KeyMultiplicity, hab, hex, hrep]
          · by_cases hcanonical : S ∈ sevenHighT4TripleSet index
            · have hS3 := sevenHighT4TripleSet_member_card
                index hindex hcanonical
              rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e S
                (Finset.card_pos.mp (by omega))]
              rw [sevenHigh_t4_triple_fiber_card G hfree index e s
                hmap hmember huniq S hS3]
              simp [sevenHighT4KeyMultiplicity, h0, h1, h2, hcanonical]
            · simpa [sevenHighT4KeyMultiplicity, h0, h1, h2, hcanonical] using
                sevenHigh_t4_alignedLow_other_fiber_card_eq_zero
                  G hfree hmin index e s hmap huniq
                    S h0 h1 h2 hcanonical

theorem sevenHighCanonicalFiberCover_four :
    SevenHighCanonicalFiberCover 4 := by
  intro G _ _ _ hfree hmin hHigh hfour
  obtain ⟨index, hindex, e, x, y, z, u, hcanon,
      hxy, hxz, hxu, hyz, hyu, hzu, huniq0⟩ :=
    sevenHigh_t4_exists_normalized_labeling G hfree hmin hHigh hfour
  let s : Finset (Fin 49) := {x, y, z, u}
  have hmap : s.image (sevenHighLabeledSupport G e) =
      sevenHighT4TripleSet index := by
    simpa [s] using hcanon
  have hmember : ∀ q ∈ s,
      (sevenHighLabeledSupport G e q).card = 3 := by
    intro q hqs
    apply sevenHighT4TripleSet_member_card index hindex
    rw [← hmap]
    exact Finset.mem_image.mpr ⟨q, hqs, rfl⟩
  have huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 → q ∈ s := by
    intro q hq3
    simpa [s] using huniq0 q hq3
  refine ⟨index, by interval_cases index <;> native_decide,
    e, by interval_cases index <;> native_decide, ?_⟩
  intro key
  rw [sevenHigh_t4_graph_key_fiber_card G hfree hmin hHigh hfour
      index hindex e s hmap hmember huniq key,
    sevenHigh_t4_mask_key_fiber_card index hindex key]

theorem sevenHighCanonicalGraphCover_four :
    SevenHighCanonicalGraphCover 4 :=
  sevenHighCanonicalGraphCover_of_labelingCover
    (sevenHighCanonicalLabelingCover_of_fiberCover
      sevenHighCanonicalFiberCover_four)

end

end Erdos85
