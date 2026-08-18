import Proofs.Erdos85OrderFortyNineSevenHighTwoFiber

/-!
# Fiber census for the three-block seven-high triple systems

The finite canonicalization theorem below checks every ordered triple of
three-subsets of `Fin 7`, and produces one of the three stored representatives
up to a permutation of the seven high points.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT3TripleSet (index : Nat) : Finset (Finset (Fin 7)) :=
  match index with
  | 0 => {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}}
  | 1 => {{0, 1, 2}, {0, 3, 4}, {1, 3, 5}}
  | _ => {{0, 1, 2}, {0, 3, 4}, {1, 5, 6}}

abbrev SevenHighTriple := {S : Finset (Fin 7) // S.card = 3}

def sevenHighFirstTriple : Finset (Fin 7) := {0, 1, 2}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fixed_first_three_linear_triples_canonical
    (B C : SevenHighTriple)
    (hfirstB : sevenHighFirstTriple ≠ B.1)
    (hfirstC : sevenHighFirstTriple ≠ C.1)
    (hBC : B ≠ C)
    (hlinB : (sevenHighFirstTriple ∩ B.1).card ≤ 1)
    (hlinC : (sevenHighFirstTriple ∩ C.1).card ≤ 1)
    (hlinBC : (B.1 ∩ C.1).card ≤ 1) :
    ∃ index : Nat, index < 3 ∧ ∃ σ : Equiv.Perm (Fin 7),
      ({sevenHighFirstTriple.map σ.toEmbedding, B.1.map σ.toEmbedding,
          C.1.map σ.toEmbedding} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index := by
  native_decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem three_linear_triples_canonical
    (A B C : SevenHighTriple)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hlinAB : (A.1 ∩ B.1).card ≤ 1)
    (hlinAC : (A.1 ∩ C.1).card ≤ 1)
    (hlinBC : (B.1 ∩ C.1).card ≤ 1) :
    ∃ index : Nat, index < 3 ∧ ∃ σ : Equiv.Perm (Fin 7),
      ({A.1.map σ.toEmbedding, B.1.map σ.toEmbedding,
          C.1.map σ.toEmbedding} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index := by
  obtain ⟨a, b, c, hab, hac, hbc, hAform⟩ :=
    Finset.card_eq_three.mp A.2
  let f : Fin 3 → Fin 7 := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  obtain ⟨σ0, hσ0⟩ := exists_perm7_send_to_initialSegment
    (by omega) f hf
  have hAσ0 : A.1.map σ0.toEmbedding = sevenHighFirstTriple := by
    rw [hAform]
    have h0 := hσ0 (0 : Fin 3)
    have h1 := hσ0 (1 : Fin 3)
    have h2 := hσ0 (2 : Fin 3)
    ext w
    fin_cases w <;> simp_all [f, sevenHighFirstTriple]
  let B0 : SevenHighTriple := ⟨B.1.map σ0.toEmbedding, by simp [B.2]⟩
  let C0 : SevenHighTriple := ⟨C.1.map σ0.toEmbedding, by simp [C.2]⟩
  have hfirstB : sevenHighFirstTriple ≠ B0.1 := by
    rw [← hAσ0]
    intro h
    apply hAB
    apply Subtype.ext
    exact Finset.map_injective σ0.toEmbedding h
  have hfirstC : sevenHighFirstTriple ≠ C0.1 := by
    rw [← hAσ0]
    intro h
    apply hAC
    apply Subtype.ext
    exact Finset.map_injective σ0.toEmbedding h
  have hB0C0 : B0 ≠ C0 := by
    intro h
    apply hBC
    apply Subtype.ext
    exact Finset.map_injective σ0.toEmbedding (congrArg Subtype.val h)
  have hlinB : (sevenHighFirstTriple ∩ B0.1).card ≤ 1 := by
    rw [← hAσ0]
    change (A.1.map σ0.toEmbedding ∩ B.1.map σ0.toEmbedding).card ≤ 1
    rw [← Finset.map_inter, Finset.card_map]
    exact hlinAB
  have hlinC : (sevenHighFirstTriple ∩ C0.1).card ≤ 1 := by
    rw [← hAσ0]
    change (A.1.map σ0.toEmbedding ∩ C.1.map σ0.toEmbedding).card ≤ 1
    rw [← Finset.map_inter, Finset.card_map]
    exact hlinAC
  have hlinB0C0 : (B0.1 ∩ C0.1).card ≤ 1 := by
    change (B.1.map σ0.toEmbedding ∩ C.1.map σ0.toEmbedding).card ≤ 1
    rw [← Finset.map_inter, Finset.card_map]
    exact hlinBC
  obtain ⟨index, hindex, τ, hτcanon⟩ :=
    fixed_first_three_linear_triples_canonical
      B0 C0 hfirstB hfirstC hB0C0 hlinB hlinC hlinB0C0
  refine ⟨index, hindex, σ0.trans τ, ?_⟩
  have hAcomp : A.1.map (σ0.trans τ).toEmbedding =
      sevenHighFirstTriple.map τ.toEmbedding := by
    rw [Equiv.trans_toEmbedding, ← Finset.map_map, hAσ0]
  rw [hAcomp]
  simpa [Finset.map_map, B0, C0] using hτcanon

theorem sevenHigh_t3_exists_three_triple_supports
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hthree : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ x y z : Fin 49, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      x ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G x).card = 3 ∧
      y ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G y).card = 3 ∧
      z ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G z).card = 3 ∧
      ∀ q : Fin 49,
        q ∈ orderFortyNineLowVertices G →
        (orderFortyNineHighSupport G q).card = 3 →
        q = x ∨ q = y ∨ q = z := by
  let T := (orderFortyNineLowVertices G).filter fun q =>
    (orderFortyNineHighSupport G q).card = 3
  have hT : T.card = 3 := by exact hthree
  obtain ⟨x, y, z, hxy, hxz, hyz, hTset⟩ := Finset.card_eq_three.mp hT
  have hx := Finset.mem_filter.mp (by simp [T, hTset] : x ∈ T)
  have hy := Finset.mem_filter.mp (by simp [T, hTset] : y ∈ T)
  have hz := Finset.mem_filter.mp (by simp [T, hTset] : z ∈ T)
  refine ⟨x, y, z, hxy, hxz, hyz, hx.1, hx.2, hy.1, hy.2,
    hz.1, hz.2, ?_⟩
  intro q hqLow hq3
  have hqT : q ∈ T := Finset.mem_filter.mpr ⟨hqLow, hq3⟩
  simpa [T, hTset] using hqT

theorem sevenHigh_t3_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hthree : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ index : Nat, index < 3 ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7,
      ∃ x y z : Fin 49,
        ({sevenHighLabeledSupport G e x,
          sevenHighLabeledSupport G e y,
          sevenHighLabeledSupport G e z} : Finset (Finset (Fin 7))) =
            sevenHighT3TripleSet index ∧
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        ∀ q : Fin 49, (sevenHighLabeledSupport G e q).card = 3 →
          q = x ∨ q = y ∨ q = z := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hxLow, hx3, hyLow, hy3,
      hzLow, hz3, huniq⟩ := sevenHigh_t3_exists_three_triple_supports G hthree
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  let A := sevenHighLabeledSupport G e0 x
  let B := sevenHighLabeledSupport G e0 y
  let C := sevenHighLabeledSupport G e0 z
  have hA : A.card = 3 := by
    change (sevenHighLabeledSupport G e0 x).card = 3
    rw [sevenHighLabeledSupport_card]
    exact hx3
  have hB : B.card = 3 := by
    change (sevenHighLabeledSupport G e0 y).card = 3
    rw [sevenHighLabeledSupport_card]
    exact hy3
  have hC : C.card = 3 := by
    change (sevenHighLabeledSupport G e0 z).card = 3
    rw [sevenHighLabeledSupport_card]
    exact hz3
  have hAB : A ≠ B := by
    intro h
    exact hxy (sevenHighLabeledSupport_injective_of_two_le
      G hfree e0 (by rw [hA]; omega) h)
  have hAC : A ≠ C := by
    intro h
    exact hxz (sevenHighLabeledSupport_injective_of_two_le
      G hfree e0 (by rw [hA]; omega) h)
  have hBC : B ≠ C := by
    intro h
    exact hyz (sevenHighLabeledSupport_injective_of_two_le
      G hfree e0 (by rw [hB]; omega) h)
  have hlinAB : (A ∩ B).card ≤ 1 := by
    change (sevenHighLabeledSupport G e0 x ∩
      sevenHighLabeledSupport G e0 y).card ≤ 1
    rw [sevenHighLabeledSupport_inter_card]
    exact orderFortyNine_card_inter_highSupport_le_one G hfree hxy
  have hlinAC : (A ∩ C).card ≤ 1 := by
    change (sevenHighLabeledSupport G e0 x ∩
      sevenHighLabeledSupport G e0 z).card ≤ 1
    rw [sevenHighLabeledSupport_inter_card]
    exact orderFortyNine_card_inter_highSupport_le_one G hfree hxz
  have hlinBC : (B ∩ C).card ≤ 1 := by
    change (sevenHighLabeledSupport G e0 y ∩
      sevenHighLabeledSupport G e0 z).card ≤ 1
    rw [sevenHighLabeledSupport_inter_card]
    exact orderFortyNine_card_inter_highSupport_le_one G hfree hyz
  let A3 : SevenHighTriple := ⟨A, hA⟩
  let B3 : SevenHighTriple := ⟨B, hB⟩
  let C3 : SevenHighTriple := ⟨C, hC⟩
  have hAB3 : A3 ≠ B3 := by
    intro h
    exact hAB (congrArg Subtype.val h)
  have hAC3 : A3 ≠ C3 := by
    intro h
    exact hAC (congrArg Subtype.val h)
  have hBC3 : B3 ≠ C3 := by
    intro h
    exact hBC (congrArg Subtype.val h)
  obtain ⟨index, hindex, σ, hcanon⟩ := three_linear_triples_canonical
    A3 B3 C3 hAB3 hAC3 hBC3 hlinAB hlinAC hlinBC
  let e := e0.trans σ
  have heSupport (q : Fin 49) : sevenHighLabeledSupport G e q =
      (sevenHighLabeledSupport G e0 q).map σ.toEmbedding := by
    simp [sevenHighLabeledSupport, e, Finset.map_map]
  refine ⟨index, hindex, e, x, y, z, ?_, hxy, hxz, hyz, ?_⟩
  · rw [heSupport, heSupport, heSupport]
    change ({A.map σ.toEmbedding, B.map σ.toEmbedding,
      C.map σ.toEmbedding} : Finset (Finset (Fin 7))) = _
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

theorem sevenHighT3TripleSet_member_card
    (index : Nat) (hindex : index < 3)
    {T : Finset (Fin 7)} (hT : T ∈ sevenHighT3TripleSet index) :
    T.card = 3 := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t3_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x y z : Fin 49)
    (hcanon : ({sevenHighLabeledSupport G e x,
      sevenHighLabeledSupport G e y,
      sevenHighLabeledSupport G e z} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 →
        q = x ∨ q = y ∨ q = z)
    (w : Fin 7) :
    ((G.neighborFinset (e.symm w).1).filter fun q =>
      (orderFortyNineHighSupport G q).card = 3).card =
      ((sevenHighT3TripleSet index).filter fun T => w ∈ T).card := by
  let s : Finset (Fin 49) := {x, y, z}
  let f : Fin 49 → Finset (Fin 7) := sevenHighLabeledSupport G e
  have hsMemberCard {q : Fin 49} (hq : q ∈ s) : (f q).card = 3 := by
    have hfmem : f q ∈ ({f x, f y, f z} : Finset (Finset (Fin 7))) := by
      simpa [s, f] using Finset.mem_image.mpr ⟨q, hq, rfl⟩
    rw [hcanon] at hfmem
    exact sevenHighT3TripleSet_member_card index hindex hfmem
  have hinj : Set.InjOn f ↑s := by
    intro a ha b hb hab
    have ha3 := hsMemberCard ha
    change (sevenHighLabeledSupport G e a).card = 3 at ha3
    exact sevenHighLabeledSupport_injective_of_two_le
      G hfree e (by omega) hab
  have hgraphSet : ((G.neighborFinset (e.symm w).1).filter fun q =>
      (orderFortyNineHighSupport G q).card = 3) =
      s.filter fun q => w ∈ f q := by
    ext q
    constructor
    · intro hq
      have hq3 : (f q).card = 3 := by
        change (sevenHighLabeledSupport G e q).card = 3
        rw [sevenHighLabeledSupport_card]
        exact (Finset.mem_filter.mp hq).2
      have hqw : w ∈ f q := by
        apply (mem_sevenHighLabeledSupport_iff G e q w).mpr
        simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (Finset.mem_filter.mp hq).1
      have hqs : q ∈ s := by
        rcases huniq q hq3 with rfl | rfl | rfl <;> simp [s]
      exact Finset.mem_filter.mpr ⟨hqs, hqw⟩
    · intro hq
      have hqs := (Finset.mem_filter.mp hq).1
      have hqw := (Finset.mem_filter.mp hq).2
      apply Finset.mem_filter.mpr
      constructor
      · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_sevenHighLabeledSupport_iff G e q w).mp hqw
      · rw [← sevenHighLabeledSupport_card G e q]
        exact hsMemberCard hqs
  rw [hgraphSet]
  have hmap : s.image f = sevenHighT3TripleSet index := by
    simpa [s, f] using hcanon
  have hfilterImage :
      (s.image f).filter (fun T => w ∈ T) =
        (s.filter fun q => w ∈ f q).image f := by
    exact Finset.filter_image
  rw [← hmap, hfilterImage]
  symm
  exact Finset.card_image_iff.mpr (hinj.mono (Finset.filter_subset _ _))

theorem sevenHigh_t3_singleton_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x y z : Fin 49)
    (hcanon : ({sevenHighLabeledSupport G e x,
      sevenHighLabeledSupport G e y,
      sevenHighLabeledSupport G e z} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 →
        q = x ∨ q = y ∨ q = z)
    (w : Fin 7) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = {w}} =
      ((sevenHighT3TripleSet index).filter fun T => w ∈ T).card + 2 := by
  rw [sevenHigh_singleton_fiber_card_eq_local G e w]
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
      (Finset.mem_filter.mp (e.symm w).2).2
  dsimp only at hp
  rw [sevenHigh_t3_local_triple_card G hfree index hindex e x y z
    hcanon huniq w] at hp
  omega

theorem sevenHigh_t3_exists_triple_superset_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x y z : Fin 49)
    (hcanon : ({sevenHighLabeledSupport G e x,
      sevenHighLabeledSupport G e y,
      sevenHighLabeledSupport G e z} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 →
        q = x ∨ q = y ∨ q = z)
    (P : Finset (Fin 7)) :
    (∃ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 ∧
      P ⊆ sevenHighLabeledSupport G e q) ↔
      ∃ T ∈ sevenHighT3TripleSet index, P ⊆ T := by
  constructor
  · rintro ⟨q, hq3, hPq⟩
    refine ⟨sevenHighLabeledSupport G e q, ?_, hPq⟩
    rw [← hcanon]
    rcases huniq q hq3 with rfl | rfl | rfl <;> simp
  · rintro ⟨T, hT, hPT⟩
    have hTrep := hT
    rw [← hcanon] at hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with hT | hT | hT
    · refine ⟨x, ?_, by simpa [hT] using hPT⟩
      rw [← hT]
      exact sevenHighT3TripleSet_member_card index hindex hTrep
    · refine ⟨y, ?_, by simpa [hT] using hPT⟩
      rw [← hT]
      exact sevenHighT3TripleSet_member_card index hindex hTrep
    · refine ⟨z, ?_, by simpa [hT] using hPT⟩
      rw [← hT]
      exact sevenHighT3TripleSet_member_card index hindex hTrep

theorem sevenHigh_t3_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x y z : Fin 49)
    (hcanon : ({sevenHighLabeledSupport G e x,
      sevenHighLabeledSupport G e y,
      sevenHighLabeledSupport G e z} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 →
        q = x ∨ q = y ∨ q = z)
    (S : Finset (Fin 7)) (hS3 : S.card = 3) :
    Fintype.card {q : Fin 49 // sevenHighLabeledSupport G e q = S} =
      if S ∈ sevenHighT3TripleSet index then 1 else 0 := by
  by_cases hmem : S ∈ sevenHighT3TripleSet index
  · rw [if_pos hmem]
    rw [← hcanon] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hS | hS | hS
    · have hone := sevenHighLabeledSupport_fiber_card_eq_one
        G hfree e x (by rw [← hS]; omega)
      simpa [hS] using hone
    · have hone := sevenHighLabeledSupport_fiber_card_eq_one
        G hfree e y (by rw [← hS]; omega)
      simpa [hS] using hone
    · have hone := sevenHighLabeledSupport_fiber_card_eq_one
        G hfree e z (by rw [← hS]; omega)
      simpa [hS] using hone
  · rw [if_neg hmem, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqEq := (Finset.mem_filter.mp hq).2
    have hq3 : (sevenHighLabeledSupport G e q).card = 3 := by
      rw [hqEq]
      exact hS3
    apply hmem
    rw [← hcanon]
    rcases huniq q hq3 with rfl | rfl | rfl <;> simp [hqEq]

def sevenHighT3KeyMultiplicity
    (index : Nat) (key : Option (Fin 7) × Finset (Fin 7)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 4
      else if key.2.card = 1 then
        ((sevenHighT3TripleSet index).filter fun T => key.2 ⊆ T).card + 2
      else if key.2.card = 2 then
        if ∃ T ∈ sevenHighT3TripleSet index, key.2 ⊆ T then 0 else 1
      else if key.2 ∈ sevenHighT3TripleSet index then 1 else 0

theorem sevenHigh_t3_mask_key_fiber_card
    (index : Nat) (hindex : index < 3)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {i : Fin 49 //
      sevenHighMaskAlignedKey
        (OrderFortyNineSevenHighCensus.representativeMasks 3 index) i = key} =
      sevenHighT3KeyMultiplicity index key := by
  interval_cases index <;> native_decide +revert

theorem sevenHigh_t3_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x y z : Fin 49)
    (hcanon : ({sevenHighLabeledSupport G e x,
      sevenHighLabeledSupport G e y,
      sevenHighLabeledSupport G e z} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 →
        q = x ∨ q = y ∨ q = z)
    (S : Finset (Fin 7))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2)
    (hcanonical : S ∉ sevenHighT3TripleSet index) :
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
  have hq3 : (sevenHighLabeledSupport G e q).card = 3 := by
    rw [hsupp]
    exact hS3
  apply hcanonical
  rw [← hcanon]
  rcases huniq q hq3 with rfl | rfl | rfl <;> simp [hsupp]

theorem sevenHigh_t3_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hthree : orderFortyNineHighIncidenceCount G 3 = 3)
    (index : Nat) (hindex : index < 3)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x y z : Fin 49)
    (hcanon : ({sevenHighLabeledSupport G e x,
      sevenHighLabeledSupport G e y,
      sevenHighLabeledSupport G e z} : Finset (Finset (Fin 7))) =
        sevenHighT3TripleSet index)
    (huniq : ∀ q : Fin 49,
      (sevenHighLabeledSupport G e q).card = 3 →
        q = x ∨ q = y ∨ q = z)
    (key : Option (Fin 7) × Finset (Fin 7)) :
    Fintype.card {q : Fin 49 // sevenHighGraphAlignedKey G e q = key} =
      sevenHighT3KeyMultiplicity index key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [sevenHighT3KeyMultiplicity] using
          sevenHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [sevenHighT3KeyMultiplicity, hS0] using
          sevenHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        have hp := orderFortyNine_highIncidence_profile_of_seven_high
          G hfree hmin (Fintype.card_fin 49) hHigh
        dsimp only at hp
        have hn0 : orderFortyNineHighIncidenceCount G 0 = 4 := by omega
        simpa [sevenHighT3KeyMultiplicity, hn0] using
          sevenHigh_aligned_emptyLow_fiber_card G e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
            (by simp)]
          rw [sevenHigh_t3_singleton_fiber_card G hfree hmin hHigh
            index hindex e x y z hcanon huniq w]
          simp only [sevenHighT3KeyMultiplicity, Finset.card_singleton,
            ↓reduceIte]
          congr 2
          ext T
          simp
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
              (by simp)]
            rw [sevenHigh_pair_fiber_card G hfree hmin e a b hab]
            have hiff := sevenHigh_t3_exists_triple_superset_iff
              G index hindex e x y z hcanon huniq {a, b}
            by_cases hex : ∃ q : Fin 49,
                (sevenHighLabeledSupport G e q).card = 3 ∧
                ({a, b} : Finset (Fin 7)) ⊆ sevenHighLabeledSupport G e q
            · have hrep := hiff.mp hex
              simp [sevenHighT3KeyMultiplicity, hab, hex, hrep]
            · have hrep := (not_congr hiff).mp hex
              simp [sevenHighT3KeyMultiplicity, hab, hex, hrep]
          · by_cases hcanonical : S ∈ sevenHighT3TripleSet index
            · have hS3 := sevenHighT3TripleSet_member_card
                index hindex hcanonical
              rw [sevenHigh_nonempty_alignedLowFiber_card G hfree hmin e S
                (Finset.card_pos.mp (by omega))]
              rw [sevenHigh_t3_triple_fiber_card G hfree index hindex e x y z
                hcanon huniq S hS3]
              simp [sevenHighT3KeyMultiplicity, h0, h1, h2, hcanonical]
            · simpa [sevenHighT3KeyMultiplicity, h0, h1, h2, hcanonical] using
                sevenHigh_t3_alignedLow_other_fiber_card_eq_zero
                  G hfree hmin index hindex e x y z hcanon huniq
                    S h0 h1 h2 hcanonical

theorem sevenHighCanonicalFiberCover_three :
    SevenHighCanonicalFiberCover 3 := by
  intro G _ _ _ hfree hmin hHigh hthree
  obtain ⟨index, hindex, e, x, y, z, hcanon, hxy, hxz, hyz, huniq⟩ :=
    sevenHigh_t3_exists_normalized_labeling
      G hfree hmin hHigh hthree
  refine ⟨index, by
    interval_cases index <;> native_decide, e, by
    interval_cases index <;> native_decide, ?_⟩
  intro key
  rw [sevenHigh_t3_graph_key_fiber_card G hfree hmin hHigh hthree
      index hindex e x y z hcanon huniq key,
    sevenHigh_t3_mask_key_fiber_card index hindex key]

theorem sevenHighCanonicalGraphCover_three :
    SevenHighCanonicalGraphCover 3 :=
  sevenHighCanonicalGraphCover_of_labelingCover
    (sevenHighCanonicalLabelingCover_of_fiberCover
      sevenHighCanonicalFiberCover_three)

end

end Erdos85
