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

end

end Erdos85
