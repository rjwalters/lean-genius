import Proofs.Erdos85OrderFortyNineFiveHighFiberLabeling

/-!
# Canonical normalization of five-high triple supports

There are at most two low vertices with three high neighbors.  With five high
points, two distinct linear triples cannot be disjoint, so the three possible
systems normalize uniquely to `∅`, `{012}`, and `{012, 034}`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem exists_perm5_send_to_initialSegment {n : Nat} (hn : n ≤ 5)
    (f : Fin n → Fin 5) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i, σ (f i) = Fin.castLE hn i := by
  exact Equiv.Perm.exists_extending_pair f (Fin.castLE hn) hf
    (Fin.castLE_injective hn)

theorem exists_perm5_normalizing_threeFinset
    (A : Finset (Fin 5)) (hA : A.card = 3) :
    ∃ σ : Equiv.Perm (Fin 5), A.map σ.toEmbedding = {0, 1, 2} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA
  have hinj : Function.Injective ![a, b, c] := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  obtain ⟨σ, hσ⟩ := exists_perm5_send_to_initialSegment
    (by omega) ![a, b, c] hinj
  have h0 := hσ (0 : Fin 3)
  have h1 := hσ (1 : Fin 3)
  have h2 := hσ (2 : Fin 3)
  refine ⟨σ, ?_⟩
  ext x
  fin_cases x <;> simp_all

set_option maxHeartbeats 1000000 in
theorem exists_perm5_normalizing_intersecting_threeFinsets
    (A B : Finset (Fin 5)) (hA : A.card = 3) (hB : B.card = 3)
    (hinter : (A ∩ B).card = 1) :
    ∃ σ : Equiv.Perm (Fin 5),
      A.map σ.toEmbedding = {0, 1, 2} ∧
      B.map σ.toEmbedding = {0, 3, 4} := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hinter
  have hxI : x ∈ A ∩ B := by rw [hx]; simp
  have hxA : x ∈ A := (Finset.mem_inter.mp hxI).1
  have hxB : x ∈ B := (Finset.mem_inter.mp hxI).2
  have hAsub : ({x} : Finset (Fin 5)) ⊆ A := by simpa
  have hBsub : ({x} : Finset (Fin 5)) ⊆ B := by simpa
  have hAdiff : (A \ {x}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hAsub, hA]
    simp
  have hBdiff : (B \ {x}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hBsub, hB]
    simp
  obtain ⟨a, b, hab, hArest⟩ := Finset.card_eq_two.mp hAdiff
  obtain ⟨d, e, hde, hBrest⟩ := Finset.card_eq_two.mp hBdiff
  have hAform : A = {x, a, b} := by
    rw [← Finset.sdiff_union_of_subset hAsub, hArest]
    ext y
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hBform : B = {x, d, e} := by
    rw [← Finset.sdiff_union_of_subset hBsub, hBrest]
    ext y
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have haRest : a ∈ A \ {x} := by rw [hArest]; simp
  have hbRest : b ∈ A \ {x} := by rw [hArest]; simp
  have hdRest : d ∈ B \ {x} := by rw [hBrest]; simp
  have heRest : e ∈ B \ {x} := by rw [hBrest]; simp
  have hcross {y z : Fin 5} (hy : y ∈ A \ {x}) (hz : z ∈ B \ {x}) :
      y ≠ z := by
    intro hyz
    have hyI : y ∈ A ∩ B := Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hy).1, hyz ▸ (Finset.mem_sdiff.mp hz).1⟩
    have hyx : y = x := by simpa [hx] using hyI
    exact (Finset.mem_sdiff.mp hy).2 (by simpa [hyx])
  have hinj : Function.Injective ![x, a, b, d, e] := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;>
      aesop
  obtain ⟨σ, hσ⟩ := exists_perm5_send_to_initialSegment
    (by omega) ![x, a, b, d, e] hinj
  have h0 := hσ (0 : Fin 5)
  have h1 := hσ (1 : Fin 5)
  have h2 := hσ (2 : Fin 5)
  have h3 := hσ (3 : Fin 5)
  have h4 := hσ (4 : Fin 5)
  refine ⟨σ, ?_, ?_⟩
  · rw [hAform]
    ext y
    fin_cases y <;> simp_all
  · rw [hBform]
    ext y
    fin_cases y <;> simp_all

theorem fiveHigh_two_triples_inter_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    {x y : Fin 49} (hx3 : (fiveHighLabeledSupport G e x).card = 3)
    (hy3 : (fiveHighLabeledSupport G e y).card = 3) (hxy : x ≠ y) :
    (fiveHighLabeledSupport G e x ∩
      fiveHighLabeledSupport G e y).card = 1 := by
  have hle := orderFortyNine_card_inter_highSupport_le_one G hfree hxy
  rw [← fiveHighLabeledSupport_inter_card G e x y] at hle
  have hne : (fiveHighLabeledSupport G e x ∩
      fiveHighLabeledSupport G e y).card ≠ 0 := by
    intro hz
    have hdisj : Disjoint (fiveHighLabeledSupport G e x)
        (fiveHighLabeledSupport G e y) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hx3, hy3] at hu
    have hsub : fiveHighLabeledSupport G e x ∪
        fiveHighLabeledSupport G e y ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  omega

theorem fiveHigh_exists_triple_vertices
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    {t : Nat} (ht : orderFortyNineHighIncidenceCount G 3 = t) :
    ((t = 1 → ∃! x : Fin 49,
        x ∈ orderFortyNineLowVertices G ∧
        (orderFortyNineHighSupport G x).card = 3) ∧
     (t = 2 → ∃ x y : Fin 49, x ≠ y ∧
        x ∈ orderFortyNineLowVertices G ∧
        (orderFortyNineHighSupport G x).card = 3 ∧
        y ∈ orderFortyNineLowVertices G ∧
        (orderFortyNineHighSupport G y).card = 3 ∧
        ∀ z : Fin 49, z ∈ orderFortyNineLowVertices G →
          (orderFortyNineHighSupport G z).card = 3 → z = x ∨ z = y)) := by
  let T := (orderFortyNineLowVertices G).filter fun z =>
    (orderFortyNineHighSupport G z).card = 3
  constructor
  · intro ht1
    have hT : T.card = 1 := by
      change orderFortyNineHighIncidenceCount G 3 = 1
      exact ht1 ▸ ht
    obtain ⟨x, hTx⟩ := Finset.card_eq_one.mp hT
    have hx := Finset.mem_filter.mp (by simp [T, hTx] : x ∈ T)
    refine ⟨x, hx, ?_⟩
    intro y hy
    have hyT : y ∈ T := Finset.mem_filter.mpr hy
    simpa [hTx] using hyT
  · intro ht2
    have hT : T.card = 2 := by
      change orderFortyNineHighIncidenceCount G 3 = 2
      exact ht2 ▸ ht
    obtain ⟨x, y, hxy, hTset⟩ := Finset.card_eq_two.mp hT
    have hx := Finset.mem_filter.mp (by simp [T, hTset] : x ∈ T)
    have hy := Finset.mem_filter.mp (by simp [T, hTset] : y ∈ T)
    refine ⟨x, y, hxy, hx.1, hx.2, hy.1, hy.2, ?_⟩
    intro z hzLow hz3
    have hzT : z ∈ T := Finset.mem_filter.mpr ⟨hzLow, hz3⟩
    simpa [T, hTset] using hzT

theorem fiveHigh_t1_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5,
      ∃ x : Fin 49,
        fiveHighLabeledSupport G e x = {0, 1, 2} ∧
        ∀ z : Fin 49, (fiveHighLabeledSupport G e z).card = 3 → z = x := by
  obtain ⟨x, hx, huniq⟩ :=
    (fiveHigh_exists_triple_vertices G hone).1 rfl
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  let A := fiveHighLabeledSupport G e0 x
  have hA : A.card = 3 := by
    change (fiveHighLabeledSupport G e0 x).card = 3
    rw [fiveHighLabeledSupport_card]
    exact hx.2
  obtain ⟨σ, hAσ⟩ := exists_perm5_normalizing_threeFinset A hA
  let e := e0.trans σ
  have heSupport (z : Fin 49) : fiveHighLabeledSupport G e z =
      (fiveHighLabeledSupport G e0 z).map σ.toEmbedding := by
    simp [fiveHighLabeledSupport, e, Finset.map_map]
  refine ⟨e, x, ?_, ?_⟩
  · rw [heSupport]
    exact hAσ
  · intro z hz3
    have hzOrig3 : (orderFortyNineHighSupport G z).card = 3 := by
      rw [← fiveHighLabeledSupport_card G e z]
      exact hz3
    have hzLow : z ∈ orderFortyNineLowVertices G := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ z, ?_⟩
      intro hzHigh
      have hz0 := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hzHigh
      change (orderFortyNineHighSupport G z).card = 0 at hz0
      omega
    exact huniq z ⟨hzLow, hzOrig3⟩

theorem fiveHigh_t2_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (htwo : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5,
      ∃ x y : Fin 49,
        fiveHighLabeledSupport G e x = {0, 1, 2} ∧
        fiveHighLabeledSupport G e y = {0, 3, 4} ∧
        x ≠ y ∧
        ∀ z : Fin 49, (fiveHighLabeledSupport G e z).card = 3 →
          z = x ∨ z = y := by
  obtain ⟨x, y, hxy, hxLow, hx3, hyLow, hy3, huniq⟩ :=
    (fiveHigh_exists_triple_vertices G htwo).2 rfl
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  let A := fiveHighLabeledSupport G e0 x
  let B := fiveHighLabeledSupport G e0 y
  have hA : A.card = 3 := by
    change (fiveHighLabeledSupport G e0 x).card = 3
    rw [fiveHighLabeledSupport_card]
    exact hx3
  have hB : B.card = 3 := by
    change (fiveHighLabeledSupport G e0 y).card = 3
    rw [fiveHighLabeledSupport_card]
    exact hy3
  have hinter : (A ∩ B).card = 1 := by
    exact fiveHigh_two_triples_inter_card_eq_one G hfree e0 hA hB hxy
  obtain ⟨σ, hAσ, hBσ⟩ :=
    exists_perm5_normalizing_intersecting_threeFinsets A B hA hB hinter
  let e := e0.trans σ
  have heSupport (z : Fin 49) : fiveHighLabeledSupport G e z =
      (fiveHighLabeledSupport G e0 z).map σ.toEmbedding := by
    simp [fiveHighLabeledSupport, e, Finset.map_map]
  refine ⟨e, x, y, ?_, ?_, hxy, ?_⟩
  · rw [heSupport]
    exact hAσ
  · rw [heSupport]
    exact hBσ
  · intro z hz3
    have hzOrig3 : (orderFortyNineHighSupport G z).card = 3 := by
      rw [← fiveHighLabeledSupport_card G e z]
      exact hz3
    have hzLow : z ∈ orderFortyNineLowVertices G := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ z, ?_⟩
      intro hzHigh
      have hz0 := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hzHigh
      change (orderFortyNineHighSupport G z).card = 0 at hz0
      omega
    exact huniq z hzLow hzOrig3

end

end Erdos85
