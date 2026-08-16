import Proofs.Erdos85OrderFortyNineFiveHighOneFiber

/-!
# Fiber census for the two-block five-high triple system

Two linear triples on five points cannot be disjoint, so linearity forces
them to meet once.  They normalize to the unique representative `012,034`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem exists_perm5_send_to_initialSegment {n : Nat} (hn : n ≤ 5)
    (f : Fin n → Fin 5) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i, σ (f i) = Fin.castLE hn i := by
  exact Equiv.Perm.exists_extending_pair f (Fin.castLE hn) hf
    (Fin.castLE_injective hn)

theorem exists_perm5_normalizing_disjoint_triples
    (a b c d e f : Fin 5)
    (hinj : Function.Injective ![a, b, c, d, e, f]) :
    ∃ σ : Equiv.Perm (Fin 5),
      ({σ a, σ b, σ c} : Finset (Fin 5)) = {0, 1, 2} ∧
      ({σ d, σ e, σ f} : Finset (Fin 5)) = {0, 3, 4} := by
  have hcard := Fintype.card_le_of_injective ![a, b, c, d, e, f] hinj
  simp at hcard

theorem exists_perm5_normalizing_intersecting_triples
    (x a b d e : Fin 5)
    (hinj : Function.Injective ![x, a, b, d, e]) :
    ∃ σ : Equiv.Perm (Fin 5),
      ({σ x, σ a, σ b} : Finset (Fin 5)) = {0, 1, 2} ∧
      ({σ x, σ d, σ e} : Finset (Fin 5)) = {0, 3, 4} := by
  obtain ⟨σ, hσ⟩ := exists_perm5_send_to_initialSegment
    (by omega) ![x, a, b, d, e] hinj
  have h0 := hσ (0 : Fin 5)
  have h1 := hσ (1 : Fin 5)
  have h2 := hσ (2 : Fin 5)
  have h3 := hσ (3 : Fin 5)
  have h4 := hσ (4 : Fin 5)
  refine ⟨σ, ?_, ?_⟩ <;> ext y <;> fin_cases y <;> simp_all

set_option maxHeartbeats 1000000 in
theorem exists_perm5_normalizing_two_threeFinsets
    (A B : Finset (Fin 5)) (hA : A.card = 3) (hB : B.card = 3)
    (hlin : (A ∩ B).card ≤ 1) :
    ∃ σ : Equiv.Perm (Fin 5),
      A.map σ.toEmbedding = {0, 1, 2} ∧
      (B.map σ.toEmbedding = {0, 3, 4} ∨
       B.map σ.toEmbedding = {0, 3, 4}) := by
  have hcases : (A ∩ B).card = 0 ∨ (A ∩ B).card = 1 := by omega
  rcases hcases with hzero | hone
  · have hinter : A ∩ B = ∅ := Finset.card_eq_zero.mp hzero
    have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hinter
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA
    obtain ⟨d, e, f, hde, hdf, hef, rfl⟩ := Finset.card_eq_three.mp hB
    simp only [Finset.disjoint_insert_left, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hdisj
    have hinj : Function.Injective ![a, b, c, d, e, f] := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;> aesop
    obtain ⟨σ, hfirst, hsecond⟩ :=
      exists_perm5_normalizing_disjoint_triples a b c d e f hinj
    refine ⟨σ, ?_, Or.inl ?_⟩
    · simpa using hfirst
    · simpa using hsecond
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
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
    have had := hcross haRest hdRest
    have hae := hcross haRest heRest
    have hbd := hcross hbRest hdRest
    have hbe := hcross hbRest heRest
    have hinj : Function.Injective ![x, a, b, d, e] := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;> aesop
    obtain ⟨σ, hfirst, hsecond⟩ :=
      exists_perm5_normalizing_intersecting_triples x a b d e hinj
    refine ⟨σ, ?_, Or.inr ?_⟩
    · rw [hAform]
      simpa using hfirst
    · rw [hBform]
      simpa using hsecond

theorem fiveHigh_t2_exists_two_triple_supports
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (htwo : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ x y : Fin 49, x ≠ y ∧
      x ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G x).card = 3 ∧
      y ∈ orderFortyNineLowVertices G ∧
      (orderFortyNineHighSupport G y).card = 3 ∧
      ∀ z : Fin 49,
        z ∈ orderFortyNineLowVertices G →
        (orderFortyNineHighSupport G z).card = 3 → z = x ∨ z = y := by
  let T := (orderFortyNineLowVertices G).filter fun z =>
    (orderFortyNineHighSupport G z).card = 3
  have hT : T.card = 2 := by exact htwo
  obtain ⟨x, y, hxy, hTset⟩ := Finset.card_eq_two.mp hT
  have hx := Finset.mem_filter.mp (by simp [T, hTset] : x ∈ T)
  have hy := Finset.mem_filter.mp (by simp [T, hTset] : y ∈ T)
  refine ⟨x, y, hxy, hx.1, hx.2, hy.1, hy.2, ?_⟩
  intro z hzLow hz3
  have hzT : z ∈ T := Finset.mem_filter.mpr ⟨hzLow, hz3⟩
  simpa [T, hTset] using hzT

theorem fiveHigh_t2_exists_normalized_labeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (htwo : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ index : Nat, index < 2 ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5,
      ∃ x y : Fin 49,
        smallHighLabeledSupport G e x = {0, 1, 2} ∧
        smallHighLabeledSupport G e y =
          (if index = 0 then {0, 3, 4} else {0, 3, 4}) ∧
        x ≠ y ∧
        ∀ z : Fin 49, (smallHighLabeledSupport G e z).card = 3 →
          z = x ∨ z = y := by
  obtain ⟨x, y, hxy, hxLow, hx3, hyLow, hy3, huniq⟩ :=
    fiveHigh_t2_exists_two_triple_supports G htwo
  let e0 : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by simpa using hHigh)
  let A := smallHighLabeledSupport G e0 x
  let B := smallHighLabeledSupport G e0 y
  have hA : A.card = 3 := by
    change (smallHighLabeledSupport G e0 x).card = 3
    rw [smallHighLabeledSupport_card]
    exact hx3
  have hB : B.card = 3 := by
    change (smallHighLabeledSupport G e0 y).card = 3
    rw [smallHighLabeledSupport_card]
    exact hy3
  have hlin : (A ∩ B).card ≤ 1 := by
    change (smallHighLabeledSupport G e0 x ∩
      smallHighLabeledSupport G e0 y).card ≤ 1
    rw [smallHighLabeledSupport_inter_card]
    exact orderFortyNine_card_inter_highSupport_le_one G hfree hxy
  obtain ⟨σ, hAσ, hBσ⟩ :=
    exists_perm5_normalizing_two_threeFinsets A B hA hB hlin
  let e := e0.trans σ
  have heSupport (z : Fin 49) : smallHighLabeledSupport G e z =
      (smallHighLabeledSupport G e0 z).map σ.toEmbedding := by
    simp [smallHighLabeledSupport, e, Finset.map_map]
  have hxNorm : smallHighLabeledSupport G e x = {0, 1, 2} := by
    rw [heSupport]
    change A.map σ.toEmbedding = {0, 1, 2}
    exact hAσ
  have htripleUnique : ∀ z : Fin 49,
      (smallHighLabeledSupport G e z).card = 3 → z = x ∨ z = y := by
    intro z hz3
    have hzOrig3 : (orderFortyNineHighSupport G z).card = 3 := by
      rw [← smallHighLabeledSupport_card G e z]
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
  rcases hBσ with hdisjoint | hintersecting
  · refine ⟨1, by omega, e, x, y, hxNorm, ?_, hxy, htripleUnique⟩
    change smallHighLabeledSupport G e y = {0, 3, 4}
    rw [heSupport]
    change B.map σ.toEmbedding = {0, 3, 4}
    exact hdisjoint
  · refine ⟨0, by omega, e, x, y, hxNorm, ?_, hxy, htripleUnique⟩
    change smallHighLabeledSupport G e y = {0, 3, 4}
    rw [heSupport]
    change B.map σ.toEmbedding = {0, 3, 4}
    exact hintersecting

def fiveHighT2TripleSet (index : Nat) : Finset (Finset (Fin 5)) :=
  if index = 0 then
    {{0, 1, 2}, {0, 3, 4}}
  else
    {{0, 1, 2}, {0, 3, 4}}

theorem fiveHigh_t2_local_triple_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : smallHighLabeledSupport G e y =
      (if index = 0 then {0, 3, 4} else {0, 3, 4}))
    (hxy : x ≠ y)
    (huniq : ∀ z : Fin 49,
      (smallHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (w : Fin 5) :
    ((G.neighborFinset (e.symm w).1).filter fun z =>
      (orderFortyNineHighSupport G z).card = 3).card =
      ((fiveHighT2TripleSet index).filter fun T => w ∈ T).card := by
  have hset : ((G.neighborFinset (e.symm w).1).filter fun z =>
      (orderFortyNineHighSupport G z).card = 3) =
      ({x, y} : Finset (Fin 49)).filter fun z =>
        w ∈ smallHighLabeledSupport G e z := by
    ext z
    constructor
    · intro hz
      have hz3 : (smallHighLabeledSupport G e z).card = 3 := by
        rw [smallHighLabeledSupport_card]
        exact (Finset.mem_filter.mp hz).2
      have hzw : w ∈ smallHighLabeledSupport G e z :=
        (mem_smallHighLabeledSupport_iff G e z w).mpr (by
          simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
            (Finset.mem_filter.mp hz).1)
      exact Finset.mem_filter.mpr ⟨by simpa using huniq z hz3, hzw⟩
    · intro hz
      have hzxy := (Finset.mem_filter.mp hz).1
      have hzw := (Finset.mem_filter.mp hz).2
      apply Finset.mem_filter.mpr
      constructor
      · simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (mem_smallHighLabeledSupport_iff G e z w).mp hzw
      · rcases (by simpa using hzxy : z = x ∨ z = y) with hzx | hzy
        · rw [hzx, ← smallHighLabeledSupport_card G e x, hxSupport]
          decide
        · rw [hzy, ← smallHighLabeledSupport_card G e y, hySupport]
          split <;> decide
  rw [hset]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  have hi : index = 0 ∨ index = 1 := by omega
  rcases hi with hi | hi
  · subst index
    simp at hySupport
    rw [hxSupport, hySupport]
    fin_cases w <;> simp [fiveHighT2TripleSet, hxy] <;> native_decide
  · subst index
    simp at hySupport
    rw [hxSupport, hySupport]
    fin_cases w <;> simp [fiveHighT2TripleSet, hxy] <;> native_decide

theorem fiveHigh_t2_singleton_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : smallHighLabeledSupport G e y =
      (if index = 0 then {0, 3, 4} else {0, 3, 4}))
    (hxy : x ≠ y)
    (huniq : ∀ z : Fin 49,
      (smallHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (w : Fin 5) :
    Fintype.card {z : Fin 49 // smallHighLabeledSupport G e z = {w}} =
      ((fiveHighT2TripleSet index).filter fun T => w ∈ T).card + 4 := by
  rw [fiveHigh_singleton_fiber_card_eq_local G e w]
  have hp := orderFortyNine_highNeighborhood_general_profile
    G hfree hmin (Fintype.card_fin 49)
      (Finset.mem_filter.mp (e.symm w).2).2
  dsimp only at hp
  rw [hHigh] at hp
  rw [fiveHigh_t2_local_triple_card G index hindex e x y
    hxSupport hySupport hxy huniq w] at hp
  omega

theorem fiveHigh_pair_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (a b : Fin 5) (hab : a ≠ b) :
    Fintype.card {z : Fin 49 // smallHighLabeledSupport G e z = {a, b}} =
      if ∃ q : Fin 49,
          (smallHighLabeledSupport G e q).card = 3 ∧
          ({a, b} : Finset (Fin 5)) ⊆ smallHighLabeledSupport G e q
        then 0 else 1 := by
  obtain ⟨z, hz, hzuniq⟩ :=
    fiveHigh_existsUnique_labeled_pairBlock G hfree hmin e hab
  by_cases htriple : ∃ q : Fin 49,
      (smallHighLabeledSupport G e q).card = 3 ∧
      ({a, b} : Finset (Fin 5)) ⊆ smallHighLabeledSupport G e q
  · rw [if_pos htriple, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have huEq := (Finset.mem_filter.mp hu).2
    have huQual : ({a, b} : Finset (Fin 5)) ⊆
        smallHighLabeledSupport G e u ∧
        ((smallHighLabeledSupport G e u).card = 2 ∨
         (smallHighLabeledSupport G e u).card = 3) := by
      refine ⟨by rw [huEq], Or.inl ?_⟩
      rw [huEq]
      simp [hab]
    obtain ⟨q, hq3, hqSub⟩ := htriple
    have hqQual : ({a, b} : Finset (Fin 5)) ⊆
        smallHighLabeledSupport G e q ∧
        ((smallHighLabeledSupport G e q).card = 2 ∨
         (smallHighLabeledSupport G e q).card = 3) :=
      ⟨hqSub, Or.inr hq3⟩
    have huq : u = q := (hzuniq u huQual).trans (hzuniq q hqQual).symm
    have := congrArg (fun v => (smallHighLabeledSupport G e v).card) huq
    rw [huEq] at this
    simp [hab] at this
    omega
  · rw [if_neg htriple]
    have hz2 : (smallHighLabeledSupport G e z).card = 2 := by
      rcases hz.2 with hz2 | hz3
      · exact hz2
      · exact False.elim (htriple ⟨z, hz3, hz.1⟩)
    have hzEq : smallHighLabeledSupport G e z = {a, b} :=
      (Finset.eq_of_subset_of_card_le hz.1 (by simp [hab, hz2])).symm
    have hone := smallHighLabeledSupport_fiber_card_eq_one
      G hfree e z (by omega)
    simpa [hzEq] using hone

theorem fiveHigh_t2_exists_triple_superset_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : smallHighLabeledSupport G e y =
      (if index = 0 then {0, 3, 4} else {0, 3, 4}))
    (huniq : ∀ z : Fin 49,
      (smallHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (P : Finset (Fin 5)) :
    (∃ q : Fin 49,
      (smallHighLabeledSupport G e q).card = 3 ∧
      P ⊆ smallHighLabeledSupport G e q) ↔
      ∃ T ∈ fiveHighT2TripleSet index, P ⊆ T := by
  have hi : index = 0 ∨ index = 1 := by omega
  rcases hi with hi | hi
  · subst index
    simp at hySupport
    constructor
    · rintro ⟨q, hq3, hPq⟩
      rcases huniq q hq3 with hqx | hqy
      · refine ⟨{0, 1, 2}, by simp [fiveHighT2TripleSet], ?_⟩
        simpa [hqx, hxSupport] using hPq
      · refine ⟨{0, 3, 4}, by simp [fiveHighT2TripleSet], ?_⟩
        simpa [hqy, hySupport] using hPq
    · rintro ⟨T, hT, hPT⟩
      have hcases : T = ({0, 1, 2} : Finset (Fin 5)) ∨
          T = ({0, 3, 4} : Finset (Fin 5)) := by
        simpa [fiveHighT2TripleSet] using hT
      rcases hcases with rfl | rfl
      · refine ⟨x, by rw [hxSupport]; decide, ?_⟩
        simpa [hxSupport] using hPT
      · refine ⟨y, by rw [hySupport]; decide, ?_⟩
        simpa [hySupport] using hPT
  · subst index
    simp at hySupport
    constructor
    · rintro ⟨q, hq3, hPq⟩
      rcases huniq q hq3 with hqx | hqy
      · refine ⟨{0, 1, 2}, by simp [fiveHighT2TripleSet], ?_⟩
        simpa [hqx, hxSupport] using hPq
      · refine ⟨{0, 3, 4}, by simp [fiveHighT2TripleSet], ?_⟩
        simpa [hqy, hySupport] using hPq
    · rintro ⟨T, hT, hPT⟩
      have hcases : T = ({0, 1, 2} : Finset (Fin 5)) ∨
          T = ({0, 3, 4} : Finset (Fin 5)) := by
        simpa [fiveHighT2TripleSet] using hT
      rcases hcases with rfl | rfl
      · refine ⟨x, by rw [hxSupport]; decide, ?_⟩
        simpa [hxSupport] using hPT
      · refine ⟨y, by rw [hySupport]; decide, ?_⟩
        simpa [hySupport] using hPT

theorem fiveHigh_t2_triple_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : smallHighLabeledSupport G e y =
      (if index = 0 then {0, 3, 4} else {0, 3, 4}))
    (huniq : ∀ z : Fin 49,
      (smallHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (S : Finset (Fin 5)) (hS3 : S.card = 3) :
    Fintype.card {z : Fin 49 // smallHighLabeledSupport G e z = S} =
      if S ∈ fiveHighT2TripleSet index then 1 else 0 := by
  by_cases hmem : S ∈ fiveHighT2TripleSet index
  · rw [if_pos hmem]
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with hi | hi
    · subst index
      simp [fiveHighT2TripleSet] at hmem hySupport
      rcases hmem with hS | hS
      · have hone := smallHighLabeledSupport_fiber_card_eq_one
          G hfree e x (by rw [hxSupport]; decide)
        simpa [hS, hxSupport] using hone
      · have hone := smallHighLabeledSupport_fiber_card_eq_one
          G hfree e y (by rw [hySupport]; decide)
        simpa [hS, hySupport] using hone
    · subst index
      simp [fiveHighT2TripleSet] at hmem hySupport
      rcases hmem with hS | hS
      · have hone := smallHighLabeledSupport_fiber_card_eq_one
          G hfree e x (by rw [hxSupport]; decide)
        simpa [hS, hxSupport] using hone
      · have hone := smallHighLabeledSupport_fiber_card_eq_one
          G hfree e y (by rw [hySupport]; decide)
        simpa [hS, hySupport] using hone
  · rw [if_neg hmem, Fintype.card_subtype, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzEq := (Finset.mem_filter.mp hz).2
    have hz3 : (smallHighLabeledSupport G e z).card = 3 := by
      rw [hzEq]
      exact hS3
    rcases huniq z hz3 with hzx | hzy
    · apply hmem
      have hi : index = 0 ∨ index = 1 := by omega
      rcases hi with hi | hi
      · subst index
        simp [fiveHighT2TripleSet, ← hzEq, hzx, hxSupport]
      · subst index
        simp [fiveHighT2TripleSet, ← hzEq, hzx, hxSupport]
    · apply hmem
      have hi : index = 0 ∨ index = 1 := by omega
      rcases hi with hi | hi
      · subst index
        simp at hySupport
        simp [fiveHighT2TripleSet, ← hzEq, hzy, hySupport]
      · subst index
        simp at hySupport
        simp [fiveHighT2TripleSet, ← hzEq, hzy, hySupport]

def fiveHighT2KeyMultiplicity
    (index : Nat) (key : Option (Fin 5) × Finset (Fin 5)) : Nat :=
  match key.1 with
  | some _ => if key.2 = ∅ then 1 else 0
  | none =>
      if key.2.card = 0 then 12
      else if key.2.card = 1 then
        ((fiveHighT2TripleSet index).filter fun T => key.2 ⊆ T).card + 4
      else if key.2.card = 2 then
        if ∃ T ∈ fiveHighT2TripleSet index, key.2 ⊆ T then 0 else 1
      else if key.2 ∈ fiveHighT2TripleSet index then 1 else 0

theorem fiveHigh_t2_mask_key_fiber_card
    (index : Nat) (hindex : index < 2)
    (key : Option (Fin 5) × Finset (Fin 5)) :
    Fintype.card {i : Fin 49 //
      smallHighMaskAlignedKey
        (OrderFortyNineSmallHighCensus.fiveHighRepresentativeMasks 2) i = key} =
      fiveHighT2KeyMultiplicity index key := by
  interval_cases index <;> native_decide +revert

theorem fiveHigh_t2_alignedLow_other_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : smallHighLabeledSupport G e y =
      (if index = 0 then {0, 3, 4} else {0, 3, 4}))
    (huniq : ∀ z : Fin 49,
      (smallHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (S : Finset (Fin 5))
    (h0 : S.card ≠ 0) (h1 : S.card ≠ 1) (h2 : S.card ≠ 2)
    (hcanonical : S ∉ fiveHighT2TripleSet index) :
    Fintype.card {z : Fin 49 //
      smallHighGraphAlignedKey G e z = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hkey := (Finset.mem_filter.mp hz).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : smallHighLabeledSupport G e z = S := by
    simpa [smallHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hzNotHigh : z ∉ orderFortyNineHighVertices G := by
    intro hzHigh
    simp [smallHighGraphAlignedKey, hzHigh] at hfirst
  have hz7 : G.degree z = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) z with hz7 | hz8
    · exact hz7
    · exact False.elim (hzNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, smallHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hz7
  have hS3 : S.card = 3 := by omega
  have hz3 : (smallHighLabeledSupport G e z).card = 3 := by
    rw [hsupp]
    exact hS3
  rcases huniq z hz3 with hzx | hzy
  · apply hcanonical
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with hi | hi
    · subst index
      simp [fiveHighT2TripleSet, ← hsupp, hzx, hxSupport]
    · subst index
      simp [fiveHighT2TripleSet, ← hsupp, hzx, hxSupport]
  · apply hcanonical
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with hi | hi
    · subst index
      simp at hySupport
      simp [fiveHighT2TripleSet, ← hsupp, hzy, hySupport]
    · subst index
      simp at hySupport
      simp [fiveHighT2TripleSet, ← hsupp, hzy, hySupport]

theorem fiveHigh_t2_graph_key_fiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 5)
    (htwo : orderFortyNineHighIncidenceCount G 3 = 2)
    (index : Nat) (hindex : index < 2)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (x y : Fin 49)
    (hxSupport : smallHighLabeledSupport G e x = {0, 1, 2})
    (hySupport : smallHighLabeledSupport G e y =
      (if index = 0 then {0, 3, 4} else {0, 3, 4}))
    (hxy : x ≠ y)
    (huniq : ∀ z : Fin 49,
      (smallHighLabeledSupport G e z).card = 3 → z = x ∨ z = y)
    (key : Option (Fin 5) × Finset (Fin 5)) :
    Fintype.card {z : Fin 49 // smallHighGraphAlignedKey G e z = key} =
      fiveHighT2KeyMultiplicity index key := by
  rcases key with ⟨label, S⟩
  cases label with
  | some w =>
      by_cases hS0 : S = ∅
      · subst S
        simpa [fiveHighT2KeyMultiplicity] using
          fiveHigh_alignedHigh_fiber_card_eq_one G hfree hmin e w
      · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0
        simpa [fiveHighT2KeyMultiplicity, hS0] using
          fiveHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
            G hfree hmin e w S hSne
  | none =>
      by_cases h0 : S.card = 0
      · have hS0 : S = ∅ := Finset.card_eq_zero.mp h0
        subst S
        have hp := orderFortyNine_highIncidence_profile_of_five_high
          G hfree hmin (Fintype.card_fin 49) hHigh
        dsimp only at hp
        have hn0 : orderFortyNineHighIncidenceCount G 0 = 12 := by omega
        simpa [fiveHighT2KeyMultiplicity, hn0] using
          fiveHigh_aligned_emptyLow_fiber_card G e
      · by_cases h1 : S.card = 1
        · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
          rw [fiveHigh_nonempty_alignedLowFiber_card G hfree hmin e {w}
            (by simp)]
          rw [fiveHigh_t2_singleton_fiber_card G hfree hmin hHigh
            index hindex e x y hxSupport hySupport hxy huniq w]
          simp only [fiveHighT2KeyMultiplicity, Finset.card_singleton,
            ↓reduceIte]
          congr 2
          ext T
          simp
        · by_cases h2 : S.card = 2
          · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
            rw [fiveHigh_nonempty_alignedLowFiber_card G hfree hmin e {a, b}
              (by simp)]
            rw [fiveHigh_pair_fiber_card G hfree hmin e a b hab]
            have hiff := fiveHigh_t2_exists_triple_superset_iff
              G index hindex e x y hxSupport hySupport huniq {a, b}
            by_cases hex : ∃ q : Fin 49,
                (smallHighLabeledSupport G e q).card = 3 ∧
                ({a, b} : Finset (Fin 5)) ⊆ smallHighLabeledSupport G e q
            · have hrep := hiff.mp hex
              simp [fiveHighT2KeyMultiplicity, hab, hex, hrep]
            · have hrep := (not_congr hiff).mp hex
              simp [fiveHighT2KeyMultiplicity, hab, hex, hrep]
          · by_cases hcanonical : S ∈ fiveHighT2TripleSet index
            · have hS3 : S.card = 3 := by
                have hi : index = 0 ∨ index = 1 := by omega
                rcases hi with hi | hi
                · subst index
                  simp [fiveHighT2TripleSet] at hcanonical
                  rcases hcanonical with rfl | rfl <;> decide
                · subst index
                  simp [fiveHighT2TripleSet] at hcanonical
                  rcases hcanonical with rfl | rfl <;> decide
              rw [fiveHigh_nonempty_alignedLowFiber_card G hfree hmin e S
                (Finset.card_pos.mp (by omega))]
              rw [fiveHigh_t2_triple_fiber_card G hfree index hindex e x y
                hxSupport hySupport huniq S hS3]
              simp [fiveHighT2KeyMultiplicity, h0, h1, h2, hcanonical]
            · simpa [fiveHighT2KeyMultiplicity, h0, h1, h2, hcanonical] using
                fiveHigh_t2_alignedLow_other_fiber_card_eq_zero
                  G hfree hmin index hindex e x y hxSupport hySupport huniq
                    S h0 h1 h2 hcanonical

theorem fiveHighCanonicalFiberCover_two :
    FiveHighCanonicalFiberCover 2 := by
  intro G _ _ _ hfree hmin hHigh htwo
  obtain ⟨index, hindex, e, x, y, hxSupport, hySupport, hxy, huniq⟩ :=
    fiveHigh_t2_exists_normalized_labeling
      G hfree hmin hHigh htwo
  refine ⟨e, by
    interval_cases index <;> native_decide, ?_⟩
  intro key
  rw [fiveHigh_t2_graph_key_fiber_card G hfree hmin hHigh htwo
      index hindex e x y hxSupport hySupport hxy huniq key,
    fiveHigh_t2_mask_key_fiber_card index hindex key]

theorem fiveHighCanonicalGraphCover_two :
    FiveHighCanonicalGraphCover 2 :=
  fiveHighCanonicalGraphCover_of_labelingCover
    (fiveHighCanonicalLabelingCover_of_fiberCover
      fiveHighCanonicalFiberCover_two)

theorem fiveHighCanonicalGraphCover_all
    (blocks : Nat) (hblocks : blocks ≤ 2) :
    FiveHighCanonicalGraphCover blocks := by
  interval_cases blocks
  · exact fiveHighCanonicalGraphCover_zero
  · exact fiveHighCanonicalGraphCover_one
  · exact fiveHighCanonicalGraphCover_two

theorem orderFortyNineStratumExcluded_five_of_representativeExclusions
    (hexcluded : ∀ index, index ≤ 2 →
      FiveHighCanonicalRepresentativeExcluded index) :
    OrderFortyNineStratumExcluded 5 :=
  orderFortyNineStratumExcluded_five_of_canonical
    fiveHighCanonicalGraphCover_all hexcluded

end

end Erdos85
