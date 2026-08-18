import Proofs.Erdos85OrderFortyNineCanonicalProfileFibers

/-!
# Full canonical labeling of the order-49, nine-high strata

This file closes the gap between canonicalizing only the triple system and
labeling all 49 vertices.  The proof compares every high-support fiber with
the independently generated canonical mask census.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

open OrderFortyNineWitnessTable

theorem array_mem_of_getElem?_eq_some
    {α : Type*} [DecidableEq α] {xs : Array α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  have hi : i < xs.size := by
    by_contra hnot
    rw [getElem?_neg xs i hnot] at h
    contradiction
  have hvalue : xs[i] = x := by
    rw [getElem?_pos xs i hi] at h
    exact Option.some.inj h
  rw [← hvalue]
  exact Array.getElem_mem hi

theorem orderFortyNine_card_labeledHighSupport_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (x : V) :
    (orderFortyNineLabeledHighSupport G e x).card ≤ 3 := by
  rw [card_orderFortyNineLabeledHighSupport]
  rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard x with
    hx7 | hx8
  · exact orderFortyNine_highNeighborCount_le_three G hfree hmin hcard hx7
  · have hxHigh : x ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hx8]
    have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin hcard hxHigh
    change (orderFortyNineHighSupport G x).card = 0 at hz
    omega

/-- In the nine-high stratum the number of empty low supports is `4-t`,
where `t` is the number of triple supports. -/
theorem orderFortyNine_emptyIncidenceCount_eq_four_sub_triples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9) :
    orderFortyNineHighIncidenceCount G 0 =
      4 - orderFortyNineHighIncidenceCount G 3 := by
  rcases orderFortyNine_highIncidence_profile_of_nine_high
      G hfree hmin hcard hHigh with h | h | h | h | h <;> omega

/-- A three-element support occurs in the graph exactly when its natural
image belongs to the selected representative triple set. -/
theorem OrderFortyNineCanonicalTripleSystemSpec.exists_support_iff_mem_rep
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (S : Finset (Fin 9)) (hS3 : S.card = 3) :
    (∃ x : V, orderFortyNineLabeledHighSupport G e x = S) ↔
      S.image Fin.val ∈ orderFortyNineRepresentativeTripleSet rep := by
  constructor
  · rintro ⟨x, hxS⟩
    have hxOrig3 : (orderFortyNineHighSupport G x).card = 3 := by
      rw [← card_orderFortyNineLabeledHighSupport G e x, hxS]
      exact hS3
    have hxLow : x ∈ orderFortyNineLowVertices G := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      intro hxHigh
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin hcard hxHigh
      change (orderFortyNineHighSupport G x).card = 0 at hz
      omega
    obtain ⟨T, hT, hEq⟩ := hcanon.1 x
      (Finset.mem_filter.mpr ⟨hxLow, hxOrig3⟩)
    apply Finset.mem_image.mpr
    exact ⟨T, List.mem_toFinset.mpr hT, by simpa [hxS] using hEq.symm⟩
  · intro hS
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hS
    obtain ⟨x, hx, hEq⟩ := hcanon.2 T (List.mem_toFinset.mp hT)
    refine ⟨x, ?_⟩
    apply Finset.image_injective Fin.val_injective
    exact hEq.trans hTS

/-- Pair containment by a graph triple is equivalent to containment by a
representative triple. -/
theorem OrderFortyNineCanonicalTripleSystemSpec.exists_triple_superset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (S : Finset (Fin 9)) :
    (∃ x : V,
      (orderFortyNineLabeledHighSupport G e x).card = 3 ∧
        S ⊆ orderFortyNineLabeledHighSupport G e x) ↔
      ∃ T ∈ orderFortyNineRepresentativeTripleSet rep,
        S.image Fin.val ⊆ T := by
  constructor
  · rintro ⟨x, hx3, hSx⟩
    have hxOrig3 : (orderFortyNineHighSupport G x).card = 3 := by
      rw [← card_orderFortyNineLabeledHighSupport G e x]
      exact hx3
    have hxLow : x ∈ orderFortyNineLowVertices G := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      intro hxHigh
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin hcard hxHigh
      change (orderFortyNineHighSupport G x).card = 0 at hz
      omega
    obtain ⟨L, hL, hEq⟩ := hcanon.1 x
      (Finset.mem_filter.mpr ⟨hxLow, hxOrig3⟩)
    refine ⟨L.toFinset, Finset.mem_image.mpr
      ⟨L, List.mem_toFinset.mpr hL, rfl⟩, ?_⟩
    rw [← hEq]
    exact Finset.image_mono Fin.val hSx
  · rintro ⟨T, hT, hST⟩
    obtain ⟨L, hL, hLT⟩ := Finset.mem_image.mp hT
    obtain ⟨x, hx, hEq⟩ := hcanon.2 L (List.mem_toFinset.mp hL)
    have hx3 : (orderFortyNineLabeledHighSupport G e x).card = 3 := by
      rw [card_orderFortyNineLabeledHighSupport]
      exact (Finset.mem_filter.mp hx).2
    refine ⟨x, hx3, ?_⟩
    intro w hw
    have hwNat : w.val ∈ S.image Fin.val :=
      Finset.mem_image.mpr ⟨w, hw, rfl⟩
    have : w.val ∈ (orderFortyNineLabeledHighSupport G e x).image Fin.val := by
      rw [hEq, hLT]
      exact hST hwNat
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp this
    exact Fin.ext huw ▸ hu

/-- Complete graph-side support census in the same structural vocabulary as
the generated canonical profile. -/
theorem OrderFortyNineCanonicalTripleSystemSpec.card_supportFiber_eq_multiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (t : Nat) (ht : t ≤ 4) (hlen : rep.length = t)
    (hn0 : orderFortyNineHighIncidenceCount G 0 = 4 - t)
    (S : Finset (Fin 9)) :
    Fintype.card {x : V // orderFortyNineLabeledHighSupport G e x = S} =
      orderFortyNineCanonicalSupportMultiplicity rep S := by
  rw [← card_orderFortyNineLabeledSupportFiber G e S]
  by_cases h0 : S.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp h0
    subst S
    rw [orderFortyNine_card_emptySupportFiber G hfree hmin hcard e]
    simp only [orderFortyNineCanonicalSupportMultiplicity, Finset.card_empty,
      if_pos]
    rw [hHigh, hn0, hlen]
    omega
  by_cases h1 : S.card = 1
  · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
    rw [orderFortyNine_card_singletonFiber_eq_tripleIncidence
      G hfree hmin hcard hHigh e w]
    rw [hcanon.card_tripleIncidence G hfree hmin hcard e rep w]
    simp [orderFortyNineCanonicalSupportMultiplicity]
  by_cases h2 : S.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    rw [orderFortyNine_card_pairFiber G hfree hmin hcard e hab]
    have hp := hcanon.exists_triple_superset_iff
      G hfree hmin hcard e rep ({a, b} : Finset (Fin 9))
    have himage : ({a, b} : Finset (Fin 9)).image Fin.val =
        ({a.val, b.val} : Finset Nat) := by
      ext n
      simp
    by_cases hg : ∃ x : V,
        (orderFortyNineLabeledHighSupport G e x).card = 3 ∧
          ({a, b} : Finset (Fin 9)) ⊆
            orderFortyNineLabeledHighSupport G e x
    · have hr := hp.mp hg
      have hr' : ∃ T ∈ orderFortyNineRepresentativeTripleSet rep,
          ({a.val, b.val} : Finset Nat) ⊆ T := by simpa [himage] using hr
      simp [orderFortyNineCanonicalSupportMultiplicity, hab, hg, hr']
    · have hr := (not_congr hp).mp hg
      have hr' : ¬ ∃ T ∈ orderFortyNineRepresentativeTripleSet rep,
          ({a.val, b.val} : Finset Nat) ⊆ T := by simpa [himage] using hr
      simp [orderFortyNineCanonicalSupportMultiplicity, hab, hg, hr']
  by_cases h3 : S.card = 3
  · have hiff := hcanon.exists_support_iff_mem_rep
      G hfree hmin hcard e rep S h3
    by_cases hex : ∃ x : V, orderFortyNineLabeledHighSupport G e x = S
    · have hmem := hiff.mp hex
      obtain ⟨x, hxS⟩ := hex
      have hx3 : (orderFortyNineLabeledHighSupport G e x).card = 3 := by
        rw [hxS]
        exact h3
      have hone := orderFortyNine_card_labeledHighSupportFiber_eq_one
        G hfree e x (by omega)
      rw [← card_orderFortyNineLabeledSupportFiber G e
        (orderFortyNineLabeledHighSupport G e x)] at hone
      rw [hxS] at hone
      rw [hone]
      simp [orderFortyNineCanonicalSupportMultiplicity, h0, h1, h2, h3,
        hmem]
    · have hempty : orderFortyNineLabeledSupportFiber G e S = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hne
        obtain ⟨x, hx⟩ := hne
        exact hex ⟨x, (Finset.mem_filter.mp hx).2⟩
      have hnotmem := (not_congr hiff).mp hex
      rw [hempty]
      simp [orderFortyNineCanonicalSupportMultiplicity, h0, h1, h2, h3,
        hnotmem]
  · have hempty : orderFortyNineLabeledSupportFiber G e S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      obtain ⟨x, hx⟩ := hne
      have hxS := (Finset.mem_filter.mp hx).2
      have hle := orderFortyNine_card_labeledHighSupport_le_three
        G hfree hmin hcard e x
      rw [hxS] at hle
      omega
    rw [hempty]
    simp [orderFortyNineCanonicalSupportMultiplicity, h0, h1, h2, h3]

/-- Graph-side key remembering both the degree-eight stratum and the labeled
high support. -/
def orderFortyNineGraphVertexKey
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (x : V) : Bool × Finset (Fin 9) :=
  (decide (x ∈ orderFortyNineHighVertices G),
    orderFortyNineLabeledHighSupport G e x)

/-- Complete high-stratum/support-key census on the graph side. -/
theorem OrderFortyNineCanonicalTripleSystemSpec.card_vertexKeyFiber_eq_multiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (t : Nat) (ht : t ≤ 4) (hlen : rep.length = t)
    (hn0 : orderFortyNineHighIncidenceCount G 0 = 4 - t)
    (key : Bool × Finset (Fin 9)) :
    Fintype.card {x : V // orderFortyNineGraphVertexKey G e x = key} =
      orderFortyNineCanonicalVertexKeyMultiplicity rep key := by
  rcases key with ⟨b, S⟩
  cases b with
  | false =>
      by_cases hS0 : S.card = 0
      · have hS : S = ∅ := Finset.card_eq_zero.mp hS0
        subst S
        rw [Fintype.card_subtype]
        have heq : (Finset.univ.filter fun x : V =>
            orderFortyNineGraphVertexKey G e x = (false, ∅)) =
            (orderFortyNineLowVertices G).filter fun x =>
              (orderFortyNineHighSupport G x).card = 0 := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hx
            have hxLow : x ∈ orderFortyNineLowVertices G := by
              apply Finset.mem_sdiff.mpr
              refine ⟨Finset.mem_univ x, ?_⟩
              simpa [orderFortyNineGraphVertexKey] using congrArg Prod.fst hx
            have hx0 : (orderFortyNineHighSupport G x).card = 0 := by
              apply (orderFortyNineLabeledHighSupport_eq_empty_iff G e x).mp
              simpa [orderFortyNineGraphVertexKey] using congrArg Prod.snd hx
            exact ⟨hxLow, hx0⟩
          · rintro ⟨hxLow, hx0⟩
            apply Prod.ext
            · simp [orderFortyNineGraphVertexKey,
                (Finset.mem_sdiff.mp hxLow).2]
            · exact (orderFortyNineLabeledHighSupport_eq_empty_iff G e x).mpr hx0
        rw [heq]
        change orderFortyNineHighIncidenceCount G 0 = _
        simp only [orderFortyNineCanonicalVertexKeyMultiplicity,
          Bool.false_eq_true, if_false, Finset.card_empty, if_pos]
        rw [hn0, hlen]
      · have heq : (Finset.univ.filter fun x : V =>
            orderFortyNineGraphVertexKey G e x = (false, S)) =
            orderFortyNineLabeledSupportFiber G e S := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hx
            simpa [orderFortyNineLabeledSupportFiber,
              orderFortyNineGraphVertexKey] using congrArg Prod.snd hx
          · intro hx
            have hxSupp := (Finset.mem_filter.mp hx).2
            apply Prod.ext
            · have hxNotHigh : x ∉ orderFortyNineHighVertices G := by
                intro hxHigh
                have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
                  G hfree hmin hcard hxHigh
                change (orderFortyNineHighSupport G x).card = 0 at hz
                have hcardEq := card_orderFortyNineLabeledHighSupport G e x
                rw [hxSupp] at hcardEq
                omega
              simp [orderFortyNineGraphVertexKey, hxNotHigh]
            · exact hxSupp
        rw [Fintype.card_subtype, heq,
          card_orderFortyNineLabeledSupportFiber,
          hcanon.card_supportFiber_eq_multiplicity
            G hfree hmin hcard hHigh e rep t ht hlen hn0 S]
        simp [orderFortyNineCanonicalVertexKeyMultiplicity, hS0]
  | true =>
      by_cases hS0 : S.card = 0
      · have hS : S = ∅ := Finset.card_eq_zero.mp hS0
        subst S
        rw [Fintype.card_subtype]
        have heq : (Finset.univ.filter fun x : V =>
            orderFortyNineGraphVertexKey G e x = (true, ∅)) =
            orderFortyNineHighVertices G := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hx
            simpa [orderFortyNineGraphVertexKey] using congrArg Prod.fst hx
          · intro hxHigh
            apply Prod.ext
            · simp [orderFortyNineGraphVertexKey, hxHigh]
            · apply (orderFortyNineLabeledHighSupport_eq_empty_iff G e x).mpr
              exact orderFortyNine_highNeighborCount_eq_zero_of_high
                G hfree hmin hcard hxHigh
        rw [heq, hHigh]
        simp [orderFortyNineCanonicalVertexKeyMultiplicity]
      · rw [Fintype.card_subtype]
        have heq : (Finset.univ.filter fun x : V =>
            orderFortyNineGraphVertexKey G e x = (true, S)) = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨x, hx⟩ := hne
          have hxEq := (Finset.mem_filter.mp hx).2
          have hxHigh : x ∈ orderFortyNineHighVertices G := by
            simpa [orderFortyNineGraphVertexKey] using congrArg Prod.fst hxEq
          have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
            G hfree hmin hcard hxHigh
          have hsupp : orderFortyNineLabeledHighSupport G e x = S := by
            simpa [orderFortyNineGraphVertexKey] using congrArg Prod.snd hxEq
          have hcardEq := card_orderFortyNineLabeledHighSupport G e x
          change (orderFortyNineHighSupport G x).card = 0 at hz
          rw [hsupp] at hcardEq
          omega
        rw [heq]
        simp [orderFortyNineCanonicalVertexKeyMultiplicity, hS0]

/-- Graph-side key with an exact label for every high vertex. -/
def orderFortyNineGraphAlignedVertexKey
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (x : V) : Option (Fin 9) × Finset (Fin 9) :=
  (if hx : x ∈ orderFortyNineHighVertices G then some (e ⟨x, hx⟩) else none,
    orderFortyNineLabeledHighSupport G e x)

/-- Exact-label refinement of the graph-side vertex-key census. -/
theorem OrderFortyNineCanonicalTripleSystemSpec.card_alignedVertexKeyFiber_eq_multiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (t : Nat) (ht : t ≤ 4) (hlen : rep.length = t)
    (hn0 : orderFortyNineHighIncidenceCount G 0 = 4 - t)
    (key : Option (Fin 9) × Finset (Fin 9)) :
    Fintype.card {x : V // orderFortyNineGraphAlignedVertexKey G e x = key} =
      orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key := by
  rcases key with ⟨o, S⟩
  cases o with
  | none =>
      have heq : (Finset.univ.filter fun x : V =>
          orderFortyNineGraphAlignedVertexKey G e x = (none, S)) =
          (Finset.univ.filter fun x : V =>
            orderFortyNineGraphVertexKey G e x = (false, S)) := by
        ext x
        by_cases hx : x ∈ orderFortyNineHighVertices G <;>
          simp [orderFortyNineGraphAlignedVertexKey,
            orderFortyNineGraphVertexKey, hx]
      rw [Fintype.card_subtype, heq, ← Fintype.card_subtype]
      rw [hcanon.card_vertexKeyFiber_eq_multiplicity
        G hfree hmin hcard hHigh e rep t ht hlen hn0 (false, S)]
      simp [orderFortyNineCanonicalAlignedVertexKeyMultiplicity,
        orderFortyNineCanonicalVertexKeyMultiplicity]
  | some w =>
      by_cases hS0 : S.card = 0
      · have hS : S = ∅ := Finset.card_eq_zero.mp hS0
        subst S
        rw [Fintype.card_subtype]
        have heq : (Finset.univ.filter fun x : V =>
            orderFortyNineGraphAlignedVertexKey G e x = (some w, ∅)) =
            {((e.symm w).1 : V)} := by
          ext x
          constructor
          · intro hx
            have hxEq := (Finset.mem_filter.mp hx).2
            have hxHigh : x ∈ orderFortyNineHighVertices G := by
              by_contra hxNot
              have := congrArg Prod.fst hxEq
              simp [orderFortyNineGraphAlignedVertexKey, hxNot] at this
            have hw : e ⟨x, hxHigh⟩ = w := by
              have := congrArg Prod.fst hxEq
              simpa [orderFortyNineGraphAlignedVertexKey, hxHigh] using this
            have hsub : (⟨x, hxHigh⟩ :
                {v // v ∈ orderFortyNineHighVertices G}) = e.symm w := by
              apply e.injective
              simpa [hw]
            simpa using congrArg Subtype.val hsub
          · intro hx
            have hxv : x = (e.symm w).1 := by simpa using hx
            subst x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            apply Prod.ext
            · simp [orderFortyNineGraphAlignedVertexKey]
            · apply (orderFortyNineLabeledHighSupport_eq_empty_iff
                G e (e.symm w).1).mpr
              exact orderFortyNine_highNeighborCount_eq_zero_of_high
                G hfree hmin hcard (e.symm w).2
        rw [heq]
        simp [orderFortyNineCanonicalAlignedVertexKeyMultiplicity]
      · rw [Fintype.card_subtype]
        have heq : (Finset.univ.filter fun x : V =>
            orderFortyNineGraphAlignedVertexKey G e x = (some w, S)) = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨x, hx⟩
          have hxEq := (Finset.mem_filter.mp hx).2
          have hxHigh : x ∈ orderFortyNineHighVertices G := by
            by_contra hxNot
            have := congrArg Prod.fst hxEq
            simp [orderFortyNineGraphAlignedVertexKey, hxNot] at this
          have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
            G hfree hmin hcard hxHigh
          have hs : orderFortyNineLabeledHighSupport G e x = S := by
            simpa [orderFortyNineGraphAlignedVertexKey, hxHigh] using
              congrArg Prod.snd hxEq
          have hc := card_orderFortyNineLabeledHighSupport G e x
          change (orderFortyNineHighSupport G x).card = 0 at hz
          rw [hs] at hc
          omega
        rw [heq]
        simp [orderFortyNineCanonicalAlignedVertexKeyMultiplicity, hS0]

theorem orderFortyNineH9T2_rep_length
    {rep : OrderFortyNineH9System} (hrep : rep ∈ orderFortyNineH9T2Systems) :
    rep.length = 2 := by
  native_decide +revert

theorem orderFortyNineH9T3_rep_length
    {rep : OrderFortyNineH9System} (hrep : rep ∈ orderFortyNineH9T3Systems) :
    rep.length = 3 := by
  native_decide +revert

theorem orderFortyNineH9T4_rep_length
    {rep : OrderFortyNineH9System} (hrep : rep ∈ orderFortyNineH9T4Systems) :
    rep.length = 4 := by
  native_decide +revert

/-- Fiberwise equality of the enriched vertex keys produces a full labeling
that simultaneously preserves the high stratum and every support. -/
theorem exists_orderFortyNine_fullVertexLabeling_of_keyFiberCardEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat)
    (hcard : ∀ key : Bool × Finset (Fin 9),
      Fintype.card {x : V // orderFortyNineGraphVertexKey G e x = key} =
      Fintype.card {i : Fin 49 // orderFortyNineMaskVertexKey masks i = key}) :
    ∃ E : V ≃ Fin 49, ∀ x,
      orderFortyNineMaskVertexKey masks (E x) =
        orderFortyNineGraphVertexKey G e x := by
  let E := equivOfFiberCardEq
    (orderFortyNineGraphVertexKey G e)
    (orderFortyNineMaskVertexKey masks) hcard
  exact ⟨E, fun x => equivOfFiberCardEq_map _ _ hcard x⟩

theorem OrderFortyNineCanonicalTripleSystemSpec.exists_fullLabeling_t2
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (hrep : rep ∈ orderFortyNineH9T2Systems)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ E : V ≃ Fin 49, ∀ x,
      orderFortyNineMaskVertexKey (orderFortyNineH9ProfileMasks rep) (E x) =
        orderFortyNineGraphVertexKey G e x := by
  have hn0 := orderFortyNine_emptyIncidenceCount_eq_four_sub_triples
    G hfree hmin hcard hHigh
  rw [hcount] at hn0
  apply exists_orderFortyNine_fullVertexLabeling_of_keyFiberCardEq G e
  intro key
  rw [hcanon.card_vertexKeyFiber_eq_multiplicity
      G hfree hmin hcard hHigh e rep 2 (by norm_num)
        (orderFortyNineH9T2_rep_length hrep) hn0 key,
    orderFortyNine_card_maskVertexKeyFiber,
    orderFortyNineH9T2_vertexKeyFiberCount rep hrep key]

theorem OrderFortyNineCanonicalTripleSystemSpec.exists_fullLabeling_t3
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (hrep : rep ∈ orderFortyNineH9T3Systems)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ E : V ≃ Fin 49, ∀ x,
      orderFortyNineMaskVertexKey (orderFortyNineH9ProfileMasks rep) (E x) =
        orderFortyNineGraphVertexKey G e x := by
  have hn0 := orderFortyNine_emptyIncidenceCount_eq_four_sub_triples
    G hfree hmin hcard hHigh
  rw [hcount] at hn0
  apply exists_orderFortyNine_fullVertexLabeling_of_keyFiberCardEq G e
  intro key
  rw [hcanon.card_vertexKeyFiber_eq_multiplicity
      G hfree hmin hcard hHigh e rep 3 (by norm_num)
        (orderFortyNineH9T3_rep_length hrep) hn0 key,
    orderFortyNine_card_maskVertexKeyFiber,
    orderFortyNineH9T3_vertexKeyFiberCount rep hrep key]

theorem OrderFortyNineCanonicalTripleSystemSpec.exists_fullLabeling_t4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (hrep : rep ∈ orderFortyNineH9T4Systems)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ E : V ≃ Fin 49, ∀ x,
      orderFortyNineMaskVertexKey (orderFortyNineH9ProfileMasks rep) (E x) =
        orderFortyNineGraphVertexKey G e x := by
  have hn0 := orderFortyNine_emptyIncidenceCount_eq_four_sub_triples
    G hfree hmin hcard hHigh
  rw [hcount] at hn0
  apply exists_orderFortyNine_fullVertexLabeling_of_keyFiberCardEq G e
  intro key
  rw [hcanon.card_vertexKeyFiber_eq_multiplicity
      G hfree hmin hcard hHigh e rep 4 (by norm_num)
        (orderFortyNineH9T4_rep_length hrep) hn0 key,
    orderFortyNine_card_maskVertexKeyFiber,
    orderFortyNineH9T4_vertexKeyFiberCount rep hrep key]

theorem orderFortyNine_exists_fullCanonicalT2Labeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ rep ∈ orderFortyNineH9T2Systems,
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ E : V ≃ Fin 49, ∀ x,
        orderFortyNineMaskVertexKey (orderFortyNineH9ProfileMasks rep) (E x) =
          orderFortyNineGraphVertexKey G e x := by
  obtain ⟨row, hrow, rep, hlookup, e, hcanon⟩ :=
    orderFortyNine_exists_canonicalT2System G hfree hHigh hcount
  have hrep : rep ∈ orderFortyNineH9T2Systems :=
    array_mem_of_getElem?_eq_some hlookup
  obtain ⟨E, hE⟩ := hcanon.exists_fullLabeling_t2
    G hfree hmin hcard hHigh e rep hrep hcount
  exact ⟨rep, hrep, e, E, hE⟩

theorem orderFortyNine_exists_fullCanonicalT3Labeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ rep ∈ orderFortyNineH9T3Systems,
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ E : V ≃ Fin 49, ∀ x,
        orderFortyNineMaskVertexKey (orderFortyNineH9ProfileMasks rep) (E x) =
          orderFortyNineGraphVertexKey G e x := by
  obtain ⟨row, hrow, rep, hlookup, e, hcanon⟩ :=
    orderFortyNine_exists_canonicalT3System G hfree hHigh hcount
  have hrep : rep ∈ orderFortyNineH9T3Systems :=
    array_mem_of_getElem?_eq_some hlookup
  obtain ⟨E, hE⟩ := hcanon.exists_fullLabeling_t3
    G hfree hmin hcard hHigh e rep hrep hcount
  exact ⟨rep, hrep, e, E, hE⟩

theorem orderFortyNine_exists_fullCanonicalT4Labeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ rep ∈ orderFortyNineH9T4Systems,
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ E : V ≃ Fin 49, ∀ x,
        orderFortyNineMaskVertexKey (orderFortyNineH9ProfileMasks rep) (E x) =
          orderFortyNineGraphVertexKey G e x := by
  obtain ⟨row, hrow, rep, hlookup, e, hcanon⟩ :=
    orderFortyNine_exists_canonicalT4System G hfree hHigh hcount
  have hrep : rep ∈ orderFortyNineH9T4Systems :=
    array_mem_of_getElem?_eq_some hlookup
  obtain ⟨E, hE⟩ := hcanon.exists_fullLabeling_t4
    G hfree hmin hcard hHigh e rep hrep hcount
  exact ⟨rep, hrep, e, E, hE⟩

/-- Fiberwise equality for the exact-label key produces a labeling which
sends the high vertex labeled `w` to the literal index `w`. -/
theorem exists_orderFortyNine_alignedVertexLabeling_of_keyFiberCardEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat)
    (hcard : ∀ key : Option (Fin 9) × Finset (Fin 9),
      Fintype.card {x : V //
        orderFortyNineGraphAlignedVertexKey G e x = key} =
      Fintype.card {i : Fin 49 //
        orderFortyNineMaskAlignedVertexKey masks i = key}) :
    ∃ E : V ≃ Fin 49, ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x := by
  let E := equivOfFiberCardEq
    (orderFortyNineGraphAlignedVertexKey G e)
    (orderFortyNineMaskAlignedVertexKey masks) hcard
  exact ⟨E, fun x => equivOfFiberCardEq_map _ _ hcard x⟩

theorem OrderFortyNineCanonicalTripleSystemSpec.exists_alignedLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep)
    (t : Nat) (ht : t ≤ 4) (hlen : rep.length = t)
    (hn0 : orderFortyNineHighIncidenceCount G 0 = 4 - t)
    (htarget : ∀ key : Option (Fin 9) × Finset (Fin 9),
      orderFortyNineMaskAlignedVertexKeyFiberCount
          (orderFortyNineH9ProfileMasks rep) key =
        orderFortyNineCanonicalAlignedVertexKeyMultiplicity rep key) :
    ∃ E : V ≃ Fin 49, ∀ x,
      orderFortyNineMaskAlignedVertexKey
          (orderFortyNineH9ProfileMasks rep) (E x) =
        orderFortyNineGraphAlignedVertexKey G e x := by
  apply exists_orderFortyNine_alignedVertexLabeling_of_keyFiberCardEq G e
  intro key
  rw [hcanon.card_alignedVertexKeyFiber_eq_multiplicity
      G hfree hmin hcard hHigh e rep t ht hlen hn0 key,
    orderFortyNine_card_maskAlignedVertexKeyFiber,
    htarget key]

theorem orderFortyNine_exists_alignedCanonicalT2Labeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ rep ∈ orderFortyNineH9T2Systems,
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ E : V ≃ Fin 49, ∀ x,
        orderFortyNineMaskAlignedVertexKey
            (orderFortyNineH9ProfileMasks rep) (E x) =
          orderFortyNineGraphAlignedVertexKey G e x := by
  obtain ⟨row, hrow, rep, hlookup, e, hcanon⟩ :=
    orderFortyNine_exists_canonicalT2System G hfree hHigh hcount
  have hrep : rep ∈ orderFortyNineH9T2Systems :=
    array_mem_of_getElem?_eq_some hlookup
  have hn0 := orderFortyNine_emptyIncidenceCount_eq_four_sub_triples
    G hfree hmin hcard hHigh
  rw [hcount] at hn0
  obtain ⟨E, hE⟩ := hcanon.exists_alignedLabeling
    G hfree hmin hcard hHigh e rep 2 (by norm_num)
      (orderFortyNineH9T2_rep_length hrep) hn0
      (orderFortyNineH9T2_alignedVertexKeyFiberCount rep hrep)
  exact ⟨rep, hrep, e, E, hE⟩

theorem orderFortyNine_exists_alignedCanonicalT3Labeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ rep ∈ orderFortyNineH9T3Systems,
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ E : V ≃ Fin 49, ∀ x,
        orderFortyNineMaskAlignedVertexKey
            (orderFortyNineH9ProfileMasks rep) (E x) =
          orderFortyNineGraphAlignedVertexKey G e x := by
  obtain ⟨row, hrow, rep, hlookup, e, hcanon⟩ :=
    orderFortyNine_exists_canonicalT3System G hfree hHigh hcount
  have hrep : rep ∈ orderFortyNineH9T3Systems :=
    array_mem_of_getElem?_eq_some hlookup
  have hn0 := orderFortyNine_emptyIncidenceCount_eq_four_sub_triples
    G hfree hmin hcard hHigh
  rw [hcount] at hn0
  obtain ⟨E, hE⟩ := hcanon.exists_alignedLabeling
    G hfree hmin hcard hHigh e rep 3 (by norm_num)
      (orderFortyNineH9T3_rep_length hrep) hn0
      (orderFortyNineH9T3_alignedVertexKeyFiberCount rep hrep)
  exact ⟨rep, hrep, e, E, hE⟩

theorem orderFortyNine_exists_alignedCanonicalT4Labeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ rep ∈ orderFortyNineH9T4Systems,
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      ∃ E : V ≃ Fin 49, ∀ x,
        orderFortyNineMaskAlignedVertexKey
            (orderFortyNineH9ProfileMasks rep) (E x) =
          orderFortyNineGraphAlignedVertexKey G e x := by
  obtain ⟨row, hrow, rep, hlookup, e, hcanon⟩ :=
    orderFortyNine_exists_canonicalT4System G hfree hHigh hcount
  have hrep : rep ∈ orderFortyNineH9T4Systems :=
    array_mem_of_getElem?_eq_some hlookup
  have hn0 := orderFortyNine_emptyIncidenceCount_eq_four_sub_triples
    G hfree hmin hcard hHigh
  rw [hcount] at hn0
  obtain ⟨E, hE⟩ := hcanon.exists_alignedLabeling
    G hfree hmin hcard hHigh e rep 4 (by norm_num)
      (orderFortyNineH9T4_rep_length hrep) hn0
      (orderFortyNineH9T4_alignedVertexKeyFiberCount rep hrep)
  exact ⟨rep, hrep, e, E, hE⟩

end

end Erdos85
