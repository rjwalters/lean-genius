import Proofs.Erdos85OrderFortyNineFiveHighTripleNormalization

/-!
# Canonical fiber covers for the five-high cells

This file packages the graph-side fiber census in a form shared by all three
canonical triple systems.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem fiveHigh_alignedHigh_fiber_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (w : Fin 5) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (some w, ∅)} = 1 := by
  rw [Fintype.card_subtype]
  let v : Fin 49 := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hset : (Finset.univ.filter fun x : Fin 49 =>
      fiveHighGraphAlignedKey G e x = (some w, ∅)) = {v} := by
    ext x
    constructor
    · intro hx
      have hkey := (Finset.mem_filter.mp hx).2
      have hfirst := congrArg Prod.fst hkey
      have hxHigh : x ∈ orderFortyNineHighVertices G := by
        by_contra hxNot
        simp [fiveHighGraphAlignedKey, hxNot] at hfirst
      have heq : e ⟨x, hxHigh⟩ = w := by
        simpa [fiveHighGraphAlignedKey, hxHigh] using hfirst
      have hxv : x = v := by
        have hsub : (⟨x, hxHigh⟩ : {u // u ∈
            orderFortyNineHighVertices G}) = e.symm w := by
          apply e.injective
          simpa using heq
        exact congrArg Subtype.val hsub
      simp [hxv]
    · intro hx
      have hxv : x = v := by simpa using hx
      subst x
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ v, ?_⟩
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hv
      have hs : fiveHighLabeledSupport G e v = ∅ :=
        Finset.card_eq_zero.mp (by
          rw [fiveHighLabeledSupport_card]
          exact hz)
      simp [fiveHighGraphAlignedKey, hv, v, hs]
  rw [hset]
  simp

theorem fiveHigh_alignedHigh_nonemptySupport_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (w : Fin 5) (S : Finset (Fin 5)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (some w, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp := congrArg Prod.snd hkey
  have hxHigh : x ∈ orderFortyNineHighVertices G := by
    by_contra hxNot
    simp [fiveHighGraphAlignedKey, hxNot] at hfirst
  have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
    G hfree hmin (Fintype.card_fin 49) hxHigh
  have hcard : (fiveHighLabeledSupport G e x).card = 0 := by
    rw [fiveHighLabeledSupport_card]
    exact hz
  have hs : fiveHighLabeledSupport G e x = S := by
    simpa [fiveHighGraphAlignedKey] using hsupp
  rw [hs] at hcard
  exact hS.ne_empty (Finset.card_eq_zero.mp hcard)

theorem fiveHigh_nonempty_alignedLowFiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (S : Finset (Fin 5)) (hS : S.Nonempty) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (none, S)} =
      Fintype.card {x : Fin 49 // fiveHighLabeledSupport G e x = S} := by
  apply Fintype.card_congr
  let f : {x : Fin 49 // fiveHighGraphAlignedKey G e x = (none, S)} →
      {x : Fin 49 // fiveHighLabeledSupport G e x = S} := fun x =>
    ⟨x.1, by
      have hs := congrArg Prod.snd x.2
      simpa [fiveHighGraphAlignedKey] using hs⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  · intro y
    have hyNotHigh : y.1 ∉ orderFortyNineHighVertices G := by
      intro hyHigh
      have hz := orderFortyNine_highNeighborCount_eq_zero_of_high
        G hfree hmin (Fintype.card_fin 49) hyHigh
      have hcard : (fiveHighLabeledSupport G e y.1).card = 0 := by
        rw [fiveHighLabeledSupport_card]
        exact hz
      rw [y.2] at hcard
      exact hS.ne_empty (Finset.card_eq_zero.mp hcard)
    refine ⟨⟨y.1, ?_⟩, rfl⟩
    simp [fiveHighGraphAlignedKey, hyNotHigh, y.2]

theorem fiveHigh_alignedLow_support_card_gt_three_fiber_card_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 5)
    (S : Finset (Fin 5)) (hS : 3 < S.card) :
    Fintype.card {x : Fin 49 //
      fiveHighGraphAlignedKey G e x = (none, S)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hkey := (Finset.mem_filter.mp hx).2
  have hfirst := congrArg Prod.fst hkey
  have hsupp : fiveHighLabeledSupport G e x = S := by
    simpa [fiveHighGraphAlignedKey] using congrArg Prod.snd hkey
  have hxNotHigh : x ∉ orderFortyNineHighVertices G := by
    intro hxHigh
    simp [fiveHighGraphAlignedKey, hxHigh] at hfirst
  have hx7 : G.degree x = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) x with hx7 | hx8
    · exact hx7
    · exact False.elim (hxNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx8⟩))
  have hle : S.card ≤ 3 := by
    rw [← hsupp, fiveHighLabeledSupport_card]
    simpa [orderFortyNineHighSupport] using
      orderFortyNine_highNeighborCount_le_three
        G hfree hmin (Fintype.card_fin 49) hx7
  omega

end

end Erdos85
