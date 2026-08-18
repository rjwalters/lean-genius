import Proofs.Erdos85CycleCoverPairMassExact
import Proofs.Erdos85MixedAnchorMasterQuantization

/-!
# Exact pair-mass formulas for unequal defect-cycle blocks
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A positive block from a shorter source cycle to a longer target cycle is
an exact cyclic cover, selected precisely by source-length divisibility. -/
theorem sum_anchorPairMultiplicity_shorter_positive_eq_ite_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hn3 : 3 ≤ n)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c e)
    (u : ZMod r → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (δ : ZMod n) :
    (∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ) =
      if r ∣ δ.val then n else 0 := by
  have hentries := secondOrder_componentQuotientMatrix_entries_of_size_lt
    G hfree hd heven hmin hcard c e hlt hpos
  exact sum_anchorPairMultiplicity_of_componentQuotient_eq_one G hfree hd
    heven hmin hcard hr3 hn3 c e u v huinj hvinj huRange hvRange huD hvD
      hentries.1 δ

/-- A zero quotient block from a shorter source has zero pair mass at every
nonzero target displacement. -/
theorem sum_anchorPairMultiplicity_shorter_zero_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (v : ZMod n → V)
    (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (hq0 : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0)
    (δ : ZMod n) (hδ : δ ≠ 0) :
    ∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ = 0 := by
  have hs : ∀ x, (mixedAnchorSupport G (u x) v).card ≤ 1 := by
    intro x
    rw [card_mixedAnchorSupport_eq_componentQuotient G hfree hd heven
      hmin hcard c e (by rw [← huRange]; exact ⟨x, rfl⟩) hvinj hvRange,
      hq0]
    omega
  exact sum_anchorPairMultiplicity_of_singleton G u v hs δ hδ

/-- A block from a strictly longer source cycle to a shorter target has zero
pair mass at every nonzero displacement. -/
theorem sum_anchorPairMultiplicity_longer_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hgt : e.supp.ncard < c.supp.ncard)
    (u : ZMod r → V) (v : ZMod n → V)
    (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (δ : ZMod n) (hδ : δ ≠ 0) :
    ∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ = 0 := by
  have hndvd : ¬ c.supp.ncard ∣ e.supp.ncard := by
    intro hdvd
    have hle := Nat.le_of_dvd e.nonempty_supp.ncard_pos hdvd
    omega
  have hqle := secondOrder_componentQuotientMatrix_le_one_of_not_dvd
    G hfree hd heven hmin hcard c e hndvd
  have hs : ∀ x, (mixedAnchorSupport G (u x) v).card ≤ 1 := by
    intro x
    rw [card_mixedAnchorSupport_eq_componentQuotient G hfree hd heven
      hmin hcard c e (by rw [← huRange]; exact ⟨x, rfl⟩) hvinj hvRange]
    exact hqle
  exact sum_anchorPairMultiplicity_of_singleton G u v hs δ hδ

end

end Erdos85
