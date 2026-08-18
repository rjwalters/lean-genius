import Proofs.Erdos85MixedAnchorQuantization
import Proofs.Erdos85BoundaryQuotientDivisibility

/-!
# Master pair-mass quantization for mixed defect cycles

This file combines the three geometric block types.  A block from a source
cycle to an odd target cycle is either singleton, equal-size, or an oriented
cyclic cover.  Consequently its aggregate pair mass is always zero or the
full target length.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Master mixed-block quantization.**  For arbitrary labeled defect-cycle
components `c` and `e`, with `e` of odd order, every nonzero target
displacement has aggregate `c`-block pair mass in `{0,n}`. -/
theorem sum_anchorPairMultiplicity_mixedBlock_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hn3 : 3 ≤ n) (hnOdd : Odd n)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (hrcard : c.supp.ncard = r) (hncard : e.supp.ncard = n)
    (δ : ZMod n) (hδ : δ ≠ 0) :
    (∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ) ∈
      ({0, n} : Set ℕ) := by
  classical
  let D := secondOrderDefectGraph G
  by_cases hlt : c.supp.ncard < e.supp.ncard
  · by_cases hpos : 0 < componentQuotientMatrix G D c e
    · have hentries := secondOrder_componentQuotientMatrix_entries_of_size_lt
        G hfree hd heven hmin hcard c e hlt hpos
      exact sum_anchorPairMultiplicity_mem_of_componentQuotient_eq_one
        G hfree hd heven hmin hcard hr3 hn3 c e u v huinj hvinj huRange
          hvRange huD hvD hentries.1 δ
    · have hq0 : componentQuotientMatrix G D c e = 0 := by omega
      have hs : ∀ x, (mixedAnchorSupport G (u x) v).card ≤ 1 := by
        intro x
        rw [card_mixedAnchorSupport_eq_componentQuotient G hfree hd heven
          hmin hcard c e (by rw [← huRange]; exact ⟨x, rfl⟩) hvinj hvRange,
          hq0]
        omega
      rw [sum_anchorPairMultiplicity_of_singleton G u v hs δ hδ]
      exact Or.inl rfl
  · by_cases heq : c.supp.ncard = e.supp.ncard
    · have hrn : r = n := by omega
      cases hrn
      have hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
          D.adjMatrix ℤ * G.adjMatrix ℤ :=
        adjMatrix_comm_secondOrderDefect_of_even G hfree hd heven hmin hcard
      exact sum_anchorPairMultiplicity_of_equalSize_mem G D hr3 hnOdd u v
        huinj hvinj hcomm huD hvD hfree δ hδ
    · have hgt : e.supp.ncard < c.supp.ncard := by omega
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
      rw [sum_anchorPairMultiplicity_of_singleton G u v hs δ hδ]
      exact Or.inl rfl

end

end Erdos85
