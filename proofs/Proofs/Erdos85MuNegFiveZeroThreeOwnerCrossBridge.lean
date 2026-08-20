import Proofs.Erdos85MuNegFiveZeroThreeOwnerBridge
import Proofs.Erdos85EightEightHighOwnerCnfBridgeCounting

/-!
# Structural cross-clause bridge for h503

The first increment discharges the complete intertwining truth table from the
entrywise C8 balance equation.  It is independent of the eventual graph
coordinate realization.
-/

namespace Erdos85

open Std Sat

theorem muNegFiveZeroThreeCrossIndex?_some_pos
    {x y id : Nat} (h : muNegFiveZeroThreeCrossIndex? x y = some id) :
    0 < id := by
  simp only [muNegFiveZeroThreeCrossIndex?] at h
  split at h
  · obtain ⟨k, _, rfl⟩ := Option.map_eq_some_iff.mp h
    omega
  · contradiction

/-- Every forbidden four-bit mask is excluded when the actual cross-owner
matrix commutes with the two C8 adjacency operators. -/
theorem muNegFiveZeroThreeIntertwiningClauses_satisfied
    (val : DimacsValuation)
    (hbalance : ∀ x y a b c d,
      muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = some a →
      muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = some b →
      muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = some c →
      muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = some d →
      (val a).toNat + (val b).toNat =
        (val c).toNat + (val d).toNat) :
    ∀ clause ∈ muNegFiveZeroThreeIntertwiningClauses,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegFiveZeroThreeIntertwiningClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨x, hx, y, hy, hclause⟩ := hclause
  generalize ha : muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = oa
    at hclause
  generalize hb : muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = ob
    at hclause
  generalize hc : muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = oc
    at hclause
  generalize hd : muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = od
    at hclause
  cases oa <;> cases ob <;> cases oc <;> cases od <;>
    simp at hclause
  rename_i a b c d
  obtain ⟨mask, hmask, hclause⟩ := hclause
  obtain ⟨hbad, hclause⟩ := hclause
  subst clause
  simpa using
    dimacsIntertwiningMaskClauseSatisfied_of_balance val a b c d
      (muNegFiveZeroThreeCrossIndex?_some_pos ha)
      (muNegFiveZeroThreeCrossIndex?_some_pos hb)
      (muNegFiveZeroThreeCrossIndex?_some_pos hc)
      (muNegFiveZeroThreeCrossIndex?_some_pos hd)
      (muNegFiveZeroThreeBit mask 3) (muNegFiveZeroThreeBit mask 2)
      (muNegFiveZeroThreeBit mask 1) (muNegFiveZeroThreeBit mask 0)
      hbad (hbalance x y a b c d ha hb hc hd)

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeIntertwiningClauses_satisfied
