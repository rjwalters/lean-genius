import Proofs.Erdos85OneHighOddProfileRepeatedOwnerTargetCapacity
import Proofs.Erdos85OneHighOddProfileSeparatedRepeat

/-!
# Endpoint saturation from two exhausted matching edges

If two distinguished internal edges exhaust a branch matching, the branch's
entire miss-label pairing consists of their two exact keys.  A source label
which is far from the first key can occur at most once overall, because the
second key has distinct endpoints.  This is the combinatorial core of the
four-of-five cross-cut saturation bound.
-/

namespace Erdos85

private theorem list_perm_pair_of_length_two_of_mem
    {α : Type*} [DecidableEq α] (xs : List α) (a b : α)
    (hlen : xs.length = 2) (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) :
    xs.Perm [a, b] := by
  cases xs with
  | nil => simp at hlen
  | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y tail =>
          have htail : tail = [] := by simpa using hlen
          subst tail
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
          rcases ha with hax | hay <;> rcases hb with hbx | hby
          · exact False.elim (hab (hax.trans hbx.symm))
          · subst x; subst y; exact List.Perm.refl _
          · subst x; subst y; exact List.Perm.swap _ _ _
          · exact False.elim (hab (hay.trans hby.symm))

/-- Two exact distinct matching-edge sources which exhaust the matching give
an endpoint multiplicity at most one for any label far from the first key. -/
theorem oneHighPairingEndpointCount_le_one_of_exhausted_pair
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8)
    (yq yr : X) (hyq : yq ∈ matchingEdgeSources mate)
    (hyr : yr ∈ matchingEdgeSources mate) (hyne : yq ≠ yr)
    (hexhaust : matchingEdgeSources mate = {yq, yr})
    (keyq keyr : OneHighLabelPair) (source : Fin 8)
    (hyqKey : (min (label yq) (label (mate yq)),
      max (label yq) (label (mate yq))) = keyq)
    (hyrKey : (min (label yr) (label (mate yr)),
      max (label yr) (label (mate yr))) = keyr)
    (hfar : OneHighKeyFarFromSource keyq source)
    (hkeys : keyq ≠ keyr)
    (hkeyrlt : keyr.1 < keyr.2) :
    oneHighPairingEndpointCount
      (matchingPairingListSorted mate label) source ≤ 1 := by
  have hlen : (matchingPairingListSorted mate label).length = 2 := by
    rw [matchingPairingListSorted_length, matchingPairingList_length,
      hexhaust]
    simp [hyne]
  have hmemq : keyq ∈ matchingPairingListSorted mate label := by
    rw [← hyqKey]
    exact canonicalPair_mem_matchingPairingListSorted_of_mem_source
      mate label hyq
  have hmemr : keyr ∈ matchingPairingListSorted mate label := by
    rw [← hyrKey]
    exact canonicalPair_mem_matchingPairingListSorted_of_mem_source
      mate label hyr
  have hperm := list_perm_pair_of_length_two_of_mem
    (matchingPairingListSorted mate label) keyq keyr hlen hmemq hmemr hkeys
  have hsum := hperm.map
    (fun key => oneHighLabelPairEndpointCount key source) |>.sum_eq
  unfold oneHighPairingEndpointCount
  rw [hsum]
  have hqzero : oneHighLabelPairEndpointCount keyq source = 0 := by
    simp [oneHighLabelPairEndpointCount, hfar.1, hfar.2.1]
  have hrle : oneHighLabelPairEndpointCount keyr source ≤ 1 := by
    unfold oneHighLabelPairEndpointCount
    by_cases h₁ : keyr.1 = source <;> by_cases h₂ : keyr.2 = source <;>
      simp_all
  simp [hqzero, hrle]

end Erdos85

#print axioms Erdos85.oneHighPairingEndpointCount_le_one_of_exhausted_pair
