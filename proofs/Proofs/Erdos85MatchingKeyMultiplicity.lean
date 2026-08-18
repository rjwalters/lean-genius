import Proofs.Erdos85MatchingKeyIncidence

/-! # Grouping matching-edge incidence by exchanged keys -/

namespace Erdos85

noncomputable section

/-- Endpoint incidence grouped by genuine unordered key fibers. -/
theorem nonconstantMatchingKeyIncidence_eq_sum_multiplicity
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (l : L) :
    nonconstantMatchingKeyIncidence mate label l =
      ∑ key ∈ exchangedMissPairKeys L,
        unorderedKeyIncidence key l *
          exchangedMissPairMultiplicity mate label key := by
  classical
  let S := nonconstantMatchingEdgeSources mate label
  let K := exchangedMissPairKeys L
  let key := exchangedMissPairKey mate label
  have hmaps : ∀ x ∈ S, key x ∈ K := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨by simp [K, exchangedMissPairKeys], ?_⟩
    exact exchangedMissPairKey_lt_of_mem hx
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := K) hmaps
    (fun x => unorderedKeyIncidence (key x) l)
  change (∑ x ∈ S, unorderedKeyIncidence (key x) l) = _
  rw [← hfiber]
  simp only [nonconstantMatchingKeyIncidence, S, K, key]
  apply Finset.sum_congr rfl
  intro q hq
  let F := S.filter fun x => key x = q
  change (∑ x ∈ F, unorderedKeyIncidence (key x) l) =
    unorderedKeyIncidence q l * F.card
  calc
    (∑ x ∈ F, unorderedKeyIncidence (key x) l) =
        ∑ _x ∈ F, unorderedKeyIncidence q l := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
    _ = unorderedKeyIncidence q l * F.card := by
      simp [Nat.mul_comm]

/-- Weighted key multiplicities inherit parity from endpoint-label parity. -/
theorem even_sum_keyIncidence_mul_multiplicity_of_even
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (l : L)
    (heven : Even (nonconstantMatchingKeyIncidence mate label l)) :
    Even (∑ key ∈ exchangedMissPairKeys L,
      unorderedKeyIncidence key l *
        exchangedMissPairMultiplicity mate label key) := by
  rwa [nonconstantMatchingKeyIncidence_eq_sum_multiplicity
    mate label l] at heven

end

end Erdos85
