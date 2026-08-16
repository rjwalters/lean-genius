import Proofs.Erdos85OneHighMissLabelFiber
import Proofs.Erdos85OneHighGlobalExchangeParity
import Proofs.Erdos85MatchingKeyMultiplicity
import Proofs.Erdos85OneHighOddKeyCycleExtraction

/-! # Unconditional odd-support cycle bridge for the one-high case

The graph-side miss-column parity is transported through the global internal
matching, constant-label orbit cancellation, and unordered-key grouping.  It
follows that either every exchanged-key multiplicity is even or its odd
support contains an actual cycle.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- In the degree-eight one-high configuration, nonempty odd exchanged-key
support necessarily contains a shared-label cycle.  No same-miss or
source-emptiness hypothesis is used. -/
theorem oneHigh_even_multiplicities_or_oddKey_cycle
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (hrootInv : Function.Involutive rootMate) :
    let X := OneHighAllMatchedVertices G v
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    let m := exchangedMissPairMultiplicity mate label
    (∀ k ∈ exchangedMissPairKeys {z : V // z ∈ G.neighborSet v}, Even (m k)) ∨
      ∃ k : OddExchangedKey m,
        ∃ c : (oddExchangedKeyGraph m).Walk k k, c.IsCycle := by
  classical
  dsimp only
  let mate := oneHighGlobalInternalMate G hfree v
  let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
    rootMate hrootAdj
  let m := exchangedMissPairMultiplicity mate label
  by_cases hall : ∀ k ∈ exchangedMissPairKeys
      {z : V // z ∈ G.neighborSet v}, Even (m k)
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨k, hk, hkNotEven⟩ := hall
    have hkodd : Odd (m k) := Nat.not_even_iff_odd.mp hkNotEven
    apply exists_oddExchangedKey_isCycle m k hk hkodd
    intro l
    have hfiberEven : Even (matchingLabelFiber label l).card := by
      have hcolumn := even_sum_far_highBranchMissCount_column
        G hfree (d := 7) (by omega) hv hneigh hlocal hexternal
          rootMate hrootAdj houterDegree l
      rw [← card_oneHighGlobalMissLabelFiber_eq_farColumn
        G hfree hv hexternal houterDegree rootMate hrootAdj hrootInv l]
        at hcolumn
      simpa [matchingLabelFiber, label] using hcolumn
    have hnonconstant : Even
        (nonconstantMatchingLabelFiber mate label l).card :=
      even_nonconstantMatchingLabelFiber_of_even mate label l
        (oneHighGlobalInternalMate_involutive G hfree v)
        (oneHighGlobalInternalMate_ne G hfree v) hfiberEven
    have hkey : Even (nonconstantMatchingKeyIncidence mate label l) :=
      even_nonconstantMatchingKeyIncidence_of_even mate label l
        (oneHighGlobalInternalMate_involutive G hfree v)
        (oneHighGlobalInternalMate_ne G hfree v) hnonconstant
    convert (even_sum_keyIncidence_mul_multiplicity_of_even
      mate label l hkey) using 1
    apply Finset.sum_congr rfl
    intro q _
    simp [unorderedKeyIncidence, m]

end

end Erdos85
