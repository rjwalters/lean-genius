import Proofs.Erdos85DyadicStoppingSupportGlobalSqueeze
import Proofs.Erdos85C4FreeSubsetCherryBound

/-!
# C4 cherry squeeze for a dyadic stopping support

The pointwise service inequality gives an exact ceiling lower bound on the
number of marked lines through every shore point.  C4-freeness then limits
the resulting cherries by the number of pairs in the marked support.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Minimum marked-line degree forced by the level-`j` service law. -/
def dyadicStoppingServiceMinimum (q s j : ℕ) : ℕ :=
  (((2 * 2 ^ j - 1) * q + 1 - s) ⌈/⌉ (2 ^ j))

/-- The pointwise service inequality forces every shore point to have at
least `dyadicStoppingServiceMinimum` marked neighbors. -/
theorem c4Free_dyadicStoppingSupport_degree_ge_serviceMinimum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (p : V) (hpS : p ∈ S) :
    dyadicStoppingServiceMinimum q S.card j ≤
      (G.neighborFinset p ∩ dyadicOccupancySupport G S j).card := by
  have hservice := c4Free_dyadicStoppingSupport_pointwise_service
    G hfree hreg S j hdiv p hpS
  apply (ceilDiv_le_iff_le_mul (show 0 < 2 ^ j by positivity)).2
  omega

/-- Generic C4 cherry consumer: a uniform lower bound `L` on the number of
neighbors in `B` over every center in `S` forces
`|S| choose(L,2) ≤ choose(|B|,2)`. -/
theorem c4Free_uniform_subset_service_cherry_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (S B : Finset V) (L : ℕ)
    (hservice : ∀ p ∈ S, L ≤ (G.neighborFinset p ∩ B).card) :
    S.card * L.choose 2 ≤ B.card.choose 2 := by
  have hlocal :
      S.card * L.choose 2 ≤
        ∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose 2 := by
    calc
      S.card * L.choose 2 = ∑ _p ∈ S, L.choose 2 := by simp
      _ ≤ ∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.choose_le_choose 2 (hservice p hp)
  have hsub :
      (∑ p ∈ S, ((G.neighborFinset p ∩ B).card).choose 2) ≤
        ∑ p : V, ((G.neighborFinset p ∩ B).card).choose 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  exact hlocal.trans <| hsub.trans <|
    sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      G hfree B

/-- One-shore cherry squeeze for the canonical dyadic stopping support. -/
theorem c4Free_dyadicStoppingSupport_shore_cherry_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 ≤
      (dyadicOccupancySupport G S j).card.choose 2 := by
  apply c4Free_uniform_subset_service_cherry_le G hfree S
    (dyadicOccupancySupport G S j)
    (dyadicStoppingServiceMinimum q S.card j)
  intro p hp
  exact c4Free_dyadicStoppingSupport_degree_ge_serviceMinimum
    G hfree hreg S j hdiv p hp

/-- **Two-shore C4 cherry squeeze (audit (48)--(49)).**  When the next
dyadic scale divides `q`, a shore and its complement have the same marked
support `B`; both ceiling service minima must fit into the single pair
budget `choose(|B|,2)`. -/
theorem c4Free_dyadicStoppingSupport_twoShore_cherry_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 ≤
        (dyadicOccupancySupport G S j).card.choose 2 ∧
      (Sᶜ : Finset V).card *
          (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 ≤
        (dyadicOccupancySupport G S j).card.choose 2 := by
  have hajq : 2 ^ j ∣ q := by
    obtain ⟨u, hu⟩ := hqdiv
    refine ⟨2 * u, ?_⟩
    rw [hu, pow_succ]
    ring
  have hdivc : ∀ v, 2 ^ j ∣
      (G.neighborFinset v ∩ (Sᶜ : Finset V)).card :=
    dvd_complement_occupancy G hreg S (by positivity) hajq hdiv
  constructor
  · exact c4Free_dyadicStoppingSupport_shore_cherry_squeeze
      G hfree hreg S j hdiv
  · have hc := c4Free_dyadicStoppingSupport_shore_cherry_squeeze
      G hfree hreg (Sᶜ : Finset V) j hdivc
    rwa [dyadicOccupancySupport_compl G hreg S j hdiv hqdiv] at hc

end

end Erdos85

#print axioms Erdos85.c4Free_dyadicStoppingSupport_degree_ge_serviceMinimum
#print axioms Erdos85.c4Free_uniform_subset_service_cherry_le
#print axioms Erdos85.c4Free_dyadicStoppingSupport_twoShore_cherry_squeeze
