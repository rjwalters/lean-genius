import Proofs.Erdos85FinalDyadicExceptionalPopulationFreeCapacity

/-!
# Even positive boundary of a proper exceptional support

In a preconnected regular graph, a nonempty proper even shore has a positive
even boundary, hence at least two directed shore-to-complement incidences.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Directed boundary incidence from a finite shore. -/
def shoreBoundaryIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (B : Finset V) : ℕ :=
  ∑ v ∈ B, (D.neighborFinset v ∩ (Bᶜ : Finset V)).card

/-- Regular degree splits into twice the internal edge count and the shore
boundary incidence. -/
theorem twice_supportedEdges_add_shoreBoundary_eq_regular_mass
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {d : ℕ} (hreg : ∀ v, D.degree v = d) (B : Finset V) :
    2 * (supportedEdgeGraph D B).edgeFinset.card +
        shoreBoundaryIncidence D B = d * B.card := by
  have hpoint : ∀ v ∈ B,
      (D.neighborFinset v ∩ B).card +
        (D.neighborFinset v ∩ (Bᶜ : Finset V)).card = d := by
    intro v _
    rw [← Finset.card_union_of_disjoint]
    · have hunion :
          D.neighborFinset v ∩ B ∪
              D.neighborFinset v ∩ (Bᶜ : Finset V) =
            D.neighborFinset v := by
        ext w
        by_cases hw : w ∈ B <;> simp [hw]
      rw [hunion, D.card_neighborFinset_eq_degree, hreg]
    · exact Finset.disjoint_left.mpr fun w hwB hwC =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hwC).2)
          (Finset.mem_inter.mp hwB).2
  have hsum := Finset.sum_congr rfl hpoint
  rw [Finset.sum_add_distrib, sum_internal_incidence_eq_twice_supported_edges]
    at hsum
  simpa [shoreBoundaryIncidence, Nat.mul_comm] using hsum

/-- Preconnectedness forces a crossing edge for every nontrivial finite shore. -/
theorem shoreBoundaryIncidence_pos_of_preconnected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Preconnected) (B : Finset V)
    (hB : B.Nonempty) (hBc : (Bᶜ : Finset V).Nonempty) :
    0 < shoreBoundaryIncidence D B := by
  obtain ⟨x, hxB⟩ := hB
  obtain ⟨z, hzBc⟩ := hBc
  have hcross : ∃ u ∈ B, ∃ v ∈ (Bᶜ : Finset V), D.Adj u v := by
    by_contra hnone
    push Not at hnone
    have hclosed : ∀ u v, D.Adj u v → u ∈ B → v ∈ B := by
      intro u v huv huB
      by_contra hvB
      exact hnone u huB v (by simpa using hvB) huv
    have hpropagate : ∀ {u v}, D.Reachable u v → u ∈ B → v ∈ B := by
      intro u v huv hu
      obtain ⟨p⟩ := huv
      induction p with
      | nil => exact hu
      | cons hadj _ ih => exact ih (hclosed _ _ hadj hu)
    have hzB := hpropagate (hconn x z) hxB
    exact (Finset.mem_compl.mp hzBc) hzB
  obtain ⟨u, huB, v, hvBc, huv⟩ := hcross
  have hvInter : v ∈ D.neighborFinset u ∩ (Bᶜ : Finset V) :=
    Finset.mem_inter.mpr ⟨by
      simpa [SimpleGraph.mem_neighborFinset] using huv, hvBc⟩
  have hterm : 0 < (D.neighborFinset u ∩ (Bᶜ : Finset V)).card :=
    Finset.card_pos.mpr ⟨v, hvInter⟩
  have hle : (D.neighborFinset u ∩ (Bᶜ : Finset V)).card ≤
      shoreBoundaryIncidence D B := by
    change (D.neighborFinset u ∩ (Bᶜ : Finset V)).card ≤
      ∑ x ∈ B, (D.neighborFinset x ∩ (Bᶜ : Finset V)).card
    apply Finset.single_le_sum
      (f := fun x => (D.neighborFinset x ∩ (Bᶜ : Finset V)).card)
    · intro _ _
      omega
    · exact huB
  omega

/-- A nontrivial even shore in a preconnected regular graph has boundary at
least two. -/
theorem two_le_shoreBoundaryIncidence_of_preconnected_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Preconnected) {d : ℕ} (hreg : ∀ v, D.degree v = d)
    (B : Finset V) (hB : B.Nonempty) (hBc : (Bᶜ : Finset V).Nonempty)
    (hEven : Even B.card) :
    2 ≤ shoreBoundaryIncidence D B := by
  have hpos := shoreBoundaryIncidence_pos_of_preconnected D hconn B hB hBc
  have hmass := twice_supportedEdges_add_shoreBoundary_eq_regular_mass
    D hreg B
  obtain ⟨k, hk⟩ := hEven
  let e := (supportedEdgeGraph D B).edgeFinset.card
  change 2 * e + shoreBoundaryIncidence D B = d * B.card at hmass
  rw [hk, Nat.mul_add] at hmass
  have heLe : e ≤ d * k := by omega
  have hboundaryEven : Even (shoreBoundaryIncidence D B) := by
    refine ⟨d * k - e, ?_⟩
    omega
  obtain ⟨t, ht⟩ := hboundaryEven
  omega

/-- Canonical square-order exceptional support specialization. -/
theorem binarySquare_two_le_exceptionalSignedSupport_defectBoundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q c : ℕ} (hq : 8 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hcpos : 0 < c) (hcle : c ≤ q) (hceven : Even c) :
    2 ≤ shoreBoundaryIncidence (secondOrderDefectGraph G)
      (exceptionalSignedSupport G S q) := by
  let B := exceptionalSignedSupport G S q
  have hBcard : B.card = c := hsupport
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  have hsplit : (Bᶜ : Finset V).card + B.card = q * q := by
    rw [Finset.card_compl_add_card, hcard]
  have hBc : (Bᶜ : Finset V).Nonempty :=
    Finset.card_pos.mp (by nlinarith)
  apply two_le_shoreBoundaryIncidence_of_preconnected_even
    (secondOrderDefectGraph G) hconn
      (binarySquare_regular_secondOrderDefect_degree_eq
        G hfree (by omega) hreg hcard)
      B hB hBc
  simpa [hBcard] using hceven

end

end Erdos85

#print axioms Erdos85.twice_supportedEdges_add_shoreBoundary_eq_regular_mass
#print axioms Erdos85.shoreBoundaryIncidence_pos_of_preconnected
#print axioms Erdos85.two_le_shoreBoundaryIncidence_of_preconnected_even
#print axioms
  Erdos85.binarySquare_two_le_exceptionalSignedSupport_defectBoundary
