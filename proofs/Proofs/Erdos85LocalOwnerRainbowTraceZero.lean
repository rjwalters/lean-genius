import Proofs.Erdos85LocalOwnerCubePatternSplit
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus
import Proofs.Erdos85OrderSixtyFourRoutingCensusDichotomy

/-! # No local owner rainbow makes distinct-color traces vanish -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A distinct-color restricted-owner cubic trace is zero whenever the
source component has no routing-owner rainbow in those colors. -/
theorem trace_three_restrictedOwnerMatrices_eq_zero_of_noRainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hno : ¬ routingOwnerRainbow G source a b c) :
    Matrix.trace
      ((restrictedComponentOwnerGraph G source a).adjMatrix ℤ *
       (restrictedComponentOwnerGraph G source b).adjMatrix ℤ *
       (restrictedComponentOwnerGraph G source c).adjMatrix ℤ) = 0 := by
  classical
  let A := restrictedComponentOwnerGraph G source a
  let B := restrictedComponentOwnerGraph G source b
  let C := restrictedComponentOwnerGraph G source c
  rw [trace_three_adjMatrices_eq_card_cyclicColoredTriples A B C]
  have hempty : cyclicColoredTriples A B C = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    have hp' := (Finset.mem_filter.mp hp).2
    apply hno
    refine ⟨p.1, p.2.2, p.2.1,
      (A.ne_of_adj hp'.1), (B.ne_of_adj hp'.2.1),
      (C.ne_of_adj hp'.2.2), ?_, ?_, ?_⟩
    · exact hp'.1
    · exact hp'.2.1
    · exact hp'.2.2
  rw [hempty]
  simp

/-- Consequently the entire pairwise-distinct summand in the local cubic
pattern split vanishes under the componentwise no-rainbow hypothesis. -/
theorem sum_rainbow_restrictedOwner_traces_eq_zero_of_noRainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source : (secondOrderDefectGraph G).ConnectedComponent)
    (hno : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      ¬ routingOwnerRainbow G source a b c) :
    let A := fun owner : (secondOrderDefectGraph G).ConnectedComponent =>
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ
    let tr := fun i j k => Matrix.trace (A i * A j * A k)
    (∑ k, ∑ j, ∑ i,
      if ownerTripleRainbow i j k then tr i j k else 0) = 0 := by
  classical
  dsimp
  apply Finset.sum_eq_zero
  intro k _hk
  apply Finset.sum_eq_zero
  intro j _hj
  apply Finset.sum_eq_zero
  intro i _hi
  by_cases hr : ownerTripleRainbow i j k
  · rw [if_pos hr]
    exact trace_three_restrictedOwnerMatrices_eq_zero_of_noRainbow
      G source i j k (hno i j k hr.1 hr.2.1 hr.2.2)
  · rw [if_neg hr]

end

end Erdos85
