import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveSixthOrbitElementRealization

/-! # The 768-to-48 semantic quotient of the adaptive sixth frontier -/

namespace Erdos85

open SimpleGraph

/-- Every live adaptive sixth cell with an admissible graph realization has
an admissible realization of one of the forty-eight canonical cells.  This
is graph-semantic: it does not assume an automorphism of DIMACS auxiliary
variables. -/
theorem orderFortyNineAdaptiveSixth_exists_canonical_semantic_realization
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (c : OrderFortyNineAdaptiveSixthCell) (d : Nat)
    (hlive : orderFortyNineThreeHighB1AdaptiveSixthResidual
      c.li c.ri c.ai c.bi c.ci c.di c.ei = true)
    (hfree : ¬ containsC4 (Fin 49) G)
    (hdegree : ∀ v, d ≤ G.degree v)
    (hreal : OrderFortyNineRealizesAdaptiveSixthCell G
      c.li c.ri c.ai c.bi c.ci c.di c.ei) :
    ∃ k : Fin 16,
      orderFortyNineAdaptiveSixthCanonicalRepresentative
          (orderFortyNineAdaptiveSixthOrbitElement k c) = true ∧
        let H := orderFortyNineAdaptiveSixthOrbitGraph k G
        let t := orderFortyNineAdaptiveSixthOrbitElement k c
        letI : DecidableRel H.Adj := Classical.decRel _
        ¬ containsC4 (Fin 49) H ∧
          (∀ v, d ≤ H.degree v) ∧
          OrderFortyNineRealizesAdaptiveSixthCell H
            t.li t.ri t.ai t.bi t.ci t.di t.ei := by
  obtain ⟨k, hk⟩ :=
    orderFortyNineAdaptiveSixthResidual_has_normalForm c hlive
  refine ⟨k, hk, ?_⟩
  exact orderFortyNineAdaptiveSixthOrbitElement_semantic_transport
    G k c d hfree hdegree hreal

end Erdos85
