import Proofs.Erdos85CanonicalSaturatedExceptionalTransport
import Proofs.Erdos85TwoPoleKernelImageDichotomy
import Proofs.Erdos85TwoPoleMinimumExceptionalTransportCollapse

/-!
# Canonical saturated two-pole dichotomy

The canonical empty poles at a saturated layer feed the ambient
kernel/image alternative.  The kernel horn already has weighted residual
transport; in the image horn, the resulting potential automatically has the
exceptional residual correction derived from the same poles.
-/

open SimpleGraph

namespace Erdos85

/-- Saturated canonical separator-or-exceptional-potential alternative. -/
theorem binarySquare_saturatedDeficit_emptyPole_transport_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r : ℕ} (hq : 3 ≤ q)
    (hqEven : Even q) (hr : 2 ≤ r)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hsupportCard : (exceptionalSignedSupport G S q).card = q)
    (hdisplacement :
      2 * (S.card : ℤ) - Fintype.card V = (q : ℤ) - 2 * r) :
    ∃ pole₁ pole₂ : V,
      pole₁ ∈ emptyLineCenters G S ∧
      pole₂ ∈ emptyLineCenters G S ∧ pole₁ ≠ pole₂ ∧
      ((∃ v : V → ZMod 2,
          v pole₁ + v pole₂ = 1 ∧
          ∀ center,
            (∑ z, graphEdgeIndicator
                (binaryTransportResidualGraph G hqEven hreg) center z * v z) =
              ∑ z, graphEdgeIndicator
                (triangleFreeEdgeGraph G) center z * v z) ∨
        ∃ x : V → ZMod 2,
          (G.adjMatrix (ZMod 2)).mulVec x =
              Pi.single pole₁ 1 + Pi.single pole₂ 1 ∧
          ((binaryTransportResidualGraph G hqEven hreg).adjMatrix
              (ZMod 2)).mulVec x =
            ((triangleFreeEdgeGraph G).adjMatrix (ZMod 2)).mulVec x +
              (G.adjMatrix (ZMod 2)).mulVec
                (Pi.single pole₁ 1 + Pi.single pole₂ 1) ∧
          q ≤ (f2PotentialSupport x).card ∧
          (q < (f2PotentialSupport x).card ∨
            ((∃ p y r,
                p ∈ f2PotentialSupport x ∧
                r ∈ f2PotentialSupport x ∧ p ≠ r ∧
                G.Adj pole₁ p ∧ G.Adj p y ∧ G.Adj y r ∧
                G.Adj r pole₂) ∧
              ((binaryTransportResidualGraph G hqEven hreg).adjMatrix
                    (ZMod 2)).mulVec x +
                  ((secondOrderDefectGraph G).adjMatrix
                    (ZMod 2)).mulVec x =
                ((triangleFreeEdgeGraph G).adjMatrix
                    (ZMod 2)).mulVec x + x))) := by
  obtain ⟨pole₁, pole₂, hpole₁, hpole₂, hpoles, htransport⟩ :=
    binarySquare_saturatedDeficit_exists_emptyPoles_exceptionalTransport
      G hfree hq hqEven hr hreg hcard S htri hemptyClique
      hsupportCard hdisplacement
  refine ⟨pole₁, pole₂, hpole₁, hpole₂, hpoles, ?_⟩
  rcases exists_starDistinguishing_residualTransport_or_exists_adjPotential
      G hqEven hreg pole₁ pole₂ with hsep | ⟨x, hAx⟩
  · exact Or.inl hsep
  · have hDadj : (secondOrderDefectGraph G).Adj pole₁ pole₂ :=
      hemptyClique hpole₁ hpole₂ hpoles
    have hcommonCard :
        (G.neighborFinset pole₁ ∩ G.neighborFinset pole₂).card = 0 :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hpoles).mp hDadj
    have hcommon : G.neighborFinset pole₁ ∩ G.neighborFinset pole₂ = ∅ :=
      Finset.card_eq_zero.mp hcommonCard
    have hpack := degree_le_card_f2PotentialSupport_of_twoPole
      G hfree hreg x pole₁ pole₂ hpoles hcommon hAx
    have hrefine : q < (f2PotentialSupport x).card ∨
        ((∃ p y r,
            p ∈ f2PotentialSupport x ∧
            r ∈ f2PotentialSupport x ∧ p ≠ r ∧
            G.Adj pole₁ p ∧ G.Adj p y ∧ G.Adj y r ∧
            G.Adj r pole₂) ∧
          ((binaryTransportResidualGraph G hqEven hreg).adjMatrix
                (ZMod 2)).mulVec x +
              ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec x =
            ((triangleFreeEdgeGraph G).adjMatrix (ZMod 2)).mulVec x + x) := by
      rcases lt_or_eq_of_le hpack with hlt | heq
      · exact Or.inl hlt
      · refine Or.inr ⟨?_, ?_⟩
        · exact exists_lengthFourRoute_of_twoPolePotentialSupport_card_eq
            G hfree hreg x pole₁ pole₂ hpoles hcommon hAx heq.symm
        · exact minimumTwoPole_exceptionalTransport_collapse
            G hfree hqEven hreg x pole₁ pole₂ hAx heq.symm (htransport x hAx)
    exact Or.inr ⟨x, hAx, htransport x hAx, hpack, hrefine⟩

end Erdos85

#print axioms Erdos85.binarySquare_saturatedDeficit_emptyPole_transport_dichotomy
