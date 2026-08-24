import Proofs.Erdos85CanonicalExceptionalSaturatedDeficit
import Proofs.Erdos85TwoPoleExceptionalLineCorrection

/-!
# Canonical saturated exceptional transport

At a saturated exceptional layer `r ≥ 2`, the canonical population equations
produce two empty poles and empty-core saturation proves their defect pair
indicator fixed.  Consequently every potential with that two-pole syndrome
satisfies the exceptional residual-transport identity, without a separate
`Dh=h` assumption.
-/

open SimpleGraph

namespace Erdos85

/-- Canonical saturated form of exceptional-line transport `(73rnz_bs)`.
Both the poles and their defect-fixed property are derived. -/
theorem binarySquare_saturatedDeficit_exists_emptyPoles_exceptionalTransport
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
      ∀ x : V → ZMod 2,
        (G.adjMatrix (ZMod 2)).mulVec x =
            Pi.single pole₁ 1 + Pi.single pole₂ 1 →
          ((binaryTransportResidualGraph G hqEven hreg).adjMatrix
              (ZMod 2)).mulVec x =
            ((triangleFreeEdgeGraph G).adjMatrix (ZMod 2)).mulVec x +
              (G.adjMatrix (ZMod 2)).mulVec
                (Pi.single pole₁ 1 + Pi.single pole₂ 1) := by
  obtain ⟨pole₁, pole₂, hpole₁, hpole₂, hpoles, hfixed⟩ :=
    binarySquare_saturatedDeficit_exists_emptyPoles_mulVec_eq_self
      G hfree hq hr hreg hcard S htri hemptyClique
      hsupportCard hdisplacement
  refine ⟨pole₁, pole₂, hpole₁, hpole₂, hpoles, ?_⟩
  intro x hAx
  exact binaryTransportResidualGraph_mulVec_eq_triangle_add_poleLines
    G hfree hqEven hreg x pole₁ pole₂ hAx hfixed

end Erdos85

#print axioms Erdos85.binarySquare_saturatedDeficit_exists_emptyPoles_exceptionalTransport
