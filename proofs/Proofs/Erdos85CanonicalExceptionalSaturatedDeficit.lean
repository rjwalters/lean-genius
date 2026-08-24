import Proofs.Erdos85CanonicalExceptionalMassBalance

/-!
# Saturated exceptional deficit populations

At the saturated endpoint the exceptional support has size `q`.  If its
signed mass is `q-2r`, then the canonical empty population is exactly `r`
and the full population is `q-r`.  Thus every layer `r ≥ 2` supplies two
distinct empty poles automatically.
-/

open SimpleGraph

namespace Erdos85

/-- Elementary population recovery from total size and signed difference. -/
theorem full_empty_populations_of_saturated_deficit
    {full empty q r : ℕ}
    (hsum : full + empty = q)
    (hdiff : (full : ℤ) - empty = (q : ℤ) - 2 * r) :
    empty = r ∧ full = q - r := by
  constructor <;> omega

/-- In a saturated canonical exceptional support with deficit parameter
`r ≥ 2`, two distinct empty poles exist and their indicator is fixed by the
second-order defect matrix. -/
theorem binarySquare_saturatedDeficit_exists_emptyPoles_mulVec_eq_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r : ℕ} (hq : 3 ≤ q) (hr : 2 ≤ r)
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
      ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec
          (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
        Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  have hsum : (fullLineCenters G S q).card +
      (emptyLineCenters G S).card = q := by
    rw [← exceptionalSignedSupport_card_eq_full_add_empty G S (by omega),
      hsupportCard]
  have hdiff : ((fullLineCenters G S q).card : ℤ) -
      (emptyLineCenters G S).card = (q : ℤ) - 2 * r := by
    rw [fullLineCenters_card_sub_emptyLineCenters_card_eq_cutDisplacement
      G (by omega) hreg S htri, hdisplacement]
  have hpop := full_empty_populations_of_saturated_deficit hsum hdiff
  have hemptyCard : (emptyLineCenters G S).card = r := hpop.1
  have htwo : 1 < (emptyLineCenters G S).card := by omega
  obtain ⟨pole₁, hpole₁, pole₂, hpole₂, hpoles⟩ :=
    Finset.one_lt_card.mp htwo
  refine ⟨pole₁, pole₂, hpole₁, hpole₂, hpoles, ?_⟩
  exact binarySquare_exceptionalSignedSupport_emptyCenters_mulVec_eq_self
    G hfree hq hreg hcard S hemptyClique hsupportCard
    pole₁ pole₂ hpole₁ hpole₂ hpoles

end Erdos85

#print axioms Erdos85.full_empty_populations_of_saturated_deficit
#print axioms Erdos85.binarySquare_saturatedDeficit_exists_emptyPoles_mulVec_eq_self
