import Proofs.Erdos85OrderSixtyFourDefectComplementTriangleLedger
import Proofs.Erdos85BinarySquareComplementTriangleColorPartition

/-! # Global codegree ledger over a sixteen-vertex defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The directed sum of common-neighbor counts over graph edges is six times
the triangle count.  This is the codegree form of the cubic adjacency trace. -/
theorem sum_directedEdge_commonNeighbor_card_eq_six_mul_triangleCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V) :
    (∑ x : V, ∑ y ∈ H.neighborFinset x,
      ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
        6 * (adjacencyTriangleMinorFinset H).card := by
  have hcommon := trace_adjMatrix_mul_adjMatrix_sq_eq_sum_common_over_neighbors
    H H
  have htri := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount H hcard
  calc
    (∑ x : V, ∑ y ∈ H.neighborFinset x,
        ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
        Matrix.trace
          (H.adjMatrix ℤ * (H.adjMatrix ℤ * H.adjMatrix ℤ)) := hcommon.symm
    _ = Matrix.trace
          (H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ) := by
      rw [Matrix.mul_assoc]
    _ = 6 * (adjacencyTriangleMinorFinset H).card := htri

/-- On a seven-regular graph with sixteen vertices, summing the pointwise
source-common transition mass `2 + λ(x,y)` over directed defect edges gives
`224 + 6t`. -/
theorem sevenRegular_sixteen_sum_directedEdge_two_add_codegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x, H.degree x = 7) :
    (∑ x : V, ∑ y ∈ H.neighborFinset x,
      (2 + (H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
        224 + 6 * (adjacencyTriangleMinorFinset H).card := by
  have hcommon :=
    sum_directedEdge_commonNeighbor_card_eq_six_mul_triangleCount H (by omega)
  calc
    (∑ x : V, ∑ y ∈ H.neighborFinset x,
        (2 + (H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
      (∑ x : V, (2 : ℤ) * (H.neighborFinset x).card) +
        ∑ x : V, ∑ y ∈ H.neighborFinset x,
          ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) := by
      simp_rw [Finset.sum_add_distrib]
      simp
      ring_nf
    _ = 224 + 6 * (adjacencyTriangleMinorFinset H).card := by
      rw [hcommon]
      have hdeg : ∀ x, (H.neighborFinset x).card = 7 := by
        intro x
        rw [H.card_neighborFinset_eq_degree, hreg x]
      simp_rw [hdeg]
      simp [hcard]

/-- The complementary pointwise transition mass `14 - λ(x,y)`, expressed
over the integers, has directed total `1568 - 6t`. -/
theorem sevenRegular_sixteen_sum_directedEdge_fourteen_sub_codegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x, H.degree x = 7) :
    (∑ x : V, ∑ y ∈ H.neighborFinset x,
      ((14 : ℤ) - (H.neighborFinset x ∩ H.neighborFinset y).card)) =
        1568 - 6 * (adjacencyTriangleMinorFinset H).card := by
  have hcommon :=
    sum_directedEdge_commonNeighbor_card_eq_six_mul_triangleCount H (by omega)
  calc
    (∑ x : V, ∑ y ∈ H.neighborFinset x,
        ((14 : ℤ) - (H.neighborFinset x ∩ H.neighborFinset y).card)) =
      (∑ x : V, (14 : ℤ) * (H.neighborFinset x).card) -
        ∑ x : V, ∑ y ∈ H.neighborFinset x,
          ((H.neighborFinset x ∩ H.neighborFinset y).card : ℤ) := by
      simp_rw [Finset.sum_sub_distrib]
      simp
      ring_nf
    _ = 1568 - 6 * (adjacencyTriangleMinorFinset H).card := by
      rw [hcommon]
      have hdeg : ∀ x, (H.neighborFinset x).card = 7 := by
        intro x
        rw [H.card_neighborFinset_eq_degree, hreg x]
      simp_rw [hdeg]
      simp [hcard]

/-- Component-specialized package for the regular four-component order-64
branch.  Both directed transition-potential totals are now expressed using
the actual induced defect-component triangle count. -/
theorem orderSixtyFour_defectComponent_directedEdge_transitionPotential_ledger
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let H := (secondOrderDefectGraph G).induce c.supp
    ((∑ x : c.supp, ∑ y ∈ H.neighborFinset x,
        (2 + (H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
      224 + 6 * (adjacencyTriangleMinorFinset H).card) ∧
    ((∑ x : c.supp, ∑ y ∈ H.neighborFinset x,
        ((14 : ℤ) - (H.neighborFinset x ∩ H.neighborFinset y).card)) =
      1568 - 6 * (adjacencyTriangleMinorFinset H).card) := by
  let H := (secondOrderDefectGraph G).induce c.supp
  have hc := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount c
  have hcardH : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]
    exact hc
  have hregH : ∀ x, H.degree x = 7 := by
    intro x
    exact binarySquare_regular_inducedDefectComponent_degree
      G hfree (q := 8) (by omega) hreg (by decide) c x
  exact ⟨
    sevenRegular_sixteen_sum_directedEdge_two_add_codegree
      H hcardH hregH,
    sevenRegular_sixteen_sum_directedEdge_fourteen_sub_codegree
      H hcardH hregH⟩

/-- Owner-complement form of the same ledger.  Since a size-sixteen defect
component and its complement contain 112 triangles in total, the two
directed transition-potential masses are symmetric around 896 and are
controlled by the complement (equivalently, owner-union) triangle count. -/
theorem orderSixtyFour_defectComponent_transitionPotential_ownerComplement_ledger
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let H := (secondOrderDefectGraph G).induce c.supp
    ((∑ x : c.supp, ∑ y ∈ H.neighborFinset x,
        (2 + (H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
      896 - 6 * (adjacencyTriangleMinorFinset Hᶜ).card) ∧
    ((∑ x : c.supp, ∑ y ∈ H.neighborFinset x,
        ((14 : ℤ) - (H.neighborFinset x ∩ H.neighborFinset y).card)) =
      896 + 6 * (adjacencyTriangleMinorFinset Hᶜ).card) := by
  let H := (secondOrderDefectGraph G).induce c.supp
  have hled :=
    orderSixtyFour_defectComponent_directedEdge_transitionPotential_ledger
      G hfree hreg hcount c
  have hsum := orderSixtyFour_defectComponent_compl_triangleMinorCount_sum
    G hfree hreg hcount c
  have hsumZ :
      ((adjacencyTriangleMinorFinset H).card : ℤ) +
        (adjacencyTriangleMinorFinset Hᶜ).card = 112 := by
    exact_mod_cast hsum
  constructor
  · calc
      (∑ x : c.supp, ∑ y ∈ H.neighborFinset x,
          (2 + (H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
        224 + 6 * (adjacencyTriangleMinorFinset H).card := hled.1
      _ = 896 - 6 * (adjacencyTriangleMinorFinset Hᶜ).card := by omega
  · calc
      (∑ x : c.supp, ∑ y ∈ H.neighborFinset x,
          ((14 : ℤ) - (H.neighborFinset x ∩ H.neighborFinset y).card)) =
        1568 - 6 * (adjacencyTriangleMinorFinset H).card := hled.2
      _ = 896 + 6 * (adjacencyTriangleMinorFinset Hᶜ).card := by omega

/-- Exact owner-color-fiber form.  The directed source-common potential plus
the entire oriented restricted-owner triangle census is `896`; the directed
center-defect potential is `896` plus that same census.  This is the direct
interface from fourth-factor transition statistics to the no-owner-rainbow
color-pattern analysis. -/
theorem orderSixtyFour_defectComponent_transitionPotential_ownerColor_ledger
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    let H := (secondOrderDefectGraph G).induce d.supp
    let C := ∑ colors :
        (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent,
      (cyclicColoredTriples
        (restrictedComponentOwnerGraph G d colors.1)
        (restrictedComponentOwnerGraph G d colors.2.2)
        (restrictedComponentOwnerGraph G d colors.2.1)).card
    ((∑ x : d.supp, ∑ y ∈ H.neighborFinset x,
        (2 + (H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
      896 - C) ∧
    ((∑ x : d.supp, ∑ y ∈ H.neighborFinset x,
        ((14 : ℤ) - (H.neighborFinset x ∩ H.neighborFinset y).card)) =
      896 + C) := by
  let H := (secondOrderDefectGraph G).induce d.supp
  let C := ∑ colors :
      (secondOrderDefectGraph G).ConnectedComponent ×
        (secondOrderDefectGraph G).ConnectedComponent ×
        (secondOrderDefectGraph G).ConnectedComponent,
    (cyclicColoredTriples
      (restrictedComponentOwnerGraph G d colors.1)
      (restrictedComponentOwnerGraph G d colors.2.2)
      (restrictedComponentOwnerGraph G d colors.2.1)).card
  have hled :=
    orderSixtyFour_defectComponent_directedEdge_transitionPotential_ledger
      G hfree hreg hcount d
  have howner :=
    orderSixtyFour_restrictedOwner_color_defect_orientedTriangleLedger
      G hfree hreg hcount d
  have hownerZ :
      (C : ℤ) + 6 * (adjacencyTriangleMinorFinset H).card = 672 := by
    exact_mod_cast howner
  constructor
  · calc
      (∑ x : d.supp, ∑ y ∈ H.neighborFinset x,
          (2 + (H.neighborFinset x ∩ H.neighborFinset y).card : ℤ)) =
        224 + 6 * (adjacencyTriangleMinorFinset H).card := hled.1
      _ = 896 - C := by omega
  · calc
      (∑ x : d.supp, ∑ y ∈ H.neighborFinset x,
          ((14 : ℤ) - (H.neighborFinset x ∩ H.neighborFinset y).card)) =
        1568 - 6 * (adjacencyTriangleMinorFinset H).card := hled.2
      _ = 896 + C := by omega

end

end Erdos85
