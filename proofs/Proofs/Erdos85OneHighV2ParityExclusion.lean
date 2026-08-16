import Proofs.Erdos85OneHighV2ParityCover

/-!
# Certificate terminal for the parity-filtered one-high inventory

The graph-side reduction leaves one structural statement: the canonical
miss-label function is constant on every internal matching edge.  This file
packages that statement once and connects the resulting 87-row orbit cover
directly to the existing checked-UNSAT consumer.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The sole graph-side hypothesis left by the current one-high parity
reduction, packaged independently of any finite inventory or certificate. -/
def OneHighNonconstantSourcesEmpty : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (p : OneHighRawV2Presentation G hfree v),
      nonconstantMatchingEdgeSources
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv p.external_empty
          p.outer_degree p.mate p.mate_adj) = ∅

/-- A parity-capacity certificate bank excludes the complete one-high
stratum once the remaining graph-side constancy statement is supplied. -/
theorem orderFortyNineStratumExcluded_one_of_parityCapacity_checked
    (hempty : OneHighNonconstantSourcesEmpty)
    (hchecked : ∀ (profile : Fin 5) table,
      table ∈ oneHighParityCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 := by
  apply orderFortyNineStratumExcluded_one_of_rawV2OrbitCover
    (oneHighRawV2OrbitCover_parityCapacity_of_nonconstantSources_empty_checked
      hempty)
  exact hchecked

/-- Version parametrized by a capacity cover.  This separates the logical
parity reduction from the executable proof of the capacity inventory. -/
theorem orderFortyNineStratumExcluded_one_of_parityCapacity
    (hcapacity : OneHighRawV2OrbitCover oneHighCapacityInventoryTables)
    (hempty : OneHighNonconstantSourcesEmpty)
    (hchecked : ∀ (profile : Fin 5) table,
      table ∈ oneHighParityCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 := by
  apply orderFortyNineStratumExcluded_one_of_rawV2OrbitCover
    (oneHighRawV2OrbitCover_parityCapacity_of_nonconstantSources_empty
      hcapacity hempty)
  exact hchecked

end

end Erdos85
