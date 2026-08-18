import Proofs.Erdos85BinarySquareCrossTriangleLiteralMixed
import Proofs.Erdos85BinarySquareMixedOwnerComponentSplit

/-!
# Calibration of the global mixed-ambient census

The 48 triangles rooted in one all-triangle-free component are a local
contribution, not automatically the entire global multi-component census.
This file records the exact global partition needed to audit that distinction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two definitions of the ambient cross-component ordered census agree.
The apparent difference is only the cyclic order used in the component
equalities. -/
theorem multiComponentAmbientCyclicTriangles_eq_crossComponentCyclicColoredTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] :
    multiComponentAmbientCyclicTriangles G =
      crossComponentCyclicColoredTriples (secondOrderDefectGraph G) G G G := by
  classical
  let D := secondOrderDefectGraph G
  ext p
  simp only [multiComponentAmbientCyclicTriangles,
    crossComponentCyclicColoredTriples, Finset.mem_filter]
  constructor
  · rintro ⟨htri, hnot⟩
    refine ⟨htri, ?_⟩
    rintro ⟨h₁, h₂⟩
    apply hnot
    exact ⟨h₁.trans h₂, h₁⟩
  · rintro ⟨htri, hnot⟩
    refine ⟨htri, ?_⟩
    rintro ⟨h₁, h₂⟩
    apply hnot
    exact ⟨h₂, h₂.symm.trans h₁⟩

/-- **Global calibration ledger.**  If there are 480 ordered ambient
triangles in total and at most 90 ordered triangles lie wholly in one defect
component, then at least 390 ordered ambient triangles span components.
In particular the global census cannot have cardinality 288.

The numerical hypotheses are the ordered versions of 80 total triangles and
at most 15 internal triangles. -/
theorem card_multiComponentAmbient_ge_390_of_total_480_same_le_90
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (htotal : (cyclicColoredTriples G G G).card = 480)
    (hsame :
      (sameComponentCyclicColoredTriples
        (secondOrderDefectGraph G) G G G).card ≤ 90) :
    390 ≤ (multiComponentAmbientCyclicTriangles G).card := by
  have hsplit :=
    card_sameComponent_add_card_crossComponent_eq_card_cyclicColoredTriples
      (secondOrderDefectGraph G) G G G
  rw [← multiComponentAmbientCyclicTriangles_eq_crossComponentCyclicColoredTriples
    G, htotal] at hsplit
  omega

/-- Under the calibrated global ledger, `288` is impossible as the cardinality
of the whole multi-component ambient census. -/
theorem card_multiComponentAmbient_ne_288_of_total_480_same_le_90
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (htotal : (cyclicColoredTriples G G G).card = 480)
    (hsame :
      (sameComponentCyclicColoredTriples
        (secondOrderDefectGraph G) G G G).card ≤ 90) :
    (multiComponentAmbientCyclicTriangles G).card ≠ 288 := by
  have hge := card_multiComponentAmbient_ge_390_of_total_480_same_le_90
    G htotal hsame
  omega

end

end Erdos85

#print axioms
  Erdos85.multiComponentAmbientCyclicTriangles_eq_crossComponentCyclicColoredTriples
#print axioms
  Erdos85.card_multiComponentAmbient_ge_390_of_total_480_same_le_90
#print axioms
  Erdos85.card_multiComponentAmbient_ne_288_of_total_480_same_le_90
