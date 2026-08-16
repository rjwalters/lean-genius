import Proofs.Erdos85OrderFortyNineThreeHighDistOneC2ScoutTerminal

/-!
# Combined terminal for the two three-high scout geometries

The graph analysis splits the three-high stratum into the common-root
(`dist2`) geometry and the surviving distinct-root (`dist1_c2`) geometry.
This file is the single certificate-backed consumer of that dichotomy.
-/

namespace Erdos85

open SimpleGraph

/-- The two independently checked certificates needed after the graph-side
three-high geometry dichotomy has been normalized. -/
structure ThreeHighScoutCertificateBundle where
  distTwoProof : Array Std.Tactic.BVDecide.LRAT.IntAction
  distTwoChecked : Std.Tactic.BVDecide.LRAT.check distTwoProof
    orderFortyNineGeneratedThreeHighDistTwoScoutCnf
  distOneC2 : ThreeHighDistOneC2ScoutCertificate

/-- A normalized three-high candidate lies in one of the two exact scout
coordinate systems. -/
def ThreeHighScoutAlignedDichotomy
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] : Prop :=
  (∃ E : Equiv.Perm (Fin 49), ThreeHighDistTwoScoutAlignedLabeling G E) ∨
  (∃ E : Equiv.Perm (Fin 49), ThreeHighDistOneC2ScoutAlignedLabeling G E)

/-- Once the graph-side dichotomy and both LRAT checks are available, no
three-high order-49 candidate survives. -/
theorem false_of_threeHighScoutAlignedDichotomy
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hdichotomy : ThreeHighScoutAlignedDichotomy G)
    (certificates : ThreeHighScoutCertificateBundle) : False := by
  rcases hdichotomy with ⟨E, hE⟩ | hdistOne
  · exact false_of_threeHighDistTwoScoutAlignedLabeling_lrat
      G hfree E hE certificates.distTwoProof certificates.distTwoChecked
  · exact false_of_exists_threeHighDistOneC2ScoutAlignedLabeling
      G hfree hdistOne certificates.distOneC2

/-- Graph-side normalization obligation for the complete three-high stratum.
It deliberately contains no certificate data. -/
def ThreeHighScoutDichotomyCover : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 3 →
    ThreeHighScoutAlignedDichotomy G

/-- The exact graph normalization cover plus the two checked scout
certificates discharge the `h = 3` input of the order-49 strata capstone. -/
theorem orderFortyNineStratumExcluded_three_of_scoutDichotomy
    (hcover : ThreeHighScoutDichotomyCover)
    (certificates : ThreeHighScoutCertificateBundle) :
    OrderFortyNineStratumExcluded 3 := by
  intro G _ _ _ hfree hmin hHigh
  exact false_of_threeHighScoutAlignedDichotomy G hfree
    (hcover G inferInstance inferInstance inferInstance hfree hmin hHigh)
    certificates

end Erdos85
