import Proofs.Erdos85OrderFortyNineThreeHighDistOneC2ScoutTerminal
import Proofs.Erdos85OrderFortyNineThreeHighDistTwoScoutTerminal

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

/-- The still-structural obligation after the common-root branch has been
closed by the distance-two scout. -/
def ThreeHighDistinctRootExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    ∀ v1 v2 v3 u12 u13 u23 : Fin 49,
    orderFortyNineHighVertices G = {v1, v2, v3} →
    G.degree v1 = 8 → G.degree v2 = 8 → G.degree v3 = 8 →
    v1 ≠ v2 → v1 ≠ v3 → v2 ≠ v3 →
    G.neighborFinset v1 ∩ G.neighborFinset v2 = {u12} →
    G.neighborFinset v1 ∩ G.neighborFinset v3 = {u13} →
    G.neighborFinset v2 ∩ G.neighborFinset v3 = {u23} →
    u12 ≠ u13 → u12 ≠ u23 → u13 ≠ u23 → False

/-- The verified distance-two terminal removes the equal-root half of the
canonical three-high normal form.  Thus a consumer for only the distinct-root
half suffices to discharge the entire stratum. -/
theorem orderFortyNineStratumExcluded_three_of_distinctRoot_and_distTwo_lrat
    (hdistinct : ThreeHighDistinctRootExcluded)
    (distTwoProof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (distTwoChecked : Std.Tactic.BVDecide.LRAT.check distTwoProof
      orderFortyNineGeneratedThreeHighDistTwoScoutCnf) :
    OrderFortyNineStratumExcluded 3 := by
  intro G _ _ _ hfree hmin hHighCard
  obtain ⟨v1, v2, v3, u12, u13, u23, hHigh,
      hv1, hv2, hv3, h12, h13, h23, hu12, hu13, hu23, hroots⟩ :=
    orderFortyNine_three_high_normal_form
      G hfree hmin (Fintype.card_fin 49) hHighCard
  rcases hroots with ⟨h1213, h1323⟩ | hdistinctRoots
  · have hu12mem : u12 ∈
        G.neighborFinset v1 ∩ G.neighborFinset v2 := by
      simp [hu12]
    have hu13mem : u13 ∈
        G.neighborFinset v1 ∩ G.neighborFinset v3 := by
      simp [hu13]
    have hs1 : G.Adj u12 v1 := by
      exact (G.mem_neighborFinset v1 u12).mp
        (Finset.mem_inter.mp hu12mem).1 |>.symm
    have hs2 : G.Adj u12 v2 := by
      exact (G.mem_neighborFinset v2 u12).mp
        (Finset.mem_inter.mp hu12mem).2 |>.symm
    have hs3 : G.Adj u12 v3 := by
      have : G.Adj u13 v3 :=
        (G.mem_neighborFinset v3 u13).mp
          (Finset.mem_inter.mp hu13mem).2 |>.symm
      simpa [h1213] using this
    have hsLow : G.degree u12 = 7 :=
      orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin (Fintype.card_fin 49) hv1 hs1.symm
    exact false_of_orderFortyNine_threeHighDistTwo_lrat
      G hfree hmin hv1 hv2 hv3 hsLow h12 h13 h23
      hs1 hs2 hs3 hHigh distTwoProof distTwoChecked
  · exact hdistinct G inferInstance inferInstance inferInstance
      hfree hmin v1 v2 v3 u12 u13 u23 hHigh hv1 hv2 hv3
      h12 h13 h23 hu12 hu13 hu23
      hdistinctRoots.1 hdistinctRoots.2.1 hdistinctRoots.2.2

end Erdos85
