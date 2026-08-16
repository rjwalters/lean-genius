import Proofs.Erdos85OrderFortyNineThreeHighDistOneCaseSplit
import Proofs.Erdos85OrderFortyNineThreeHighScoutDichotomyTerminal
import Proofs.Erdos85OrderFortyNineThreeHighDistOneNoCoincidenceScoutTerminal

/-! # Exact terminal interfaces for the `b1/c1/c2` distance-one cases -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The normal-form data shared by all three distinct-root cases. -/
structure ThreeHighDistinctRootBase (G : SimpleGraph (Fin 49))
    [DecidableRel G.Adj] where
  v1 : Fin 49
  v2 : Fin 49
  v3 : Fin 49
  u12 : Fin 49
  u13 : Fin 49
  u23 : Fin 49
  hHigh : orderFortyNineHighVertices G = {v1, v2, v3}
  hv1 : G.degree v1 = 8
  hv2 : G.degree v2 = 8
  hv3 : G.degree v3 = 8
  h12 : v1 ≠ v2
  h13 : v1 ≠ v3
  h23 : v2 ≠ v3
  hu12 : G.neighborFinset v1 ∩ G.neighborFinset v2 = {u12}
  hu13 : G.neighborFinset v1 ∩ G.neighborFinset v3 = {u13}
  hu23 : G.neighborFinset v2 ∩ G.neighborFinset v3 = {u23}
  hu1213 : u12 ≠ u13
  hu1223 : u12 ≠ u23
  hu1323 : u13 ≠ u23

/-- The two canonical sibling witnesses shared by `b1`, `c1`, and `c2`. -/
def ThreeHighDistOneSiblingData (G : SimpleGraph (Fin 49))
    [DecidableRel G.Adj]
    (D : ThreeHighDistinctRootBase G) (x2 x3 : Fin 49) : Prop :=
  G.degree x2 = 7 ∧ G.degree x3 = 7 ∧
  G.Adj D.u12 x2 ∧ G.Adj D.v2 x2 ∧
  G.Adj D.u13 x3 ∧ G.Adj D.v3 x3

/-- Durable exclusion obligation for the paired/no-coincidence `b1` case. -/
def ThreeHighDistOneB1Excluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    ∀ D : ThreeHighDistinctRootBase G,
    ¬ ∃ x2 x3, ThreeHighDistOneSiblingData G D x2 x3 ∧
      G.Adj D.u12 D.u13 ∧ x2 ≠ D.u23 ∧ x3 ≠ D.u23

/-- Durable exclusion obligation for the unpaired/no-coincidence `c1` case. -/
def ThreeHighDistOneC1Excluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    ∀ D : ThreeHighDistinctRootBase G,
    ¬ ∃ x2 x3, ThreeHighDistOneSiblingData G D x2 x3 ∧
      ¬ G.Adj D.u12 D.u13 ∧ x2 ≠ D.u23 ∧ x3 ≠ D.u23

/-- Exact graph-normalization obligation for the paired/no-coincidence scout. -/
def ThreeHighDistOneB1AlignedCover : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    ∀ D : ThreeHighDistinctRootBase G,
    (∃ x2 x3, ThreeHighDistOneSiblingData G D x2 x3 ∧
      G.Adj D.u12 D.u13 ∧ x2 ≠ D.u23 ∧ x3 ≠ D.u23) →
    ∃ E : Equiv.Perm (Fin 49),
      ThreeHighDistOneB1ScoutAlignedLabeling G E

/-- Exact graph-normalization obligation for the unpaired/no-coincidence scout. -/
def ThreeHighDistOneC1AlignedCover : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    ∀ D : ThreeHighDistinctRootBase G,
    (∃ x2 x3, ThreeHighDistOneSiblingData G D x2 x3 ∧
      ¬ G.Adj D.u12 D.u13 ∧ x2 ≠ D.u23 ∧ x3 ≠ D.u23) →
    ∃ E : Equiv.Perm (Fin 49),
      ThreeHighDistOneC1ScoutAlignedLabeling G E

theorem threeHighDistOneB1Excluded_of_alignedCover_lrat
    (hcover : ThreeHighDistOneB1AlignedCover)
    (certificate : ThreeHighDistOneB1ScoutCertificate) :
    ThreeHighDistOneB1Excluded := by
  intro G _ _ _ hfree hmin D hcase
  exact false_of_exists_threeHighDistOneB1ScoutAlignedLabeling G hfree
    (hcover G inferInstance inferInstance inferInstance hfree hmin D hcase)
    certificate

theorem threeHighDistOneC1Excluded_of_alignedCover_lrat
    (hcover : ThreeHighDistOneC1AlignedCover)
    (certificate : ThreeHighDistOneC1ScoutCertificate) :
    ThreeHighDistOneC1Excluded := by
  intro G _ _ _ hfree hmin D hcase
  exact false_of_exists_threeHighDistOneC1ScoutAlignedLabeling G hfree
    (hcover G inferInstance inferInstance inferInstance hfree hmin D hcase)
    certificate

/-- Exact normalization obligation for the surviving unpaired/one-coincidence
`c2` case.  The disjunction allows swapping the second and third highs. -/
def ThreeHighDistOneC2AlignedCover : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    ∀ D : ThreeHighDistinctRootBase G,
    (∃ x2 x3, ThreeHighDistOneSiblingData G D x2 x3 ∧
      ¬ G.Adj D.u12 D.u13 ∧
      ((x2 = D.u23 ∧ x3 ≠ D.u23) ∨
       (x2 ≠ D.u23 ∧ x3 = D.u23))) →
    ∃ E : Equiv.Perm (Fin 49),
      ThreeHighDistOneC2ScoutAlignedLabeling G E

/-- The two dead-case endpoints and the surviving-case normalization together
prove the complete distinct-root aligned cover consumed by the H3 capstone. -/
theorem threeHighDistinctRootAlignedCover_of_b1_c1_c2
    (hb1 : ThreeHighDistOneB1Excluded)
    (hc1 : ThreeHighDistOneC1Excluded)
    (hc2 : ThreeHighDistOneC2AlignedCover) :
    ThreeHighDistinctRootAlignedCover := by
  intro G _ _ _ hfree hmin v1 v2 v3 u12 u13 u23 hHigh
    hv1 hv2 hv3 h12 h13 h23 hu12 hu13 hu23 hu1213 hu1223 hu1323
  let D : ThreeHighDistinctRootBase G :=
    ⟨v1, v2, v3, u12, u13, u23, hHigh, hv1, hv2, hv3,
      h12, h13, h23, hu12, hu13, hu23, hu1213, hu1223, hu1323⟩
  have hu12mem : u12 ∈ G.neighborFinset v1 ∩ G.neighborFinset v2 := by
    simp [hu12]
  have hu13mem : u13 ∈ G.neighborFinset v1 ∩ G.neighborFinset v3 := by
    simp [hu13]
  have hu23mem : u23 ∈ G.neighborFinset v2 ∩ G.neighborFinset v3 := by
    simp [hu23]
  have hu12_1 : G.Adj u12 v1 :=
    ((G.mem_neighborFinset v1 u12).mp (Finset.mem_inter.mp hu12mem).1).symm
  have hu12_2 : G.Adj u12 v2 :=
    ((G.mem_neighborFinset v2 u12).mp (Finset.mem_inter.mp hu12mem).2).symm
  have hu13_1 : G.Adj u13 v1 :=
    ((G.mem_neighborFinset v1 u13).mp (Finset.mem_inter.mp hu13mem).1).symm
  have hu13_3 : G.Adj u13 v3 :=
    ((G.mem_neighborFinset v3 u13).mp (Finset.mem_inter.mp hu13mem).2).symm
  have hu23_2 : G.Adj u23 v2 :=
    ((G.mem_neighborFinset v2 u23).mp (Finset.mem_inter.mp hu23mem).1).symm
  have hu23_3 : G.Adj u23 v3 :=
    ((G.mem_neighborFinset v3 u23).mp (Finset.mem_inter.mp hu23mem).2).symm
  obtain ⟨x2, x3, hx2deg, hx3deg, hx2u12, hx2v2,
      hx3u13, hx3v3, hcase⟩ :=
    orderFortyNine_threeHigh_distinctRoot_b1_c1_c2_split
      G hfree hmin (Fintype.card_fin 49) hv1 hv2 hv3 h12 h13
      hu1213 hu1223 hu1323 hu12_1 hu12_2 hu13_1 hu13_3 hu23_2 hu23_3
  have hsiblings : ThreeHighDistOneSiblingData G D x2 x3 :=
    ⟨hx2deg, hx3deg, hx2u12, hx2v2, hx3u13, hx3v3⟩
  rcases hcase with hb1case | hc2case | hc1case
  · exact False.elim (hb1 G inferInstance inferInstance inferInstance
      hfree hmin D ⟨x2, x3, hsiblings, hb1case.1,
        hb1case.2.1, hb1case.2.2⟩)
  · exact hc2 G inferInstance inferInstance inferInstance hfree hmin D
      ⟨x2, x3, hsiblings, hc2case.1, hc2case.2⟩
  · exact False.elim (hc1 G inferInstance inferInstance inferInstance
      hfree hmin D ⟨x2, x3, hsiblings, hc1case.1,
        hc1case.2.1, hc1case.2.2⟩)

end

end Erdos85
