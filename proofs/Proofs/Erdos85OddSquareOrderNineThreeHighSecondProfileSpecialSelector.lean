import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileRowCover

/-!
# Branch-four special-point selector at order 81

The row-cover development proves that the total special-defect mass over the
24 unmarked bin-one points is six in the four-edge high-root branch.  This
file records the direct pointwise consequence needed by the full-fiber price
route: at least one such point has positive special defect, hence its mixed
residual target is strictly larger than the branch-three baseline 27.
-/

namespace Erdos85

/-- Arithmetic selection terminal for the branch-four cover route.  If the
total special mass is six, then an aggregate cover-price bound strictly below
`27` per positive-special point plus that mass forces a positive-special
point whose individual price is strictly below `27 + special`. -/
theorem exists_positive_special_price_lt_target_of_sum_lt
    {α : Type*} [DecidableEq α]
    (U : Finset α) (special price : α → ℕ)
    (hspecial : ∑ b ∈ U, special b = 6)
    (hprice :
      ∑ b ∈ U.filter (fun b => 0 < special b), price b <
        27 * (U.filter fun b => 0 < special b).card + 6) :
    ∃ b ∈ U, 0 < special b ∧ price b < 27 + special b := by
  classical
  let P := U.filter fun b => 0 < special b
  have hPsub : P ⊆ U := Finset.filter_subset _ _
  have hspecialP : ∑ b ∈ P, special b = 6 := by
    rw [← hspecial]
    apply Finset.sum_subset hPsub
    intro b hbU hbNotP
    simp only [P, Finset.mem_filter, hbU, true_and, not_lt] at hbNotP
    omega
  by_contra hnot
  push Not at hnot
  have hle : (∑ b ∈ P, (27 + special b)) ≤ (∑ b ∈ P, price b) := by
    apply Finset.sum_le_sum
    intro b hbP
    have hbParts := Finset.mem_filter.mp hbP
    exact hnot b hbParts.1 hbParts.2
  have hleft : (∑ b ∈ P, (27 + special b)) = (27 * P.card + 6) := by
    rw [Finset.sum_add_distrib, hspecialP]
    simp [Nat.mul_comm]
  change (∑ b ∈ P, price b) < 27 * P.card + 6 at hprice
  omega

/-- Well-founded selector for a load-descent proof.  If every positive-
special point lacking the desired property produces another positive-special
point of strictly smaller natural-number load, then some positive-special
point has the property.  This packages the prospective local form of the
minimum-load branch-four argument. -/
theorem exists_good_positive_special_of_strict_load_descent
    {α : Type*} [DecidableEq α]
    (U : Finset α) (special load : α → ℕ) (Good : α → Prop)
    [DecidablePred Good]
    (hnonempty : ∃ p ∈ U, 0 < special p)
    (hdescent : ∀ p ∈ U, 0 < special p → ¬ Good p →
      ∃ q ∈ U, 0 < special q ∧ load q < load p) :
    ∃ p ∈ U, 0 < special p ∧ Good p := by
  classical
  let P := U.filter fun p => 0 < special p
  obtain ⟨p0, hp0U, hp0Special⟩ := hnonempty
  have hPnonempty : P.Nonempty :=
    ⟨p0, Finset.mem_filter.mpr ⟨hp0U, hp0Special⟩⟩
  obtain ⟨p, hpP, hpmin⟩ := Finset.exists_min_image P load hPnonempty
  have hpParts := Finset.mem_filter.mp hpP
  by_cases hpGood : Good p
  · exact ⟨p, hpParts.1, hpParts.2, hpGood⟩
  · obtain ⟨q, hqU, hqSpecial, hqLoad⟩ :=
      hdescent p hpParts.1 hpParts.2 hpGood
    have hpLe := hpmin q (Finset.mem_filter.mpr ⟨hqU, hqSpecial⟩)
    omega

/-- In the four-edge high-root branch, some unmarked bin-one point is defect
adjacent to a special B0 row.  This is the formal existence half of the six
global puncture-miss selector; the separate mixed-column theorem upgrades its
residual-row count to `27 + specialDefects`. -/
theorem squareOrderNine_threeHigh_secondProfile_exists_positive_specialDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hbranch : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    ∃ b ∈ U1, 0 < (D.neighborFinset b ∩ S).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  have hmass :=
    squareOrderNine_threeHigh_secondProfile_special_defect_mass_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmass
  rcases hmass with hthree | hfour
  · omega
  · have hsum :
        (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) = 6 := hfour.2
    have hsumPos :
        0 < ∑ b ∈ U1, (D.neighborFinset b ∩ S).card := by omega
    exact (Finset.sum_pos_iff
      (s := U1) (f := fun b => (D.neighborFinset b ∩ S).card)).mp hsumPos

/-- A positive-special point may be chosen to minimize any natural-number
load on the positive-special locus.  Instantiating `load` with the exact
mutual trace-eligibility fiber load gives the formal selection half of the
minimum-load branch-four target (13am). -/
theorem squareOrderNine_threeHigh_secondProfile_exists_minimal_positive_specialDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hbranch : (G.induce (G.neighborSet x)).edgeFinset.card = 4)
    (load : V → ℕ) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    ∃ b ∈ U1, 0 < (D.neighborFinset b ∩ S).card ∧
      ∀ c ∈ U1, 0 < (D.neighborFinset c ∩ S).card → load b ≤ load c := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  let P := U1.filter fun b => 0 < (D.neighborFinset b ∩ S).card
  obtain ⟨b0, hb0U1, hb0Special⟩ :=
    squareOrderNine_threeHigh_secondProfile_exists_positive_specialDefect
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hbranch
  have hPnonempty : P.Nonempty :=
    ⟨b0, Finset.mem_filter.mpr ⟨hb0U1, hb0Special⟩⟩
  obtain ⟨b, hbP, hbmin⟩ := Finset.exists_min_image P load hPnonempty
  have hbParts := Finset.mem_filter.mp hbP
  refine ⟨b, hbParts.1, hbParts.2, ?_⟩
  intro c hcU1 hcSpecial
  exact hbmin c (Finset.mem_filter.mpr ⟨hcU1, hcSpecial⟩)

/-- The positive special point has at least 28 ordinary residual-resolved
rows.  This packages candidate existence together with the mixed-column law,
so the branch-four price route can use the high target directly. -/
theorem squareOrderNine_threeHigh_secondProfile_exists_residualRows_card_ge_twentyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hbranch : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    ∃ b ∈ U1, 28 ≤
      (T.filter fun t =>
        (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).Nonempty)).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  obtain ⟨b, hbU1, hbSpecial⟩ :=
    squareOrderNine_threeHigh_secondProfile_exists_positive_specialDefect
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hbranch
  have hmixed :=
    squareOrderNine_threeHigh_secondProfile_unmarked_mixed_column_counts
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hbU1
  dsimp only at hmixed
  rcases hmixed with ⟨_hdefect, _hcore, hresidual⟩
  refine ⟨b, hbU1, ?_⟩
  omega

/-- Aggregate form of the branch-four target ledger.  Across all 24
unmarked bin-one points, the ordinary residual-resolved row counts have
total mass `24 * 27 + 6 = 654`.  This is the exact global threshold against
which a family of full-fiber cover prices must be compared in order to
obtain the six-special-point alternative. -/
theorem squareOrderNine_threeHigh_secondProfile_residualRows_total_eq_654
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (hbranch : (G.induce (G.neighborSet x)).edgeFinset.card = 4) :
    let B := squareOrderNineLowIncidenceBin G
    let S := G.neighborFinset x ∩ B 0
    let T := B 0 \ S
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    ∑ b ∈ U1, (T.filter fun t =>
      (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).Nonempty)).card = 654 := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let S := G.neighborFinset x ∩ B 0
  let T := B 0 \ S
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hMcard :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hU1card : U1.card = 24 := by
    rw [Finset.card_sdiff_of_subset hMsub, hmarked.1, hMcard]
  have hmass :=
    squareOrderNine_threeHigh_secondProfile_special_defect_mass_dichotomy
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmass
  have hspecial : (∑ b ∈ U1, (D.neighborFinset b ∩ S).card) = 6 := by
    rcases hmass with hthree | hfour
    · omega
    · exact hfour.2
  calc
    (∑ b ∈ U1, (T.filter fun t =>
        (((G.neighborFinset t ∩ T) ∩ G.neighborFinset b).Nonempty)).card) =
        ∑ b ∈ U1, (27 + (D.neighborFinset b ∩ S).card) := by
      apply Finset.sum_congr rfl
      intro b hbU1
      have hmixed :=
        squareOrderNine_threeHigh_secondProfile_unmarked_mixed_column_counts
          G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 hx hbU1
      dsimp only at hmixed
      exact hmixed.2.2
    _ = 27 * U1.card + ∑ b ∈ U1, (D.neighborFinset b ∩ S).card := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ = 654 := by omega

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exists_positive_specialDefect
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exists_minimal_positive_specialDefect
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_exists_residualRows_card_ge_twentyEight
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_residualRows_total_eq_654
#print axioms Erdos85.exists_positive_special_price_lt_target_of_sum_lt
#print axioms Erdos85.exists_good_positive_special_of_strict_load_descent
