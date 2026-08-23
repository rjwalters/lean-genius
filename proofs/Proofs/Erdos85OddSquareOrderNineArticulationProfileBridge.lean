import Proofs.Erdos85OddSquareOrderNineArticulationGraphBridge
import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileBinZeroDefectTypes
import Proofs.Erdos85BranchDeficitSymmetry
import Proofs.Erdos85OddSquareOrderNineArticulationArithmetic

/-! # Actual-profile inputs for the q = 9 articulation bridge

Node: B.3 / GAP B-CLASSIFY.  This file specializes the abstract deleted-owner
articulation machinery to the `(53,27,0,1,0)` three-high profile.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the second three-high profile, every defect neighbor of the unique
bin-three owner is a bin-zero vertex.  Consequently owner adjacency is
equivalent to membership in its five-element exceptional bin-zero set. -/
theorem squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
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
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    E.card = 5 ∧ D.neighborFinset owner = E ∧
      ∀ u : V, D.Adj u owner ↔ u ∈ E := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := D.neighborFinset owner ∩ B 0
  have hneighbors := squareOrderNine_threeHigh_secondProfile_binThree_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hneighbors
  have hdegree := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard howner
  dsimp only at hdegree
  have hEcard : E.card = 5 := by
    exact hneighbors.1
  have hneighborCard : (D.neighborFinset owner).card = 5 := by
    rw [D.card_neighborFinset_eq_degree, hdegree.1]
  have hneighborEq : D.neighborFinset owner = E := by
    apply Finset.eq_of_subset_of_card_le
    · exact fun u hu => by
        have hcardLe : (D.neighborFinset owner).card ≤ E.card := by
          rw [hneighborCard, hEcard]
        have hinterSubset : E ⊆ D.neighborFinset owner := Finset.inter_subset_left
        exact (Finset.eq_of_subset_of_card_le hinterSubset hcardLe).symm.subset hu
    · rw [hneighborCard, hEcard]
  refine ⟨hEcard, hneighborEq, ?_⟩
  intro u
  rw [D.adj_comm, ← D.mem_neighborFinset]
  exact Iff.of_eq (congrArg (fun s : Finset V => u ∈ s) hneighborEq)

/-- After deleting the bin-three owner and its five exceptional bin-zero
neighbors from the regular class, the remaining bin-zero vertices have
three bin-one defect neighbors, while every bin-one vertex has five defect
neighbors in that regular class. -/
theorem squareOrderNine_threeHigh_secondProfile_articulation_cross_degrees
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
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    let R := B 0 \ E
    (∀ x ∈ R, (D.neighborFinset x ∩ B 0).card = 5 ∧
      (D.neighborFinset x ∩ B 1).card = 3) ∧
    ∀ y ∈ B 1, (D.neighborFinset y ∩ R).card = 5 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := D.neighborFinset owner ∩ B 0
  let R := B 0 \ E
  have hB3card : (B 3).card = 1 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hEexceptional : ∀ x ∈ E,
      (D.neighborFinset x ∩ B 0).card = 7 ∧
      (D.neighborFinset x ∩ B 1).card = 0 := by
    intro x hxE
    have hxParts := Finset.mem_inter.mp hxE
    have htype :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hxParts.2
    dsimp only at htype
    rcases htype with hregular | hexceptional
    · have hownerInter : owner ∈ D.neighborFinset x ∩ B 3 := by
        refine Finset.mem_inter.mpr ⟨?_, howner⟩
        exact (D.mem_neighborFinset x owner).mpr
          ((D.adj_comm owner x).mp ((D.mem_neighborFinset owner x).mp hxParts.1))
      have : 0 < (D.neighborFinset x ∩ B 3).card :=
        Finset.card_pos.mpr ⟨owner, hownerInter⟩
      rw [hregular.2.2] at this
      omega
    · exact ⟨hexceptional.1, hexceptional.2.1⟩
  constructor
  · intro x hxR
    have hxParts := Finset.mem_sdiff.mp hxR
    have htype :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hxParts.1
    dsimp only at htype
    rcases htype with hregular | hexceptional
    · exact ⟨hregular.1, hregular.2.1⟩
    · exfalso
      have hinter : D.neighborFinset x ∩ B 3 = B 3 := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.inter_subset_right
        · rw [hexceptional.2.2, hB3card]
      have hownerNx : owner ∈ D.neighborFinset x := by
        have : owner ∈ D.neighborFinset x ∩ B 3 := by
          rw [hinter]
          exact howner
        exact (Finset.mem_inter.mp this).1
      apply hxParts.2
      exact Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset owner x).mpr
          ((D.adj_comm x owner).mp ((D.mem_neighborFinset x owner).mp hownerNx)),
        hxParts.1⟩
  · intro y hyB1
    have hyType := squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hyB1
    dsimp only at hyType
    have hinter : D.neighborFinset y ∩ R = D.neighborFinset y ∩ B 0 := by
      ext x
      simp only [R, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · exact fun hx => ⟨hx.1, hx.2.1⟩
      · intro hx
        refine ⟨hx.1, hx.2, ?_⟩
        intro hxE
        have hxExceptional := hEexceptional x hxE
        have hyAtX : y ∈ D.neighborFinset x ∩ B 1 := by
          refine Finset.mem_inter.mpr ⟨?_, hyB1⟩
          exact (D.mem_neighborFinset x y).mpr
            ((D.adj_comm y x).mp ((D.mem_neighborFinset y x).mp hx.1))
        have : 0 < (D.neighborFinset x ∩ B 1).card :=
          Finset.card_pos.mpr ⟨y, hyAtX⟩
        omega
    rw [hinter]
    exact hyType.1

/-- Every shore in the low-vertex defect graph after deleting the unique
bin-three owner is the disjoint union of its exceptional bin-zero, regular
bin-zero, and bin-one parts. -/
theorem squareOrderNine_threeHigh_secondProfile_deleted_owner_shore_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S : Finset V)
    (hS : S ⊆ (((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner)) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    let R := B 0 \ E
    S.card = (E ∩ S).card + (R ∩ S).card + (B 1 ∩ S).card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := D.neighborFinset owner ∩ B 0
  let R := B 0 \ E
  let U := (Finset.univ : Finset V) \ squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  have hB2empty : B 2 = ∅ := by
    rw [← Finset.card_eq_zero]
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 2) (by omega), hc2]
  have hcover : U.erase owner ⊆ E ∪ R ∪ B 1 := by
    intro u hu
    have huParts := Finset.mem_erase.mp hu
    have huU : u ∈ U := huParts.2
    have hkLe : k u ≤ 3 := by
      have := Finset.card_le_card
        (Finset.inter_subset_right : G.neighborFinset u ∩
          squareOrderHighVertices G 9 ⊆ squareOrderHighVertices G 9)
      dsimp [k, squareOrderHighIncidenceCount]
      rw [hhigh] at this
      exact this
    have hkCases : k u = 0 ∨ k u = 1 ∨ k u = 2 ∨ k u = 3 := by omega
    rcases hkCases with hk0 | hk1 | hk2 | hk3
    · have huB0 : u ∈ B 0 := Finset.mem_filter.mpr ⟨huU, hk0⟩
      by_cases huE : u ∈ E
      · simp [huE]
      · have huR : u ∈ R := Finset.mem_sdiff.mpr ⟨huB0, huE⟩
        simp [huR]
    · have huB1 : u ∈ B 1 := Finset.mem_filter.mpr ⟨huU, hk1⟩
      simp [huB1]
    · have huB2 : u ∈ B 2 := Finset.mem_filter.mpr ⟨huU, hk2⟩
      rw [hB2empty] at huB2
      simp at huB2
    · have huB3 : u ∈ B 3 := Finset.mem_filter.mpr ⟨huU, hk3⟩
      have hB3card : (B 3).card = 1 := by
        dsimp [B]
        rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
          G hp (i := 3) (by omega), hc3]
      have huo : u = owner :=
        Finset.card_le_one.mp (by omega) u huB3 owner howner
      exact (huParts.1 huo).elim
  have hset : S = (E ∩ S) ∪ (R ∩ S) ∪ (B 1 ∩ S) := by
    ext u
    constructor
    · intro huS
      have huCover := hcover (hS huS)
      simp only [Finset.mem_union, Finset.mem_inter] at huCover ⊢
      rcases huCover with (huE | huR) | huB1
      · exact Or.inl (Or.inl ⟨huE, huS⟩)
      · exact Or.inl (Or.inr ⟨huR, huS⟩)
      · exact Or.inr ⟨huB1, huS⟩
    · intro hu
      rcases Finset.mem_union.mp hu with huER | huB1
      · rcases Finset.mem_union.mp huER with huE | huR
        · exact (Finset.mem_inter.mp huE).2
        · exact (Finset.mem_inter.mp huR).2
      · exact (Finset.mem_inter.mp huB1).2
  have hER : Disjoint (E ∩ S) (R ∩ S) := by
    rw [Finset.disjoint_left]
    intro u huE huR
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp huR).1).2
      (Finset.mem_inter.mp huE).1
  have hERB : Disjoint ((E ∩ S) ∪ (R ∩ S)) (B 1 ∩ S) := by
    rw [Finset.disjoint_left]
    intro u huER huB1
    have huB1' := (Finset.mem_inter.mp huB1).1
    have hk1 := (Finset.mem_filter.mp huB1').2
    rcases Finset.mem_union.mp huER with huE | huR
    · have huB0 := (Finset.mem_inter.mp (Finset.mem_inter.mp huE).1).2
      have hk0 := (Finset.mem_filter.mp huB0).2
      omega
    · have huB0 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp huR).1).1
      have hk0 := (Finset.mem_filter.mp huB0).2
      omega
  have hcard := congrArg Finset.card hset
  rw [Finset.card_union_of_disjoint hERB,
    Finset.card_union_of_disjoint hER] at hcard
  exact hcard

/-- On a deleted-owner shore, total incidence into the three high vertices is
exactly the number of bin-one vertices in the shore. -/
theorem squareOrderNine_threeHigh_secondProfile_deleted_owner_beta_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S : Finset V)
    (hS : S ⊆ (((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).erase owner)) :
    (G.neighborFinset h₁ ∩ S).card +
      (G.neighborFinset h₂ ∩ S).card +
      (G.neighborFinset h₃ ∩ S).card =
      (squareOrderNineLowIncidenceBin G 1 ∩ S).card := by
  classical
  let H := squareOrderHighVertices G 9
  let U := (Finset.univ : Finset V) \ H
  let B := squareOrderNineLowIncidenceBin G
  let k := squareOrderHighIncidenceCount G 9
  have hB2empty : B 2 = ∅ := by
    rw [← Finset.card_eq_zero]
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 2) (by omega), hc2]
  have hB3card : (B 3).card = 1 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hpoint : ∀ x ∈ S, k x = if x ∈ B 1 then 1 else 0 := by
    intro x hxS
    have hxErase := hS hxS
    have hxParts := Finset.mem_erase.mp hxErase
    have hxU : x ∈ U := hxParts.2
    have hkLe : k x ≤ 3 := by
      have := Finset.card_le_card
        (Finset.inter_subset_right : G.neighborFinset x ∩ H ⊆ H)
      dsimp [k, squareOrderHighIncidenceCount, H] at this
      rw [hhigh] at this
      exact this
    have hkCases : k x = 0 ∨ k x = 1 ∨ k x = 2 ∨ k x = 3 := by omega
    rcases hkCases with hk0 | hk1 | hk2 | hk3
    · have hxNotB1 : x ∉ B 1 := by
        intro hxB1
        have hxB1' := hxB1
        dsimp [B, squareOrderNineLowIncidenceBin] at hxB1'
        have hxk := (Finset.mem_filter.mp hxB1').2
        dsimp [k] at hk0
        omega
      simp [hk0, hxNotB1]
    · have hxB1 : x ∈ B 1 := Finset.mem_filter.mpr ⟨hxU, hk1⟩
      simp [hk1, hxB1]
    · have hxB2 : x ∈ B 2 := Finset.mem_filter.mpr ⟨hxU, hk2⟩
      rw [hB2empty] at hxB2
      simp at hxB2
    · have hxB3 : x ∈ B 3 := Finset.mem_filter.mpr ⟨hxU, hk3⟩
      have hxo : x = owner :=
        Finset.card_le_one.mp (by omega) x hxB3 owner howner
      exact (hxParts.1 hxo).elim
  have hsumPoint : (∑ x ∈ S, k x) = (B 1 ∩ S).card := by
    calc
      ∑ x ∈ S, k x = ∑ x ∈ S, if x ∈ B 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpoint x hx
      _ = (B 1 ∩ S).card := by
        rw [Finset.sum_boole]
        apply congrArg Finset.card
        ext x
        simp [and_comm]
  have hswap := sum_card_neighbor_inter_comm G H S
  have hH' : H = {h₁, h₂, h₃} := by exact hH
  have hswap' :
      (G.neighborFinset h₁ ∩ S).card +
        (G.neighborFinset h₂ ∩ S).card +
        (G.neighborFinset h₃ ∩ S).card = ∑ x ∈ S, k x := by
    rw [hH'] at hswap
    simpa [H, k, squareOrderHighIncidenceCount, hH,
      h₁₂, h₁₃, h₂₃, add_assoc] using hswap
  exact hswap'.trans hsumPoint

/-- The B0 part of a relatively closed deleted-owner shore inherits internal
degrees seven on exceptional vertices and five on regular vertices.  Its
handshake supplies parity and the simple-graph bound; a nonempty exceptional
part forces at least eight B0 vertices. -/
theorem squareOrderNine_threeHigh_secondProfile_shore_binZero_handshake
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
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S : Finset V)
    (hclosed : ∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
      (((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner) ⊆ S) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    let R := B 0 \ E
    let e := (E ∩ S).card
    let r := (R ∩ S).card
    (7 * e + 5 * r) % 2 = 0 ∧
      7 * e + 5 * r ≤ (e + r) * (e + r - 1) ∧
      ((E ∩ S).Nonempty → 8 ≤ e + r) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let U := (Finset.univ : Finset V) \ squareOrderHighVertices G 9
  let E := D.neighborFinset owner ∩ B 0
  let R := B 0 \ E
  let B₀S := B 0 ∩ S
  let ES := E ∩ S
  let RS := R ∩ S
  have hownerInfo := squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hownerInfo
  have hcross := squareOrderNine_threeHigh_secondProfile_articulation_cross_degrees
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hcross
  have hB0erase : B 0 ⊆ U.erase owner := by
    intro x hxB0
    have hxU : x ∈ U := (Finset.mem_filter.mp hxB0).1
    have hxo : x ≠ owner := by
      intro hxo
      subst x
      have hk0 := (Finset.mem_filter.mp hxB0).2
      have hk3 := (Finset.mem_filter.mp howner).2
      omega
    exact Finset.mem_erase.mpr ⟨hxo, hxU⟩
  have hB0split : B₀S = ES ∪ RS := by
    ext x
    simp only [B₀S, ES, RS, R, Finset.mem_inter, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxE : x ∈ E
      · exact Or.inl ⟨hxE, hx.2⟩
      · exact Or.inr ⟨⟨hx.1, hxE⟩, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨(Finset.mem_inter.mp hx.1).2, hx.2⟩
      · exact ⟨hx.1.1, hx.2⟩
  have hdis : Disjoint ES RS := by
    rw [Finset.disjoint_left]
    intro x hxE hxR
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxR).1).2
      (Finset.mem_inter.mp hxE).1
  have hB0card : B₀S.card = ES.card + RS.card := by
    rw [hB0split, Finset.card_union_of_disjoint hdis]
  have hEdegree : ∀ x ∈ ES, (D.neighborFinset x ∩ B₀S).card = 7 := by
    intro x hxES
    have hxParts := Finset.mem_inter.mp hxES
    have hxEParts := Finset.mem_inter.mp hxParts.1
    have htype :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hxEParts.2
    dsimp only at htype
    have hexceptional : (D.neighborFinset x ∩ B 0).card = 7 := by
      rcases htype with hregular | hexceptional
      · have hxOwner : owner ∈ D.neighborFinset x ∩ B 3 := by
          refine Finset.mem_inter.mpr ⟨?_, howner⟩
          exact (D.mem_neighborFinset x owner).mpr
            ((D.adj_comm owner x).mp
              ((D.mem_neighborFinset owner x).mp hxEParts.1))
        have : 0 < (D.neighborFinset x ∩ B 3).card :=
          Finset.card_pos.mpr ⟨owner, hxOwner⟩
        rw [hregular.2.2] at this
        omega
      · exact hexceptional.1
    have hinter : D.neighborFinset x ∩ B₀S = D.neighborFinset x ∩ B 0 := by
      ext y
      simp only [B₀S, Finset.mem_inter]
      constructor
      · exact fun hy => ⟨hy.1, hy.2.1⟩
      · intro hy
        exact ⟨hy.1, hy.2, hclosed x hxParts.2
          (Finset.mem_inter.mpr ⟨hy.1, hB0erase hy.2⟩)⟩
    rw [hinter]
    exact hexceptional
  have hRdegree : ∀ x ∈ RS, (D.neighborFinset x ∩ B₀S).card = 5 := by
    intro x hxRS
    have hxParts := Finset.mem_inter.mp hxRS
    have hglobal := (hcross.1 x hxParts.1).1
    have hinter : D.neighborFinset x ∩ B₀S = D.neighborFinset x ∩ B 0 := by
      ext y
      simp only [B₀S, Finset.mem_inter]
      constructor
      · exact fun hy => ⟨hy.1, hy.2.1⟩
      · intro hy
        exact ⟨hy.1, hy.2, hclosed x hxParts.2
          (Finset.mem_inter.mpr ⟨hy.1, hB0erase hy.2⟩)⟩
    rw [hinter]
    exact hglobal
  obtain ⟨m, hhand, hsimple⟩ := articulation_binZero_internal_handshake
    D B₀S ES (by
      intro x hx
      exact Finset.mem_inter.mpr ⟨
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp hx).2⟩)
    hEdegree (by
      intro x hx
      have hxB0S := (Finset.mem_sdiff.mp hx).1
      have hxNotES := (Finset.mem_sdiff.mp hx).2
      apply hRdegree x
      have hxParts := Finset.mem_inter.mp hxB0S
      exact Finset.mem_inter.mpr ⟨
        Finset.mem_sdiff.mpr ⟨hxParts.1, fun hxE =>
          hxNotES (Finset.mem_inter.mpr ⟨hxE, hxParts.2⟩)⟩,
        hxParts.2⟩)
  have hparity : (7 * ES.card + 5 * RS.card) % 2 = 0 := by omega
  have hsimple' : 7 * ES.card + 5 * RS.card ≤
      (ES.card + RS.card) * (ES.card + RS.card - 1) := by
    have hdiff : B₀S.card - ES.card = RS.card := by omega
    rw [hdiff] at hsimple
    rw [← hB0card]
    exact hsimple
  refine ⟨hparity, hsimple', ?_⟩
  intro hESnonempty
  obtain ⟨x, hxES⟩ := hESnonempty
  have hNsub : D.neighborFinset x ∩ B₀S ⊆ B₀S.erase x := by
    intro y hy
    have hyParts := Finset.mem_inter.mp hy
    exact Finset.mem_erase.mpr ⟨fun hyx => by
      subst y
      exact D.loopless.irrefl x ((D.mem_neighborFinset x x).mp hyParts.1), hyParts.2⟩
  have hsevenLe : 7 ≤ B₀S.card - 1 := by
    calc
      7 = (D.neighborFinset x ∩ B₀S).card := (hEdegree x hxES).symm
      _ ≤ (B₀S.erase x).card := Finset.card_le_card hNsub
      _ = B₀S.card - 1 := Finset.card_erase_of_mem
        (Finset.mem_inter.mpr ⟨
          (Finset.mem_inter.mp (Finset.mem_inter.mp hxES).1).2,
          (Finset.mem_inter.mp hxES).2⟩)
  have height : 8 ≤ B₀S.card := by omega
  rw [hB0card] at height
  exact height

/-- Composition of all profile-local articulation inputs.  Once the graph
moment layer supplies the two cut inequalities and their elementary bounds,
the shore has a scale `k`, order `e+8k`, and one of the eleven classified
parameter types. -/
theorem squareOrderNine_threeHigh_secondProfile_shore_parameter_type_of_cut_bounds
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
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (hH : squareOrderHighVertices G 9 = {h₁, h₂, h₃})
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S : Finset V)
    (hSsub : S ⊆ (((Finset.univ : Finset V) \
      squareOrderHighVertices G 9).erase owner))
    (hSproper : S.card < 78)
    (hclosed : ∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
      (((Finset.univ : Finset V) \ squareOrderHighVertices G 9).erase owner) ⊆ S)
    (hEmeet : (((secondOrderDefectGraph G).neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 0) ∩ S).Nonempty)
    (hb₁ : (G.neighborFinset h₁ ∩ S).card ≤ 9)
    (hb₂ : (G.neighborFinset h₂ ∩ S).card ≤ 9)
    (hb₃ : (G.neighborFinset h₃ ∩ S).card ≤ 9)
    (hcut : orderNineNearRegularCutLower S.card
      (G.neighborFinset h₁ ∩ S).card
      (G.neighborFinset h₂ ∩ S).card
      (G.neighborFinset h₃ ∩ S).card ≤
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card)
    (hcutCompl : orderNineNearRegularCutLower (78 - S.card)
      (10 - (G.neighborFinset h₁ ∩ S).card)
      (10 - (G.neighborFinset h₂ ∩ S).card)
      (10 - (G.neighborFinset h₃ ∩ S).card) ≤
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    ∃ k : ℕ, S.card = (E ∩ S).card + 8 * k ∧
      orderNineArticulationSideParameterType (E ∩ S).card k := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let O := (Finset.univ : Finset V) \ squareOrderHighVertices G 9
  let E := D.neighborFinset owner ∩ B 0
  let R := B 0 \ E
  let e := (E ∩ S).card
  let r := (R ∩ S).card
  let n₁ := (B 1 ∩ S).card
  change (E ∩ S).Nonempty at hEmeet
  change orderNineNearRegularCutLower S.card
    (G.neighborFinset h₁ ∩ S).card
    (G.neighborFinset h₂ ∩ S).card
    (G.neighborFinset h₃ ∩ S).card ≤ e at hcut
  change orderNineNearRegularCutLower (78 - S.card)
    (10 - (G.neighborFinset h₁ ∩ S).card)
    (10 - (G.neighborFinset h₂ ∩ S).card)
    (10 - (G.neighborFinset h₃ ∩ S).card) ≤ e at hcutCompl
  have hcross := squareOrderNine_threeHigh_secondProfile_articulation_cross_degrees
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hcross
  have hRsub : R ⊆ O.erase owner := by
    intro x hxR
    have hxB0 := (Finset.mem_sdiff.mp hxR).1
    have hxO := (Finset.mem_filter.mp hxB0).1
    have hxo : x ≠ owner := by
      intro hxo
      subst x
      have hk0 := (Finset.mem_filter.mp hxB0).2
      have hk3 := (Finset.mem_filter.mp howner).2
      omega
    exact Finset.mem_erase.mpr ⟨hxo, hxO⟩
  have hB1sub : B 1 ⊆ O.erase owner := by
    intro x hxB1
    have hxO := (Finset.mem_filter.mp hxB1).1
    have hxo : x ≠ owner := by
      intro hxo
      subst x
      have hk1 := (Finset.mem_filter.mp hxB1).2
      have hk3 := (Finset.mem_filter.mp howner).2
      omega
    exact Finset.mem_erase.mpr ⟨hxo, hxO⟩
  have hbalance : 3 * r = 5 * n₁ := by
    exact three_mul_regular_eq_five_mul_binOne_of_erase_owner_closed
      D O S R (B 1) owner hRsub hB1sub hclosed
        (fun x hx => (hcross.1 x hx).2) hcross.2
  have hpartition :=
    squareOrderNine_threeHigh_secondProfile_deleted_owner_shore_partition
      G hp hhigh hc2 hc3 howner S hSsub
  dsimp only at hpartition
  change S.card = e + r + n₁ at hpartition
  have hscale := exists_articulation_scale_of_three_mul_regular_eq_five_mul_binOne
    e r n₁ S.card hbalance hpartition
  obtain ⟨k, hr, hn₁, horder⟩ := hscale
  have hhand := squareOrderNine_threeHigh_secondProfile_shore_binZero_handshake
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner S hclosed
  dsimp only at hhand
  change (7 * e + 5 * r) % 2 = 0 ∧
    7 * e + 5 * r ≤ (e + r) * (e + r - 1) ∧
    ((E ∩ S).Nonempty → 8 ≤ e + r) at hhand
  have hparity : (7 * e + 25 * k) % 2 = 0 := by omega
  have hsimple : 7 * e + 25 * k ≤
      (e + 5 * k) * (e + 5 * k - 1) := by
    have hs := hhand.2.1
    rw [hr] at hs
    calc
      7 * e + 25 * k = 7 * e + 5 * (5 * k) := by ring
      _ ≤ (e + 5 * k) * (e + 5 * k - 1) := hs
  have hn₀ : 8 ≤ e + 5 * k := by
    rw [← hr]
    exact hhand.2.2 hEmeet
  have he : e ≠ 0 := Finset.card_ne_zero.mpr hEmeet
  have hEcard := squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hEcard
  have heBound : e ≤ 5 := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hEcard.1
  have hB1card :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hB1card
  have hkBound : k ≤ 9 := by
    have hn₁le : n₁ ≤ 27 := by
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hB1card.1
    omega
  have hbeta0 :=
    squareOrderNine_threeHigh_secondProfile_deleted_owner_beta_sum
      G hp hhigh hc2 hc3 h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hH howner S hSsub
  have hbeta : (G.neighborFinset h₁ ∩ S).card +
      (G.neighborFinset h₂ ∩ S).card +
      (G.neighborFinset h₃ ∩ S).card = 3 * k := by
    exact hbeta0.trans hn₁
  have htype := orderNine_articulation_side_parameter_classification_nat
    e k (G.neighborFinset h₁ ∩ S).card
      (G.neighborFinset h₂ ∩ S).card (G.neighborFinset h₃ ∩ S).card
      he heBound hkBound hb₁ hb₂ hb₃ hn₀ hparity hsimple
      (by omega) hbeta (by simpa [horder] using hcut)
      (by simpa [horder] using hcutCompl)
  refine ⟨k, horder, ?_⟩
  change orderNineArticulationSideParameterType e k
  simpa [orderNineArticulationSideParameterType] using htype

end

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_articulation_cross_degrees
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_deleted_owner_shore_partition
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_deleted_owner_beta_sum
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_shore_binZero_handshake
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_shore_parameter_type_of_cut_bounds

end Erdos85
