import Proofs.Erdos85PositiveExcessOne

/-!
# Operator package for odd excess one

In an odd-degree regular `C₄`-free graph of order `d(d-1)+4`, the
triangle-free-edge color is a perfect matching.  This file records the
matrix consequences independently of any congruence assumption: its
adjacency matrix is an involution, its mixed trace with the original
adjacency matrix is the number of vertices, and the combined defect matrix
is the sum of the antipodal two-factor and matching matrices.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The triangle-free-edge matching matrix is an involution in every
odd-degree excess-one graph. -/
theorem triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    (triangleFreeEdgeGraph G).adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ = (1 : Matrix V V ℤ) := by
  apply adjMatrix_sq_eq_one_of_degree_one
  exact triangleFreeEdgeGraph_degree_eq_one_of_odd_excessOne
    G hfree hd hodd hreg hcard

/-- The matching consists of original edges, one at every vertex, so its
mixed trace with the original adjacency matrix is `|V|`. -/
theorem trace_adjMatrix_mul_triangleFreeEdgeGraph_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    Matrix.trace (G.adjMatrix ℤ *
      (triangleFreeEdgeGraph G).adjMatrix ℤ) = Fintype.card V := by
  rw [Matrix.trace]
  have hentry : ∀ x : V,
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x x = 1 := by
    intro x
    rw [(triangleFreeEdgeGraph G).mul_adjMatrix_apply]
    rw [triangleFreeEdgeGraph_neighborFinset]
    calc
      (∑ z ∈ triangleFreeNeighbors G x, G.adjMatrix ℤ x z) =
          ∑ _z ∈ triangleFreeNeighbors G x, 1 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [SimpleGraph.adjMatrix_apply, if_pos]
        exact ((mem_triangleFreeNeighbors G x z).mp hz).1
      _ = (triangleFreeNeighbors G x).card := by simp
      _ = 1 := by
        exact_mod_cast excessOne_triangleFreeNeighbors_card_eq_one_of_odd
          G hfree hd hodd hreg hcard x
  calc
    (∑ x : V, (G.adjMatrix ℤ *
        (triangleFreeEdgeGraph G).adjMatrix ℤ) x x) =
        ∑ _x : V, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hentry x
    _ = Fintype.card V := by simp

/-- No vertex can be adjacent to both ends of a triangle-free edge.  This
is the local obstruction excluding two quotient edges that share an
endpoint inside one matching pair. -/
theorem not_adj_both_ends_of_triangleFreeEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y y' : V}
    (hyy' : (triangleFreeEdgeGraph G).Adj y y') :
    ¬(G.Adj x y ∧ G.Adj x y') := by
  intro hx
  have hzero : G.neighborFinset y ∩ G.neighborFinset y' = ∅ :=
    Finset.card_eq_zero.mp
      ((mem_triangleFreeNeighbors G y y').mp hyy').2
  have hxmem : x ∈ G.neighborFinset y ∩ G.neighborFinset y' := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hx.1.symm, hx.2.symm⟩
  rw [hzero] at hxmem
  exact Finset.notMem_empty x hxmem

/-- Two disjoint matching edges cannot support both corresponding cross
edges: together the four edges would be a `C₄`.  Combined with
`not_adj_both_ends_of_triangleFreeEdge`, this is the combinatorial core of
the sparse quotient on matching pairs. -/
theorem false_of_two_crossEdges_between_triangleFreeEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x x' y y' : V}
    (hxx' : (triangleFreeEdgeGraph G).Adj x x')
    (hyy' : (triangleFreeEdgeGraph G).Adj y y')
    (hxy' : x ≠ y') (hyx' : y ≠ x')
    (hxy : G.Adj x y) (hx'y' : G.Adj x' y') : False := by
  apply hfree
  apply containsC4_of_two_common
      (x := x) (y := y') (v := y) (v' := x')
  · exact hxy'
  · exact hyx'
  · exact hxy.symm
  · exact ((mem_triangleFreeNeighbors G y y').mp hyy').1
  · exact ((mem_triangleFreeNeighbors G x x').mp hxx').1.symm
  · exact hx'y'

/-- A three-edge path of triangular edges cannot connect the endpoints of a
triangle-free edge: closing it with that edge would give a `C₄`.  This is
the combinatorial content of the mixed fourth-moment vanishing
`tr(M E³) = 0`. -/
theorem false_of_triangleFreeEdge_and_three_triangularEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y z w : V}
    (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hyz : (triangularEdgeGraph G).Adj y z)
    (hzw : (triangularEdgeGraph G).Adj z w)
    (hwx : (triangularEdgeGraph G).Adj w x) : False := by
  have hGxy : G.Adj x y :=
    ((mem_triangleFreeNeighbors G x y).mp hxy).1
  have hGyz : G.Adj y z := (triangularEdgeGraph_adj G y z).mp hyz |>.1
  have hGzw : G.Adj z w := (triangularEdgeGraph_adj G z w).mp hzw |>.1
  have hGwx : G.Adj w x := (triangularEdgeGraph_adj G w x).mp hwx |>.1
  have hxz : x ≠ z := by
    intro hxz
    subst z
    have hnonzero := (triangularEdgeGraph_adj G y x).mp hyz |>.2
    have hzero := ((mem_triangleFreeNeighbors G x y).mp hxy).2
    rw [Finset.inter_comm] at hzero
    exact hnonzero hzero
  have hyw : y ≠ w := by
    intro hyw
    subst w
    have hnonzero := (triangularEdgeGraph_adj G y x).mp hwx |>.2
    have hzero := ((mem_triangleFreeNeighbors G x y).mp hxy).2
    rw [Finset.inter_comm] at hzero
    exact hnonzero hzero
  exact hfree (containsC4_of_rim hGxy hGyz hGzw hGwx
    hxz hyw (G.ne_of_adj hGxy).symm (G.ne_of_adj hGyz)
    (G.ne_of_adj hGwx) (G.ne_of_adj hGzw).symm)

/-- Matrix-moment form of the preceding path exclusion. -/
theorem trace_triangleFree_mul_triangular_cube_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    Matrix.trace
      (((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (triangularEdgeGraph G).adjMatrix ℤ) *
        (triangularEdgeGraph G).adjMatrix ℤ *
        (triangularEdgeGraph G).adjMatrix ℤ) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change (((triangleFreeEdgeGraph G).adjMatrix ℤ *
    (triangularEdgeGraph G).adjMatrix ℤ) *
    (triangularEdgeGraph G).adjMatrix ℤ *
    (triangularEdgeGraph G).adjMatrix ℤ) x x = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hwx : (triangularEdgeGraph G).Adj w x
  · rw [SimpleGraph.adjMatrix_apply, if_pos hwx, mul_one]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hzw : (triangularEdgeGraph G).Adj z w
    · rw [SimpleGraph.adjMatrix_apply, if_pos hzw, mul_one]
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro y _
      by_cases hxy : (triangleFreeEdgeGraph G).Adj x y
      · by_cases hyz : (triangularEdgeGraph G).Adj y z
        · exact (false_of_triangleFreeEdge_and_three_triangularEdges
            G hfree hxy hyz hzw hwx).elim
        · have htzero : (triangularEdgeGraph G).adjMatrix ℤ y z = 0 := by
            rw [SimpleGraph.adjMatrix_apply, if_neg hyz]
          rw [htzero, mul_zero]
      · have hmzero : (triangleFreeEdgeGraph G).adjMatrix ℤ x y = 0 := by
          rw [SimpleGraph.adjMatrix_apply, if_neg hxy]
        rw [hmzero, zero_mul]
    · simp [SimpleGraph.adjMatrix_apply, hzw]
  · simp [SimpleGraph.adjMatrix_apply, hwx]

/-- Deleting the triangle-free-edge color is ordinary matrix subtraction,
because that color is a spanning subgraph of `G`. -/
theorem triangularEdgeGraph_adjMatrix_eq_sub_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj] :
    (triangularEdgeGraph G).adjMatrix ℤ =
      G.adjMatrix ℤ - (triangleFreeEdgeGraph G).adjMatrix ℤ := by
  classical
  ext x y
  simp only [Matrix.sub_apply, SimpleGraph.adjMatrix_apply]
  have hsub : (triangleFreeEdgeGraph G).Adj x y → G.Adj x y := by
    intro h
    exact ((mem_triangleFreeNeighbors G x y).mp h).1
  by_cases hg : G.Adj x y
  · by_cases hm : (triangleFreeEdgeGraph G).Adj x y
    · have ht : ¬(triangularEdgeGraph G).Adj x y := by
        intro ht
        exact ((sdiff_adj G (triangleFreeEdgeGraph G) x y).mp ht).2 hm
      have hempty : G.neighborFinset x ∩ G.neighborFinset y = ∅ :=
        Finset.card_eq_zero.mp
          ((mem_triangleFreeNeighbors G x y).mp hm).2
      simp [hg, hm, ht, hempty]
    · have ht : (triangularEdgeGraph G).Adj x y :=
        (sdiff_adj G (triangleFreeEdgeGraph G) x y).mpr ⟨hg, hm⟩
      have hneempty : G.neighborFinset x ∩ G.neighborFinset y ≠ ∅ := by
        intro hempty
        apply hm
        apply (mem_triangleFreeNeighbors G x y).mpr
        exact ⟨hg, Finset.card_eq_zero.mpr hempty⟩
      simp [hg, hm, ht, hneempty]
  · have hm : ¬(triangleFreeEdgeGraph G).Adj x y := fun hm => hg (hsub hm)
    have ht : ¬(triangularEdgeGraph G).Adj x y := by
      intro ht
      exact hg ((sdiff_adj G (triangleFreeEdgeGraph G) x y).mp ht).1
    simp [hg, hm, ht]

/-- External-edge form of the mixed fourth-moment vanishing. -/
theorem trace_matching_mul_external_cube_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    let A := G.adjMatrix ℤ
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    Matrix.trace (((M * (A - M)) * (A - M)) * (A - M)) = 0 := by
  dsimp only
  rw [← triangularEdgeGraph_adjMatrix_eq_sub_triangleFree G]
  exact trace_triangleFree_mul_triangular_cube_eq_zero G hfree

/-- Off the diagonal, the two opposite entries of `AM` cannot both be one.
Equivalently, the directed support of `AM` has no directed two-cycle away
from its forced diagonal. -/
theorem adjMatrix_mul_triangleFreeEdgeGraph_opposite_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {x y : V} (hxy : x ≠ y) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y *
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) y x = 0 := by
  have hcardx : (triangleFreeNeighbors G x).card = 1 :=
    excessOne_triangleFreeNeighbors_card_eq_one_of_odd
      G hfree hd hodd hreg hcard x
  have hcardy : (triangleFreeNeighbors G y).card = 1 :=
    excessOne_triangleFreeNeighbors_card_eq_one_of_odd
      G hfree hd hodd hreg hcard y
  obtain ⟨mx, hmx⟩ := Finset.card_eq_one.mp hcardx
  obtain ⟨my, hmy⟩ := Finset.card_eq_one.mp hcardy
  rw [(triangleFreeEdgeGraph G).mul_adjMatrix_apply,
    (triangleFreeEdgeGraph G).mul_adjMatrix_apply,
    triangleFreeEdgeGraph_neighborFinset,
    triangleFreeEdgeGraph_neighborFinset, hmx, hmy]
  simp only [Finset.sum_singleton]
  by_cases hxmy : G.Adj x my
  · by_cases hymx : G.Adj y mx
    · have hmxMem : mx ∈ triangleFreeNeighbors G x := by simp [hmx]
      have hmyMem : my ∈ triangleFreeNeighbors G y := by simp [hmy]
      have hMxx : (triangleFreeEdgeGraph G).Adj x mx :=
        (triangleFreeEdgeGraph_adj G x mx).mpr hmxMem
      have hMyy : (triangleFreeEdgeGraph G).Adj y my :=
        (triangleFreeEdgeGraph_adj G y my).mpr hmyMem
      have hmxmy : mx ≠ my := by
        intro heq
        have hxm : x ∈ (triangleFreeEdgeGraph G).neighborFinset mx :=
          ((triangleFreeEdgeGraph G).mem_neighborFinset mx x).mpr hMxx.symm
        have hym : y ∈ (triangleFreeEdgeGraph G).neighborFinset mx :=
          ((triangleFreeEdgeGraph G).mem_neighborFinset mx y).mpr (heq ▸ hMyy.symm)
        have hpair : ({x, y} : Finset V) ⊆
            (triangleFreeEdgeGraph G).neighborFinset mx := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxm
          · exact hym
        have hle := Finset.card_le_card hpair
        rw [Finset.card_pair hxy,
          (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_degree_eq_one_of_odd_excessOne
            G hfree hd hodd hreg hcard mx] at hle
        omega
      exfalso
      apply hfree
      apply containsC4_of_two_common
          (x := x) (y := y) (v := my) (v' := mx)
      · exact hxy
      · exact hmxmy.symm
      · exact hxmy.symm
      · exact ((mem_triangleFreeNeighbors G y my).mp hmyMem).1.symm
      · exact ((mem_triangleFreeNeighbors G x mx).mp hmxMem).1.symm
      · exact hymx.symm
    · simp [SimpleGraph.adjMatrix_apply, hymx]
  · simp [SimpleGraph.adjMatrix_apply, hxmy]

/-- Every diagonal entry of `AM` is one: the matching partner of a vertex
is an original neighbor. -/
theorem adjMatrix_mul_triangleFreeEdgeGraph_apply_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x x = 1 := by
  rw [(triangleFreeEdgeGraph G).mul_adjMatrix_apply,
    triangleFreeEdgeGraph_neighborFinset]
  calc
    (∑ z ∈ triangleFreeNeighbors G x, G.adjMatrix ℤ x z) =
        ∑ _z ∈ triangleFreeNeighbors G x, 1 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [SimpleGraph.adjMatrix_apply, if_pos]
      exact ((mem_triangleFreeNeighbors G x z).mp hz).1
    _ = (triangleFreeNeighbors G x).card := by simp
    _ = 1 := by
      exact_mod_cast excessOne_triangleFreeNeighbors_card_eq_one_of_odd
        G hfree hd hodd hreg hcard x

/-- Every entry of the matching-twisted adjacency matrix `AM` is binary.
Multiplication by the perfect-matching matrix merely permutes the columns
of the original adjacency matrix. -/
theorem adjMatrix_mul_triangleFreeEdgeGraph_apply_eq_zero_or_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x y : V) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y = 0 ∨
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y = 1 := by
  have hcardy : (triangleFreeNeighbors G y).card = 1 :=
    excessOne_triangleFreeNeighbors_card_eq_one_of_odd
      G hfree hd hodd hreg hcard y
  obtain ⟨my, hmy⟩ := Finset.card_eq_one.mp hcardy
  rw [(triangleFreeEdgeGraph G).mul_adjMatrix_apply,
    triangleFreeEdgeGraph_neighborFinset, hmy]
  simp only [Finset.sum_singleton, SimpleGraph.adjMatrix_apply]
  by_cases h : G.Adj x my <;> simp [h]

/-- Exact skew-incidence law for `B = AM`: its diagonal entries are one,
while no off-diagonal pair of transposed entries can both be one. -/
theorem adjMatrix_mul_triangleFreeEdgeGraph_apply_mul_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x y : V) :
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) x y *
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) y x =
        if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl,
      adjMatrix_mul_triangleFreeEdgeGraph_apply_self
        G hfree hd hodd hreg hcard x]
    norm_num
  · rw [if_neg hxy]
    exact adjMatrix_mul_triangleFreeEdgeGraph_opposite_mul_eq_zero
      G hfree hd hodd hreg hcard hxy

/-- The matching-twisted incidence matrix `B = AM` has constant row and
column sum `d`. -/
theorem matchingIncidence_mul_ones_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let B := G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ
    let J := FriendshipTheoremOQ01.onesMatrix V
    B * J = (d : ℤ) • J ∧ J * B = (d : ℤ) • J := by
  dsimp only
  have hmreg : ∀ x,
      (triangleFreeEdgeGraph G).degree x = 1 :=
    triangleFreeEdgeGraph_degree_eq_one_of_odd_excessOne
      G hfree hd hodd hreg hcard
  constructor
  · calc
      (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) *
          FriendshipTheoremOQ01.onesMatrix V =
        G.adjMatrix ℤ *
          ((triangleFreeEdgeGraph G).adjMatrix ℤ *
            FriendshipTheoremOQ01.onesMatrix V) := by
              simp only [Matrix.mul_assoc]
      _ = G.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V := by
        rw [FriendshipTheoremOQ01.adjMatrix_mul_ones
          (triangleFreeEdgeGraph G) 1 hmreg]
        simp
      _ = (d : ℤ) • FriendshipTheoremOQ01.onesMatrix V :=
        FriendshipTheoremOQ01.adjMatrix_mul_ones G d hreg
  · calc
      FriendshipTheoremOQ01.onesMatrix V *
          (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) =
        (FriendshipTheoremOQ01.onesMatrix V * G.adjMatrix ℤ) *
          (triangleFreeEdgeGraph G).adjMatrix ℤ := by
            simp only [Matrix.mul_assoc]
      _ = ((d : ℤ) • FriendshipTheoremOQ01.onesMatrix V) *
          (triangleFreeEdgeGraph G).adjMatrix ℤ := by
        rw [onesMatrix_mul_adjMatrix_of_regular G d hreg]
      _ = (d : ℤ) •
          (FriendshipTheoremOQ01.onesMatrix V *
            (triangleFreeEdgeGraph G).adjMatrix ℤ) := by
        rw [Matrix.smul_mul]
      _ = (d : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
        rw [onesMatrix_mul_adjMatrix_of_regular
          (triangleFreeEdgeGraph G) 1 hmreg]
        simp

/-- The first genuinely noncommutative matching moment is nevertheless
forced: `tr((AM)²)=|V|`.  Its diagonal contribution is one per vertex and
all off-diagonal directed two-cycles are forbidden by `C₄`-freeness. -/
theorem trace_adjMatrix_mul_triangleFreeEdgeGraph_sq_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    Matrix.trace
      ((G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) *
       (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)) =
      Fintype.card V := by
  rw [Matrix.trace]
  have hdiag : ∀ x : V,
      ((G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) *
       (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)) x x = 1 := by
    intro x
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single x]
    · rw [adjMatrix_mul_triangleFreeEdgeGraph_apply_self
          G hfree hd hodd hreg hcard x]
      norm_num
    · intro y _ hyx
      exact adjMatrix_mul_triangleFreeEdgeGraph_opposite_mul_eq_zero
        G hfree hd hodd hreg hcard hyx.symm
    · intro hx
      simp at hx
  calc
    (∑ x : V,
      ((G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) *
       (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ)) x x) =
        ∑ _x : V, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hdiag x
    _ = Fintype.card V := by simp

/-- The combined defect adjacency matrix splits entrywise as the sum of the
antipodal two-factor matrix and the triangle-free matching matrix. -/
theorem secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    (secondOrderDefectGraph G).adjMatrix ℤ =
      (antipodalGraph G).adjMatrix ℤ +
        (triangleFreeEdgeGraph G).adjMatrix ℤ := by
  classical
  have adjMatrix_sup_of_edge_disjoint
      (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
      (hdisj : ∀ x y, H.Adj x y → K.Adj x y → False) :
      (H ⊔ K).adjMatrix ℤ = H.adjMatrix ℤ + K.adjMatrix ℤ := by
    ext x y
    rw [Matrix.add_apply, SimpleGraph.adjMatrix_apply,
      SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    change (if H.Adj x y ∨ K.Adj x y then 1 else 0) =
      (if H.Adj x y then 1 else 0) + (if K.Adj x y then 1 else 0)
    by_cases hh : H.Adj x y
    · have hk : ¬K.Adj x y := fun hk => hdisj x y hh hk
      simp [hh, hk]
    · by_cases hk : K.Adj x y <;> simp [hh, hk]
  have hmat := adjMatrix_sup_of_edge_disjoint
    (antipodalGraph G) (triangleFreeEdgeGraph G) (by
      intro x y ha hm
      exact (Finset.disjoint_left.mp
        (disjoint_antipodal_triangleFreeNeighbors G x))
          ((antipodalGraph_adj G x y).mp ha)
          ((triangleFreeEdgeGraph_adj G x y).mp hm))
  ext x y
  convert congrFun (congrFun hmat x) y using 1
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y <;>
    simp [secondOrderDefectGraph, h]

/-- Let `E = A - M` be the adjacency matrix after deleting the canonical
triangle-free matching.  Its square has an exact five-color decomposition.
This is the matrix form of the saturated matching-pair quotient: a missing
external two-path is accounted for by an antipodal pair or by one of the
two matching-assisted orientations of an original edge. -/
theorem externalAdjMatrix_sq_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let J := FriendshipTheoremOQ01.onesMatrix V
    (A - M) * (A - M) =
      (d : ℤ) • (1 : Matrix V V ℤ) + J - C - M - A * M - M * A := by
  dsimp only
  have hA2 := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    G hfree hreg
  have hD := secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree
    G
  have hM2 := triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_odd_excessOne
    G hfree hd hodd hreg hcard
  rw [hD] at hA2
  calc
    (G.adjMatrix ℤ - (triangleFreeEdgeGraph G).adjMatrix ℤ) *
        (G.adjMatrix ℤ - (triangleFreeEdgeGraph G).adjMatrix ℤ) =
      G.adjMatrix ℤ * G.adjMatrix ℤ -
        G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ -
        (triangleFreeEdgeGraph G).adjMatrix ℤ * G.adjMatrix ℤ +
        (triangleFreeEdgeGraph G).adjMatrix ℤ *
          (triangleFreeEdgeGraph G).adjMatrix ℤ := by noncomm_ring
    _ = _ := by rw [hA2, hM2]; module

/-- Entrywise saturated form of `externalAdjMatrix_sq_of_odd_excessOne`.
For two distinct vertices, the external two-path count and the four defect
colors sum to exactly one. -/
theorem externalAdjMatrix_sq_entry_partition_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {x y : V} (hxy : x ≠ y) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    ((A - M) * (A - M)) x y + C x y + M x y +
      (A * M) x y + (M * A) x y = 1 := by
  dsimp only
  have h := congrFun (congrFun
    (externalAdjMatrix_sq_of_odd_excessOne
      G hfree hd hodd hreg hcard) x) y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply,
    hxy, if_false, smul_eq_mul, mul_zero] at h
  omega

/-- The matrix `B = AM` is a square incidence realization of the cubic
deficiency graph.  Since `M² = I`, its Gram matrix is exactly `A²`, hence
`(d-1)I + J - C - M`.  Together with the diagonal-one and no-reciprocal-one
lemmas above, this packages the excess-one graph as an oriented symmetric
partial design. -/
theorem matchingIncidence_gram_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let J := FriendshipTheoremOQ01.onesMatrix V
    (A * M) * (M * A) =
      (d - 1 : ℤ) • (1 : Matrix V V ℤ) + J - C - M := by
  dsimp only
  have hM2 := triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_odd_excessOne
    G hfree hd hodd hreg hcard
  have hA2 := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    G hfree hreg
  have hD := secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree
    G
  rw [hD] at hA2
  calc
    (G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ) *
        ((triangleFreeEdgeGraph G).adjMatrix ℤ * G.adjMatrix ℤ) =
      G.adjMatrix ℤ *
        ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          (triangleFreeEdgeGraph G).adjMatrix ℤ) * G.adjMatrix ℤ := by
            simp only [Matrix.mul_assoc]
    _ = G.adjMatrix ℤ * G.adjMatrix ℤ := by rw [hM2]; simp
    _ = _ := by rw [hA2]; module

end

end Erdos85
