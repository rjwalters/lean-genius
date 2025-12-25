import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-!
# Randomized MaxCut Approximation Algorithm

## What This Proves
We prove that a simple randomized algorithm achieves a 1/2-approximation for the
Maximum Cut problem in expectation. The algorithm: assign each vertex to partition
A or B uniformly at random.

## The MaxCut Problem
Given a graph G = (V, E), partition V into two disjoint sets A and B to maximize
the number of edges crossing between them. This is NP-Complete, but we prove the
randomized algorithm achieves E[|C|] >= |MaxCut|/2.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `SimpleGraph` for graph structure,
  `Finset` for finite sets, and `Sym2` for unordered edges.
- **Original Contributions:** The Cut structure, edge indicator functions, and all
  six core theorems are adapted from the source with Mathlib integration.
- **Key Insight:** Linearity of expectation allows us to compute E[|C|] as the sum
  of individual edge probabilities, each being 1/2.

## Main Results
1. `cut_size_eq_sum_indicators` : |C| = sum of edge indicators
2. `count_diff_assignments` : Half of 2^|V| assignments separate any two vertices
3. `prob_edge_in_cut` : Pr[e in C] = 1/2 for any edge
4. `expected_cut_size` : E[|C|] = |E|/2 (the main theorem)
5. `maxCut_le_edges` : MaxCut <= |E|
6. `rand_approx_guarantee` : E[|C|] >= MaxCut/2 (the approximation guarantee)

## Status
- [x] Complete proof
- [x] Uses Mathlib for graph infrastructure
- [x] Fully verified (no sorries)

## Mathlib Dependencies
- `SimpleGraph` : Graph structure with adjacency relation
- `Finset` : Finite set operations and cardinality
- `Sym2` : Unordered pairs for edges
- `edgeFinset` : Finite set of graph edges

Original author: Aditya Bhamra
Source: https://abhamra.com/blog/randomized-maxcut/
Repository: https://github.com/abhamra/verif-randomized-maxcut
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The Cut Structure

A cut partitions vertices into two disjoint sets A and B.
The cut value is the number of edges with one endpoint in each set.
-/

/-- A cut of a graph partitions vertices into two disjoint sets A and B.
    Proof obligations ensure A ∪ B = V and A ∩ B = ∅. -/
structure Cut (V : Type*) (G : SimpleGraph V) [DecidableEq V] [Fintype V] where
  A : Finset V
  B : Finset V
  partition : A ∪ B = Finset.univ
  disjoint  : Disjoint A B

namespace Cut

/-- Determine whether an edge is in the cut (endpoints in different partitions). -/
def edgeInCut {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  (C : Cut V G) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun u v => (u ∈ C.A ∧ v ∈ C.B) ∨ (u ∈ C.B ∧ v ∈ C.A),
    fun _ _ => by simp only [or_comm, and_comm]⟩ e

/-- The size of a cut: count of edges crossing between A and B. -/
def size {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj] (C : Cut V G) : ℕ :=
  (G.edgeFinset.filter (fun e => C.edgeInCut e)).card

/-- Construct a cut from a boolean assignment function.
    Vertices where f returns true go to A, others to B. -/
def ofAssignment {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  (f : V → Bool) : Cut V G where
    A := Finset.univ.filter (fun v => f v)
    B := Finset.univ.filter (fun v => !f v)
    partition := by
      ext v
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases f v <;> simp
    disjoint := by
      simp only [Finset.disjoint_iff_inter_eq_empty]
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.not_eq_true, Finset.not_mem_empty, iff_false, not_and]
      intro h
      simp [h]

end Cut

/-! ## The Randomized Algorithm

The algorithm is remarkably simple: for each vertex, flip a fair coin
to decide whether it goes to A or B.
-/

/-- The randomized MaxCut algorithm: given a random boolean assignment
    (representing fair coin flips), construct the corresponding cut. -/
def randomizedMaxCut {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} : (V → Bool) → Cut V G :=
  fun assignment => Cut.ofAssignment (G := G) assignment

/-- Edge indicator function: returns 1 if edge is in the cut, 0 otherwise.
    This is the characteristic function used in the expectation calculation. -/
def edgeIndicator {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  (C : Cut V G) (e : Sym2 V) : ℕ :=
  if Cut.edgeInCut C e then 1 else 0

/-! ## Theorem 1: Cut Size as Sum of Indicators

The size of any cut equals the sum of its edge indicator values.
This allows us to use linearity of expectation.
-/

/-- **Theorem 1**: The cut size equals the sum of edge indicators.
    |C| = sum of edge indicators for all edges e in E -/
lemma cut_size_eq_sum_indicators {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (assignment : V → Bool) :
    (Cut.ofAssignment (G := G) assignment).size =
    ∑ e ∈ G.edgeFinset, edgeIndicator (Cut.ofAssignment (G := G) assignment) e := by
      unfold Cut.size edgeIndicator
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-! ## Theorem 2: Counting Different Assignments

For any two distinct vertices u ≠ v, exactly half of all possible
assignments place them in different partitions.
-/

/-- **Theorem 2**: Half of the 2^|V| assignments have f(u) ≠ f(v).
    This is the combinatorial heart of the probability calculation.

    The proof constructs a bijection via toggle operation. -/
lemma count_diff_assignments {V : Type*} [Fintype V] [DecidableEq V]
  (u v : V) (huv : u ≠ v) : 2 * (Finset.univ.filter (fun f : V → Bool => f u ≠ f v)).card =
    Fintype.card (V → Bool) := by
    -- Toggle operation: flip the value at u
    let toggle : (V → Bool) → (V → Bool) := fun f => Function.update f u (!f u)
    -- Toggle is an involution
    have toggle_inv : ∀ f, toggle (toggle f) = f := fun f => by
      ext w
      simp only [toggle]
      by_cases hw : w = u
      · subst hw; simp
      · simp [Function.update_noteq hw, Function.update_noteq hw]
    -- Toggle swaps "same" and "different" assignments
    have toggle_swap : ∀ f, (f u ≠ f v) ↔ (toggle f u = toggle f v) := fun f => by
      simp only [toggle, Function.update_same, Function.update_noteq huv.symm]
      cases f u <;> cases f v <;> decide
    -- Bijection between "different" and "same" sets
    let diff := Finset.univ.filter (fun f : V → Bool => f u ≠ f v)
    let same := Finset.univ.filter (fun f : V → Bool => f u = f v)
    have card_eq : diff.card = same.card := by
      apply Finset.card_bij (fun f _ => toggle f)
      · intro f hf
        simp only [diff, same, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hf ⊢
        exact (toggle_swap f).mp hf
      · intro f₁ _ f₂ _ h
        calc f₁ = toggle (toggle f₁) := (toggle_inv f₁).symm
          _ = toggle (toggle f₂) := by rw [h]
          _ = f₂ := toggle_inv f₂
      · intro g hg
        refine ⟨toggle g, ?_, toggle_inv g⟩
        simp only [diff, same, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hg ⊢
        have : toggle g u ≠ toggle g v := by
          simp only [toggle, Function.update_same, Function.update_noteq huv.symm]
          cases h1 : g u <;> cases h2 : g v <;> simp_all
        exact this
    -- diff and same partition the space
    have partition : diff.card + same.card = Fintype.card (V → Bool) := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext f
        simp only [diff, same, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and, ne_eq]
        by_cases h : f u = f v <;> simp [h]
      · simp only [diff, same, Finset.disjoint_filter]
        intro f _ h
        simp [h]
    -- Combine
    linarith

/-! ## Theorem 3: Edge Probability

Each edge has exactly 1/2 probability of being in a random cut.
This follows from the counting lemma above.
-/

/-- **Theorem 3**: Pr[e in C] = 1/2 for any edge e.
    The probability that a random cut contains edge e is exactly 1/2. -/
lemma prob_edge_in_cut {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
  (e : Sym2 V) (h : ¬e.IsDiag) :
  (∑ assignment : V → Bool, (edgeIndicator (G := G) (randomizedMaxCut assignment) e : ℝ)) /
  (Fintype.card (V → Bool)) = 1/2 := by
    -- Destruct edge into two endpoints
    induction e using Sym2.ind with
    | _ u v =>
      -- Extract u ≠ v from non-diagonal
      simp only [Sym2.isDiag_iff_proj_eq] at h
      -- Show indicator = 1 iff assignment separates u and v
      have indicator_eq : ∀ f : V → Bool,
          (edgeIndicator (G := G) (randomizedMaxCut f) s(u, v) : ℝ) =
          if f u ≠ f v then 1 else 0 := by
        intro f
        unfold edgeIndicator randomizedMaxCut Cut.edgeInCut Cut.ofAssignment
        simp only [Sym2.lift_mk, Finset.mem_filter, Finset.mem_univ, true_and,
          Bool.not_eq_true, decide_eq_true_eq]
        cases f u <;> cases f v <;> simp
      simp_rw [indicator_eq]
      -- Sum of indicators equals cardinality of filter
      have sum_eq : (∑ f : V → Bool, (if f u ≠ f v then (1 : ℝ) else 0)) =
          ((Finset.univ.filter (fun f : V → Bool => f u ≠ f v)).card : ℝ) := by
        rw [Finset.sum_ite]
        simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [sum_eq]
      -- Apply count_diff_assignments
      have key := count_diff_assignments u v h
      simp only [ne_eq] at key sum_eq ⊢
      have h1 : (Fintype.card (V → Bool) : ℝ) =
          2 * (Finset.univ.filter (fun f : V → Bool => ¬f u = f v)).card := by
        exact_mod_cast key.symm
      rw [h1, mul_comm]
      have hpos : (0 : ℝ) < (Finset.univ.filter (fun f : V → Bool => ¬f u = f v)).card := by
        simp only [Nat.cast_pos, Finset.card_pos, Finset.filter_nonempty_iff]
        use fun x => decide (x = u)
        simp only [Finset.mem_univ, true_and, decide_eq_true]
        have hvu : v ≠ u := fun hvu => h hvu.symm
        simp [hvu]
      rw [div_mul_eq_div_div, div_self (ne_of_gt hpos), one_div]

/-! ## Theorem 4: Expected Cut Size (Main Result)

The expected size of a random cut is exactly |E|/2.
This is the central theorem, proved using linearity of expectation.
-/

/-- **Theorem 4 (Main)**: E[|C|] = |E|/2.
    The expected cut size equals half the number of edges.
    Proof uses linearity of expectation: E[|C|] = E[∑ χₑ] = ∑ E[χₑ] = ∑ 1/2 = |E|/2 -/
theorem expected_cut_size {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
  [DecidableRel G.Adj] :
    (∑ assignment : V → Bool,
    ((randomizedMaxCut (G := G) assignment).size : ℝ)) / (Fintype.card (V → Bool)) =
      (G.edgeFinset.card : ℝ) / 2 := by
        -- Step 1: Express cut size as sum of indicators
        have size_eq : ∀ f, (randomizedMaxCut (G := G) f).size =
            ∑ e ∈ G.edgeFinset, edgeIndicator (G := G) (randomizedMaxCut (G := G) f) e := by
          intro f
          exact cut_size_eq_sum_indicators G f
        simp_rw [size_eq]
        -- Step 2: Cast to ℝ
        simp only [Nat.cast_sum]
        -- Step 3: Swap order of summation
        rw [Finset.sum_comm]
        -- Step 4: Factor out division
        rw [Finset.sum_div]
        -- Step 5: Apply prob_edge_in_cut to each edge
        have edge_prob : ∀ e ∈ G.edgeFinset,
            (∑ f : V → Bool, (edgeIndicator (G := G) (randomizedMaxCut (G := G) f) e : ℝ)) /
            Fintype.card (V → Bool) = 1/2 := by
          intro e he
          have not_diag : ¬e.IsDiag := G.not_isDiag_of_mem_edgeFinset he
          exact prob_edge_in_cut G e not_diag
        rw [Finset.sum_congr rfl edge_prob]
        simp only [Finset.sum_const, smul_eq_mul]
        ring

/-! ## Theorem 5: MaxCut Upper Bound

The maximum cut value cannot exceed the total number of edges.
-/

/-- The maximum cut value: supremum over all possible assignments. -/
def maxCutValue {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
  [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun f : V → Bool => (Cut.ofAssignment (G := G) f).size)

/-- **Theorem 5**: MaxCut ≤ |E|.
    No cut can contain more edges than exist in the graph. -/
lemma maxCut_le_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    maxCutValue G ≤ G.edgeFinset.card := by
  unfold maxCutValue
  apply Finset.sup_le
  intro S _
  unfold Cut.ofAssignment Cut.size
  -- A filtered subset of edges has cardinality ≤ original
  exact Finset.card_filter_le _ _

/-! ## Theorem 6: Approximation Guarantee

The randomized algorithm achieves a 1/2-approximation in expectation.
-/

/-- **Theorem 6 (Approximation Guarantee)**: E[|C|] >= MaxCut/2.
    The expected cut size is at least half the optimal.
    This proves the randomized algorithm is a 1/2-approximation. -/
theorem rand_approx_guarantee {V : Type*} [DecidableEq V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ assignment : V → Bool,
    ((randomizedMaxCut (G := G) assignment).size : ℝ)) / (Fintype.card (V → Bool)) >=
    (maxCutValue G : ℝ) / 2 := by
      rw [expected_cut_size, ge_iff_le]
      have h := maxCut_le_edges (G := G)
      have h' : (maxCutValue G : ℝ) ≤ G.edgeFinset.card := by exact_mod_cast h
      exact div_le_div_of_nonneg_right h' (by norm_num : (0 : ℝ) ≤ 2)

#check cut_size_eq_sum_indicators
#check count_diff_assignments
#check prob_edge_in_cut
#check expected_cut_size
#check maxCut_le_edges
#check rand_approx_guarantee
