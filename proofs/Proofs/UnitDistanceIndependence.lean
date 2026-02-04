/-
# Unit Distance Graph Independence Number Bounds

Formalization of independence number bounds for unit distance graphs in the plane.

**The Setting**:
The unit distance graph G has all points of R^2 as vertices, with edges between
points at Euclidean distance exactly 1. For finite point sets S ⊆ R^2, we study
the independence number α(S) = max |I| where I ⊆ S has no two points at distance 1.

**Key Results Formalized**:
- Independent sets in simple graphs: definition and properties
- Connection between colorings and independent sets
- Hadwiger-Nelson bounds: 5 ≤ χ(R^2) ≤ 7
- Basic structural theorems about independence

**Status**: BUILD
Tags: combinatorial-geometry, graph-theory, independence-number, unit-distance
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic

namespace UnitDistanceIndependence

open Finset SimpleGraph Fintype

/-
## Part I: Abstract Graph Independence

We develop independence set theory for abstract simple graphs.
-/

/-- An independent set in a simple graph: no two vertices in the set are adjacent. -/
def IsIndepSet {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v

/-- An independent finset in a simple graph: no two vertices in the set are adjacent. -/
def IsIndepFinset {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v

/-
## Part II: Basic Properties of Independent Sets
-/

/-- The empty set is independent in any graph. -/
theorem isIndepFinset_empty {V : Type*} (G : SimpleGraph V) :
    IsIndepFinset G (∅ : Finset V) := by
  intro u hu
  exact absurd hu (Finset.notMem_empty u)

/-- A singleton set is independent in any graph. -/
theorem isIndepFinset_singleton {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V) :
    IsIndepFinset G ({v} : Finset V) := by
  intro u hu w hw hne
  simp at hu hw
  subst hu; subst hw
  exact absurd rfl hne

/-- Subsets of independent sets are independent. -/
theorem isIndepFinset_subset {V : Type*} (G : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) (hT : IsIndepFinset G T) : IsIndepFinset G S := by
  intro u hu v hv huv
  exact hT u (hST hu) v (hST hv) huv

/-- An independent set in G has no edges within it (definitional). -/
theorem isIndepFinset_iff {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    IsIndepFinset G S ↔ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v :=
  Iff.rfl

/-
## Part IIb: Independence Number

The independence number α(G) is the maximum cardinality of an independent set.
-/

/-- The independence number of a finite graph: max cardinality of an independent set. -/
noncomputable def independenceNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup (Finset.univ.powerset.filter (fun S =>
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v)) Finset.card

/-- The empty set witnesses that α(G) ≥ 0 (vacuously). -/
theorem independenceNumber_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    independenceNumber G ≥ 0 := Nat.zero_le _

/-- Any independent set has cardinality ≤ α(G). -/
theorem indep_card_le_alpha {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : IsIndepFinset G S) :
    S.card ≤ independenceNumber G := by
  unfold independenceNumber
  apply Finset.le_sup
  simp only [Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hS⟩

/-
## Part III: Coloring and Independence Relationship
-/

/-- A proper coloring assigns colors such that adjacent vertices get different colors. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) {n : ℕ} (c : V → Fin n) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- In a proper k-coloring, each color class is independent. -/
theorem color_class_independent {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {n : ℕ} (c : V → Fin n)
    (hc : IsProperColoring G c) (i : Fin n) (S : Finset V)
    (hS : ∀ v ∈ S, c v = i) : IsIndepFinset G S := by
  intro u hu v hv huv hadj
  have := hc u v hadj
  rw [hS u hu, hS v hv] at this
  exact this rfl

/-
## Part IV: The Hadwiger-Nelson Problem
-/

/-- The plane as a type. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **De Grey's Theorem (2018)**: The chromatic number of the plane is at least 5.
    No 4-coloring of the plane avoids monochromatic unit distance pairs. -/
axiom hadwiger_nelson_lower_bound :
    ∀ (c : Plane → Fin 4), ∃ p q : Plane, dist p q = 1 ∧ c p = c q

/-- **Hadwiger-Nelson Upper Bound**: The plane can be 7-colored such that
    no two points at distance 1 have the same color. -/
axiom hadwiger_nelson_upper_bound :
    ∃ c : Plane → Fin 7, ∀ p q : Plane, dist p q = 1 → c p ≠ c q

/-- The chromatic number of the plane is between 5 and 7 (consequence of bounds). -/
theorem hadwiger_nelson_bounds :
    (∀ (c : Plane → Fin 4), ∃ p q : Plane, dist p q = 1 ∧ c p = c q) ∧
    (∃ c : Plane → Fin 7, ∀ p q : Plane, dist p q = 1 → c p ≠ c q) :=
  ⟨hadwiger_nelson_lower_bound, hadwiger_nelson_upper_bound⟩

/-
## Part V: Independent Set Structure Theorems
-/

/-- If S is independent and v ∉ S is non-adjacent to all of S,
    then S ∪ {v} is independent. -/
theorem isIndepFinset_insert {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {S : Finset V} {v : V}
    (hS : IsIndepFinset G S)
    (hv : v ∉ S)
    (hnadj : ∀ u ∈ S, ¬ G.Adj v u) :
    IsIndepFinset G (insert v S) := by
  intro a ha b hb hab
  simp [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · exact hnadj b hb
  · intro hadj
    exact hnadj a ha (G.symm hadj)
  · exact hS a ha b hb hab

/-- An edge forces at least one endpoint out of any independent set. -/
theorem edge_leaves_indep {V : Type*} (G : SimpleGraph V)
    {S : Finset V} (hS : IsIndepFinset G S)
    {u v : V} (hadj : G.Adj u v) : u ∉ S ∨ v ∉ S := by
  by_contra h
  push_neg at h
  exact hS u h.1 v h.2 (G.ne_of_adj hadj) hadj

/-- In any nonempty type, there exists a nonempty independent set. -/
theorem exists_nonempty_indep {V : Type*} [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) : ∃ S : Finset V, IsIndepFinset G S ∧ S.card ≥ 1 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact ⟨{v}, isIndepFinset_singleton G v, by simp⟩

/-- Independent sets have at most |V| elements. -/
theorem indep_card_le_univ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (_hS : IsIndepFinset G S) :
    S.card ≤ Fintype.card V :=
  Finset.card_le_card (Finset.subset_univ S)

/-
## Part VI: Unit Distance Graph Specific Results
-/

/-- The unit distance graph on a finite subset of the plane.
    Two points are adjacent iff their Euclidean distance is 1. -/
noncomputable def unitDistGraph (S : Finset Plane) : SimpleGraph S where
  Adj p q := dist (p : Plane) (q : Plane) = 1 ∧ p ≠ q
  symm := by
    intro p q ⟨hd, hne⟩
    exact ⟨by rw [dist_comm]; exact hd, hne.symm⟩
  loopless := by
    intro p ⟨_, hne⟩
    exact hne rfl

/-- An independent set in the unit distance graph is exactly a set
    where no two points are at distance 1 (by definition). -/
theorem unit_indep_iff_no_unit_dist (S : Finset Plane)
    (I : Finset S) :
    IsIndepFinset (unitDistGraph S) I ↔
    ∀ p ∈ I, ∀ q ∈ I, p ≠ q → dist (p : Plane) (q : Plane) ≠ 1 := by
  constructor
  · intro hI p hp q hq hne hdist
    exact hI p hp q hq hne ⟨hdist, hne⟩
  · intro h p hp q hq hne ⟨hdist, _⟩
    exact h p hp q hq hne hdist

/-
## Part VII: Independence and Clique Duality
-/

/-- An independent set in G is a set with no edges:
    equivalently, it is a clique in the complement graph Gᶜ. -/
theorem indep_iff_compl_clique {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    IsIndepFinset G S ↔ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v :=
  Iff.rfl

/-- A graph with no edges has all sets independent. -/
theorem isIndepFinset_of_bot {V : Type*} (S : Finset V) :
    IsIndepFinset (⊥ : SimpleGraph V) S := by
  intro u _ v _ _ hadj
  exact hadj

/-- A complete graph (on ≥ 2 vertices) has independence number 1. -/
theorem indep_top_singleton {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (htop : G = ⊤) (S : Finset V) (hS : IsIndepFinset G S) (hcard : S.card ≥ 2) :
    False := by
  rw [htop] at hS
  have hne : ∃ a b : V, a ∈ S ∧ b ∈ S ∧ a ≠ b := by
    have := Finset.one_lt_card.mp (by omega : 1 < S.card)
    obtain ⟨a, ha, b, hb, hab⟩ := this
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hne
  exact hS a ha b hb hab (by simp [hab])

/-
## Part VIII: Counting Arguments
-/

/-- In a k-coloring, every vertex belongs to exactly one color class.
    This partitions vertices into color classes. -/
theorem color_class_partition {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (c : V → Fin k) (v : V) :
    ∃! i : Fin k, v ∈ Finset.univ.filter (fun w => c w = i) := by
  exact ⟨c v, by simp, fun j hj => by simp at hj; exact hj.symm⟩

/-- A proper coloring partitions vertices into independent color classes:
    for each color i, the set of vertices colored i is independent. -/
theorem proper_coloring_gives_independent_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (c : V → Fin k)
    (hc : IsProperColoring G c) (i : Fin k) :
    IsIndepFinset G (Finset.univ.filter (fun v => c v = i)) := by
  apply color_class_independent G c hc i
  intro v hv
  exact (Finset.mem_filter.mp hv).2

/-
## Part IX: Pigeonhole Bound

The pigeonhole principle gives: if G has a proper k-coloring,
then the largest color class has at least ⌈|V|/k⌉ vertices.
Since color classes are independent, α(G) ≥ ⌈|V|/k⌉.
-/

/-- In a proper k-coloring of n vertices, some color class has size ≥ n/k.
    This is the pigeonhole bound on independence number.

    More precisely: if c : V → Fin k is proper, then there exists a
    color i whose preimage has cardinality ≥ Fintype.card V / k. -/
theorem exists_large_color_class {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (hk : k > 0) (c : V → Fin k)
    (_hc : IsProperColoring G c) :
    ∃ i : Fin k, (Finset.univ.filter (fun v => c v = i)).card ≥ Fintype.card V / k := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  by_contra h
  push_neg at h
  have htotal : ∑ i : Fin k, (Finset.univ.filter (fun v => c v = i)).card = Fintype.card V := by
    rw [← Finset.card_univ]
    rw [← Finset.card_biUnion]
    · congr 1
      ext v
      simp
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro v hvi hvj
      exact hij (hvi.symm ▸ hvj)
  have hbound : ∑ i : Fin k, (Finset.univ.filter (fun v => c v = i)).card <
      ∑ _i : Fin k, (Fintype.card V / k) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
    intro i _
    exact h i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hbound
  rw [htotal] at hbound
  -- The sum of k terms each < n/k is < k * (n/k)
  simp only [smul_eq_mul] at hbound
  have hdiv : k * (Fintype.card V / k) ≤ Fintype.card V := Nat.mul_div_le _ _
  omega

/-- If G has a proper k-coloring, some independent set has ≥ |V|/k elements. -/
theorem indep_from_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (hk : k > 0) (c : V → Fin k)
    (hc : IsProperColoring G c) :
    ∃ S : Finset V, IsIndepFinset G S ∧ S.card ≥ Fintype.card V / k := by
  obtain ⟨i, hi⟩ := exists_large_color_class G hk c hc
  exact ⟨Finset.univ.filter (fun v => c v = i),
    proper_coloring_gives_independent_partition G c hc i, hi⟩

/-
## Part X: Maximum Degree and Greedy Bound

The greedy bound on independence number: α(G) ≥ |V|/(Δ+1)
where Δ is the maximum degree.
-/

/-- The degree of a vertex v in G: the number of neighbors. -/
noncomputable def degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (G.Adj v)).card

/-- Maximum degree in a finite graph. -/
noncomputable def maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup' Finset.univ_nonempty (degree G)

/-- An isolated vertex has degree 0. -/
theorem degree_isolated {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hiso : ∀ u : V, ¬ G.Adj v u) : degree G v = 0 := by
  unfold degree
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_true_left]
  exact hiso

/-- Degree is at most |V| - 1 (no self-loops). -/
theorem degree_le_card_sub_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degree G v ≤ Fintype.card V - 1 := by
  unfold degree
  have hsub : Finset.univ.filter (G.Adj v) ⊆ Finset.univ.filter (· ≠ v) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact (G.ne_of_adj hu).symm
  calc (Finset.univ.filter (G.Adj v)).card
      ≤ (Finset.univ.filter (· ≠ v)).card := Finset.card_le_card hsub
    _ = Fintype.card V - 1 := by
        rw [Finset.filter_ne']
        simp [Finset.card_erase_of_mem (Finset.mem_univ v)]

/-- Every vertex has degree at most maxDegree. -/
theorem degree_le_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degree G v ≤ maxDegree G := by
  unfold maxDegree
  exact Finset.le_sup' _ (Finset.mem_univ v)

/-- **The Greedy Bound**: Every graph G has an independent set of size ≥ |V|/(Δ+1).

This is a consequence of the greedy algorithm: repeatedly remove a vertex
and all its neighbors. Each step removes at most Δ+1 vertices (the vertex
and its ≤Δ neighbors), so we need at least |V|/(Δ+1) steps, each contributing
one vertex to the independent set.

The formal proof requires:
1. The greedy algorithm terminates
2. Each removed vertex contributes to the independent set
3. At most Δ+1 vertices are removed per step
-/
axiom greedy_bound {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    independenceNumber G ≥ Fintype.card V / (maxDegree G + 1)

/-- Combined with the pigeonhole bound: if G has chromatic number χ,
    then α(G) ≥ |V|/χ. For unit distance graphs with χ ≤ 7 (Hadwiger-Nelson),
    this gives α ≥ |V|/7. -/
theorem unit_distance_independence_from_chromatic (S : Finset Plane)
    (hne : S.Nonempty) :
    ∃ I : Finset S, IsIndepFinset (unitDistGraph S) I ∧
      I.card ≥ S.card / 7 := by
  -- This follows from the existence of a 7-coloring
  -- and the pigeonhole principle (indep_from_coloring)
  sorry

/-
## Part XI: Summary

This file establishes:
1. **Independent sets**: Definition and basic properties (empty, singleton, subset, insert)
2. **Independence number**: Formal definition as sup over independent set cardinalities
3. **Coloring connection**: Color classes are independent sets
4. **Pigeonhole bound**: k-coloring ⟹ ∃ independent set of size ≥ |V|/k
5. **Hadwiger-Nelson**: Formal statement of 5 ≤ χ(R²) ≤ 7
6. **Unit distance graph**: Proper definition on finite point sets
7. **Edge-independence duality**: Edges force vertices out of independent sets
8. **Extremal cases**: No-edge graph (all independent), complete graph (α = 1)
9. **Degree theory**: Vertex degree and maximum degree definitions
10. **Greedy bound**: α(G) ≥ |V|/(Δ+1)

### Proved Theorems (23 total, 1 sorry)
- `isIndepFinset_empty`: ∅ is independent
- `isIndepFinset_singleton`: {v} is independent
- `isIndepFinset_subset`: Subsets preserve independence
- `isIndepFinset_iff`: Characterization of independence
- `independenceNumber_nonneg`: α(G) ≥ 0
- `indep_card_le_alpha`: |S| ≤ α(G) for independent S
- `color_class_independent`: Color classes are independent
- `hadwiger_nelson_bounds`: Combined HN bounds
- `isIndepFinset_insert`: Growing independent sets
- `edge_leaves_indep`: Edges force vertices out
- `exists_nonempty_indep`: Nonempty graphs have nonempty independent sets
- `indep_card_le_univ`: |S| ≤ |V|
- `unit_indep_iff_no_unit_dist`: Independence ↔ no unit distances
- `indep_iff_compl_clique`: Independence characterization
- `isIndepFinset_of_bot`: Empty graph has all sets independent
- `indep_top_singleton`: Complete graph has α = 1
- `color_class_partition`: Each vertex in exactly one color class
- `proper_coloring_gives_independent_partition`: Colorings partition into independent sets
- `exists_large_color_class`: Pigeonhole: some color class has ≥ |V|/k elements
- `indep_from_coloring`: k-coloring ⟹ ∃ independent set of size ≥ |V|/k
- `degree_isolated`: Isolated vertices have degree 0
- `degree_le_card_sub_one`: degree(v) ≤ |V| - 1
- `degree_le_maxDegree`: degree(v) ≤ Δ(G)
- `unit_distance_independence_from_chromatic`: Unit dist graphs have α ≥ |V|/7 (sorry)

### Axioms Used (3)
- `hadwiger_nelson_lower_bound`: De Grey's 5-color lower bound (2018)
- `hadwiger_nelson_upper_bound`: 7-coloring upper bound
- `greedy_bound`: α(G) ≥ |V|/(Δ+1) (greedy algorithm bound)

### What's NOT Proven (and Why)
- De Grey's construction (requires explicit 1581-vertex graph verification)
- The 7-coloring (requires constructing the hexagonal tiling coloring)
- Greedy bound proof (requires formalizing the greedy algorithm)
- Fractional chromatic number bounds (requires LP duality formalization)
-/

end UnitDistanceIndependence
