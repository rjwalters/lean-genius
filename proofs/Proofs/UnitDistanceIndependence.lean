/-
# Unit Distance Graph Independence Number Bounds

Formalization of independence number bounds for unit distance graphs in the plane.

**The Setting**:
The unit distance graph G has all points of R^2 as vertices, with edges between
points at Euclidean distance exactly 1. For finite point sets S ⊆ R^2, we study
the independence number α(S) = max |I| where I ⊆ S has no two points at distance 1.

**Key Results Formalized**:
- Independent sets in simple graphs: definition and properties
- Independence number: formal definition and bounds
- Connection between colorings and independent sets
- α(G) · k ≥ |V| for any proper k-coloring
- Independence-clique duality: independent in G ↔ clique in Gᶜ
- Hadwiger-Nelson bounds: 5 ≤ χ(R^2) ≤ 7

**Status**: DEEP DIVE
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

open Finset SimpleGraph

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
  exact absurd hu (Finset.not_mem_empty u)

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

/-- A graph with no edges has all sets independent. -/
theorem isIndepFinset_of_bot {V : Type*} (S : Finset V) :
    IsIndepFinset (⊥ : SimpleGraph V) S := by
  intro u _ v _ _ hadj
  exact hadj

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
## Part VI: Independence Number
-/

/-- The independence number of a finite graph: the maximum size of an independent set. -/
noncomputable def indepNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ S : Finset V, IsIndepFinset G S ∧ S.card = n}

/-- Every independent set has cardinality at most the independence number. -/
theorem indep_card_le_indepNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (hS : IsIndepFinset G S) :
    S.card ≤ indepNumber G := by
  apply le_csSup
  · exact ⟨Fintype.card V, fun m hm => by
      obtain ⟨T, _, rfl⟩ := hm
      exact Finset.card_le_card (Finset.subset_univ T)⟩
  · exact ⟨S, hS, rfl⟩

/-- The independence number is at least 1 for nonempty graphs. -/
theorem indepNumber_pos {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) : 0 < indepNumber G := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h1 : ({v} : Finset V).card ≤ indepNumber G :=
    indep_card_le_indepNumber G {v} (isIndepFinset_singleton G v)
  simp at h1
  omega

/-- The independence number is at most |V|. -/
theorem indepNumber_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    indepNumber G ≤ Fintype.card V := by
  apply csSup_le
  · exact ⟨0, ∅, isIndepFinset_empty G, by simp⟩
  · rintro m ⟨S, _, rfl⟩
    exact Finset.card_le_card (Finset.subset_univ S)

/-- The independence number of the empty graph equals |V|. -/
theorem indepNumber_bot {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G = ⊥) :
    indepNumber G = Fintype.card V := by
  apply le_antisymm (indepNumber_le_card G)
  have hIndep : IsIndepFinset G (Finset.univ : Finset V) := by
    subst hG; exact isIndepFinset_of_bot Finset.univ
  have hcard : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  calc Fintype.card V = (Finset.univ : Finset V).card := hcard.symm
    _ ≤ indepNumber G := indep_card_le_indepNumber G Finset.univ hIndep

/-
## Part VII: Independence and Clique Duality
-/

/-- **Independence-Clique Duality**: An independent set in G is exactly a set where
    all distinct pairs are non-adjacent, which is the same as a clique in the complement.
    We state this as: S independent in G implies the set-version is a clique in Gᶜ. -/
theorem indepSet_iff_compl_clique {V : Type*} (G : SimpleGraph V) (S : Set V) :
    IsIndepSet G S ↔ (Gᶜ).IsClique S := by
  constructor
  · intro hI u hu v hv huv
    -- Gᶜ.Adj u v means ⟨u ≠ v, ¬G.Adj u v⟩
    exact ⟨huv, hI u hu v hv huv⟩
  · intro hC u hu v hv huv hadj
    have hcadj := hC hu hv huv
    exact hcadj.2 hadj

/-- The Finset version: S independent in G iff the corresponding set is a clique in Gᶜ. -/
theorem indepFinset_iff_compl_clique {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    IsIndepFinset G S ↔ (Gᶜ).IsClique (S : Set V) := by
  rw [← indepSet_iff_compl_clique]
  rfl

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

/-- **Independence number lower bound from coloring**:
    If a graph has a proper k-coloring, then α(G) · k ≥ |V|.
    This follows from: each color class is independent with size ≤ α(G),
    and the color classes partition V, so |V| = Σ|Cᵢ| ≤ k · α(G). -/
theorem indep_times_colors_ge_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (_hk : k > 0) (c : V → Fin k)
    (hc : IsProperColoring G c) :
    indepNumber G * k ≥ Fintype.card V := by
  -- Each color class is independent, and their sizes sum to |V|
  have hsum : Fintype.card V =
      (Finset.univ : Finset (Fin k)).sum
        (fun i => (Finset.univ.filter (fun v => c v = i)).card) := by
    rw [← Finset.card_univ (α := V)]
    rw [← Finset.card_biUnion]
    · congr 1
      ext v; simp
    · intro i _ j _ hij
      apply Finset.disjoint_filter.mpr
      intro x _ hxi hxj
      exact hij (hxi.symm.trans hxj)
  -- Each color class has size ≤ α(G)
  have hle : ∀ i : Fin k,
      (Finset.univ.filter (fun v => c v = i)).card ≤ indepNumber G := by
    intro i
    exact indep_card_le_indepNumber G _
      (proper_coloring_gives_independent_partition G c hc i)
  -- Sum of k things each ≤ α is ≤ k·α
  have hbound : (Finset.univ : Finset (Fin k)).sum
      (fun i => (Finset.univ.filter (fun v => c v = i)).card) ≤
      (Finset.univ : Finset (Fin k)).sum (fun _ => indepNumber G) := by
    apply Finset.sum_le_sum
    intro i _
    exact hle i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  linarith [mul_comm (indepNumber G) k]

/-
## Part IX: Summary

This file establishes:
1. **Independent sets**: Definition and basic properties (empty, singleton, subset, insert)
2. **Independence number**: Formal definition as sSup + basic bounds
3. **Coloring connection**: Color classes are independent sets
4. **α·k ≥ n**: Independence number times chromatic number covers all vertices
5. **Independence-clique duality**: Independent in G ↔ clique in Gᶜ
6. **Hadwiger-Nelson**: Formal statement of 5 ≤ χ(R²) ≤ 7
7. **Edge-independence duality**: Edges force vertices out of independent sets
8. **Extremal cases**: Empty graph (α = n), complete graph (α = 1)

### Proved Theorems (0 sorries)
- `isIndepFinset_empty`: ∅ is independent
- `isIndepFinset_singleton`: {v} is independent
- `isIndepFinset_subset`: Subsets preserve independence
- `isIndepFinset_iff`: Characterization of independence
- `isIndepFinset_of_bot`: Empty graph has all sets independent
- `isIndepFinset_insert`: Growing independent sets
- `color_class_independent`: Color classes are independent
- `hadwiger_nelson_bounds`: Combined HN bounds
- `edge_leaves_indep`: Edges force vertices out
- `exists_nonempty_indep`: Nonempty graphs have nonempty independent sets
- `indep_card_le_univ`: |S| ≤ |V|
- `indep_card_le_indepNumber`: |S| ≤ α(G)
- `indepNumber_pos`: α(G) ≥ 1 for nonempty graphs
- `indepNumber_le_card`: α(G) ≤ |V|
- `indepNumber_bot`: α(⊥) = |V|
- `indepSet_iff_compl_clique`: Independent ↔ clique in complement (Set version)
- `indepFinset_iff_compl_clique`: Independent ↔ clique in complement (Finset version)
- `indep_top_singleton`: Complete graph has α = 1
- `color_class_partition`: Each vertex in exactly one color class
- `proper_coloring_gives_independent_partition`: Proper colorings give independent partitions
- `indep_times_colors_ge_card`: α(G) · k ≥ n

### Axioms Used (2)
- `hadwiger_nelson_lower_bound`: De Grey's 5-color lower bound (2018)
- `hadwiger_nelson_upper_bound`: 7-coloring upper bound
-/

end UnitDistanceIndependence
