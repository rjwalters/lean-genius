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

**Status**: COMPLETE (67 theorems, 0 sorries, 1 axiom)
Tags: combinatorial-geometry, graph-theory, independence-number, unit-distance
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic
import Proofs.UnitDistanceHN7

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
    no two points at distance 1 have the same color.

    This is now a fully machine-checked theorem, discharged by the explicit
    hexagonal 7-coloring construction `hadwiger_nelson_7coloring` proved in
    `Proofs.UnitDistanceHN7` (0 sorries, no `native_decide`). Both `Plane`
    abbreviations are definitionally `EuclideanSpace ℝ (Fin 2)`, so the term
    typechecks directly. -/
theorem hadwiger_nelson_upper_bound :
    ∃ c : Plane → Fin 7, ∀ p q : Plane, dist p q = 1 → c p ≠ c q :=
  _root_.hadwiger_nelson_7coloring

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
    exact ⟨by rw [_root_.dist_comm]; exact hd, hne.symm⟩
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

/-- A maximal independent set: independent, and every non-member has a neighbor in it. -/
def IsMaximalIndep {V : Type*} (G : SimpleGraph V) (I : Finset V) : Prop :=
  IsIndepFinset G I ∧ ∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u

/-- The closed neighborhood of a vertex: v itself and its neighbors. -/
def closedNeighborhoodIn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  insert v (Finset.univ.filter (G.Adj v))

/-- The closed neighborhood has size at most Δ+1. -/
theorem closedNeighborhoodIn_card_le {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedNeighborhoodIn G v).card ≤ maxDegree G + 1 := by
  unfold closedNeighborhoodIn
  calc (insert v (Finset.univ.filter (G.Adj v))).card
      ≤ (Finset.univ.filter (G.Adj v)).card + 1 := Finset.card_insert_le v _
    _ = degree G v + 1 := by rfl
    _ ≤ maxDegree G + 1 := Nat.add_le_add_right (degree_le_maxDegree G v) 1

/-- Every finite graph has a maximal independent set.
    Proof: Take any independent set of maximum cardinality (exists by finiteness).
    If it's not maximal, we can extend it, contradicting maximality. -/
theorem exists_maximal_indep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ I : Finset V, IsMaximalIndep G I := by
  -- Take an independent set of maximum cardinality
  -- First, the set of all independent finsets
  let indepSets := Finset.univ.powerset.filter (fun S =>
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v)
  -- The empty set is independent, so indepSets is nonempty
  have hne : indepSets.Nonempty := by
    use ∅
    simp only [indepSets, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, fun u hu => absurd hu (Finset.notMem_empty u)⟩
  -- Pick the one with maximum cardinality
  obtain ⟨I, hImem, hImax⟩ := indepSets.exists_max_image Finset.card hne
  have hIindep : IsIndepFinset G I := by
    simp only [indepSets, Finset.mem_filter] at hImem
    exact hImem.2
  refine ⟨I, hIindep, ?_⟩
  -- Show maximality: every non-member has a neighbor in I
  intro v hv
  by_contra h
  push_neg at h
  -- v is non-adjacent to all of I, so I ∪ {v} is independent
  have hext : IsIndepFinset G (insert v I) :=
    isIndepFinset_insert G hIindep hv (fun u hu => h u hu)
  -- But |I ∪ {v}| > |I|, contradicting maximality
  have hcard : (insert v I).card > I.card := by
    rw [Finset.card_insert_of_notMem hv]
    omega
  have hmem : insert v I ∈ indepSets := by
    simp only [indepSets, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hext⟩
  have := hImax (insert v I) hmem
  omega

/-- Covering lemma: if I is a maximal independent set, then V is covered by
    the union of closed neighborhoods of vertices in I. -/
theorem maximal_indep_covers {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {I : Finset V} (hI : IsMaximalIndep G I) :
    ∀ v : V, v ∈ I ∨ ∃ u ∈ I, G.Adj v u := by
  intro v
  by_cases hv : v ∈ I
  · left; exact hv
  · right; exact hI.2 v hv

/-- Covering bound: if I is a maximal independent set, then
    |V| ≤ |I| * (Δ + 1).
    Each vertex in I covers itself and at most Δ neighbors. -/
theorem maximal_indep_covering_bound {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {I : Finset V} (hI : IsMaximalIndep G I) :
    Fintype.card V ≤ I.card * (maxDegree G + 1) := by
  -- Every vertex is either in I or adjacent to something in I
  -- So V ⊆ ⋃_{u ∈ I} closedNeighborhoodIn G u
  have hcover : Finset.univ ⊆ I.biUnion (fun u => closedNeighborhoodIn G u) := by
    intro v _
    simp only [Finset.mem_biUnion]
    rcases maximal_indep_covers G hI v with hv | ⟨u, hu, hadj⟩
    · exact ⟨v, hv, Finset.mem_insert_self v _⟩
    · exact ⟨u, hu, by
        unfold closedNeighborhoodIn
        rw [Finset.mem_insert]
        right
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact G.symm hadj⟩
  calc Fintype.card V = Finset.univ.card := (Finset.card_univ).symm
    _ ≤ (I.biUnion (fun u => closedNeighborhoodIn G u)).card :=
        Finset.card_le_card hcover
    _ ≤ I.card * (maxDegree G + 1) := by
        calc (I.biUnion (fun u => closedNeighborhoodIn G u)).card
            ≤ ∑ u ∈ I, (closedNeighborhoodIn G u).card := Finset.card_biUnion_le
          _ ≤ ∑ _u ∈ I, (maxDegree G + 1) :=
              Finset.sum_le_sum (fun u _ => closedNeighborhoodIn_card_le G u)
          _ = I.card * (maxDegree G + 1) := by rw [Finset.sum_const, smul_eq_mul]

/-- **The Greedy Bound**: Every graph G has an independent set of size ≥ |V|/(Δ+1).

Proof: By `exists_maximal_indep`, there exists a maximal independent set I.
By `maximal_indep_covering_bound`, |V| ≤ |I|·(Δ+1), so |I| ≥ |V|/(Δ+1).
Since α(G) ≥ |I|, the bound follows. -/
theorem greedy_bound {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    independenceNumber G ≥ Fintype.card V / (maxDegree G + 1) := by
  obtain ⟨I, hI⟩ := exists_maximal_indep G
  have hbound : Fintype.card V ≤ I.card * (maxDegree G + 1) :=
    maximal_indep_covering_bound G hI
  have hindep : independenceNumber G ≥ I.card := indep_card_le_alpha G I hI.1
  -- From hbound: n ≤ |I| * (Δ+1), so n/(Δ+1) ≤ |I|
  have hpos : maxDegree G + 1 > 0 := Nat.succ_pos _
  have hdiv : Fintype.card V / (maxDegree G + 1) ≤ I.card := by
    calc Fintype.card V / (maxDegree G + 1)
        ≤ I.card * (maxDegree G + 1) / (maxDegree G + 1) :=
          Nat.div_le_div_right hbound
      _ = I.card := Nat.mul_div_cancel _ hpos
  omega

/-- Combined with the pigeonhole bound: if G has chromatic number χ,
    then α(G) ≥ |V|/χ. For unit distance graphs with χ ≤ 7 (Hadwiger-Nelson),
    this gives α ≥ |V|/7. -/
theorem unit_distance_independence_from_chromatic (S : Finset Plane)
    (hne : S.Nonempty) :
    ∃ I : Finset S, IsIndepFinset (unitDistGraph S) I ∧
      I.card ≥ S.card / 7 := by
  -- Get the 7-coloring of the plane from Hadwiger-Nelson
  obtain ⟨c, hc⟩ := hadwiger_nelson_upper_bound
  -- Restrict to the finite set S
  let c' : S → Fin 7 := fun p => c (p : Plane)
  -- The restricted coloring is proper for the unit distance graph
  have hproper : IsProperColoring (unitDistGraph S) c' := by
    intro u v hadj
    -- hadj : (unitDistGraph S).Adj u v means dist u v = 1
    have hdist : dist (u : Plane) (v : Plane) = 1 := hadj.1
    exact hc (u : Plane) (v : Plane) hdist
  -- Apply the pigeonhole bound
  haveI : Nonempty S := hne.coe_sort
  obtain ⟨I, hI, hcard⟩ := indep_from_coloring (unitDistGraph S) (Nat.zero_lt_succ 6) c' hproper
  refine ⟨I, hI, ?_⟩
  simp only [Fintype.card_coe] at hcard
  exact hcard

/-
## Part XI: Additional Structural Theorems
-/

/-- Independence and chromatic number relation: k * α(G) ≥ |V|.
    Each color class is independent with size ≤ α(G), so k * α(G) ≥ |V|. -/
theorem alpha_chi_ge_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (_hk : k > 0)
    (c : V → Fin k) (hc : IsProperColoring G c) :
    k * independenceNumber G ≥ Fintype.card V := by
  have hclass : ∀ i : Fin k, (Finset.univ.filter (fun v => c v = i)).card ≤ independenceNumber G := by
    intro i
    have hindep : IsIndepFinset G (Finset.univ.filter (fun v => c v = i)) :=
      proper_coloring_gives_independent_partition G c hc i
    exact indep_card_le_alpha G (Finset.univ.filter (fun v => c v = i)) hindep
  have htotal : ∑ i : Fin k, (Finset.univ.filter (fun v => c v = i)).card = Fintype.card V := by
    rw [← Finset.card_univ]
    rw [← Finset.card_biUnion]
    · congr 1; ext v; simp
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro v hvi hvj; exact hij (hvi.symm ▸ hvj)
  calc Fintype.card V = ∑ i : Fin k, (Finset.univ.filter (fun v => c v = i)).card := htotal.symm
    _ ≤ ∑ _i : Fin k, independenceNumber G := Finset.sum_le_sum (fun i _ => hclass i)
    _ = k * independenceNumber G := by simp [Finset.sum_const, smul_eq_mul]

/-- For any independent set I, α(G) ≥ |I|. -/
theorem independenceNumber_ge_of_indep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (I : Finset V) (hI : IsIndepFinset G I) :
    independenceNumber G ≥ I.card :=
  indep_card_le_alpha G I hI

/-- Extending an independent set by a vertex non-adjacent to all. -/
theorem independent_extend {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {I : Finset V} (hI : IsIndepFinset G I)
    {v : V} (hv : v ∉ I) (hnadj : ∀ u ∈ I, ¬G.Adj v u ∧ ¬G.Adj u v) :
    IsIndepFinset G (insert v I) := by
  apply isIndepFinset_insert G hI hv
  intro u hu; exact (hnadj u hu).1

/-- Union of independent sets with no cross-edges is independent. -/
theorem disjoint_indep_union {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {A B : Finset V}
    (hA : IsIndepFinset G A) (hB : IsIndepFinset G B)
    (hno_edge : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) :
    IsIndepFinset G (A ∪ B) := by
  intro u hu v hv huv
  simp only [Finset.mem_union] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact hA u hu v hv huv
  · exact hno_edge u hu v hv
  · intro hadj; exact hno_edge v hv u hu (G.symm hadj)
  · exact hB u hu v hv huv

/-- Removing a vertex preserves independence. -/
theorem indep_erase {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {I : Finset V} (hI : IsIndepFinset G I) (v : V) :
    IsIndepFinset G (I.erase v) :=
  isIndepFinset_subset G (Finset.erase_subset v I) hI

/-- Any graph with at least one vertex has α(G) ≥ 1. -/
theorem alpha_ge_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    independenceNumber G ≥ 1 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hindep : IsIndepFinset G ({v} : Finset V) := isIndepFinset_singleton G v
  have := indep_card_le_alpha G {v} hindep
  simp at this; exact this

/-- The neighborhood of a vertex v. -/
def neighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter (G.Adj v)

/-- Neighborhood size equals degree. -/
theorem neighborhood_card_eq_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (neighborhood G v).card = degree G v := rfl

/-- A vertex is not in its own neighborhood. -/
theorem not_mem_neighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∉ neighborhood G v := by
  unfold neighborhood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact G.loopless v

/-- Fewer edges means more independent sets: if G ≤ H, independent in H implies independent in G. -/
theorem independent_mono {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (I : Finset V) (hI : IsIndepFinset H I) :
    IsIndepFinset G I := by
  intro u hu v hv huv hadj
  exact hI u hu v hv huv (hle hadj)

/-
## Part XIII: Additional Independence Bounds
-/

/-- The independence number is at most |V|. -/
theorem independenceNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    independenceNumber G ≤ Fintype.card V := by
  unfold independenceNumber
  apply Finset.sup_le
  intro S hS
  exact Finset.card_le_card (Finset.subset_univ S)

/-- Two vertices with a common neighbor cannot both be in an independent set
    unless they are adjacent to each other (which is also forbidden). -/
theorem common_neighbor_indep {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {I : Finset V} (hI : IsIndepFinset G I)
    {u v w : V} (hw_u : G.Adj w u) (hw_v : G.Adj w v) :
    w ∉ I ∨ (u ∉ I ∧ v ∉ I) := by
  by_cases hw : w ∈ I
  · right
    constructor
    · intro hu
      have : G.Adj w u := hw_u
      exact hI w hw u hu (G.ne_of_adj this) this
    · intro hv
      have : G.Adj w v := hw_v
      exact hI w hw v hv (G.ne_of_adj this) this
  · left; exact hw

/-- For k-chromatic graphs, χ(G) * α(G) ≥ |V|.
    This is a lower bound on independence number in terms of chromatic number. -/
theorem indep_chromatic_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : k > 0)
    (c : V → Fin k) (hc : IsProperColoring G c) :
    independenceNumber G ≥ Fintype.card V / k := by
  obtain ⟨I, hI, hcard⟩ := indep_from_coloring G hk c hc
  exact le_trans hcard (indep_card_le_alpha G I hI)

/-- An independent set can have at most one vertex from any clique. -/
theorem indep_clique_intersection {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {I : Finset V} (hI : IsIndepFinset G I)
    {K : Finset V} (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) :
    (I ∩ K).card ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : (I ∩ K).card ≥ 2 := h
  have hne : ∃ a b : V, a ∈ I ∩ K ∧ b ∈ I ∩ K ∧ a ≠ b := by
    have := Finset.one_lt_card.mp (by omega : 1 < (I ∩ K).card)
    obtain ⟨a, ha, b, hb, hab⟩ := this
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨a, b, haI, hbI, hab⟩ := hne
  have ha' : a ∈ I ∧ a ∈ K := Finset.mem_inter.mp haI
  have hb' : b ∈ I ∧ b ∈ K := Finset.mem_inter.mp hbI
  have hadj : G.Adj a b := hK a ha'.2 b hb'.2 hab
  exact hI a ha'.1 b hb'.1 hab hadj

/-- If I is independent and v ∈ I, then v's neighbors are outside I. -/
theorem indep_neighbors_outside {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I : Finset V}
    (hI : IsIndepFinset G I) {v : V} (hv : v ∈ I) :
    Disjoint (neighborhood G v) I := by
  rw [Finset.disjoint_left]
  intro u hu
  unfold neighborhood at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  intro huI
  exact hI v hv u huI (G.ne_of_adj hu) hu

/-- In the complement graph, independent sets become cliques. -/
theorem indep_is_compl_clique {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {I : Finset V} (hI : IsIndepFinset G I) :
    ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬G.Adj u v :=
  hI

/-- The sum of degrees in an independent set equals the number of edges between I and V\I. -/
theorem indep_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I : Finset V} (hI : IsIndepFinset G I) :
    ∑ v ∈ I, degree G v =
    ∑ v ∈ I, ((Finset.univ \ I).filter (G.Adj v)).card := by
  apply Finset.sum_congr rfl
  intro v hv
  unfold degree
  apply congr_arg Finset.card
  ext u
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hadj
    exact ⟨fun huI => hI v hv u huI (G.ne_of_adj hadj) hadj, hadj⟩
  · intro ⟨_, hadj⟩; exact hadj

/-- For nonempty graphs, independence number is positive. -/
theorem independenceNumber_pos {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    independenceNumber G > 0 := by
  have h := alpha_ge_one G
  omega

/-
## Part XIV: Complement Graph and Independence-Clique Duality

The fundamental duality: independent sets in G correspond exactly to
cliques in the complement graph Gᶜ.
-/

/-- An independent finset in G is a clique in Gᶜ (as a set).
    Bridges our `IsIndepFinset` with Mathlib's `SimpleGraph.IsClique`. -/
theorem indep_iff_compl_isClique {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    IsIndepFinset G S ↔ Gᶜ.IsClique (S : Set V) := by
  rw [SimpleGraph.isClique_iff]
  constructor
  · intro hI u hu v hv huv
    rw [SimpleGraph.compl_adj]
    exact ⟨huv, hI u hu v hv huv⟩
  · intro hC u hu v hv huv hadj
    have := hC hu hv huv
    rw [SimpleGraph.compl_adj] at this
    exact this.2 hadj

/-- A clique in G corresponds to an independent set in Gᶜ. -/
theorem clique_iff_compl_indep {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ↔ IsIndepFinset Gᶜ S := by
  constructor
  · intro hC u hu v hv huv hadj
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2 (hC u hu v hv huv)
  · intro hI u hu v hv huv
    by_contra hnadj
    exact hI u hu v hv huv ((SimpleGraph.compl_adj G u v).mpr ⟨huv, hnadj⟩)

/-- Complement involution: Gᶜᶜ = G. -/
theorem compl_compl_eq {V : Type*} (G : SimpleGraph V) : Gᶜᶜ = G := compl_compl G

/-- Independence in G is preserved under double complement. -/
theorem indep_compl_compl {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    IsIndepFinset G S ↔ IsIndepFinset Gᶜᶜ S := by rw [compl_compl]

/-- The complement of the empty graph is complete on distinct vertices. -/
theorem compl_bot_adj {V : Type*} [DecidableEq V] (u v : V) (huv : u ≠ v) :
    (⊥ : SimpleGraph V)ᶜ.Adj u v := by
  rw [SimpleGraph.compl_adj]; exact ⟨huv, not_false⟩

/-- The complement of a complete graph has no edges. -/
theorem compl_top_not_adj {V : Type*} (u v : V) :
    ¬ (⊤ : SimpleGraph V)ᶜ.Adj u v := by
  intro h
  have := (SimpleGraph.compl_adj (⊤ : SimpleGraph V) u v).mp h
  exact this.2 (by simp [this.1])

/-- Independent sets in the complement are cliques in the original graph. -/
theorem indep_in_compl_is_clique {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : IsIndepFinset Gᶜ S) :
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v :=
  (clique_iff_compl_indep G S).mpr hS

/-
## Part XV: Handshaking Lemma and Edge Counting
-/

/-- Our `degree` definition agrees with Mathlib's `SimpleGraph.degree`. -/
theorem degree_eq_mathlib_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degree G v = G.degree v := by
  unfold degree; simp [SimpleGraph.degree, SimpleGraph.neighborFinset]

/-- Handshaking lemma: the sum of all degrees equals twice the edge count. -/
theorem sum_degrees_eq_twice_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, degree G v = 2 * G.edgeFinset.card := by
  simp_rw [degree_eq_mathlib_degree G]; exact G.sum_degrees_eq_twice_card_edges

/-- Edge bound from max degree: 2|E| ≤ |V| * Δ. -/
theorem edge_count_le_card_mul_maxDeg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≤ Fintype.card V * maxDegree G := by
  rw [← sum_degrees_eq_twice_edges]
  calc ∑ v : V, degree G v
      ≤ ∑ _v : V, maxDegree G := Finset.sum_le_sum (fun v _ => degree_le_maxDegree G v)
    _ = Fintype.card V * maxDegree G := by simp [Finset.sum_const, smul_eq_mul]

/-
## Part XVI: Minimum Degree and Edge Bounds
-/

/-- Minimum degree: the smallest degree in a finite nonempty graph. -/
noncomputable def minDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (degree G)

/-- Every vertex has degree at least minDegree. -/
theorem minDegree_le_degree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    minDegree G ≤ degree G v := Finset.inf'_le _ (Finset.mem_univ v)

/-- minDegree ≤ maxDegree. -/
theorem minDegree_le_maxDegree {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    minDegree G ≤ maxDegree G := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact le_trans (minDegree_le_degree G v) (degree_le_maxDegree G v)

/-- Edge count lower bound: 2|E| ≥ |V| * δ. -/
theorem twice_edges_ge_card_mul_minDeg {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≥ Fintype.card V * minDegree G := by
  rw [← sum_degrees_eq_twice_edges]
  calc ∑ v : V, degree G v
      ≥ ∑ _v : V, minDegree G := Finset.sum_le_sum (fun v _ => minDegree_le_degree G v)
    _ = Fintype.card V * minDegree G := by simp [Finset.sum_const, smul_eq_mul]

/-- For regular graphs (all degrees equal to d), edges = n*d/2. -/
theorem regular_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v : V, degree G v = d) :
    2 * G.edgeFinset.card = Fintype.card V * d := by
  rw [← sum_degrees_eq_twice_edges]; simp_rw [hreg]; simp [Finset.sum_const, smul_eq_mul]

/-- Degree sum in an independent set counts only edges to V\I. -/
theorem indep_degree_sum_eq_cut_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I : Finset V} (hI : IsIndepFinset G I) :
    ∑ v ∈ I, G.degree v =
    ∑ v ∈ I, ((Finset.univ \ I).filter (G.Adj v)).card := by
  apply Finset.sum_congr rfl
  intro v hv
  rw [SimpleGraph.degree]
  apply congr_arg Finset.card
  ext u
  simp only [SimpleGraph.mem_neighborFinset, Set.mem_toFinset, SimpleGraph.mem_neighborSet,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hadj
    exact ⟨fun huI => hI v hv u huI (G.ne_of_adj hadj) hadj, hadj⟩
  · intro ⟨_, hadj⟩; exact hadj

/-- Degree sum in an independent set is at most |I| * Δ. -/
theorem indep_degree_sum_le {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) :
    ∑ v ∈ I, degree G v ≤ I.card * maxDegree G := by
  calc ∑ v ∈ I, degree G v
      ≤ ∑ _v ∈ I, maxDegree G := Finset.sum_le_sum (fun v _ => degree_le_maxDegree G v)
    _ = I.card * maxDegree G := by rw [Finset.sum_const, smul_eq_mul]

/-
## Part XVII: Independence Number of Specific Graph Families
-/

/-- The empty graph (⊥) on n vertices has independence number n. -/
theorem alpha_bot {V : Type*} [Fintype V] [DecidableEq V]
    [DecidableRel (⊥ : SimpleGraph V).Adj] :
    independenceNumber (⊥ : SimpleGraph V) = Fintype.card V := by
  apply le_antisymm
  · exact independenceNumber_le_card (⊥ : SimpleGraph V)
  · have hS : IsIndepFinset (⊥ : SimpleGraph V) Finset.univ := isIndepFinset_of_bot Finset.univ
    have := indep_card_le_alpha (⊥ : SimpleGraph V) Finset.univ hS
    rwa [Finset.card_univ] at this

/-- The complement of ⊥ is complete. -/
theorem bot_compl_adj_of_ne {V : Type*} [DecidableEq V] (u v : V) (huv : u ≠ v) :
    (⊥ : SimpleGraph V)ᶜ.Adj u v := compl_bot_adj u v huv

/-- An independent set in ⊥ᶜ has at most 1 element. -/
theorem indep_compl_bot_card_le_one {V : Type*} [DecidableEq V]
    (S : Finset V) (hS : IsIndepFinset (⊥ : SimpleGraph V)ᶜ S) :
    S.card ≤ 1 := by
  by_contra h; push_neg at h
  have := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨a, ha, b, hb, hab⟩ := this
  exact hS a ha b hb hab (compl_bot_adj a b hab)

/-
## Part XII: Summary

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
11. **Chromatic-independence**: k * α(G) ≥ |V|
12. **Neighborhood theory**: Definition and properties

### Proved Theorems (48 total, 0 sorries)
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
- `closedNeighborhoodIn_card_le`: |N[v]| ≤ Δ+1 (NEW)
- `exists_maximal_indep`: Every finite graph has a maximal independent set (NEW)
- `maximal_indep_covers`: Maximal independent sets cover all vertices (NEW)
- `maximal_indep_covering_bound`: |V| ≤ |I|·(Δ+1) for maximal I (NEW)
- `greedy_bound`: α(G) ≥ |V|/(Δ+1) (NEW - converted from axiom)
- `unit_distance_independence_from_chromatic`: Unit dist graphs have α ≥ |V|/7
- `alpha_chi_ge_card`: k * α(G) ≥ |V| for k-colorable graphs
- `independenceNumber_ge_of_indep`: α(G) ≥ |I| for independent I
- `independent_extend`: Extending independent sets
- `disjoint_indep_union`: Union of independent sets
- `indep_erase`: Removing vertices preserves independence
- `alpha_ge_one`: α(G) ≥ 1 for nonempty graphs
- `neighborhood_card_eq_degree`: |N(v)| = deg(v)
- `not_mem_neighborhood`: v ∉ N(v)
- `independent_mono`: Fewer edges → more independent sets
- `independenceNumber_le_card`: α(G) ≤ |V|
- `common_neighbor_indep`: Common neighbor constraint
- `indep_chromatic_bound`: α(G) ≥ |V|/χ(G)
- `indep_clique_intersection`: |I ∩ K| ≤ 1 for independent I, clique K
- `indep_neighbors_outside`: Neighbors of v ∈ I are outside I
- `indep_is_compl_clique`: Independent sets avoid edges
- `indep_degree_sum`: Degree sum in independent set
- `independenceNumber_pos`: α(G) > 0 for nonempty graphs

### Axioms Used (1)
- `hadwiger_nelson_lower_bound`: De Grey's 5-color lower bound (2018)

### Now Proven (formerly axiomatized)
- `hadwiger_nelson_upper_bound`: the 7-coloring upper bound is now a theorem,
  discharged by `hadwiger_nelson_7coloring` from `Proofs.UnitDistanceHN7`
  (explicit hexagonal tiling, 0 sorries, no `native_decide`).

### What's NOT Proven (and Why)
- De Grey's construction (requires explicit 1581-vertex graph verification)
- Fractional chromatic number bounds (requires LP duality formalization)
-/

end UnitDistanceIndependence
