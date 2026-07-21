/-
Erdős Problem #85: Minimum Degree for 4-Cycles

Let f(n) be the smallest integer such that every graph on n vertices with
minimum degree ≥ f(n) contains a 4-cycle (C₄).

Is it true that f(n+1) ≥ f(n) for all large n?

**Status**: OPEN

**Known Results**:
- f(n) = (1 + o(1))√n asymptotically
- f(n) < √n + 1
- f(4) = 2
- Connected to Ramsey number R(C₄, K_{1,n})

Reference: https://erdosproblems.com/85
-/

import Mathlib

open SimpleGraph Finset Filter
open scoped Topology

namespace Erdos85

/-
## Background

A **4-cycle** (or C₄) is a cycle on 4 vertices: a-b-c-d-a with exactly
these 4 edges. It's the simplest even cycle.

The **minimum degree** of a graph is the smallest degree of any vertex.
High minimum degree forces certain substructures to appear.

This problem asks: what minimum degree guarantees a C₄?
-/

/--
The **4-cycle graph** C₄ on 4 vertices, where vertex i is adjacent to
vertices i-1 and i+1 (mod 4).

This is a cycle: 0 - 1 - 2 - 3 - 0.
-/
def C4 : SimpleGraph (Fin 4) where
  Adj := fun i j => (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val
  symm.symm := fun i j h => by cases h <;> simp_all [or_comm]
  loopless.irrefl := fun i h => by fin_cases i <;> simp_all

/--
A graph G **contains a 4-cycle** if C₄ is a subgraph of G.
We use the notion of graph homomorphism embedding.
-/
def containsC4 (V : Type*) (G : SimpleGraph V) : Prop :=
  ∃ (f : Fin 4 → V), Function.Injective f ∧
    ∀ i j, C4.Adj i j → G.Adj (f i) (f j)

/--
**f(n)** is the minimum degree threshold such that every n-vertex graph
with minimum degree ≥ f(n) contains a 4-cycle.

Formally: f(n) = min{k : ∀ G on n vertices, minDeg(G) ≥ k → C₄ ⊆ G}
-/
noncomputable def minDegreeForC4 (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.minDegree ≥ k → containsC4 (Fin n) G}

/-
## The Main Question

Erdős asked whether f is eventually monotone: f(n+1) ≥ f(n) for large n.
-/

/--
**Erdős Problem #85 (OPEN)**

Is f(n) eventually non-decreasing? That is, for all sufficiently large n,
does f(n+1) ≥ f(n)?

We state this without asserting its truth value.
-/
def Erdos85Question : Prop :=
  ∀ᶠ n in atTop, minDegreeForC4 n ≤ minDegreeForC4 (n + 1)

/--
The negation: there exist arbitrarily large n where f(n+1) < f(n).
-/
def Erdos85Negation : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, minDegreeForC4 (n + 1) < minDegreeForC4 n

/-
## Known Bounds

The asymptotic behavior of f(n) is well-understood.
-/

/- 
**Asymptotic Upper Bound**

f(n) < √n + 1 for all n ≥ 4.

This means if minimum degree exceeds √n, a 4-cycle must exist.
-/
/- 
**Asymptotic Behavior**

f(n) = (1 + o(1))√n as n → ∞.

The minimum degree threshold grows like the square root of n.
-/
/- 
**Base Case**: f(4) = 2.

In a graph on 4 vertices, minimum degree ≥ 2 guarantees a 4-cycle.
(In fact, such a graph must be the 4-cycle itself.)
-/
/-
## Connection to Ramsey Numbers

The function f(n) is intimately connected to the Ramsey number R(C₄, K_{1,n}).
-/

/--
The **star graph** K_{1,n} has one central vertex connected to n leaves.
-/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj := fun i j => (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)
  symm.symm := fun i j h => by cases h <;> simp_all [or_comm]
  loopless.irrefl := fun i h => by cases h <;> simp_all

/-- The star adjacency is decidable (equalities/inequalities of `Fin` vertices),
so `starGraph n` has computable degrees — needed to talk about its `minDegree`. -/
instance starGraph_decidableAdj (n : ℕ) : DecidableRel (starGraph n).Adj :=
  fun i j => by unfold starGraph; infer_instance

/--
**Ramsey Connection**

The Ramsey number R(C₄, K_{1,n}) is related to f by:
  R(C₄, K_{1,n}) = min{m : f(m) ≤ m - n}

And conversely:
  f(n) = min{m : m ≥ R(C₄, K_{1,n-m})}

This reformulation connects the degree threshold problem to Ramsey theory.
-/
def ramseyConnection : Prop :=
  ∀ n m : ℕ, n ≥ 4 → m ≥ n →
    (minDegreeForC4 m ≤ m - n) ↔
    (∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
      containsC4 (Fin m) G ∨ ∃ v, G.degree v ≥ n)

/-
## Weaker Conjecture

A weaker version asks whether f is "almost monotone"—it can decrease,
but only by a bounded amount.
-/

/--
**Weaker Conjecture**

There exists a constant c such that for all m > n,
  f(m) > f(n) - c

This allows f to occasionally decrease, but by at most c.
-/
def WeakerConjecture : Prop :=
  ∃ c : ℕ, ∀ m n : ℕ, m > n → n ≥ 4 →
    minDegreeForC4 m + c > minDegreeForC4 n

/-
## Historical Notes

This problem explores the extremal theory of even cycles. The 4-cycle (C₄)
is special because:
- It's the smallest even cycle
- It appears in the Kővári–Sós–Turán theorem
- It's connected to the Zarankiewicz problem

The monotonicity question is subtle because adding vertices might create
"room" for C₄-avoiding configurations with high minimum degree.
-/

/-
The Kővári-Sós-Turán theorem gives bounds on C₄-free graphs:
A C₄-free graph on n vertices has at most (1/2)n^{3/2} + n/2 edges.
-/

/-
## Foundational lemmas (axiom-free)

The asymptotics `f(n) = (1+o(1))√n`, the base case `f(4) = 2`, the Ramsey
reformulation and the monotonicity question itself require substantial extremal
graph theory beyond current Mathlib and stay documented above only.  The
structural facts about `C4`, `containsC4`, and `starGraph` are, however, fully
machine-checkable.  All lemmas below are axiom-free
(`propext / Classical.choice / Quot.sound` only). -/

/-- The four defining edges of the 4-cycle `C₄`: `0–1–2–3–0`. -/
theorem C4_adj_zero_one : C4.Adj 0 1 := by simp [C4]
theorem C4_adj_one_two : C4.Adj 1 2 := by simp [C4]
theorem C4_adj_two_three : C4.Adj 2 3 := by simp [C4]
theorem C4_adj_three_zero : C4.Adj 3 0 := by simp [C4]

/-- The "diagonals" of `C₄` are non-edges: `0` and `2` are not adjacent. -/
theorem C4_not_adj_zero_two : ¬ C4.Adj 0 2 := by simp [C4]

/-- The other diagonal of `C₄` is also a non-edge: `1` and `3` are not adjacent.
Together with `C4_not_adj_zero_two` this pins down `C₄` exactly: the only edges are
the four cycle edges. -/
theorem C4_not_adj_one_three : ¬ C4.Adj 1 3 := by simp [C4]

/-- `C₄` contains a copy of itself (the identity embedding), so `containsC4` is a
non-vacuous predicate. -/
theorem containsC4_C4 : containsC4 (Fin 4) C4 :=
  ⟨id, Function.injective_id, fun _ _ h => h⟩

/-- **A copy of `C₄` needs at least four vertices.** Since `containsC4` supplies an
injection `Fin 4 ↪ V`, any host graph carrying a `C₄` has `4 ≤ |V|`.  This is the
necessary size condition behind the degree-threshold question. -/
theorem containsC4_four_le_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h : containsC4 V G) : 4 ≤ Fintype.card V := by
  obtain ⟨f, hinj, _⟩ := h
  simpa using Fintype.card_le_of_injective f hinj

/-- **Complete graphs on `≥ 4` vertices contain a `C₄`.**  Embed `Fin 4 ↪ Fin n`
by `Fin.castLE`; every cycle edge joins two *distinct* vertices, and in `⊤` all
distinct vertices are adjacent.  This is the extremal counterpart to
`starGraph_not_containsC4`: complete graphs are the densest hosts and always carry
a `C₄`, whereas stars are the sparse `C₄`-free extreme. -/
theorem completeGraph_containsC4 {n : ℕ} (hn : 4 ≤ n) :
    containsC4 (Fin n) (⊤ : SimpleGraph (Fin n)) := by
  refine ⟨Fin.castLE hn, Fin.castLE_injective hn, fun i j hij => ?_⟩
  rw [top_adj]
  exact fun heq => hij.ne (Fin.castLE_injective hn heq)

/-- Containing a `C₄` is preserved under passing to a larger graph on the same
vertex set (adding edges cannot destroy a copy of `C₄`). -/
theorem containsC4_mono {V : Type*} {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : containsC4 V G) : containsC4 V G' := by
  obtain ⟨f, hf, hadj⟩ := hG
  exact ⟨f, hf, fun i j hij => h (hadj i j hij)⟩

/-- **Stars are `C₄`-free.** The star graph `K_{1,n}` contains no 4-cycle: every
edge of a star meets the centre `0`, but a `C₄` has two disjoint edges (`0–1` and
`2–3`), which would force two distinct cycle-vertices onto the centre — impossible
by injectivity.  This is the extremal reason stars appear in the Ramsey
reformulation of `f(n)`. -/
theorem starGraph_not_containsC4 (n : ℕ) :
    ¬ containsC4 (Fin (n + 1)) (starGraph n) := by
  rintro ⟨f, hinj, hadj⟩
  have e01 := hadj 0 1 C4_adj_zero_one
  have e23 := hadj 2 3 C4_adj_two_three
  simp only [starGraph] at e01 e23
  have h01 : f 0 = 0 ∨ f 1 = 0 := e01.imp And.left And.left
  have h23 : f 2 = 0 ∨ f 3 = 0 := e23.imp And.left And.left
  rcases h01 with h0 | h1 <;> rcases h23 with h2 | h3
  · exact absurd (hinj (h0.trans h2.symm)) (by decide)
  · exact absurd (hinj (h0.trans h3.symm)) (by decide)
  · exact absurd (hinj (h1.trans h2.symm)) (by decide)
  · exact absurd (hinj (h1.trans h3.symm)) (by decide)

/-- **Full minimum degree forces the complete graph.**  On `Fin n`, a simple graph
whose minimum degree is at least `n - 1` must be the complete graph `⊤`: every
vertex `i` has `deg i ≤ n - 1` (its neighbours avoid `i`), so `deg i ≥ n - 1`
forces its neighbourhood to be *all* other vertices, i.e. `i` is adjacent to every
`j ≠ i`. -/
theorem eq_top_of_minDegree_ge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : n - 1 ≤ G.minDegree) : G = ⊤ := by
  ext i j
  rw [top_adj]
  refine ⟨fun h => h.ne, fun hij => ?_⟩
  -- `deg i ≥ n - 1`, and the neighbourhood of `i` sits inside the `n - 1` other vertices
  have hdeg : n - 1 ≤ (G.neighborFinset i).card := by
    rw [G.card_neighborFinset_eq_degree]
    exact le_trans hmin (G.minDegree_le_degree i)
  have hsub : G.neighborFinset i ⊆ Finset.univ.erase i := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    exact (G.ne_of_adj ((G.mem_neighborFinset i x).mp hx)).symm
  have hcard : (Finset.univ.erase i).card ≤ (G.neighborFinset i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    exact hdeg
  have heq : G.neighborFinset i = Finset.univ.erase i :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hjmem : j ∈ G.neighborFinset i := by
    rw [heq]; exact Finset.mem_erase.mpr ⟨(Ne.symm hij), Finset.mem_univ j⟩
  exact (G.mem_neighborFinset i j).mp hjmem

/-- **A crude but honest upper bound on `f(n)`.**  For `n ≥ 4`,
`minDegreeForC4 n ≤ n - 1`: minimum degree `n - 1` on `Fin n` forces the complete
graph (`eq_top_of_minDegree_ge`), which contains a `C₄` (`completeGraph_containsC4`).
In particular the threshold set defining `minDegreeForC4` is non-empty, so the
`sInf` is a genuine minimum rather than the junk value `sInf ∅ = 0` — some finite
minimum degree really does force a 4-cycle.  (The true value is `f(n) = (1+o(1))√n`,
far below this bound, but that requires Kővári–Sós–Turán, beyond current Mathlib.) -/
theorem minDegreeForC4_le_sub_one {n : ℕ} (hn : 4 ≤ n) :
    minDegreeForC4 n ≤ n - 1 := by
  apply Nat.sInf_le
  intro G _ hmin
  rw [eq_top_of_minDegree_ge G hmin]
  exact completeGraph_containsC4 hn

/-- **The star has minimum degree at least `1`.**  In `K_{1,n}` on `Fin (n+1)` the
centre `0` is adjacent to every leaf and each leaf is adjacent to the centre, so
no vertex is isolated: `1 ≤ minDegree`. -/
theorem one_le_starGraph_minDegree {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (starGraph n).minDegree := by
  classical
  obtain ⟨v, hv⟩ := (starGraph n).exists_minimal_degree_vertex
  rw [hv, ← SimpleGraph.card_neighborFinset_eq_degree, Finset.one_le_card]
  rcases eq_or_ne v 0 with hv0 | hv0
  · -- the centre is adjacent to the leaf `1`
    refine ⟨⟨1, by omega⟩, ?_⟩
    rw [SimpleGraph.mem_neighborFinset]
    subst hv0
    exact Or.inl ⟨rfl, by simp [Fin.ext_iff]⟩
  · -- a leaf is adjacent to the centre `0`
    refine ⟨0, ?_⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact Or.inr ⟨rfl, hv0⟩

/-- **A matching lower bound on `f(n)`.**  For `n ≥ 3`, `2 ≤ minDegreeForC4 (n+1)`:
the star `K_{1,n}` on `Fin (n+1)` is `C₄`-free (`starGraph_not_containsC4`) yet has
minimum degree `≥ 1` (`one_le_starGraph_minDegree`), so no threshold `k ≤ 1` can
force a `C₄` — witnessing that `0, 1 ∉` the defining set.  Together with the upper
bound `minDegreeForC4 n ≤ n − 1` this brackets `2 ≤ f(n+1) ≤ n`, and in particular
pins the base case lower half `f(4) ≥ 2` (the true value is `f(4) = 2`). -/
theorem two_le_minDegreeForC4 {n : ℕ} (hn : 3 ≤ n) :
    2 ≤ minDegreeForC4 (n + 1) := by
  classical
  have hfree : ¬ containsC4 (Fin (n + 1)) (starGraph n) := starGraph_not_containsC4 n
  have hstar : 1 ≤ (starGraph n).minDegree := one_le_starGraph_minDegree (by omega)
  -- The threshold set is nonempty: full min-degree forces the complete graph, hence `C₄`.
  have hne : {k : ℕ | ∀ (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj],
      G.minDegree ≥ k → containsC4 (Fin (n + 1)) G}.Nonempty := by
    refine ⟨n, fun G _ hmin => ?_⟩
    rw [eq_top_of_minDegree_ge G (by simpa using hmin)]
    exact completeGraph_containsC4 (by omega)
  unfold minDegreeForC4
  refine le_csInf hne (fun k hk => ?_)
  -- any threshold `k` in the set is `≥ 2`: else the star (min-degree `≥ 1`) forces a `C₄`.
  by_contra hk2
  rw [not_le] at hk2
  exact hfree (hk (starGraph n) (le_trans (by omega : k ≤ 1) hstar))

/-- `C₄`'s adjacency `(i+1)%4 = j ∨ (j+1)%4 = i` is a decidable predicate, so `C4`
has computable degrees and finite membership tests — needed to `decide` whether a
concrete graph contains a `C₄`. -/
instance : DecidableRel C4.Adj := fun i j => by unfold C4; infer_instance

/-- **A cycle beats the star: `f(5) ≥ 3`.**  The 5-cycle `C₅` (`SimpleGraph.cycleGraph 5`)
has *every* degree equal to `2` (`cycleGraph_degree_three_le`) yet contains no `C₄`
(a `4`-cycle needs four consecutive `±1` steps in `ℤ/5` summing to `0`, forcing two of
the four vertices to coincide — verified by `decide`).  So no threshold `k ≤ 2` can force
a `C₄` on `5` vertices, giving `minDegreeForC4 5 ≥ 3`.  This strictly improves the generic
star bound `f(5) ≥ 2` and confirms `f(5) ≥ 3` (the true asymptotic is `f(n) = (1+o(1))√n`,
so `f(5)` sits just above `√5 ≈ 2.24`). -/
theorem three_le_minDegreeForC4_five : 3 ≤ minDegreeForC4 5 := by
  -- `C₅` is `C₄`-free (concrete `Decidable` instances, no `classical`).
  have hfree : ¬ containsC4 (Fin 5) (cycleGraph 5) := by
    unfold containsC4
    set_option maxRecDepth 100000 in decide
  -- `C₅` has minimum degree `2` (every vertex has degree `2`).
  have hdeg : ∀ v : Fin 5, 2 ≤ (cycleGraph 5).degree v := by decide
  have hmin2 : 2 ≤ (cycleGraph 5).minDegree := by
    apply le_minDegree_of_forall_le_degree
    exact hdeg
  -- The threshold set is nonempty (min-degree `≥ 4` forces `⊤`, hence a `C₄`).
  have hne : {k : ℕ | ∀ (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj],
      G.minDegree ≥ k → containsC4 (Fin 5) G}.Nonempty := by
    refine ⟨4, fun G _ hmin => ?_⟩
    rw [eq_top_of_minDegree_ge G (by simpa using hmin)]
    exact completeGraph_containsC4 (by norm_num)
  unfold minDegreeForC4
  refine le_csInf hne (fun k hk => ?_)
  -- Any threshold `k` in the set is `≥ 3`: else `C₅` (min-degree `2 ≥ k`) forces a `C₄`.
  by_contra hk3
  rw [not_le] at hk3
  exact hfree (hk (cycleGraph 5) (le_trans (by omega : k ≤ 2) hmin2))

open Fin.CommRing in
/-- **The `n`-cycle is `C₄`-free for `n ≥ 5`.**  A copy of `C₄` in `cycleGraph n`
is an injection `f : Fin 4 ↪ Fin n` whose four consecutive images are cycle-adjacent,
i.e. each consecutive difference `f (i+1) − f i` is `±1` in the additive group `Fin n`.
The four differences telescope to `0`; injectivity of the two "diagonals" `f 2 − f 0`
and `f 3 − f 1` forces all three interior steps to share the same sign, so the closing
difference equals `±3`.  But the closing edge also forces it to be `±1`, giving `2 = 0`
or `4 = 0` in `Fin n` — impossible once `n ≥ 5`.  (At `n = 4` this fails precisely
because `cycleGraph 4` *is* a `C₄`; the argument genuinely needs `n ≥ 5`.)  This is the
general form of the `C₅` witness behind `three_le_minDegreeForC4_five`. -/
theorem cycleGraph_not_containsC4 {n : ℕ} (hn : 5 ≤ n) :
    ¬ containsC4 (Fin n) (cycleGraph n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 3 ≤ m := by omega
  haveI : NeZero (m + 2) := ⟨by omega⟩
  rintro ⟨f, hinj, hadj⟩
  -- numeral facts in `Fin (m + 2)` (needs `m ≥ 3`, i.e. `n ≥ 5`)
  have h2 : (2 : Fin (m + 2)) ≠ 0 := by
    have hv : (2 : Fin (m + 2)).val = 2 := by simp; omega
    intro h; rw [h, Fin.val_zero] at hv; omega
  have h4 : (4 : Fin (m + 2)) ≠ 0 := by
    have hv : (4 : Fin (m + 2)).val = 4 := by simp; omega
    intro h; rw [h, Fin.val_zero] at hv; omega
  -- the four `C₄` edges as difference equations in `Fin (m + 2)`
  have h01 := cycleGraph_adj.mp (hadj 0 1 C4_adj_zero_one)
  have h12 := cycleGraph_adj.mp (hadj 1 2 C4_adj_one_two)
  have h23 := cycleGraph_adj.mp (hadj 2 3 C4_adj_two_three)
  have h30 := cycleGraph_adj.mp (hadj 3 0 C4_adj_three_zero)
  -- each consecutive difference is `±1`
  have hA : f 1 - f 0 = 1 ∨ f 1 - f 0 = -1 := by
    rcases h01 with h | h
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination h)
  have hB : f 2 - f 1 = 1 ∨ f 2 - f 1 = -1 := by
    rcases h12 with h | h
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination h)
  have hC : f 3 - f 2 = 1 ∨ f 3 - f 2 = -1 := by
    rcases h23 with h | h
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination h)
  have hD : f 0 - f 3 = 1 ∨ f 0 - f 3 = -1 := by
    rcases h30 with h | h
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination h)
  -- injectivity: the two "diagonals" of the 4-cycle are non-degenerate
  have hAB : f 2 - f 0 ≠ 0 := fun h =>
    absurd (hinj (show f 0 = f 2 by linear_combination -h)) (by decide)
  have hBC : f 3 - f 1 ≠ 0 := fun h =>
    absurd (hinj (show f 1 = f 3 by linear_combination -h)) (by decide)
  -- adjacent steps must agree in sign (else a diagonal collapses)
  have hAeqB : f 1 - f 0 = f 2 - f 1 := by
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · rw [hA, hB]
    · exact absurd (by linear_combination hA + hB : f 2 - f 0 = 0) hAB
    · exact absurd (by linear_combination hA + hB : f 2 - f 0 = 0) hAB
    · rw [hA, hB]
  have hBeqC : f 2 - f 1 = f 3 - f 2 := by
    rcases hB with hB | hB <;> rcases hC with hC | hC
    · rw [hB, hC]
    · exact absurd (by linear_combination hB + hC : f 3 - f 1 = 0) hBC
    · exact absurd (by linear_combination hB + hC : f 3 - f 1 = 0) hBC
    · rw [hB, hC]
  -- the four differences telescope to `0`
  have hsum : (f 1 - f 0) + (f 2 - f 1) + (f 3 - f 2) + (f 0 - f 3) = 0 := by ring
  -- all interior steps share `hA`'s sign, so the closing difference is `±3` — contradiction
  rcases hA with hA | hA
  · have hAB1 : f 2 - f 1 = 1 := by rw [← hAeqB, hA]
    have hBC1 : f 3 - f 2 = 1 := by rw [← hBeqC, hAB1]
    have hD3 : f 0 - f 3 = -3 := by linear_combination hsum - hA - hAB1 - hBC1
    rcases hD with hD | hD
    · exact h4 (by linear_combination hD3 - hD)
    · exact h2 (by linear_combination hD3 - hD)
  · have hAB1 : f 2 - f 1 = -1 := by rw [← hAeqB, hA]
    have hBC1 : f 3 - f 2 = -1 := by rw [← hBeqC, hAB1]
    have hD3 : f 0 - f 3 = 3 := by linear_combination hsum - hA - hAB1 - hBC1
    rcases hD with hD | hD
    · exact h2 (by linear_combination hD - hD3)
    · exact h4 (by linear_combination hD - hD3)

/-- **The `n`-cycle has minimum degree `2` for `n ≥ 3`.**  Every vertex of
`cycleGraph (k + 3)` has exactly two neighbours (`v - 1` and `v + 1`), so the minimum
degree is `2`. -/
theorem two_le_cycleGraph_minDegree {n : ℕ} (hn : 3 ≤ n) :
    2 ≤ (cycleGraph n).minDegree := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  apply le_minDegree_of_forall_le_degree
  intro v
  have hv : (cycleGraph (k + 3)).degree v = 2 := cycleGraph_degree_three_le
  omega

/-- **The general cycle lower bound: `f(n) ≥ 3` for every `n ≥ 5`.**  The `n`-cycle
`Cₙ` is `2`-regular (`two_le_cycleGraph_minDegree`) yet `C₄`-free
(`cycleGraph_not_containsC4`), so no threshold `k ≤ 2` can force a `C₄` on `n` vertices;
hence `minDegreeForC4 n ≥ 3`.  This uniformly improves the generic star bound `f(n) ≥ 2`
across all `n ≥ 5` and generalises the single-point witness
`three_le_minDegreeForC4_five`.  (The true asymptotic `f(n) = (1+o(1))√n` grows without
bound, but that needs Kővári–Sós–Turán, beyond current Mathlib.) -/
theorem three_le_minDegreeForC4 {n : ℕ} (hn : 5 ≤ n) :
    3 ≤ minDegreeForC4 n := by
  have hfree : ¬ containsC4 (Fin n) (cycleGraph n) := cycleGraph_not_containsC4 hn
  have hmin2 : 2 ≤ (cycleGraph n).minDegree := two_le_cycleGraph_minDegree (by omega)
  have hne : {k : ℕ | ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.minDegree ≥ k → containsC4 (Fin n) G}.Nonempty := by
    refine ⟨n - 1, fun G _ hmin => ?_⟩
    rw [eq_top_of_minDegree_ge G hmin]
    exact completeGraph_containsC4 (by omega)
  unfold minDegreeForC4
  refine le_csInf hne (fun k hk => ?_)
  by_contra hk3
  rw [not_le] at hk3
  exact hfree (hk (cycleGraph n) (le_trans (by omega : k ≤ 2) hmin2))

/-- **Four vertices carrying the rim of a `4`-cycle host a `C₄`.**  Given pairwise
adjacencies `a‑b`, `b‑c`, `c‑d`, `d‑a` and pairwise distinctness of `a, b, c, d`, the
map `Fin 4 → V`, `![a, b, c, d]` is an injective `C₄`-embedding.  (Only the four rim
edges and the six inequalities are needed; the diagonals `a‑c`, `b‑d` are irrelevant.) -/
theorem containsC4_of_rim {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) (hba : b ≠ a) (hbc' : b ≠ c) (hda' : d ≠ a) (hdc : d ≠ c) :
    containsC4 V G := by
  have hba' := hba.symm; have hcb := hbc.symm; have had := hda'.symm; have hcd' := hdc.symm
  have hca := hac.symm; have hdb := hbd.symm
  have s1 := hab.symm; have s2 := hbc.symm; have s3 := hcd.symm; have s4 := hda.symm
  refine ⟨![a, b, c, d], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [C4]

/-- **Minimum degree `n − 2` forces a `C₄` (`n ≥ 4`).**  If `δ(G) ≥ n − 2` on `Fin n`,
every vertex misses at most one other vertex (its non-neighbours, excluding itself,
number at most `(n−1) − (n−2) = 1`).  Either `G = ⊤` — and then `C₄ ⊆ G` by
`completeGraph_containsC4` — or `G` has a non-adjacent distinct pair `a, c`.  In the
latter case `a`'s unique possible non-neighbour is `c` and vice versa, so *every* other
vertex is a common neighbour of both `a` and `c`.  Picking two such vertices `b, d`
(there are `n − 2 ≥ 2` of them) gives the `4`-cycle `a‑b‑c‑d‑a`: the diagonals `a,c` and
`b,d` carry the only possible non-edges, while all four rim edges are present. -/
theorem containsC4_of_minDegree_ge {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : n - 2 ≤ G.minDegree) : containsC4 (Fin n) G := by
  by_cases htop : G = ⊤
  · subst htop; exact completeGraph_containsC4 hn
  -- `G ≠ ⊤` yields a non-adjacent distinct pair.
  have hpair : ∃ a c : Fin n, a ≠ c ∧ ¬ G.Adj a c := by
    by_contra hcon
    apply htop
    ext a b
    simp only [top_adj]
    refine ⟨fun h => h.ne, fun hab => ?_⟩
    by_contra hnadj
    exact hcon ⟨a, b, hab, hnadj⟩
  obtain ⟨a, c, hac, hnac⟩ := hpair
  -- Every vertex has at most one non-neighbour (other than itself).
  have hfew : ∀ v : Fin n, ((univ.erase v) \ G.neighborFinset v).card ≤ 1 := by
    intro v
    have hsub : G.neighborFinset v ⊆ univ.erase v := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset v x).mp hx)).symm,
        Finset.mem_univ x⟩
    have hdeg : n - 2 ≤ (G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact le_trans hmin (G.minDegree_le_degree v)
    have hkey : ((univ.erase v) \ G.neighborFinset v).card + (G.neighborFinset v).card
        = (univ.erase v).card := Finset.card_sdiff_add_card_eq_card hsub
    have herase : (univ.erase v).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    omega
  -- `c` is `a`'s only candidate non-neighbour, and symmetrically.
  have hmemC : c ∈ (univ.erase a) \ G.neighborFinset a := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨(Ne.symm hac), Finset.mem_univ c⟩, ?_⟩
    rw [G.mem_neighborFinset]; exact hnac
  have hmemA : a ∈ (univ.erase c) \ G.neighborFinset c := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩, ?_⟩
    rw [G.mem_neighborFinset]; exact fun h => hnac h.symm
  -- Hence any vertex outside `{a, c}` is adjacent to both `a` and `c`.
  have hadjA : ∀ x : Fin n, x ≠ a → x ≠ c → G.Adj a x := by
    intro x hxa hxc
    by_contra hnx
    have hmemx : x ∈ (univ.erase a) \ G.neighborFinset a := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩, ?_⟩
      rw [G.mem_neighborFinset]; exact hnx
    exact hxc (Finset.card_le_one.mp (hfew a) x hmemx c hmemC)
  have hadjC : ∀ x : Fin n, x ≠ a → x ≠ c → G.Adj c x := by
    intro x hxa hxc
    by_contra hnx
    have hmemx : x ∈ (univ.erase c) \ G.neighborFinset c := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxc, Finset.mem_univ x⟩, ?_⟩
      rw [G.mem_neighborFinset]; exact hnx
    exact hxa (Finset.card_le_one.mp (hfew c) x hmemx a hmemA)
  -- Two distinct vertices `b, d` outside `{a, c}` (there are `n − 2 ≥ 2`).
  have hcard2 : 1 < ((univ.erase a).erase c).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hac, Finset.mem_univ c⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcard2
  have hb' := Finset.mem_erase.mp hb
  have hd' := Finset.mem_erase.mp hd
  have hbc : b ≠ c := hb'.1
  have hba : b ≠ a := (Finset.mem_erase.mp hb'.2).1
  have hdc : d ≠ c := hd'.1
  have hda : d ≠ a := (Finset.mem_erase.mp hd'.2).1
  -- The four rim edges of `a‑b‑c‑d‑a`.
  exact containsC4_of_rim (hadjA b hba hbc) (hadjC b hba hbc).symm (hadjC d hda hdc)
    (hadjA d hda hdc).symm hac hbd hba hbc hda hdc

/-- **A sharpened upper bound: `f(n) ≤ n − 2` for `n ≥ 4`.**  By
`containsC4_of_minDegree_ge`, minimum degree `n − 2` already forces a `C₄`, so
`n − 2` lies in the threshold set and `minDegreeForC4 n ≤ n − 2`.  This strictly
improves the crude complete-graph bound `f(n) ≤ n − 1`.  (The true value is
`f(n) = (1+o(1))√n`, far below, but that needs Kővári–Sós–Turán.) -/
theorem minDegreeForC4_le_sub_two {n : ℕ} (hn : 4 ≤ n) :
    minDegreeForC4 n ≤ n - 2 := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_minDegree_ge hn G hmin

/-- **The base case is exact: `f(4) = 2`.**  The lower half `f(4) ≥ 2` is the star
witness (`two_le_minDegreeForC4`), and the upper half `f(4) ≤ 2` is the `n = 4`
instance of `minDegreeForC4_le_sub_two`: on four vertices, minimum degree `2` already
forces a `4`-cycle (indeed the graph must *be* a `C₄`, a diamond, or `K₄`).  This is
the first exactly-determined value of the threshold function. -/
theorem minDegreeForC4_four : minDegreeForC4 4 = 2 := by
  have hle : minDegreeForC4 4 ≤ 2 := by simpa using minDegreeForC4_le_sub_two (n := 4) (le_refl 4)
  have hge : 2 ≤ minDegreeForC4 4 := by simpa using two_le_minDegreeForC4 (n := 3) (by norm_num)
  omega

/-- **A second exact value: `f(5) = 3`.**  The lower half `f(5) ≥ 3` is the cycle
witness (`three_le_minDegreeForC4`, the `5`-cycle is `2`-regular and `C₄`-free), and the
upper half `f(5) ≤ 3` is the `n = 5` case of `minDegreeForC4_le_sub_two` (`5 − 2 = 3`).
The two bounds coincide at `n = 5` precisely because `n − 2` first reaches the current
lower bound `3` there. -/
theorem minDegreeForC4_five : minDegreeForC4 5 = 3 := by
  have hle : minDegreeForC4 5 ≤ 3 := by
    simpa using minDegreeForC4_le_sub_two (n := 5) (by norm_num)
  have hge : 3 ≤ minDegreeForC4 5 := three_le_minDegreeForC4 (by norm_num)
  omega

/-! ## The Kővári–Sós–Turán counting bound

The upper bounds above (`f(n) ≤ n − 2`) are linear, far from the truth `f(n) = (1+o(1))√n`.
The real mechanism is a double count of **cherries** (paths of length two): a vertex `v` of
degree `d` is the centre of `C(d, 2)` cherries, and a cherry `x–v–y` is determined by its
centre together with its *unordered* endpoint pair `{x, y}`.  If the total number of cherries
`∑_v C(deg v, 2)` exceeds the number `C(|V|, 2)` of available endpoint pairs, two distinct
cherries share an endpoint pair — i.e. some pair `{x, y}` has two common neighbours `v ≠ v'`,
which is exactly a `4`-cycle `x–v–y–v'–x`.  This is the Kővári–Sós–Turán argument at its
simplest (the `C₄` / `z(n; 2, 2)` case), and it drives the true `√n`-order threshold. -/

/-- **Cherry-counting forces a `C₄`.**  If the number of cherries `∑_v C(deg v, 2)` strictly
exceeds the number `C(|V|, 2)` of unordered vertex pairs, then `G` contains a `4`-cycle.
Proof: the cherries `⟨v, e⟩` (centre `v`, endpoint pair `e ⊆ N(v)`, `|e| = 2`) form a Finset
of size `∑_v C(deg v, 2)`; the map `⟨v, e⟩ ↦ e` lands in the `C(|V|, 2)` two-element vertex
subsets, so by pigeonhole two distinct cherries `⟨v, e⟩ ≠ ⟨v', e⟩` share their endpoint pair.
Then `v ≠ v'` are two common neighbours of the pair `e = {x, y}`, giving the rim
`x–v–y–v'–x`. -/
theorem containsC4_of_card_choose_two_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : (Fintype.card V).choose 2 < ∑ v : V, (G.degree v).choose 2) :
    containsC4 V G := by
  classical
  -- The Finset of cherries: centre `v` with a two-element subset `e ⊆ N(v)`.
  set C : Finset (Σ _ : V, Finset V) :=
    univ.sigma (fun v => (G.neighborFinset v).powersetCard 2) with hC
  -- Its cardinality is exactly the cherry count `∑_v C(deg v, 2)`.
  have hCcard : C.card = ∑ v : V, (G.degree v).choose 2 := by
    rw [hC, Finset.card_sigma]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.card_powersetCard, G.card_neighborFinset_eq_degree]
  -- The endpoint-pair map lands in the two-element subsets of `V`.
  set T : Finset (Finset V) := (univ : Finset V).powersetCard 2 with hT
  have hTcard : T.card = (Fintype.card V).choose 2 := by
    rw [hT, Finset.card_powersetCard, Finset.card_univ]
  have hmaps : ∀ p ∈ C, p.2 ∈ T := by
    intro p hp
    rw [hC, Finset.mem_sigma] at hp
    rw [hT, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hp.2).2⟩
  have hlt : T.card < C.card := by rw [hTcard, hCcard]; exact h
  -- Pigeonhole: two distinct cherries with the same endpoint pair.
  obtain ⟨p, hp, q, hq, hpq, hfe⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  obtain ⟨v, e⟩ := p
  obtain ⟨v', e'⟩ := q
  simp only at hfe
  subst hfe
  -- Different cherries with equal endpoint pair ⟹ different centres.
  have hvv : v ≠ v' := by
    rintro rfl; exact hpq rfl
  -- Unpack `e ⊆ N(v)`, `e ⊆ N(v')`, `|e| = 2`.
  rw [hC, Finset.mem_sigma] at hp hq
  obtain ⟨-, hpe⟩ := hp
  obtain ⟨-, hqe⟩ := hq
  obtain ⟨hsubv, hecard⟩ := Finset.mem_powersetCard.mp hpe
  obtain ⟨hsubv', -⟩ := Finset.mem_powersetCard.mp hqe
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
  have hxv : x ∈ G.neighborFinset v := hsubv (by simp)
  have hyv : y ∈ G.neighborFinset v := hsubv (by simp)
  have hxv' : x ∈ G.neighborFinset v' := hsubv' (by simp)
  have hyv' : y ∈ G.neighborFinset v' := hsubv' (by simp)
  -- The four rim adjacencies of `x–v–y–v'–x`.
  have avx : G.Adj v x := (G.mem_neighborFinset v x).mp hxv
  have avy : G.Adj v y := (G.mem_neighborFinset v y).mp hyv
  have av'x : G.Adj v' x := (G.mem_neighborFinset v' x).mp hxv'
  have av'y : G.Adj v' y := (G.mem_neighborFinset v' y).mp hyv'
  exact containsC4_of_rim avx.symm avy av'y.symm av'x hxy hvv
    (G.ne_of_adj avx) (G.ne_of_adj avy)
    (G.ne_of_adj av'x) (G.ne_of_adj av'y)

/-- **The counting upper bound on the threshold.**  If `C(n, 2) < n · C(k, 2)` then every
`n`-vertex graph of minimum degree `≥ k` has more than `C(n, 2)` cherries, hence a `C₄`; so
`f(n) ≤ k`.  This is the Kővári–Sós–Turán ceiling: since `C(n,2) < n · C(k,2)` holds as soon
as `n ≤ k(k−1)`, it gives `f(n) = O(√n)`, matching the true order and far beating the linear
`f(n) ≤ n − 2`. -/
theorem minDegreeForC4_le_of_choose_lt {n k : ℕ}
    (h : n.choose 2 < n * k.choose 2) : minDegreeForC4 n ≤ k := by
  apply Nat.sInf_le
  intro G _ hmin
  apply containsC4_of_card_choose_two_lt
  rw [Fintype.card_fin]
  calc n.choose 2
      < n * k.choose 2 := h
    _ = ∑ _v : Fin n, k.choose 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ ∑ v : Fin n, (G.degree v).choose 2 :=
        Finset.sum_le_sum fun v _ =>
          Nat.choose_le_choose 2 (le_trans hmin (G.minDegree_le_degree v))

/-- **A third exact value: `f(6) = 3`.**  The lower half `f(6) ≥ 3` is the `6`-cycle witness
(`three_le_minDegreeForC4`).  The upper half `f(6) ≤ 3` is the counting bound
`minDegreeForC4_le_of_choose_lt`: `C(6,2) = 15 < 18 = 6 · C(3,2)`, so minimum degree `3` on
six vertices already yields more cherries than vertex pairs, forcing a `C₄`.  Note the linear
bound `f(6) ≤ 6 − 2 = 4` is *not* sharp here — it is the Kővári–Sós–Turán count that pins the
value, the first place the two upper bounds diverge. -/
theorem minDegreeForC4_six : minDegreeForC4 6 = 3 := by
  have hle : minDegreeForC4 6 ≤ 3 := minDegreeForC4_le_of_choose_lt (by decide)
  have hge : 3 ≤ minDegreeForC4 6 := three_le_minDegreeForC4 (by norm_num)
  omega

/-!
## An explicit `O(√n)` upper bound

The counting bound `minDegreeForC4_le_of_choose_lt` gives `f(n) = O(√n)` only implicitly,
through the choose inequality `C(n,2) < n · C(k,2)`.  We now unfold that into a clean,
quotable **closed form** valid for every `n ≥ 1`:

  `f(n) ≤ √n + 2`.

This is the matching upper bound of the correct order — the true asymptotics are
`f(n) = (1 + o(1))√n`, so the leading constant `1` here is sharp; only an additive `O(1)`
is lost relative to the sharp Kővári–Sós–Turán constant `(1 + √(4n−3))/2`.  It dwarfs the
elementary linear bound `f(n) ≤ n − 2`.
-/

/-- Divisibility helper: `m · (m − 1)` is always even (one of two consecutive integers is). -/
private theorem two_dvd_mul_pred (m : ℕ) : 2 ∣ m * (m - 1) := by
  rcases Nat.even_or_odd m with he | ho
  · exact Dvd.dvd.mul_right he.two_dvd _
  · exact Dvd.dvd.mul_left (Nat.Odd.sub_odd ho odd_one).two_dvd _

/-- Doubling identity: `2 · C(m, 2) = m · (m − 1)` (the halving in `Nat.choose 2` is exact). -/
private theorem two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (two_dvd_mul_pred m)

/-- **Arithmetic core of the counting bound.**  For `n ≥ 1`, the hypothesis `n ≤ k(k−1)`
implies the strict cherry-vs-pair inequality `C(n,2) < n · C(k,2)` consumed by
`minDegreeForC4_le_of_choose_lt`.  (Both `n(n−1)` and `k(k−1)` are even, so doubling
reduces the claim to `n − 1 < k(k−1)`, which follows from `n ≤ k(k−1)`.) -/
theorem choose_two_lt_of_le_mul_pred {n k : ℕ} (hn : 1 ≤ n) (h : n ≤ k * (k - 1)) :
    n.choose 2 < n * k.choose 2 := by
  have key : 2 * n.choose 2 < 2 * (n * k.choose 2) := by
    rw [two_mul_choose_two n, mul_left_comm 2 n (k.choose 2), two_mul_choose_two k]
    have hstep : n - 1 < k * (k - 1) := by omega
    exact Nat.mul_lt_mul_of_pos_left hstep (by omega)
  exact Nat.lt_of_mul_lt_mul_left key

/-- **`n ≤ k(k−1)` forces `f(n) ≤ k`.**  A cleaner packaging of the counting bound: as soon
as `k(k−1) ≥ n`, minimum degree `k` on `n` vertices already yields more cherries than vertex
pairs, hence a `C₄`.  This is the reformulation that makes the `√n` order transparent. -/
theorem minDegreeForC4_le_of_le_mul_pred {n k : ℕ} (hn : 1 ≤ n) (h : n ≤ k * (k - 1)) :
    minDegreeForC4 n ≤ k :=
  minDegreeForC4_le_of_choose_lt (choose_two_lt_of_le_mul_pred hn h)

/-- **Explicit `O(√n)` upper bound: `f(n) ≤ √n + 2` for all `n ≥ 1`.**  Take `k = √n + 2`.
Since `n < (√n + 1)²` we have `n ≤ (√n)² + 2√n`, while `k(k−1) = (√n + 2)(√n + 1) =
(√n)² + 3√n + 2 ≥ n`, so `minDegreeForC4_le_of_le_mul_pred` applies.  The leading constant
`1` matches the true `f(n) = (1 + o(1))√n`; only an additive constant is lost. -/
theorem minDegreeForC4_le_sqrt {n : ℕ} (hn : 1 ≤ n) :
    minDegreeForC4 n ≤ Nat.sqrt n + 2 := by
  apply minDegreeForC4_le_of_le_mul_pred hn
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have hsub : Nat.sqrt n + 2 - 1 = Nat.sqrt n + 1 := by omega
  rw [hsub]
  nlinarith [hlt]

end Erdos85
