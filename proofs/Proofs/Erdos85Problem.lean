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
  push_neg at hk2
  exact hfree (hk (starGraph n) (le_trans (by omega : k ≤ 1) hstar))

end Erdos85
