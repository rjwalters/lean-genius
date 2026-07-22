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

/-- **No `C₄` below four vertices.**  The contrapositive of
`containsC4_four_le_card`: a host graph on fewer than four vertices cannot carry a
4-cycle, because `containsC4` supplies an injection `Fin 4 ↪ V`.  This is the
degenerate boundary of the whole degree-threshold question — for `n < 4` the
predicate "forces a `C₄`" can only hold vacuously. -/
theorem not_containsC4_of_card_lt_four {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h : Fintype.card V < 4) : ¬ containsC4 V G :=
  fun hc => absurd (containsC4_four_le_card hc) (by omega)

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

/-- **Degenerate small cases: `f(n) = n` for `1 ≤ n ≤ 3`.**  When `n < 4` *no*
graph on `Fin n` can contain a `C₄` at all (`not_containsC4_of_card_lt_four`), so
the defining threshold "minimum degree `≥ k` forces a `C₄`" holds only *vacuously*
— precisely for those `k` no graph attains.  The largest minimum degree attainable
on `Fin n` is `n − 1` (realised by the complete graph `⊤`, and never exceeded since
`deg v ≤ n − 1`), so the least `k` with no graph reaching it is `k = n`.  Hence
`f(1) = 1`, `f(2) = 2`, `f(3) = 3`, completing the exact-value table below the first
genuine case `f(4) = 2`.  (These are boundary values where a 4-cycle is impossible,
not evidence about the `√n` growth, which begins at `n ≥ 4`.) -/
theorem minDegreeForC4_eq_self_of_le_three {n : ℕ} (h1 : 1 ≤ n) (h3 : n ≤ 3) :
    minDegreeForC4 n = n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI hdec : DecidableRel (⊤ : SimpleGraph (Fin n)).Adj := fun i j => by
    rw [top_adj]; infer_instance
  -- No graph on `Fin n` contains a `C₄` (too few vertices).
  have hfree : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ¬ containsC4 (Fin n) G := by
    intro G _
    exact not_containsC4_of_card_lt_four (by rw [Fintype.card_fin]; omega)
  -- Every graph on `Fin n` has minimum degree at most `n − 1`.
  have hup : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.minDegree ≤ n - 1 := by
    intro G _
    set v0 : Fin n := ⟨0, by omega⟩ with hv0
    refine le_trans (G.minDegree_le_degree v0) ?_
    rw [← G.card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset v0 ⊆ Finset.univ.erase v0 := by
      intro x hx
      exact Finset.mem_erase.mpr
        ⟨(G.ne_of_adj ((G.mem_neighborFinset _ _).mp hx)).symm, Finset.mem_univ x⟩
    calc (G.neighborFinset v0).card
        ≤ (Finset.univ.erase v0).card := Finset.card_le_card hsub
      _ = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- The complete graph attains minimum degree `n − 1`.
  have htop : n - 1 ≤ (⊤ : SimpleGraph (Fin n)).minDegree := by
    apply le_minDegree_of_forall_le_degree
    intro v
    have hnb : (⊤ : SimpleGraph (Fin n)).neighborFinset v = Finset.univ.erase v := by
      ext x
      simp [SimpleGraph.mem_neighborFinset, top_adj, Finset.mem_erase, ne_comm]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  -- Assemble via antisymmetry on the defining `sInf`.
  unfold minDegreeForC4
  apply le_antisymm
  · apply Nat.sInf_le
    intro G _ hmin
    exact absurd (le_trans hmin (hup G)) (by omega)
  · apply le_csInf
    · refine ⟨n, ?_⟩
      intro G _ hmin
      exact absurd (le_trans hmin (hup G)) (by omega)
    · intro k hk
      by_contra hlt
      rw [not_le] at hlt
      exact hfree (⊤ : SimpleGraph (Fin n))
        (hk (⊤ : SimpleGraph (Fin n)) (le_trans (show k ≤ n - 1 by omega) htop))

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

/-!
## Sharpening the additive constant: `f(n) ≤ √n + 1` on the lower Beatty half

The bound `f(n) ≤ √n + 2` loses `1` in the additive constant relative to the sharp
Kővári–Sós–Turán value `k₀(n) = ⌈(1 + √(4n−3))/2⌉ = least k with k(k−1) ≥ n`.  Writing
`s = √n`, the counting bound `minDegreeForC4_le_of_le_mul_pred` uses `k = s + 1` exactly
when `k(k−1) = s(s+1) ≥ n`, i.e. `n ≤ s(s+1)`.  This holds on the **lower half** of each
gap `[s², (s+1)²)`, namely `s² ≤ n ≤ s² + s`; for those `n` we get the sharp
`f(n) ≤ s + 1`.  (On the upper half `s² + s < n < (s+1)²` the choice `k = s + 1` fails and
`√n + 2` is the best this counting argument gives.)  In particular every **perfect square**
`n = m²` satisfies `m² ≤ m(m+1)`, so `f(m²) ≤ m + 1` — the additive constant is pinned to
`+1` there, matching the true `f(n) = (1 + o(1))√n` up to the last additive unit.
-/

/-- **Sharpened `O(√n)` bound on the lower Beatty half: `f(n) ≤ √n + 1`** whenever
`n ≤ √n · (√n + 1)`.  This is the sharp Kővári–Sós–Turán constant on the lower half of each
interval `[s², (s+1)²)` with `s = √n`, improving `minDegreeForC4_le_sqrt` by one there.
Take `k = √n + 1`; then `k(k−1) = (√n + 1)·√n ≥ n` is exactly the hypothesis. -/
theorem minDegreeForC4_le_sqrt_add_one {n : ℕ} (hn : 1 ≤ n)
    (hlow : n ≤ Nat.sqrt n * (Nat.sqrt n + 1)) :
    minDegreeForC4 n ≤ Nat.sqrt n + 1 := by
  apply minDegreeForC4_le_of_le_mul_pred hn
  have hsub : Nat.sqrt n + 1 - 1 = Nat.sqrt n := by omega
  rw [hsub]
  -- goal `n ≤ (√n + 1) * √n`, hypothesis `n ≤ √n * (√n + 1)`
  rw [Nat.mul_comm]
  exact hlow

/-- **The additive constant is `+1` on every perfect square: `f(m²) ≤ m + 1`** for `m ≥ 1.**
Since `√(m²) = m` and `m² ≤ m(m + 1)`, the lower-half sharpening
`minDegreeForC4_le_sqrt_add_one` applies with `s = m`.  This is the cleanest quotable form of
the correct-order upper bound: on the squares the bound is `√n + 1`, one better than the
general `√n + 2` and within a single additive unit of the true `(1 + o(1))√n`. -/
theorem minDegreeForC4_le_sq {m : ℕ} (hm : 1 ≤ m) :
    minDegreeForC4 (m * m) ≤ m + 1 := by
  have hsqrt : Nat.sqrt (m * m) = m := Nat.sqrt_eq m
  have hn : 1 ≤ m * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h := minDegreeForC4_le_sqrt_add_one hn (by rw [hsqrt]; nlinarith)
  rwa [hsqrt] at h

/-!
## A parity refinement of the counting bound, and `f(7) = 3`

At `n = 7` the plain cherry count *just* fails: minimum degree `3` on seven vertices gives
`∑_v C(deg v, 2) ≥ 7 · C(3,2) = 21 = C(7,2)` — equality, not the strict inequality the
pigeonhole needs.  But the degree sum of any graph is even (handshake), while seven vertices
of degree exactly `3` would sum to the odd number `21`.  So minimum degree `3` on `7`
vertices in fact forces some vertex of degree `≥ 4`, boosting the cherry count to at least
`6 · C(3,2) + C(4,2) = 24 > 21` and forcing a `C₄` after all.

In general, whenever `n` and `k` are **both odd**, the threshold hypothesis upgrades itself:
some vertex has degree `≥ k + 1`, so the cherry count is at least
`(n − 1) · C(k,2) + C(k+1,2)`, strictly more than the naive `n · C(k,2)` gives credit for.
This parity refinement yields the fourth exact value `f(7) = 3` — a point where BOTH earlier
upper bounds fail (`n − 2 = 5`; plain counting only `f(7) ≤ 4`) — and an infinite family
`f(4m² + 2m + 1) ≤ 2m + 1 = √n + 1` inside the upper Beatty half `(s² + s, (s+1)²)` with
`s = 2m`, where the plain counting bound is provably inapplicable below `√n + 2`.
-/

/-- **Parity boost.**  In a graph on an odd number of vertices where every degree is at
least the odd number `k`, some vertex has degree `≥ k + 1`: otherwise every degree equals
`k` exactly, making the degree sum the odd number `|V| · k` — contradicting the handshake
identity `∑_v deg v = 2 · |E|`. -/
theorem exists_succ_le_degree_of_odd {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hodd : Odd (Fintype.card V)) (hk : Odd k) (hdeg : ∀ v : V, k ≤ G.degree v) :
    ∃ v : V, k + 1 ≤ G.degree v := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ v : V, G.degree v = k :=
    fun v => le_antisymm (Nat.lt_succ_iff.mp (hcon v)) (hdeg v)
  have hsum : ∑ v : V, G.degree v = Fintype.card V * k := by
    rw [Finset.sum_congr rfl fun v _ => hall v, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [hsum] at hhs
  obtain ⟨a, ha⟩ := hodd.mul hk
  rw [ha] at hhs
  omega

/-- **Parity-refined counting bound.**  For odd `n` and odd `k`, the sharpened cherry
inequality `C(n, 2) < (n − 1) · C(k, 2) + C(k + 1, 2)` already forces `f(n) ≤ k`:
minimum degree `k` plus the parity boost gives one vertex of degree `≥ k + 1`, so the
cherries number at least `(n − 1) · C(k, 2) + C(k + 1, 2)`, exceeding the `C(n, 2)`
available endpoint pairs — and two cherries sharing a pair form a `C₄`. -/
theorem minDegreeForC4_le_of_choose_lt_odd {n k : ℕ} (hn : Odd n) (hk : Odd k)
    (h : n.choose 2 < (n - 1) * k.choose 2 + (k + 1).choose 2) :
    minDegreeForC4 n ≤ k := by
  apply Nat.sInf_le
  intro G _ hmin
  have hdeg : ∀ v : Fin n, k ≤ G.degree v :=
    fun v => le_trans hmin (G.minDegree_le_degree v)
  obtain ⟨v₀, hv₀⟩ := exists_succ_le_degree_of_odd G (by simpa using hn) hk hdeg
  apply containsC4_of_card_choose_two_lt
  rw [Fintype.card_fin]
  have hcard : ((Finset.univ : Finset (Fin n)).erase v₀).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ, Fintype.card_fin]
  calc n.choose 2
      < (n - 1) * k.choose 2 + (k + 1).choose 2 := h
    _ = (∑ _v ∈ Finset.univ.erase v₀, k.choose 2) + (k + 1).choose 2 := by
        rw [Finset.sum_const, hcard, smul_eq_mul]
    _ ≤ (∑ v ∈ Finset.univ.erase v₀, (G.degree v).choose 2) + (G.degree v₀).choose 2 :=
        Nat.add_le_add
          (Finset.sum_le_sum fun v _ => Nat.choose_le_choose 2 (hdeg v))
          (Nat.choose_le_choose 2 hv₀)
    _ = ∑ v : Fin n, (G.degree v).choose 2 :=
        Finset.sum_erase_add _ _ (Finset.mem_univ v₀)

/-- **A fourth exact value: `f(7) = 3`.**  The lower half is the general cycle bound
`three_le_minDegreeForC4`.  The upper half `f(7) ≤ 3` is the parity-refined count:
`C(7,2) = 21 < 24 = 6 · C(3,2) + C(4,2)`.  Both earlier upper bounds fail at `n = 7`:
the linear bound gives `7 − 2 = 5`, and the plain cherry count only `f(7) ≤ 4` since
`7 · C(3,2) = 21 = C(7,2)` holds with *equality* — it is the handshake parity that pins
the value.  The exact-value table is now complete for `1 ≤ n ≤ 7`:
`f = 1, 2, 3, 2, 3, 3, 3`. -/
theorem minDegreeForC4_seven : minDegreeForC4 7 = 3 := by
  have hle : minDegreeForC4 7 ≤ 3 :=
    minDegreeForC4_le_of_choose_lt_odd (by decide) (by decide) (by decide)
  have hge : 3 ≤ minDegreeForC4 7 := three_le_minDegreeForC4 (by norm_num)
  omega

/-- Arithmetic core of the family bound: with `n = 4m² + 2m + 1` and `k = 2m + 1` we have
`n − 1 = k(k − 1)` *exactly*, so after doubling (`two_mul_choose_two`), the parity-refined
cherry inequality reduces to `n − 1 < k(k + 1)`, i.e. `4m² + 2m < 4m² + 6m + 2`. -/
private theorem choose_lt_family (m : ℕ) :
    (4 * m * m + 2 * m + 1).choose 2
      < (4 * m * m + 2 * m + 1 - 1) * (2 * m + 1).choose 2 + (2 * m + 1 + 1).choose 2 := by
  have hsub : 4 * m * m + 2 * m + 1 - 1 = 4 * m * m + 2 * m := by omega
  rw [hsub]
  have key : 2 * (4 * m * m + 2 * m + 1).choose 2
      < 2 * ((4 * m * m + 2 * m) * (2 * m + 1).choose 2 + (2 * m + 1 + 1).choose 2) := by
    rw [two_mul_choose_two, Nat.mul_add, mul_left_comm 2 (4 * m * m + 2 * m),
      two_mul_choose_two, two_mul_choose_two]
    have h1 : 4 * m * m + 2 * m + 1 - 1 = 4 * m * m + 2 * m := by omega
    have h2 : 2 * m + 1 - 1 = 2 * m := by omega
    have h3 : 2 * m + 1 + 1 - 1 = 2 * m + 1 := by omega
    rw [h1, h2, h3]
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left key

/-- **Sharp constant on an infinite family in the upper Beatty half:**
`f(4m² + 2m + 1) ≤ 2m + 1` for every `m`.  Writing `s = 2m`, these are the points
`n = s² + s + 1` — the FIRST point of the upper half-interval `(s² + s, (s+1)²)` for each
even `s`, where the plain counting bound `minDegreeForC4_le_of_le_mul_pred` is provably
inapplicable below `√n + 2` (it needs `n ≤ k(k−1)`, but `n = s² + s + 1 > s(s+1)`).
Parity rescues the sharp constant there: `n` and `k = s + 1 = 2m + 1` are both odd, and
`n − 1 = k(k−1)` exactly, so the boosted count wins by the margin
`C(k+1,2) − C(k,2) = k > 0`.  At `m = 1` this is exactly `f(7) ≤ 3`. -/
theorem minDegreeForC4_le_of_upper_beatty (m : ℕ) :
    minDegreeForC4 (4 * m * m + 2 * m + 1) ≤ 2 * m + 1 :=
  minDegreeForC4_le_of_choose_lt_odd
    ⟨2 * m * m + m, by ring⟩ ⟨m, rfl⟩ (choose_lt_family m)

/-- The family bound in `√n` form: for `m ≥ 1` we have `√(4m² + 2m + 1) = 2m`, so
`minDegreeForC4_le_of_upper_beatty` reads `f(n) ≤ √n + 1` at `n = 4m² + 2m + 1` — beating
the general `√n + 2` bound (`minDegreeForC4_le_sqrt`) at infinitely many points of the
upper Beatty half, which no plain-counting argument can reach. -/
theorem minDegreeForC4_le_sqrt_add_one_of_upper_beatty {m : ℕ} (hm : 1 ≤ m) :
    minDegreeForC4 (4 * m * m + 2 * m + 1)
      ≤ Nat.sqrt (4 * m * m + 2 * m + 1) + 1 := by
  have h1 : 2 * m ≤ Nat.sqrt (4 * m * m + 2 * m + 1) :=
    Nat.le_sqrt.mpr (by nlinarith)
  have h2 : Nat.sqrt (4 * m * m + 2 * m + 1) < 2 * m + 1 :=
    Nat.sqrt_lt.mpr (by nlinarith)
  have hsqrt : Nat.sqrt (4 * m * m + 2 * m + 1) = 2 * m := by omega
  rw [hsqrt]
  exact minDegreeForC4_le_of_upper_beatty m

/-!
## A fifth exact value: `f(8) = 3` — beyond the counting/parity barrier

Cherry counting stalls at `f(8) ≤ 4` (`C(8,2) = 28 ≥ 24 = 8·C(3,2)`, no strict excess) and
the odd-order parity boost is silent (`8` is even).  Earlier sessions recorded `f(8) = 3` as
needing the extremal table value `ex(8; C₄) = 11`.  It does not.  Minimum degree `3` on `8`
vertices reduces to the `3`-regular case — a vertex of degree `≥ 5` gives `31 > 28`
cherries, two vertices of degree `4` give `30 > 28`, and *exactly one* vertex of degree `4`
makes the degree sum `25`, odd, contradicting the handshake identity.  And a `3`-regular
`C₄`-free graph on `8` vertices is impossible by a purely **local** argument:

* **every vertex would lie in a triangle**: if the three neighbours `a, b, c` of `v` were
  pairwise non-adjacent, the punctured neighbourhoods `N(a)\{v}`, `N(b)\{v}`, `N(c)\{v}`
  (each of size `2`) would be pairwise disjoint — a shared vertex is a second common
  neighbour of two of `a, b, c`, i.e. a `C₄` — and avoid all of `v, a, b, c`, packing `6`
  vertices into the remaining `8 − 4 = 4`;
* **the triangle through a vertex is unique** at degree `3`: two triangles through `v`
  either coincide, or exhibit two common neighbours of an edge at `v` (a `C₄`), or force
  `deg v ≥ 4`;
* so the triangles would **partition** the `8` vertices into disjoint `3`-sets — `3 ∣ 8`,
  absurd.

This breaks the "needs `ex(n; C₄)` tables" barrier for the first even-order value past the
counting threshold and completes the exact-value table for `1 ≤ n ≤ 8`.
-/

/-- **Two common neighbours make a `C₄`.**  If distinct `x, y` have distinct common
neighbours `v, v'`, the rim `x–v–y–v'` is a `4`-cycle.  (Repackages `containsC4_of_rim`;
`C₄`-freeness is exactly "every vertex pair has at most one common neighbour".) -/
theorem containsC4_of_two_common {V : Type*} {G : SimpleGraph V} {x y v v' : V}
    (hxy : x ≠ y) (hvv : v ≠ v') (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hv'x : G.Adj v' x) (hv'y : G.Adj v' y) : containsC4 V G :=
  containsC4_of_rim hvx.symm hvy hv'y.symm hv'x hxy hvv
    (G.ne_of_adj hvx) (G.ne_of_adj hvy) (G.ne_of_adj hv'x) (G.ne_of_adj hv'y)

/-- **In a `3`-regular `C₄`-free graph on `8` vertices, every vertex lies in a triangle.**
If `v`'s neighbours `a, b, c` were pairwise non-adjacent, their punctured neighbourhoods
`N(·) \ {v}` would be pairwise-disjoint `2`-sets avoiding `{v, a, b, c}` — six vertices in
the remaining four slots. -/
theorem exists_triangle_of_three_regular {G : SimpleGraph (Fin 8)} [DecidableRel G.Adj]
    (hreg : ∀ w : Fin 8, G.degree w = 3) (hfree : ¬ containsC4 (Fin 8) G) (v : Fin 8) :
    ∃ a b : Fin 8, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  have hcard : (G.neighborFinset v).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]; exact hreg v
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.mp hcard
  have hva : G.Adj v a := (G.mem_neighborFinset v a).mp (by rw [hN]; simp)
  have hvb : G.Adj v b := (G.mem_neighborFinset v b).mp (by rw [hN]; simp)
  have hvc : G.Adj v c := (G.mem_neighborFinset v c).mp (by rw [hN]; simp)
  by_contra hcon
  push Not at hcon
  have hnab : ¬ G.Adj a b := hcon a b hva hvb
  have hnac : ¬ G.Adj a c := hcon a c hva hvc
  have hnbc : ¬ G.Adj b c := hcon b c hvb hvc
  -- pairwise disjointness of the punctured neighbourhoods
  have hkey : ∀ p q : Fin 8, G.Adj v p → G.Adj v q → p ≠ q →
      Disjoint ((G.neighborFinset p).erase v) ((G.neighborFinset q).erase v) := by
    intro p q hvp hvq hpq
    rw [Finset.disjoint_left]
    intro x hxp hxq
    obtain ⟨hxv, hxp'⟩ := Finset.mem_erase.mp hxp
    obtain ⟨-, hxq'⟩ := Finset.mem_erase.mp hxq
    exact hfree (containsC4_of_two_common hpq (Ne.symm hxv) hvp hvq
      ((G.mem_neighborFinset p x).mp hxp').symm ((G.mem_neighborFinset q x).mp hxq').symm)
  have hcard2 : ∀ p : Fin 8, G.Adj v p → ((G.neighborFinset p).erase v).card = 2 := by
    intro p hvp
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset p v).mpr hvp.symm),
        G.card_neighborFinset_eq_degree, hreg p]
  -- the union has six elements
  have hdab := hkey a b hva hvb hab
  have hdac := hkey a c hva hvc hac
  have hdbc := hkey b c hvb hvc hbc
  have h1 : ((G.neighborFinset a).erase v ∪ (G.neighborFinset b).erase v).card = 4 := by
    rw [Finset.card_union_of_disjoint hdab, hcard2 a hva, hcard2 b hvb]
  have hdc : Disjoint ((G.neighborFinset a).erase v ∪ (G.neighborFinset b).erase v)
      ((G.neighborFinset c).erase v) := Finset.disjoint_union_left.mpr ⟨hdac, hdbc⟩
  have hScard : (((G.neighborFinset a).erase v ∪ (G.neighborFinset b).erase v)
      ∪ (G.neighborFinset c).erase v).card = 6 := by
    rw [Finset.card_union_of_disjoint hdc, h1, hcard2 c hvc]
  -- ... but it sits inside the four vertices outside {v, a, b, c}
  have hmv : v ∈ (univ : Finset (Fin 8)) := Finset.mem_univ v
  have hma : a ∈ (univ : Finset (Fin 8)).erase v :=
    Finset.mem_erase.mpr ⟨(G.ne_of_adj hva).symm, Finset.mem_univ a⟩
  have hmb : b ∈ ((univ : Finset (Fin 8)).erase v).erase a :=
    Finset.mem_erase.mpr ⟨(hab).symm,
      Finset.mem_erase.mpr ⟨(G.ne_of_adj hvb).symm, Finset.mem_univ b⟩⟩
  have hmc : c ∈ (((univ : Finset (Fin 8)).erase v).erase a).erase b :=
    Finset.mem_erase.mpr ⟨(hbc).symm, Finset.mem_erase.mpr ⟨(hac).symm,
      Finset.mem_erase.mpr ⟨(G.ne_of_adj hvc).symm, Finset.mem_univ c⟩⟩⟩
  have htcard : (((((univ : Finset (Fin 8)).erase v).erase a).erase b).erase c).card = 4 := by
    rw [Finset.card_erase_of_mem hmc, Finset.card_erase_of_mem hmb,
        Finset.card_erase_of_mem hma, Finset.card_erase_of_mem hmv,
        Finset.card_univ, Fintype.card_fin]
  have hsub : ((G.neighborFinset a).erase v ∪ (G.neighborFinset b).erase v)
      ∪ (G.neighborFinset c).erase v
      ⊆ ((((univ : Finset (Fin 8)).erase v).erase a).erase b).erase c := by
    intro x hx
    have hx3 : x ∈ (G.neighborFinset a).erase v ∨ x ∈ (G.neighborFinset b).erase v
        ∨ x ∈ (G.neighborFinset c).erase v := by
      rcases Finset.mem_union.mp hx with h | h
      · rcases Finset.mem_union.mp h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
    rcases hx3 with hxm | hxm | hxm
    · obtain ⟨hxv, hm⟩ := Finset.mem_erase.mp hxm
      have hax : G.Adj a x := (G.mem_neighborFinset a x).mp hm
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
        Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩⟩⟩⟩
      · rintro rfl; exact hnac hax
      · rintro rfl; exact hnab hax
      · rintro rfl; exact (G.ne_of_adj hax) rfl
    · obtain ⟨hxv, hm⟩ := Finset.mem_erase.mp hxm
      have hbx : G.Adj b x := (G.mem_neighborFinset b x).mp hm
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
        Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩⟩⟩⟩
      · rintro rfl; exact hnbc hbx
      · rintro rfl; exact (G.ne_of_adj hbx) rfl
      · rintro rfl; exact hnab hbx.symm
    · obtain ⟨hxv, hm⟩ := Finset.mem_erase.mp hxm
      have hcx : G.Adj c x := (G.mem_neighborFinset c x).mp hm
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
        Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩⟩⟩⟩
      · rintro rfl; exact (G.ne_of_adj hcx) rfl
      · rintro rfl; exact hnbc hcx.symm
      · rintro rfl; exact hnac hcx.symm
  have hle := Finset.card_le_card hsub
  rw [hScard, htcard] at hle
  omega

/-- **At degree `3`, the triangle through a vertex is unique** (as its pair of non-apex
vertices): two triangles `v–a–b` and `v–a'–b'` have `{a, b} = {a', b'}`, else either an
edge at `v` acquires two common neighbours (a `C₄`) or `v` acquires four distinct
neighbours. -/
theorem triangle_pair_unique {G : SimpleGraph (Fin 8)} [DecidableRel G.Adj]
    (hreg : ∀ w : Fin 8, G.degree w = 3) (hfree : ¬ containsC4 (Fin 8) G) {v a b a' b' : Fin 8}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    (hva' : G.Adj v a') (hvb' : G.Adj v b') (hab' : G.Adj a' b') :
    ({a, b} : Finset (Fin 8)) = {a', b'} := by
  -- an edge at `v` with two distinct common neighbours yields a `C₄`
  have hkill : ∀ p q q' : Fin 8, G.Adj v p → G.Adj v q → G.Adj v q' → q ≠ q' →
      G.Adj p q → G.Adj p q' → False := by
    intro p q q' hvp hvq hvq' hqq' hpq hpq'
    exact hfree (containsC4_of_two_common (G.ne_of_adj hvp) hqq'
      hvq.symm hpq.symm hvq'.symm hpq'.symm)
  by_cases h1 : a' = a
  · by_cases h2 : b' = b
    · rw [h1, h2]
    · -- edge `v–a` has common neighbours `b` and `b'`
      have hab'' : G.Adj a b' := h1 ▸ hab'
      exact (hkill a b b' hva hvb hvb' (fun h => h2 h.symm) hab hab'').elim
  · by_cases h1b : a' = b
    · by_cases h2 : b' = a
      · rw [h1b, h2]; exact Finset.pair_comm a b
      · -- edge `v–b` has common neighbours `a` and `b'`
        have hab'' : G.Adj b b' := h1b ▸ hab'
        exact (hkill b a b' hvb hva hvb' (fun h => h2 h.symm) hab.symm hab'').elim
    · -- `a' ∉ {a, b}`: then `N(v) = {a, b, a'}` and `b'` must be one of them
      have hcard : (G.neighborFinset v).card = 3 := by
        rw [G.card_neighborFinset_eq_degree]; exact hreg v
      have hsub3 : ({a, b, a'} : Finset (Fin 8)) ⊆ G.neighborFinset v := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact (G.mem_neighborFinset v x).mpr hva
        · exact (G.mem_neighborFinset v x).mpr hvb
        · exact (G.mem_neighborFinset v x).mpr hva'
      have hcard3 : ({a, b, a'} : Finset (Fin 8)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push Not
              exact ⟨G.ne_of_adj hab, fun h => h1 h.symm⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]
              exact fun h => h1b h.symm),
            Finset.card_singleton]
      have hNeq : ({a, b, a'} : Finset (Fin 8)) = G.neighborFinset v :=
        Finset.eq_of_subset_of_card_le hsub3 (by rw [hcard, hcard3])
      have hb'mem : b' ∈ ({a, b, a'} : Finset (Fin 8)) := by
        rw [hNeq]; exact (G.mem_neighborFinset v b').mpr hvb'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb'mem
      rcases hb'mem with h | h | h
      · -- `b' = a`: edge `v–a` has common neighbours `b` and `a'`
        have hab'' : G.Adj a' a := h ▸ hab'
        exact (hkill a b a' hva hvb hva' (fun hh => h1b hh.symm) hab
          hab''.symm).elim
      · -- `b' = b`: edge `v–b` has common neighbours `a` and `a'`
        have hab'' : G.Adj a' b := h ▸ hab'
        exact (hkill b a a' hvb hva hva' (fun hh => h1 hh.symm) hab.symm
          hab''.symm).elim
      · -- `b' = a'`: a triangle needs distinct vertices
        exact absurd h.symm (G.ne_of_adj hab')

/-- **No `3`-regular `C₄`-free graph on `8` vertices.**  Every vertex lies in a triangle
(`exists_triangle_of_three_regular`), the triangle through each vertex is unique
(`triangle_pair_unique`), so the triangles partition the vertex set into `3`-sets —
`3 ∣ 8`, absurd.  Contrapositive: every `3`-regular graph on `8` vertices contains a `C₄`. -/
theorem containsC4_of_three_regular_eight (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hreg : ∀ w : Fin 8, G.degree w = 3) : containsC4 (Fin 8) G := by
  by_contra hfree
  choose f g hf hg hfg using exists_triangle_of_three_regular hreg hfree
  -- the triangle 3-set through each vertex
  set t : Fin 8 → Finset (Fin 8) := fun w => {w, f w, g w} with ht
  have htw : ∀ w : Fin 8, t w = {w, f w, g w} := fun _ => rfl
  have hmem : ∀ w, w ∈ t w := by
    intro w; rw [htw w]; exact Finset.mem_insert_self w _
  have hcard3 : ∀ w, (t w).card = 3 := by
    intro w
    rw [htw w,
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨G.ne_of_adj (hf w), G.ne_of_adj (hg w)⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact G.ne_of_adj (hfg w)),
        Finset.card_singleton]
  -- coherence: any member of `t w` has the same triangle
  have hcoh : ∀ w u : Fin 8, u ∈ t w → t u = t w := by
    intro w u hu
    rw [htw w] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h
    · rw [h]
    · -- `u = f w`: both `{f u, g u}` and `{w, g w}` are triangle pairs at `u`
      have hpair := triangle_pair_unique hreg hfree (hf (f w)) (hg (f w)) (hfg (f w))
        (hf w).symm (hfg w) (hg w)
      rw [h, htw (f w), htw w, hpair]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · -- `u = g w`: both `{f u, g u}` and `{w, f w}` are triangle pairs at `u`
      have hpair := triangle_pair_unique hreg hfree (hf (g w)) (hg (g w)) (hfg (g w))
        (hg w).symm (hfg w).symm (hf w)
      rw [h, htw (g w), htw w, hpair]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  -- the distinct triangles partition `Fin 8`
  set T : Finset (Finset (Fin 8)) := Finset.univ.image t with hT
  have hcover : (Finset.univ : Finset (Fin 8)) = T.biUnion id := by
    apply Finset.ext
    intro x
    constructor
    · intro _
      have hx : t x ∈ T := by
        rw [hT]
        exact Finset.mem_image_of_mem t (Finset.mem_univ x)
      exact Finset.mem_biUnion.mpr ⟨t x, hx, hmem x⟩
    · intro _
      exact Finset.mem_univ x
  have hdisjT : ((T : Set (Finset (Fin 8)))).PairwiseDisjoint id := by
    intro s1 hs1 s2 hs2 hne
    obtain ⟨w1, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs1)
    obtain ⟨w2, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs2)
    simp only [Function.onFun, id_eq]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact hne ((hcoh w1 x hx1).symm.trans (hcoh w2 x hx2))
  have hcount : (T.biUnion id).card = ∑ s ∈ T, s.card := Finset.card_biUnion hdisjT
  have hsum3 : ∑ s ∈ T, s.card = 3 * T.card := by
    have h3 : ∀ s ∈ T, s.card = 3 := by
      intro s hs
      rw [hT] at hs
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hs
      exact hcard3 w
    rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, mul_comm]
  have h8 : (8 : ℕ) = 3 * T.card := by
    have hu : (Finset.univ : Finset (Fin 8)).card = 3 * T.card := by
      rw [hcover, hcount, hsum3]
    simpa using hu
  omega

/-- **Minimum degree `3` forces a `C₄` on `8` vertices.**  Degree casework: a vertex of
degree `≥ 5` pushes the cherry count to `31 > 28`; two vertices of degree `≥ 4` push it to
`30 > 28`; exactly one vertex of degree `4` (all others `3`) makes the degree sum `25`,
odd — impossible by handshake; and the `3`-regular case is
`containsC4_of_three_regular_eight`. -/
theorem containsC4_of_eight_min_degree_three (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hmin : 3 ≤ G.minDegree) : containsC4 (Fin 8) G := by
  have hdeg : ∀ v : Fin 8, 3 ≤ G.degree v :=
    fun v => le_trans hmin (G.minDegree_le_degree v)
  by_cases hreg : ∀ v : Fin 8, G.degree v = 3
  · exact containsC4_of_three_regular_eight G hreg
  · push Not at hreg
    obtain ⟨v₀, hv₀⟩ := hreg
    have hv₀4 : 4 ≤ G.degree v₀ := by have := hdeg v₀; omega
    have hrest : ∀ s : Finset (Fin 8), (∀ v ∈ s, 3 ≤ G.degree v) →
        s.card * 3 ≤ ∑ v ∈ s, (G.degree v).choose 2 := by
      intro s hs
      calc s.card * 3 = s.card • 3 := by rw [smul_eq_mul]
        _ ≤ ∑ v ∈ s, (G.degree v).choose 2 :=
            Finset.card_nsmul_le_sum s _ 3
              (fun v hv => le_trans (by decide : (3 : ℕ) ≤ Nat.choose 3 2)
                (Nat.choose_le_choose 2 (hs v hv)))
    have h28 : Nat.choose 8 2 = 28 := by decide
    by_cases h5 : 5 ≤ G.degree v₀
    · -- one vertex of degree ≥ 5: cherry count `≥ 21 + 10 = 31 > 28`
      apply containsC4_of_card_choose_two_lt
      rw [Fintype.card_fin]
      have hsplit := Finset.sum_erase_add univ
        (fun v => (G.degree v).choose 2) (Finset.mem_univ v₀)
      have h7 : ((univ : Finset (Fin 8)).erase v₀).card = 7 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ,
          Fintype.card_fin]
      have hr := hrest ((univ : Finset (Fin 8)).erase v₀) (fun v _ => hdeg v)
      rw [h7] at hr
      have hbig : 10 ≤ (G.degree v₀).choose 2 :=
        le_trans (by decide : (10 : ℕ) ≤ Nat.choose 5 2) (Nat.choose_le_choose 2 h5)
      omega
    · have hv04 : G.degree v₀ = 4 := by omega
      by_cases h2nd : ∃ u : Fin 8, u ≠ v₀ ∧ 4 ≤ G.degree u
      · -- two vertices of degree ≥ 4: cherry count `≥ 18 + 6 + 6 = 30 > 28`
        obtain ⟨u₀, hu₀ne, hu₀4⟩ := h2nd
        apply containsC4_of_card_choose_two_lt
        rw [Fintype.card_fin]
        have hsplit := Finset.sum_erase_add univ
          (fun v => (G.degree v).choose 2) (Finset.mem_univ v₀)
        have hu₀mem : u₀ ∈ (univ : Finset (Fin 8)).erase v₀ :=
          Finset.mem_erase.mpr ⟨hu₀ne, Finset.mem_univ u₀⟩
        have hsplit2 := Finset.sum_erase_add ((univ : Finset (Fin 8)).erase v₀)
          (fun v => (G.degree v).choose 2) hu₀mem
        have h6 : (((univ : Finset (Fin 8)).erase v₀).erase u₀).card = 6 := by
          rw [Finset.card_erase_of_mem hu₀mem,
            Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ,
            Fintype.card_fin]
        have hr := hrest (((univ : Finset (Fin 8)).erase v₀).erase u₀) (fun v _ => hdeg v)
        rw [h6] at hr
        have hb1 : 6 ≤ (G.degree v₀).choose 2 :=
          le_trans (by decide : (6 : ℕ) ≤ Nat.choose 4 2) (Nat.choose_le_choose 2 hv₀4)
        have hb2 : 6 ≤ (G.degree u₀).choose 2 :=
          le_trans (by decide : (6 : ℕ) ≤ Nat.choose 4 2) (Nat.choose_le_choose 2 hu₀4)
        omega
      · -- exactly one vertex of degree `4`: degree sum `25` is odd — handshake kills it
        exfalso
        push Not at h2nd
        have hall : ∀ u ∈ (univ : Finset (Fin 8)).erase v₀, G.degree u = 3 := by
          intro u hu
          have hne := (Finset.mem_erase.mp hu).1
          have h4 := h2nd u hne
          have := hdeg u
          omega
        have hsplit := Finset.sum_erase_add univ (fun v => G.degree v)
          (Finset.mem_univ v₀)
        have hconst : ∑ u ∈ (univ : Finset (Fin 8)).erase v₀, G.degree u = 21 := by
          rw [Finset.sum_congr rfl hall, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
        have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges G
        omega

/-- **A fifth exact value: `f(8) = 3`.**  Lower half: the `8`-cycle is `C₄`-free with
minimum degree `2` (`three_le_minDegreeForC4`).  Upper half:
`containsC4_of_eight_min_degree_three` — the first exact value past the plain-counting
threshold at even order, obtained without any `ex(n; C₄)` extremal-table input.  The
exact-value table now reads `f = 1, 2, 3, 2, 3, 3, 3, 3` for `n = 1, …, 8`. -/
theorem minDegreeForC4_eight : minDegreeForC4 8 = 3 := by
  have hle : minDegreeForC4 8 ≤ 3 := by
    apply Nat.sInf_le
    intro G _ hmin
    exact containsC4_of_eight_min_degree_three G hmin
  have hge : 3 ≤ minDegreeForC4 8 := three_le_minDegreeForC4 (by norm_num)
  omega

/- ## Toward `f(9)`: the pigeonhole `C₄` engine

The remaining open exact value below the Petersen threshold is `f(9)`.  The two
lemmas below supply the *counting engine* for the planned elementary proof of
`f(9) = 3` (no `ex(n; C₄)` extremal-table input), whose blueprint is:

1. `δ ≥ 3`, `C₄`-free on `9` vertices bounds the cherry count
   `Σᵥ C(d(v), 2) ≤ C(9,2) = 36`, and handshake parity forces the degree
   sequence to be `(3⁸, 4)` or `(3⁶, 4³)` — a vertex of degree `≥ 6` gives
   `15 + 24 > 36`, and degree `5` forces (parity) a second vertex of degree
   `≥ 4`, giving `10 + 6 + 21 > 36`.
2. **`(3⁶, 4³)` dies by pigeonhole**: the tight cherry count `36 = C(9,2)`
   makes every pair have *exactly* one common neighbour, so counting paths of
   length `2` out of any vertex `v` gives `Σ_{u ∈ N(v)} (d(u) − 1) = 8`; for a
   degree-`4` vertex all four neighbour degrees are then forced to `3`, so the
   three degree-`4` vertices are pairwise non-adjacent with neighbourhoods
   inside the six degree-`3` vertices — and `4 + 4 = 6 + 2` triggers
   `containsC4_of_degree_sum_subset` below.
3. **`(3⁸, 4)` dies locally at the degree-`4` vertex `w`**: each of the four
   remaining vertices (`R = V ∖ ({w} ∪ N(w))`) is adjacent to at most one
   member of `N(w)` (two would be a second common neighbour with `w`), so `R`'s
   internal edge count is at least `(12 − 4)/2 = 4`; a `C₄`-free graph on `4`
   vertices has at most `4` edges, with the unique extremal graph the *paw*
   (triangle plus pendant) — whose pendant then has total degree at most `2`,
   contradicting `δ ≥ 3`.

Steps 1–3 are recorded here as the working plan; only the engine is formalized
in this file so far. -/

/-- **Pigeonhole `C₄` engine (subset form).**  If two distinct vertices have
their neighbourhoods inside a common vertex set `S` and their degrees sum to at
least `|S| + 2`, the neighbourhoods share two distinct vertices — a `C₄`.  The
`f(9)` programme applies this with `S` the six degree-`3` vertices of a
hypothetical `(3⁶, 4³)` graph and `u, v` two of its degree-`4` vertices:
`4 + 4 = 6 + 2`. -/
theorem containsC4_of_degree_sum_subset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} {S : Finset V}
    (huv : u ≠ v) (hu : G.neighborFinset u ⊆ S) (hv : G.neighborFinset v ⊆ S)
    (hsum : S.card + 2 ≤ G.degree u + G.degree v) :
    containsC4 V G := by
  have hunion : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ S.card :=
    Finset.card_le_card (Finset.union_subset hu hv)
  have hcards := Finset.card_union_add_card_inter
    (G.neighborFinset u) (G.neighborFinset v)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hcards
  have hinter : 1 < (G.neighborFinset u ∩ G.neighborFinset v).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hinter
  rw [Finset.mem_inter] at hx hy
  exact containsC4_of_two_common huv hxy
    ((G.mem_neighborFinset u x).mp hx.1).symm
    ((G.mem_neighborFinset v x).mp hx.2).symm
    ((G.mem_neighborFinset u y).mp hy.1).symm
    ((G.mem_neighborFinset v y).mp hy.2).symm

/-- **Pigeonhole `C₄` engine (global form).**  Two distinct vertices whose
degrees sum to at least `|V| + 2` force a `C₄`.  (Immediate from the subset
form with `S = univ`.)  E.g. on `9` vertices any two vertices of degree `≥ 6`,
or degrees `7 + 4`, already force a `C₄` — a cheap complement to the cherry
count. -/
theorem containsC4_of_card_add_two_le_degree_add_degree {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (huv : u ≠ v) (hsum : Fintype.card V + 2 ≤ G.degree u + G.degree v) :
    containsC4 V G :=
  containsC4_of_degree_sum_subset huv (Finset.subset_univ _) (Finset.subset_univ _)
    (by rwa [Finset.card_univ])

/-- **Common-neighbour bound.**  In a `C₄`-free graph any two distinct vertices
have at most one common neighbour (two would form the rim of a `C₄`).  The
contrapositive workhorse for the local analyses of the `f(9)` programme. -/
theorem card_inter_neighborFinset_le_one {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hfree : ¬ containsC4 V G)
    {u v : V} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_inter] at hx hy
  exact hfree (containsC4_of_two_common huv hxy
    ((G.mem_neighborFinset u x).mp hx.1).symm
    ((G.mem_neighborFinset v x).mp hx.2).symm
    ((G.mem_neighborFinset u y).mp hy.1).symm
    ((G.mem_neighborFinset v y).mp hy.2).symm)

/-- **A dense `4`-set forces a `C₄`.**  If a `4`-element vertex set `R` has every
member adjacent to at least two others inside `R`, the graph contains a `C₄`.
This is the endgame of the `(3⁸, 4)` case of the `f(9)` programme: there the
four vertices outside the closed neighbourhood of the degree-`4` vertex each
keep at least two of their three edges inside `R`.  Pure case analysis: pick
`a ∈ R` with internal neighbours `y ≠ z`, let `t` be the fourth vertex; `t` has
two internal neighbours among `{a, y, z}`, and every configuration produces two
distinct vertices with two distinct common neighbours. -/
theorem containsC4_of_four_set_min_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {R : Finset V}
    (hR : R.card = 4) (hdeg : ∀ x ∈ R, 2 ≤ (G.neighborFinset x ∩ R).card) :
    containsC4 V G := by
  by_contra hfree
  -- pick `a ∈ R` and two distinct internal neighbours `y, z`
  have hane : R.Nonempty := by rw [← Finset.card_pos, hR]; norm_num
  obtain ⟨a, ha⟩ := hane
  have h2a := hdeg a ha
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset a ∩ R).card)
  rw [Finset.mem_inter] at hy hz
  have hay : G.Adj a y := (G.mem_neighborFinset a y).mp hy.1
  have haz : G.Adj a z := (G.mem_neighborFinset a z).mp hz.1
  have hyR : y ∈ R := hy.2
  have hzR : z ∈ R := hz.2
  -- the fourth vertex `t`
  have htne : (R \ {a, y, z}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.card_insert_le a ({y, z} : Finset V)
    have h2 := Finset.card_insert_le y ({z} : Finset V)
    have hsd := Finset.le_card_sdiff ({a, y, z} : Finset V) R
    simp only [Finset.card_singleton] at h1 h2
    omega
  obtain ⟨t, ht⟩ := htne
  rw [Finset.mem_sdiff] at ht
  obtain ⟨htR, htn⟩ := ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htn
  obtain ⟨hta, hty, htz⟩ := htn
  have hya : y ≠ a := (G.ne_of_adj hay).symm
  have hza : z ≠ a := (G.ne_of_adj haz).symm
  -- `R = {a, y, z, t}`
  have hna : a ∉ ({y, z, t} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    exacts [hya rfl, hza rfl, hta rfl]
  have hny : y ∉ ({z, t} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    exacts [hyz rfl, hty rfl]
  have hnz : z ∉ ({t} : Finset V) := by
    rw [Finset.mem_singleton]
    intro h
    exact htz h.symm
  have hsub : ({a, y, z, t} : Finset V) ⊆ R := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [ha, hyR, hzR, htR]
  have hcard4 : ({a, y, z, t} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem hna, Finset.card_insert_of_notMem hny,
      Finset.card_insert_of_notMem hnz, Finset.card_singleton]
  have hReq : R = ({a, y, z, t} : Finset V) :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  -- internal neighbours of any `x` decompose over `R`'s four elements
  have hmemR : ∀ x w, w ∈ G.neighborFinset x ∩ R →
      G.Adj x w ∧ (w = a ∨ w = y ∨ w = z ∨ w = t) := by
    intro x w hw
    rw [Finset.mem_inter] at hw
    refine ⟨(G.mem_neighborFinset x w).mp hw.1, ?_⟩
    have hwR := hw.2
    rw [hReq] at hwR
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hwR
  -- helper: `t ~ y` and `t ~ z` ⟹ pair `(a, t)` has commons `y, z`
  have case_yz : G.Adj t y → G.Adj t z → False := fun h1 h2 =>
    hfree (containsC4_of_two_common (show a ≠ t from fun h => hta h.symm) hyz
      hay.symm h1.symm haz.symm h2.symm)
  -- helper: `t ~ a` and `t ~ y` ⟹ `z`'s second internal neighbour closes a `C₄`
  have case_ay : G.Adj t a → G.Adj t y → False := by
    intro h1 h2
    have h2z := hdeg z hzR
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset z ∩ R).card)
    obtain ⟨hzp, hpor⟩ := hmemR z p hp
    obtain ⟨hzq, hqor⟩ := hmemR z q hq
    have key : G.Adj z y ∨ G.Adj z t := by
      rcases hpor with rfl | rfl | rfl | rfl
      · rcases hqor with rfl | rfl | rfl | rfl
        · exact absurd rfl hpq
        · exact Or.inl hzq
        · exact absurd rfl (G.ne_of_adj hzq)
        · exact Or.inr hzq
      · exact Or.inl hzp
      · exact absurd rfl (G.ne_of_adj hzp)
      · exact Or.inr hzp
    rcases key with hzy | hzt
    · -- pair `(y, a)` has commons `z, t`
      exact hfree (containsC4_of_two_common hya
        (show z ≠ t from fun h => htz h.symm) hzy haz.symm h2 h1)
    · exact case_yz h2 hzt.symm
  -- helper: `t ~ a` and `t ~ z` ⟹ `y`'s second internal neighbour closes a `C₄`
  have case_az : G.Adj t a → G.Adj t z → False := by
    intro h1 h2
    have h2y := hdeg y hyR
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset y ∩ R).card)
    obtain ⟨hyp, hpor⟩ := hmemR y p hp
    obtain ⟨hyq, hqor⟩ := hmemR y q hq
    have key : G.Adj y z ∨ G.Adj y t := by
      rcases hpor with rfl | rfl | rfl | rfl
      · rcases hqor with rfl | rfl | rfl | rfl
        · exact absurd rfl hpq
        · exact absurd rfl (G.ne_of_adj hyq)
        · exact Or.inl hyq
        · exact Or.inr hyq
      · exact absurd rfl (G.ne_of_adj hyp)
      · exact Or.inl hyp
      · exact Or.inr hyp
    rcases key with hyz2 | hyt
    · -- pair `(z, a)` has commons `y, t`
      exact hfree (containsC4_of_two_common hza
        (show y ≠ t from fun h => hty h.symm) hyz2 hay.symm h2 h1)
    · exact case_yz hyt.symm h2
  -- main dispatch: `t`'s two internal neighbours among `{a, y, z}`
  have h2t := hdeg t htR
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset t ∩ R).card)
  obtain ⟨htp, hpor⟩ := hmemR t p hp
  obtain ⟨htq, hqor⟩ := hmemR t q hq
  rcases hpor with rfl | rfl | rfl | rfl
  · rcases hqor with rfl | rfl | rfl | rfl
    · exact absurd rfl hpq
    · exact case_ay htp htq
    · exact case_az htp htq
    · exact (G.ne_of_adj htq) rfl
  · rcases hqor with rfl | rfl | rfl | rfl
    · exact case_ay htq htp
    · exact absurd rfl hpq
    · exact case_yz htp htq
    · exact (G.ne_of_adj htq) rfl
  · rcases hqor with rfl | rfl | rfl | rfl
    · exact case_az htq htp
    · exact case_yz htq htp
    · exact absurd rfl hpq
    · exact (G.ne_of_adj htq) rfl
  · exact (G.ne_of_adj htp) rfl

/-- **The `(3⁸, 4)` case of `f(9)`: a unique degree-`4` vertex forces a `C₄`.**
On `9` vertices with `δ ≥ 3`, if exactly one vertex `w` has degree `4` and the
rest have degree `3`, the four vertices `R` outside `w`'s closed neighbourhood
each keep at least two of their three edges inside `R` (they are non-adjacent
to `w` and share at most one neighbour with it), so the dense-`4`-set lemma
applies. -/
theorem containsC4_of_nine_one_four {G : SimpleGraph (Fin 9)}
    [DecidableRel G.Adj] (w : Fin 9) (hw : G.degree w = 4)
    (hrest : ∀ v, v ≠ w → G.degree v = 3) :
    containsC4 (Fin 9) G := by
  by_contra hfree
  have hwn : w ∉ G.neighborFinset w :=
    fun h => G.irrefl ((G.mem_neighborFinset w w).mp h)
  set B : Finset (Fin 9) := insert w (G.neighborFinset w) with hB
  have hBcard : B.card = 5 := by
    rw [hB, Finset.card_insert_of_notMem hwn, G.card_neighborFinset_eq_degree, hw]
  set R : Finset (Fin 9) := Finset.univ \ B with hRdef
  have hRcard : R.card = 4 := by
    rw [hRdef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, hBcard]
  refine hfree (containsC4_of_four_set_min_two hRcard ?_)
  intro x hx
  rw [hRdef, Finset.mem_sdiff] at hx
  have hxB := hx.2
  rw [hB, Finset.mem_insert, not_or] at hxB
  obtain ⟨hxw, hxN⟩ := hxB
  have hnadj : ¬ G.Adj w x := fun h => hxN ((G.mem_neighborFinset w x).mpr h)
  have hwNx : w ∉ G.neighborFinset x :=
    fun h => hnadj ((G.mem_neighborFinset x w).mp h).symm
  have hdx : G.degree x = 3 := hrest x hxw
  -- `N(x) ∩ R = N(x) \ B` and `N(x) ∩ B = N(x) ∩ N(w)`
  have hinterR : G.neighborFinset x ∩ R = G.neighborFinset x \ B := by
    rw [hRdef]
    ext u
    simp [Finset.mem_sdiff]
  have hinterB : G.neighborFinset x ∩ B = G.neighborFinset x ∩ G.neighborFinset w := by
    rw [hB]
    ext u
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hu, rfl | hu'⟩
      · exact absurd hu hwNx
      · exact ⟨hu, hu'⟩
    · rintro ⟨hu, hu'⟩
      exact ⟨hu, Or.inr hu'⟩
  have hcomm : (G.neighborFinset x ∩ G.neighborFinset w).card ≤ 1 :=
    card_inter_neighborFinset_le_one hfree hxw
  have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset x) B
  have hxcard : (G.neighborFinset x).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hdx]
  rw [hinterB] at hsplit
  rw [hinterR]
  omega

end Erdos85

#print axioms Erdos85.containsC4_of_nine_one_four
