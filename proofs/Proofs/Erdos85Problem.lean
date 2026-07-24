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
import Archive.Wiedijk100Theorems.FriendshipGraphs

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

/-- **Degree pinch for `f(9)`.**  On `9` vertices, `C₄`-free with `δ ≥ 3`, every
degree is `3` or `4` and the number `k` of degree-`4` vertices is `1` or `3`.
Cherry counting (`Σᵥ C(d(v),2) ≤ C(9,2) = 36`): degree `≥ 6` alone gives
`15 + 8·3 = 39 > 36`; degree `5` forces by handshake parity a second vertex of
degree `≥ 4`, giving `10 + 6 + 7·3 = 37 > 36`.  Then `Σ d(v) = 27 + k` must be
even (`k` odd) and `Σ C(d(v),2) = 27 + 3k ≤ 36` (`k ≤ 3`). -/
theorem nine_degree_pinch {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 9) G) (hmin : ∀ v, 3 ≤ G.degree v) :
    (∀ v, G.degree v ≤ 4) ∧
      ((Finset.univ.filter (fun v => G.degree v = 4)).card = 1 ∨
       (Finset.univ.filter (fun v => G.degree v = 4)).card = 3) := by
  -- cherry bound
  have hcherry : ∑ v : Fin 9, (G.degree v).choose 2 ≤ 36 := by
    by_contra h
    rw [not_le] at h
    refine hfree (containsC4_of_card_choose_two_lt G ?_)
    rw [Fintype.card_fin]
    have h92 : Nat.choose 9 2 = 36 := by decide
    omega
  -- generic single-vertex split: `Σ ≥ C(d(v),2) + 3·8`
  have hsplit1 : ∀ v : Fin 9,
      (G.degree v).choose 2 + 24 ≤ ∑ u : Fin 9, (G.degree u).choose 2 := by
    intro v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have h24 : 24 ≤ ∑ u ∈ Finset.univ.erase v, (G.degree u).choose 2 := by
      calc (24 : ℕ) = (Finset.univ.erase v).card * 3 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
              Fintype.card_fin]
        _ = ∑ _u ∈ Finset.univ.erase v, 3 := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ u ∈ Finset.univ.erase v, (G.degree u).choose 2 :=
            Finset.sum_le_sum (fun u _ => Nat.choose_le_choose 2 (hmin u))
    omega
  -- no vertex of degree ≥ 6
  have hle5 : ∀ v, G.degree v ≤ 5 := by
    intro v
    by_contra h
    rw [not_le] at h
    have h15 : 15 ≤ (G.degree v).choose 2 :=
      le_trans (by decide : 15 ≤ Nat.choose 6 2) (Nat.choose_le_choose 2 h)
    have := hsplit1 v
    omega
  -- handshake
  have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges G
  -- no vertex of degree exactly 5
  have hle4 : ∀ v, G.degree v ≤ 4 := by
    intro v
    by_contra h
    rw [not_le] at h
    have hd5 : G.degree v = 5 := le_antisymm (hle5 v) h
    -- a second vertex of degree ≥ 4 must exist, else the degree sum is odd
    have hsecond : ∃ u, u ≠ v ∧ 4 ≤ G.degree u := by
      by_contra hno
      push Not at hno
      have hall3 : ∀ u ∈ Finset.univ.erase v, G.degree u = 3 := by
        intro u hu
        have hne := (Finset.mem_erase.mp hu).1
        have := hno u hne
        have := hmin u
        omega
      have hsum : ∑ u : Fin 9, G.degree u = 29 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), hd5,
          Finset.sum_congr rfl hall3, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      omega
    obtain ⟨u, huv, hu4⟩ := hsecond
    -- `Σ ≥ C(5,2) + C(4,2) + 7·3 = 37 > 36`
    have hu6 : 6 ≤ (G.degree u).choose 2 :=
      le_trans (by decide : 6 ≤ Nat.choose 4 2) (Nat.choose_le_choose 2 hu4)
    have hv10 : 10 ≤ (G.degree v).choose 2 := by rw [hd5]; decide
    have hu_mem : u ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩
    have hsum2 : (G.degree v).choose 2 + ((G.degree u).choose 2 + 21)
        ≤ ∑ x : Fin 9, (G.degree x).choose 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
        ← Finset.add_sum_erase _ _ hu_mem]
      have h21 : 21 ≤ ∑ x ∈ (Finset.univ.erase v).erase u, (G.degree x).choose 2 := by
        calc (21 : ℕ) = ((Finset.univ.erase v).erase u).card * 3 := by
              rw [Finset.card_erase_of_mem hu_mem,
                Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
                Fintype.card_fin]
          _ = ∑ _x ∈ (Finset.univ.erase v).erase u, 3 := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ x ∈ (Finset.univ.erase v).erase u, (G.degree x).choose 2 :=
              Finset.sum_le_sum (fun x _ => Nat.choose_le_choose 2 (hmin x))
      omega
    omega
  refine ⟨hle4, ?_⟩
  -- degree sum and cherry sum in terms of `k`
  set k := (Finset.univ.filter (fun v => G.degree v = 4)).card with hk
  have hcompl : (Finset.univ.filter (fun v => ¬ G.degree v = 4)).card = 9 - k := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 9))) (p := fun v => G.degree v = 4)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hdsum : ∑ v : Fin 9, G.degree v = 4 * k + 3 * (9 - k) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => G.degree v = 4)]
    have h4 : ∑ v ∈ Finset.univ.filter (fun v => G.degree v = 4), G.degree v = 4 * k := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2),
        Finset.sum_const, smul_eq_mul, mul_comm]
    have h3 : ∑ v ∈ Finset.univ.filter (fun v => ¬ G.degree v = 4), G.degree v
        = 3 * (9 - k) := by
      have hall : ∀ v ∈ Finset.univ.filter (fun v => ¬ G.degree v = 4),
          G.degree v = 3 := by
        intro v hv
        have h1 := (Finset.mem_filter.mp hv).2
        have h2 := hmin v
        have h3 := hle4 v
        omega
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, hcompl, mul_comm]
    omega
  have hcsum : ∑ v : Fin 9, (G.degree v).choose 2 = 6 * k + 3 * (9 - k) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => G.degree v = 4)]
    have h4 : ∑ v ∈ Finset.univ.filter (fun v => G.degree v = 4),
        (G.degree v).choose 2 = 6 * k := by
      have hall : ∀ v ∈ Finset.univ.filter (fun v => G.degree v = 4),
          (G.degree v).choose 2 = 6 := by
        intro v hv
        rw [(Finset.mem_filter.mp hv).2]
        decide
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_comm]
    have h3 : ∑ v ∈ Finset.univ.filter (fun v => ¬ G.degree v = 4),
        (G.degree v).choose 2 = 3 * (9 - k) := by
      have hall : ∀ v ∈ Finset.univ.filter (fun v => ¬ G.degree v = 4),
          (G.degree v).choose 2 = 3 := by
        intro v hv
        have h1 := (Finset.mem_filter.mp hv).2
        have h2 := hmin v
        have h3 := hle4 v
        have : G.degree v = 3 := by omega
        rw [this]
        decide
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, hcompl, mul_comm]
    omega
  -- `27 + k` even and `27 + 3k ≤ 36` pin `k ∈ {1, 3}`
  have hk9 : k ≤ 9 := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin 9))
      (fun v => G.degree v = 4)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  rw [hdsum] at hhs
  rw [hcsum] at hcherry
  omega

/-- **The `(3⁶, 4³)` case of `f(9)`: three degree-`4` vertices force a `C₄`.**
With exactly three degree-`4` vertices the cherry count is *exactly*
`36 = C(9,2)`, so the cherry → endpoint-pair map is a bijection and every pair
of vertices has exactly one common neighbour.  Counting paths of length two out
of a degree-`4` vertex `w` then gives `Σ_{u ∈ N(w)} (d(u) − 1) = 8`, forcing
all four neighbour degrees to `3`.  Hence the degree-`4` vertices have their
neighbourhoods inside the six degree-`3` vertices, and `4 + 4 = 6 + 2` fires
the pigeonhole engine. -/
theorem containsC4_of_nine_three_fours {G : SimpleGraph (Fin 9)}
    [DecidableRel G.Adj] (hmin : ∀ v, 3 ≤ G.degree v)
    (hle4 : ∀ v, G.degree v ≤ 4)
    (hk3 : (Finset.univ.filter (fun v => G.degree v = 4)).card = 3) :
    containsC4 (Fin 9) G := by
  by_contra hfree
  classical
  -- the complementary count: six degree-3 vertices
  have hcompl : (Finset.univ.filter (fun v => ¬ G.degree v = 4)).card = 6 := by
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 9))) (p := fun v => G.degree v = 4)
    rw [Finset.card_univ, Fintype.card_fin, hk3] at this
    omega
  -- exact cherry count 36
  have hcsum : ∑ v : Fin 9, (G.degree v).choose 2 = 36 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => G.degree v = 4)]
    have h4 : ∑ v ∈ Finset.univ.filter (fun v => G.degree v = 4),
        (G.degree v).choose 2 = 18 := by
      have hall : ∀ v ∈ Finset.univ.filter (fun v => G.degree v = 4),
          (G.degree v).choose 2 = 6 := by
        intro v hv
        rw [(Finset.mem_filter.mp hv).2]
        decide
      rw [Finset.sum_congr rfl hall, Finset.sum_const, hk3, smul_eq_mul]
    have h3 : ∑ v ∈ Finset.univ.filter (fun v => ¬ G.degree v = 4),
        (G.degree v).choose 2 = 18 := by
      have hall : ∀ v ∈ Finset.univ.filter (fun v => ¬ G.degree v = 4),
          (G.degree v).choose 2 = 3 := by
        intro v hv
        have h1 := (Finset.mem_filter.mp hv).2
        have h2 := hmin v
        have h3 := hle4 v
        have hd : G.degree v = 3 := by omega
        rw [hd]
        decide
      rw [Finset.sum_congr rfl hall, Finset.sum_const, hcompl, smul_eq_mul]
    omega
  -- tight cherry count ⟹ every pair has a common neighbour
  have hcommon : ∀ x y : Fin 9, x ≠ y → ∃ v, G.Adj v x ∧ G.Adj v y := by
    intro x y hxy
    set C : Finset (Σ _ : Fin 9, Finset (Fin 9)) :=
      Finset.univ.sigma (fun v => (G.neighborFinset v).powersetCard 2) with hC
    have hCcard : C.card = 36 := by
      rw [hC, Finset.card_sigma]
      calc ∑ v : Fin 9, ((G.neighborFinset v).powersetCard 2).card
          = ∑ v : Fin 9, (G.degree v).choose 2 :=
            Finset.sum_congr rfl (fun v _ => by
              rw [Finset.card_powersetCard, G.card_neighborFinset_eq_degree])
        _ = 36 := hcsum
    set T : Finset (Finset (Fin 9)) :=
      (Finset.univ : Finset (Fin 9)).powersetCard 2 with hT
    have hTcard : T.card = 36 := by
      rw [hT, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      decide
    have hmaps : ∀ p ∈ C, p.2 ∈ T := by
      intro p hp
      rw [hC, Finset.mem_sigma] at hp
      rw [hT, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hp.2).2⟩
    have hinj : Set.InjOn (fun p : Σ _ : Fin 9, Finset (Fin 9) => p.2) ↑C := by
      intro p hp q hq h
      obtain ⟨v, e⟩ := p
      obtain ⟨v', e'⟩ := q
      simp only at h
      subst h
      by_cases hv : v = v'
      · subst hv; rfl
      · exfalso
        rw [Finset.mem_coe, hC, Finset.mem_sigma] at hp hq
        obtain ⟨hsubv, hecard⟩ := Finset.mem_powersetCard.mp hp.2
        obtain ⟨hsubv', -⟩ := Finset.mem_powersetCard.mp hq.2
        obtain ⟨x', y', hxy', rfl⟩ := Finset.card_eq_two.mp hecard
        have hvx : G.Adj v x' := (G.mem_neighborFinset v x').mp (hsubv (by simp))
        have hvy : G.Adj v y' := (G.mem_neighborFinset v y').mp (hsubv (by simp))
        have hv'x : G.Adj v' x' := (G.mem_neighborFinset v' x').mp (hsubv' (by simp))
        have hv'y : G.Adj v' y' := (G.mem_neighborFinset v' y').mp (hsubv' (by simp))
        exact hfree (containsC4_of_two_common hv hxy' hvx.symm hv'x.symm hvy.symm hv'y.symm)
    have himg : C.image (fun p => p.2) = T := by
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
        exact hmaps p hp
      · rw [Finset.card_image_of_injOn hinj, hCcard, hTcard]
    have hxyT : ({x, y} : Finset (Fin 9)) ∈ T := by
      rw [hT, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
    rw [← himg] at hxyT
    obtain ⟨⟨v, e⟩, hpC, he⟩ := Finset.mem_image.mp hxyT
    simp only at he
    subst he
    rw [hC, Finset.mem_sigma] at hpC
    obtain ⟨hsubv, -⟩ := Finset.mem_powersetCard.mp hpC.2
    exact ⟨v, (G.mem_neighborFinset v x).mp (hsubv (by simp)),
      (G.mem_neighborFinset v y).mp (hsubv (by simp))⟩
  -- path count: the neighbours of a degree-4 vertex all have degree 3
  have hnbr3 : ∀ w, G.degree w = 4 → ∀ u ∈ G.neighborFinset w, G.degree u = 3 := by
    intro w hw4
    have hNcard : (G.neighborFinset w).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hw4]
    have hwmem : ∀ u ∈ G.neighborFinset w, w ∈ G.neighborFinset u := by
      intro u hu
      exact (G.mem_neighborFinset u w).mpr ((G.mem_neighborFinset w u).mp hu).symm
    -- each `x ≠ w` has exactly one common neighbour with `w`
    have hone : ∀ x ∈ Finset.univ.erase w,
        (G.neighborFinset x ∩ G.neighborFinset w).card = 1 := by
      intro x hx
      have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
      refine le_antisymm (card_inter_neighborFinset_le_one hfree hxw)
        (Finset.card_pos.mpr ?_)
      obtain ⟨v, hvx, hvw⟩ := hcommon x w hxw
      exact ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x v).mpr hvx.symm,
        (G.mem_neighborFinset w v).mpr hvw.symm⟩⟩
    -- double count `Σ_{u ∈ N(w)} (d(u) − 1) = 8`
    have hcount : ∑ u ∈ G.neighborFinset w, ((G.neighborFinset u).erase w).card = 8 := by
      have hstep : ∀ x ∈ Finset.univ.erase w,
          (G.neighborFinset x ∩ G.neighborFinset w).card
            = ∑ u ∈ G.neighborFinset w, if G.Adj x u then 1 else 0 := by
        intro x _
        have hset : G.neighborFinset x ∩ G.neighborFinset w
            = (G.neighborFinset w).filter (fun u => G.Adj x u) := by
          ext u
          simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          tauto
        rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
      have hL : (8 : ℕ) = ∑ x ∈ Finset.univ.erase w,
          (G.neighborFinset x ∩ G.neighborFinset w).card := by
        rw [Finset.sum_congr rfl hone, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      rw [Finset.sum_congr rfl hstep, Finset.sum_comm] at hL
      have hinner : ∀ u ∈ G.neighborFinset w,
          (∑ x ∈ Finset.univ.erase w, if G.Adj x u then 1 else 0)
            = ((G.neighborFinset u).erase w).card := by
        intro u hu
        have hset : (Finset.univ.erase w).filter (fun x => G.Adj x u)
            = (G.neighborFinset u).erase w := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
            and_true, SimpleGraph.mem_neighborFinset]
          rw [SimpleGraph.adj_comm]
        rw [← hset, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_congr rfl hinner] at hL
      omega
    -- extract: four terms, each ≥ 2, summing to 8 ⟹ all equal 2
    intro u hu
    by_contra hne
    have hu4 : G.degree u = 4 := by
      have h1 := hmin u
      have h2 := hle4 u
      omega
    have huterm : ((G.neighborFinset u).erase w).card = 3 := by
      rw [Finset.card_erase_of_mem (hwmem u hu), G.card_neighborFinset_eq_degree, hu4]
    have hrest2 : ∀ x ∈ (G.neighborFinset w).erase u,
        2 ≤ ((G.neighborFinset x).erase w).card := by
      intro x hx
      have hxN := (Finset.mem_erase.mp hx).2
      rw [Finset.card_erase_of_mem (hwmem x hxN), G.card_neighborFinset_eq_degree]
      have := hmin x
      omega
    have hsplit := Finset.add_sum_erase (G.neighborFinset w)
      (fun x => ((G.neighborFinset x).erase w).card) hu
    have hge : 6 ≤ ∑ x ∈ (G.neighborFinset w).erase u,
        ((G.neighborFinset x).erase w).card := by
      calc (6 : ℕ) = ((G.neighborFinset w).erase u).card * 2 := by
            rw [Finset.card_erase_of_mem hu, hNcard]
        _ = ∑ _x ∈ (G.neighborFinset w).erase u, 2 := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ (G.neighborFinset w).erase u,
              ((G.neighborFinset x).erase w).card :=
            Finset.sum_le_sum hrest2
    omega
  -- assembly: two degree-4 vertices with neighbourhoods inside the six
  -- degree-3 vertices
  have h2 : 1 < (Finset.univ.filter (fun v => G.degree v = 4)).card := by
    rw [hk3]; norm_num
  obtain ⟨w1, hw1, w2, hw2, hww⟩ := Finset.one_lt_card.mp h2
  have hw1d := (Finset.mem_filter.mp hw1).2
  have hw2d := (Finset.mem_filter.mp hw2).2
  set V3 : Finset (Fin 9) := Finset.univ.filter (fun v => G.degree v = 3) with hV3
  have hV3card : V3.card = 6 := by
    have heq : Finset.univ.filter (fun v => ¬ G.degree v = 4) = V3 := by
      rw [hV3]
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hmin v
      have h2 := hle4 v
      omega
    rw [← heq]
    exact hcompl
  have hsub1 : G.neighborFinset w1 ⊆ V3 := by
    intro u hu
    rw [hV3, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hnbr3 w1 hw1d u hu⟩
  have hsub2 : G.neighborFinset w2 ⊆ V3 := by
    intro u hu
    rw [hV3, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hnbr3 w2 hw2d u hu⟩
  exact hfree (containsC4_of_degree_sum_subset hww hsub1 hsub2
    (by rw [hV3card, hw1d, hw2d]))

/-- **`f(9)` upper half: minimum degree `3` on `9` vertices forces a `C₄`.**
The degree pinch (`nine_degree_pinch`) leaves the degree sequences `(3⁸, 4)` and
`(3⁶, 4³)`; the former dies locally (`containsC4_of_nine_one_four`), the latter
by the tight-cherry pigeonhole (`containsC4_of_nine_three_fours`). -/
theorem containsC4_of_nine_min_degree_three (G : SimpleGraph (Fin 9))
    [DecidableRel G.Adj] (hmin : 3 ≤ G.minDegree) : containsC4 (Fin 9) G := by
  have hdeg : ∀ v : Fin 9, 3 ≤ G.degree v :=
    fun v => le_trans hmin (G.minDegree_le_degree v)
  by_contra hfree
  obtain ⟨hle4, hk⟩ := nine_degree_pinch hfree hdeg
  rcases hk with hk1 | hk3
  · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hk1
    have hwd : G.degree w = 4 := by
      have hmem : w ∈ Finset.univ.filter (fun v => G.degree v = 4) := by
        rw [hw]
        exact Finset.mem_singleton_self w
      exact (Finset.mem_filter.mp hmem).2
    have hrest : ∀ v, v ≠ w → G.degree v = 3 := by
      intro v hv
      have hnot : v ∉ Finset.univ.filter (fun u => G.degree u = 4) := by
        rw [hw, Finset.mem_singleton]
        exact hv
      have h4 : ¬ G.degree v = 4 :=
        fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
      have h1 := hdeg v
      have h2 := hle4 v
      omega
    exact hfree (containsC4_of_nine_one_four w hwd hrest)
  · exact hfree (containsC4_of_nine_three_fours hdeg hle4 hk3)

/-- **A sixth exact value: `f(9) = 3`.**  Lower half: the `9`-cycle is `C₄`-free
with minimum degree `2` (`three_le_minDegreeForC4`).  Upper half:
`containsC4_of_nine_min_degree_three` — obtained *without* any `ex(n; C₄)`
extremal-table input, overturning the recorded blocker for `f(9)`.  The
exact-value table now reads `f = 1, 2, 3, 2, 3, 3, 3, 3, 3` for `n = 1, …, 9`;
the next value, `f(10) = 4`, is the Petersen threshold. -/
theorem minDegreeForC4_nine : minDegreeForC4 9 = 3 := by
  have hle : minDegreeForC4 9 ≤ 3 := by
    apply Nat.sInf_le
    intro G _ hmin
    exact containsC4_of_nine_min_degree_three G hmin
  have hge : 3 ≤ minDegreeForC4 9 := three_le_minDegreeForC4 (by norm_num)
  omega

/-! ## `f(10) = 4`: the Petersen graph, decide-free at the global level

The lower half `f(10) ≥ 4` needs a `C₄`-free graph of minimum degree `3` on ten
vertices — the Petersen graph, and by the Moore bound nothing smaller works.
The route recorded as blocked ("kernel `decide` over the `10⁴` injective maps")
is avoided entirely: `containsC4` is *extracted* to a pair of vertices with two
distinct common neighbours (`exists_two_common_of_containsC4`), so `C₄`-freeness
reduces to the `10 × 10` common-neighbour matrix — a tiny kernel check — via
`not_containsC4_of_forall_common_le_one`.  The graph itself is the explicit
edge-list Petersen: outer `5`-cycle `0–4`, inner pentagram `5–9`, spokes. -/

/-- **Extracting two common neighbours from a `C₄`.**  An embedded `4`-cycle
`f` gives the opposite pair `f 0 ≠ f 2` with the two distinct common neighbours
`f 1 ≠ f 3`. -/
theorem exists_two_common_of_containsC4 {V : Type*} {G : SimpleGraph V}
    (h : containsC4 V G) :
    ∃ x y v v' : V, x ≠ y ∧ v ≠ v' ∧
      G.Adj v x ∧ G.Adj v y ∧ G.Adj v' x ∧ G.Adj v' y := by
  obtain ⟨f, hinj, hadj⟩ := h
  refine ⟨f 0, f 2, f 1, f 3, fun h => ?_, fun h => ?_, ?_, ?_, ?_, ?_⟩
  · exact absurd (hinj h) (by decide)
  · exact absurd (hinj h) (by decide)
  · exact (hadj 0 1 (by decide)).symm
  · exact hadj 1 2 (by decide)
  · exact hadj 3 0 (by decide)
  · exact (hadj 2 3 (by decide)).symm

/-- **The common-neighbour criterion for `C₄`-freeness.**  If every pair of
distinct vertices has at most one common neighbour, the graph is `C₄`-free.
Converse workhorse to `containsC4_of_two_common`; together they make
`C₄`-freeness of a concrete graph a finite check on the common-neighbour
matrix rather than an enumeration of embeddings. -/
theorem not_containsC4_of_forall_common_le_one {V : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ∀ x y : V, x ≠ y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1) :
    ¬ containsC4 V G := by
  intro hc
  obtain ⟨x, y, v, v', hxy, hvv, hvx, hvy, hv'x, hv'y⟩ :=
    exists_two_common_of_containsC4 hc
  have h2 : 1 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
    Finset.one_lt_card.mpr ⟨v,
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x v).mpr hvx.symm,
        (G.mem_neighborFinset y v).mpr hvy.symm⟩, v',
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x v').mpr hv'x.symm,
        (G.mem_neighborFinset y v').mpr hv'y.symm⟩, hvv⟩
  have := h x y hxy
  omega

/-- The fifteen edges of the Petersen graph: outer `5`-cycle `0–1–2–3–4`, inner
pentagram `5–7–9–6–8`, and the five spokes `i – i+5`. -/
def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0,1), (1,2), (2,3), (3,4), (4,0),
   (5,7), (7,9), (9,6), (6,8), (8,5),
   (0,5), (1,6), (2,7), (3,8), (4,9)]

/-- **The Petersen graph** on `Fin 10`, via its explicit edge list. -/
def petersen : SimpleGraph (Fin 10) where
  Adj i j := (i, j) ∈ petersenEdges ∨ (j, i) ∈ petersenEdges
  symm.symm := fun _ _ h => Or.symm h
  loopless.irrefl := by decide

instance : DecidableRel petersen.Adj := fun i j =>
  decidable_of_iff ((i, j) ∈ petersenEdges ∨ (j, i) ∈ petersenEdges) Iff.rfl

/-- The Petersen graph is `3`-regular — a `10`-vertex kernel check. -/
theorem petersen_degree : ∀ v, petersen.degree v = 3 := by decide

/-- **Every pair of distinct Petersen vertices has at most one common
neighbour** — the `10 × 10` kernel check that replaces the `10⁴` embedding
enumeration.  (In fact girth `5` gives exactly one for non-adjacent pairs and
zero for adjacent ones; `≤ 1` is all that is needed.) -/
theorem petersen_common_le_one : ∀ x y : Fin 10, x ≠ y →
    (petersen.neighborFinset x ∩ petersen.neighborFinset y).card ≤ 1 := by decide

/-- **The Petersen graph is `C₄`-free** — no finite embedding search needed. -/
theorem petersen_not_containsC4 : ¬ containsC4 (Fin 10) petersen :=
  not_containsC4_of_forall_common_le_one petersen_common_le_one

/-- The Petersen graph has minimum degree `3`. -/
theorem petersen_three_le_minDegree : 3 ≤ petersen.minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [petersen_degree v]

/-- **`f(10) ≥ 4`**: the Petersen graph is a `C₄`-free graph of minimum degree
`3` on ten vertices, so threshold `3` does not force a `C₄` at order `10`. -/
theorem four_le_minDegreeForC4_ten : 4 ≤ minDegreeForC4 10 := by
  have hne : {k : ℕ | ∀ (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj],
      G.minDegree ≥ k → containsC4 (Fin 10) G}.Nonempty := by
    refine ⟨9, fun G _ hmin => ?_⟩
    rw [eq_top_of_minDegree_ge G hmin]
    exact completeGraph_containsC4 (by norm_num)
  unfold minDegreeForC4
  refine le_csInf hne (fun k hk => ?_)
  by_contra hk4
  rw [not_le] at hk4
  exact petersen_not_containsC4
    (hk petersen (le_trans (by omega : k ≤ 3) petersen_three_le_minDegree))

/-- **A seventh exact value: `f(10) = 4` — the Petersen threshold.**  Upper
half: plain counting, `C(10,2) = 45 < 60 = 10·C(4,2)`.  Lower half: the
Petersen graph (`four_le_minDegreeForC4_ten`).  This resolves the route
recorded as blocked on a "decide-free formalization of the Petersen graph":
the common-neighbour extraction reduces `C₄`-freeness to a `10 × 10` kernel
check, so no embedding enumeration (and no `native_decide`) is needed.  The
exact table now reads `f = 1, 2, 3, 2, 3, 3, 3, 3, 3, 4` for `n = 1, …, 10` —
the first value where the answer exceeds `3`, witnessing the `√n` growth. -/
theorem minDegreeForC4_ten : minDegreeForC4 10 = 4 := by
  have hle : minDegreeForC4 10 ≤ 4 := minDegreeForC4_le_of_choose_lt (by decide)
  have hge := four_le_minDegreeForC4_ten
  omega

/-! ## `f(11) = f(12) = 4`: growing the Petersen witness vertex by vertex

The counting ceiling `n ≤ k(k−1)` gives `f(n) ≤ 4` exactly for `n ≤ 12`, so
orders `11` and `12` are the last two values the elementary counting bound can
pin — provided matching `C₄`-free graphs of minimum degree `3` exist there.
A `3`-*regular* such graph is impossible at order `11` (handshake parity), and
no standard `11`- or `12`-vertex analogue of the Petersen graph exists.
Instead we *grow* the Petersen graph one vertex at a time by a local surgery:

  **delete** an edge `a – b`, then **add** a new vertex `v` joined to `a`,
  `b`, and one further neighbour `c` of `b`.

Degrees survive (`a` and `b` each trade one neighbour for `v`; `c` gains one),
and the common-neighbour matrix stays `≤ 1` everywhere: within `{a, b, c}` the
pairs `(a, b)` and `(b, c)` were *adjacent* (zero common neighbours, girth
`5`), while the unique common neighbour of the non-adjacent pair `(a, c)` was
exactly `b` — which the deleted edge removes just as `v` arrives to replace
it.  And a vertex `x` outside `{a, b, c}` adjacent to two of them would have
been a *second* common neighbour of that pair beforehand — impossible.
`C₄`-freeness of each explicit graph is then the same tiny kernel check as for
the Petersen graph itself, via `not_containsC4_of_forall_common_le_one`; no
embedding enumeration and no `native_decide`. -/

/-- The seventeen edges of the `11`-vertex extended Petersen graph: the
Petersen list with the outer edge `(0, 1)` deleted and the new vertex `10`
joined to `0`, `1`, and `6` (a pentagram neighbour of `1`). -/
def petersen11Edges : List (Fin 11 × Fin 11) :=
  [(1,2), (2,3), (3,4), (4,0),
   (5,7), (7,9), (9,6), (6,8), (8,5),
   (0,5), (1,6), (2,7), (3,8), (4,9),
   (10,0), (10,1), (10,6)]

/-- **An `11`-vertex `C₄`-free graph of minimum degree `3`**: the Petersen
graph after the vertex-adding surgery.  Vertex `6` has degree `4`; all other
vertices have degree `3`. -/
def petersen11 : SimpleGraph (Fin 11) where
  Adj i j := (i, j) ∈ petersen11Edges ∨ (j, i) ∈ petersen11Edges
  symm.symm := fun _ _ h => Or.symm h
  loopless.irrefl := by decide

instance : DecidableRel petersen11.Adj := fun i j =>
  decidable_of_iff ((i, j) ∈ petersen11Edges ∨ (j, i) ∈ petersen11Edges) Iff.rfl

/-- Every vertex of `petersen11` has degree at least `3` — an `11`-vertex
kernel check.  (Vertex `6` has degree `4`, so `3`-regularity fails — as it
must at odd order — but the minimum-degree bound only needs `≥ 3`.) -/
theorem petersen11_degree : ∀ v, 3 ≤ petersen11.degree v := by decide

/-- **Every pair of distinct `petersen11` vertices has at most one common
neighbour** — the `11 × 11` kernel check certifying `C₄`-freeness. -/
theorem petersen11_common_le_one : ∀ x y : Fin 11, x ≠ y →
    (petersen11.neighborFinset x ∩ petersen11.neighborFinset y).card ≤ 1 := by
  decide

/-- **`petersen11` is `C₄`-free** — via the common-neighbour criterion. -/
theorem petersen11_not_containsC4 : ¬ containsC4 (Fin 11) petersen11 :=
  not_containsC4_of_forall_common_le_one petersen11_common_le_one

/-- `petersen11` has minimum degree at least `3`. -/
theorem petersen11_three_le_minDegree : 3 ≤ petersen11.minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact petersen11_degree

/-- **`f(11) ≥ 4`**: `petersen11` is a `C₄`-free graph of minimum degree `3`
on eleven vertices, so threshold `3` does not force a `C₄` at order `11`. -/
theorem four_le_minDegreeForC4_eleven : 4 ≤ minDegreeForC4 11 := by
  have hne : {k : ℕ | ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj],
      G.minDegree ≥ k → containsC4 (Fin 11) G}.Nonempty := by
    refine ⟨10, fun G _ hmin => ?_⟩
    rw [eq_top_of_minDegree_ge G hmin]
    exact completeGraph_containsC4 (by norm_num)
  unfold minDegreeForC4
  refine le_csInf hne (fun k hk => ?_)
  by_contra hk4
  rw [not_le] at hk4
  exact petersen11_not_containsC4
    (hk petersen11 (le_trans (by omega : k ≤ 3) petersen11_three_le_minDegree))

/-- **An eighth exact value: `f(11) = 4`.**  Upper half: counting,
`11 ≤ 4·3` (`minDegreeForC4_le_of_le_mul_pred`).  Lower half: the extended
Petersen graph (`four_le_minDegreeForC4_eleven`). -/
theorem minDegreeForC4_eleven : minDegreeForC4 11 = 4 := by
  have hle : minDegreeForC4 11 ≤ 4 :=
    minDegreeForC4_le_of_le_mul_pred (by norm_num) (by norm_num)
  have hge := four_le_minDegreeForC4_eleven
  omega

/-- The nineteen edges of the `12`-vertex graph: `petersen11Edges` with the
outer edge `(2, 3)` deleted and the new vertex `11` joined to `2`, `3`, and
`8` (a spoke neighbour of `3`) — the same surgery applied once more. -/
def petersen12Edges : List (Fin 12 × Fin 12) :=
  [(1,2), (3,4), (4,0),
   (5,7), (7,9), (9,6), (6,8), (8,5),
   (0,5), (1,6), (2,7), (3,8), (4,9),
   (10,0), (10,1), (10,6),
   (11,2), (11,3), (11,8)]

/-- **A `12`-vertex `C₄`-free graph of minimum degree `3`**: the Petersen
graph after two vertex-adding surgeries.  Vertices `6` and `8` have degree
`4`; all other vertices have degree `3`. -/
def petersen12 : SimpleGraph (Fin 12) where
  Adj i j := (i, j) ∈ petersen12Edges ∨ (j, i) ∈ petersen12Edges
  symm.symm := fun _ _ h => Or.symm h
  loopless.irrefl := by decide

instance : DecidableRel petersen12.Adj := fun i j =>
  decidable_of_iff ((i, j) ∈ petersen12Edges ∨ (j, i) ∈ petersen12Edges) Iff.rfl

/-- Every vertex of `petersen12` has degree at least `3` — a `12`-vertex
kernel check. -/
theorem petersen12_degree : ∀ v, 3 ≤ petersen12.degree v := by decide

/-- **Every pair of distinct `petersen12` vertices has at most one common
neighbour** — the `12 × 12` kernel check certifying `C₄`-freeness. -/
theorem petersen12_common_le_one : ∀ x y : Fin 12, x ≠ y →
    (petersen12.neighborFinset x ∩ petersen12.neighborFinset y).card ≤ 1 := by
  decide

/-- **`petersen12` is `C₄`-free** — via the common-neighbour criterion. -/
theorem petersen12_not_containsC4 : ¬ containsC4 (Fin 12) petersen12 :=
  not_containsC4_of_forall_common_le_one petersen12_common_le_one

/-- `petersen12` has minimum degree at least `3`. -/
theorem petersen12_three_le_minDegree : 3 ≤ petersen12.minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact petersen12_degree

/-- **`f(12) ≥ 4`**: `petersen12` is a `C₄`-free graph of minimum degree `3`
on twelve vertices, so threshold `3` does not force a `C₄` at order `12`. -/
theorem four_le_minDegreeForC4_twelve : 4 ≤ minDegreeForC4 12 := by
  have hne : {k : ℕ | ∀ (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj],
      G.minDegree ≥ k → containsC4 (Fin 12) G}.Nonempty := by
    refine ⟨11, fun G _ hmin => ?_⟩
    rw [eq_top_of_minDegree_ge G hmin]
    exact completeGraph_containsC4 (by norm_num)
  unfold minDegreeForC4
  refine le_csInf hne (fun k hk => ?_)
  by_contra hk4
  rw [not_le] at hk4
  exact petersen12_not_containsC4
    (hk petersen12 (le_trans (by omega : k ≤ 3) petersen12_three_le_minDegree))

/-- **A ninth exact value: `f(12) = 4` — and the end of the counting range.**
Upper half: counting, `12 ≤ 4·3` — the *boundary case* `n = k(k−1)` of
`minDegreeForC4_le_of_le_mul_pred`, sharp with no room to spare (`C(13,2) =
78 = 13·6` fails the strict inequality, so order `13` is out of the counting
bound's reach for `k = 4`).  Lower half: the twice-extended Petersen graph
(`four_le_minDegreeForC4_twelve`).  The exact table now reads
`f = 1, 2, 3, 2, 3, 3, 3, 3, 3, 4, 4, 4` for `n = 1, …, 12` — complete over
the entire range the elementary cherry count can reach. -/
theorem minDegreeForC4_twelve : minDegreeForC4 12 = 4 := by
  have hle : minDegreeForC4 12 ≤ 4 :=
    minDegreeForC4_le_of_le_mul_pred (by norm_num) (by norm_num)
  have hge := four_le_minDegreeForC4_twelve
  omega

/-! ## The abstract vertex-adding surgery: `C₄`-free min-degree-3 witnesses grow

The `f(11)` and `f(12)` witnesses were built by hand-picked surgeries on the
Petersen graph, each verified by a fixed-size kernel `decide`.  This section
formalizes the surgery **abstractly**, so that every future lower-bound rung
`f(n+1) ≥ 4` reduces to exhibiting a small *configuration* in the current
`n`-vertex witness instead of re-verifying an entire graph:

given a `C₄`-free graph `G` (via the common-neighbour criterion) and vertices
`a, b, c` with `a ~ b`, `b ~ c`, `a ≁ c`, where the edges `ab` and `bc` each
lie in **no triangle**, the surgery

    delete the edge `a–b`, add a new vertex `v` adjacent to `a`, `b`, `c`

produces a graph on one more vertex that again has min-degree `≥ 3` (if `G`
did) and all pairwise common neighbourhoods of size `≤ 1`.  The triangle-free
hypotheses are exactly what the general step needs (they were automatic in the
girth-5 Petersen but fail for arbitrary `C₄`-free graphs — `G` may have
triangles elsewhere; only the two surgered edges must avoid them).  Note
`common(a,c) = {b}` is automatic: `b` is a common neighbour and `C₄`-freeness
caps the count at one.

Applied to `petersen12` with the configuration `a = 4, b = 9, c = 7` (both
edges triangle-free by a kernel check), this yields **`f(13) ≥ 4`** — beyond
the counting range, where the upper bound `f(13) ≤ 4` is genuinely blocked —
so `f(13) ∈ {4, 5}`. -/

section Surgery

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency relation of the surgered graph: old edges minus `a–b`
(`some`-`some`), plus a new vertex `none` adjacent to exactly `a`, `b`, `c`. -/
def surgeryAdj (G : SimpleGraph V) (a b c : V) : Option V → Option V → Prop
  | some x, some y => G.Adj x y ∧ ¬(x = a ∧ y = b) ∧ ¬(x = b ∧ y = a)
  | some x, none => x = a ∨ x = b ∨ x = c
  | none, some y => y = a ∨ y = b ∨ y = c
  | none, none => False

/-- **The vertex-adding surgery**: delete the edge `a–b` of `G`, add a new
vertex (`none`) adjacent to `a`, `b`, and `c`. -/
def surgery (G : SimpleGraph V) (a b c : V) : SimpleGraph (Option V) where
  Adj := surgeryAdj G a b c
  symm.symm := by
    intro p q h
    match p, q with
    | some x, some y =>
        exact ⟨h.1.symm, fun hc => h.2.2 ⟨hc.2, hc.1⟩, fun hc => h.2.1 ⟨hc.2, hc.1⟩⟩
    | some x, none => exact h
    | none, some y => exact h
    | none, none => exact h.elim
  loopless.irrefl := by
    intro p h
    match p with
    | some x => exact G.loopless.irrefl x h.1
    | none => exact h

instance surgeryDecidableRel (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) :
    DecidableRel (surgery G a b c).Adj := fun p q =>
  match p, q with
  | some x, some y =>
      inferInstanceAs (Decidable (G.Adj x y ∧ ¬(x = a ∧ y = b) ∧ ¬(x = b ∧ y = a)))
  | some x, none => inferInstanceAs (Decidable (x = a ∨ x = b ∨ x = c))
  | none, some y => inferInstanceAs (Decidable (y = a ∨ y = b ∨ y = c))
  | none, none => inferInstanceAs (Decidable False)

@[simp] theorem surgery_adj_some_some {G : SimpleGraph V} {a b c x y : V} :
    (surgery G a b c).Adj (some x) (some y) ↔
      G.Adj x y ∧ ¬(x = a ∧ y = b) ∧ ¬(x = b ∧ y = a) := Iff.rfl

@[simp] theorem surgery_adj_some_none {G : SimpleGraph V} {a b c x : V} :
    (surgery G a b c).Adj (some x) none ↔ (x = a ∨ x = b ∨ x = c) := Iff.rfl

@[simp] theorem surgery_adj_none_some {G : SimpleGraph V} {a b c y : V} :
    (surgery G a b c).Adj none (some y) ↔ (y = a ∨ y = b ∨ y = c) := Iff.rfl

@[simp] theorem surgery_adj_none_none {G : SimpleGraph V} {a b c : V} :
    ¬ (surgery G a b c).Adj none none := fun h => h

/-- **Old vertices keep their degree (at least)**: the map sending the deleted
neighbour `b` of `a` (resp. `a` of `b`) to the new vertex and every other
neighbour to itself injects the old neighbourhood of `x` into the new one. -/
theorem surgery_degree_some {G : SimpleGraph V} [DecidableRel G.Adj] {a b c : V}
    (hne : a ≠ b) (x : V) :
    G.degree x ≤ (surgery G a b c).degree (some x) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn
    (fun y => if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then none else some y)
  · intro y hy
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy ⊢
    by_cases hcase : (x = a ∧ y = b) ∨ (x = b ∧ y = a)
    · rw [if_pos hcase]
      rcases hcase with ⟨hxa, _⟩ | ⟨hxb, _⟩
      · rw [surgery_adj_some_none]; exact Or.inl hxa
      · rw [surgery_adj_some_none]; exact Or.inr (Or.inl hxb)
    · rw [if_neg hcase]
      rw [surgery_adj_some_some]
      exact ⟨hy, fun h => hcase (Or.inl h), fun h => hcase (Or.inr h)⟩
  · intro y₁ h₁ y₂ h₂ heq
    simp only [] at heq
    by_cases hc₁ : (x = a ∧ y₁ = b) ∨ (x = b ∧ y₁ = a) <;>
      by_cases hc₂ : (x = a ∧ y₂ = b) ∨ (x = b ∧ y₂ = a)
    · rcases hc₁ with ⟨hxa, hy₁⟩ | ⟨hxb, hy₁⟩ <;>
        rcases hc₂ with ⟨hxa₂, hy₂⟩ | ⟨hxb₂, hy₂⟩
      · rw [hy₁, hy₂]
      · exact absurd (hxa ▸ hxb₂ : a = b) hne
      · exact absurd (hxa₂ ▸ hxb : a = b) hne
      · rw [hy₁, hy₂]
    · rw [if_pos hc₁, if_neg hc₂] at heq
      exact absurd heq (by simp)
    · rw [if_neg hc₁, if_pos hc₂] at heq
      exact absurd heq (by simp)
    · rw [if_neg hc₁, if_neg hc₂] at heq
      exact Option.some.inj heq

/-- **The new vertex has degree at least `3`**: `a`, `b`, `c` are three
distinct neighbours. -/
theorem surgery_degree_none {G : SimpleGraph V} [DecidableRel G.Adj] {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ (surgery G a b c).degree none := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : ({some a, some b, some c} : Finset (Option V)) ⊆
      (surgery G a b c).neighborFinset none := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · rw [surgery_adj_none_some]; exact Or.inl rfl
    · rw [surgery_adj_none_some]; exact Or.inr (Or.inl rfl)
    · rw [surgery_adj_none_some]; exact Or.inr (Or.inr rfl)
  calc 3 = ({some a, some b, some c} : Finset (Option V)).card := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
            Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    _ ≤ _ := Finset.card_le_card hsub

/-- **The surgery preserves the common-neighbour bound.**  If in `G` every pair
of distinct vertices has at most one common neighbour, the edges `ab` and `bc`
lie in no triangle, and `a ≁ c`, then every pair of distinct vertices of the
surgered graph again has at most one common neighbour — so the result stays
`C₄`-free. -/
theorem surgery_common_le_one {G : SimpleGraph V} [DecidableRel G.Adj] {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬ G.Adj a c) (hane : a ≠ c)
    (htriab : ∀ z, G.Adj a z → G.Adj b z → False)
    (htribc : ∀ z, G.Adj b z → G.Adj c z → False)
    (hcom : ∀ x y : V, x ≠ y →
      (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1) :
    ∀ p q : Option V, p ≠ q →
      ((surgery G a b c).neighborFinset p ∩ (surgery G a b c).neighborFinset q).card ≤ 1 := by
  -- the common-neighbour bound of `G`, in element form
  have hcom' : ∀ x y z₁ z₂ : V, x ≠ y → G.Adj x z₁ → G.Adj y z₁ →
      G.Adj x z₂ → G.Adj y z₂ → z₁ = z₂ := by
    intro x y z₁ z₂ hxy h1 h2 h3 h4
    refine Finset.card_le_one.mp (hcom x y hxy) z₁ ?_ z₂ ?_
    · rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨h1, h2⟩
    · rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨h3, h4⟩
  -- `b` is the unique common neighbour of the non-adjacent pair `(a, c)`
  have huniq : ∀ z, G.Adj a z → G.Adj c z → z = b := fun z h1 h2 =>
    hcom' a c z b hane h1 h2 hab hbc.symm
  -- a common neighbour of a `some`-`some` pair inside `{a, b, c}` is impossible
  have hkey : ∀ x y z : V, (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) →
      x ≠ y → (surgery G a b c).Adj (some x) (some z) →
      (surgery G a b c).Adj (some y) (some z) → False := by
    intro x y z hx hy hxy hxz hyz
    rw [surgery_adj_some_some] at hxz hyz
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact hxy rfl
    · exact htriab z hxz.1 hyz.1
    · -- x = a, y = c: z is a common neighbour of (a, c), so z = b; but the
      -- surgered adjacency `some a ~ some z` forbids z = b (deleted edge)
      exact hxz.2.1 ⟨rfl, huniq z hxz.1 hyz.1⟩
    · exact htriab z hyz.1 hxz.1
    · exact hxy rfl
    · exact htribc z hxz.1 hyz.1
    · exact hyz.2.1 ⟨rfl, huniq z hyz.1 hxz.1⟩
    · exact htribc z hyz.1 hxz.1
    · exact hxy rfl
  intro p q hpq
  rw [Finset.card_le_one]
  intro w₁ hw₁ w₂ hw₂
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at hw₁ hw₂
  obtain ⟨hw₁p, hw₁q⟩ := hw₁
  obtain ⟨hw₂p, hw₂q⟩ := hw₂
  rcases p with _ | x <;> rcases q with _ | y
  · exact absurd rfl hpq
  · -- p = none, q = some y: all common neighbours are `some z` with
    -- z ∈ {a, b, c} and z ~ y; two distinct such z collide via `hkey`
    rcases w₁ with _ | z₁
    · exact (surgery_adj_none_none hw₁p).elim
    rcases w₂ with _ | z₂
    · exact (surgery_adj_none_none hw₂p).elim
    by_contra hne12
    have hz₁ : z₁ = a ∨ z₁ = b ∨ z₁ = c := by rwa [surgery_adj_none_some] at hw₁p
    have hz₂ : z₂ = a ∨ z₂ = b ∨ z₂ = c := by rwa [surgery_adj_none_some] at hw₂p
    exact hkey z₁ z₂ y hz₁ hz₂ (fun h => hne12 (congrArg some h))
      hw₁q.symm hw₂q.symm
  · -- p = some x, q = none: mirror of the previous case
    rcases w₁ with _ | z₁
    · exact (surgery_adj_none_none hw₁q).elim
    rcases w₂ with _ | z₂
    · exact (surgery_adj_none_none hw₂q).elim
    by_contra hne12
    have hz₁ : z₁ = a ∨ z₁ = b ∨ z₁ = c := by rwa [surgery_adj_none_some] at hw₁q
    have hz₂ : z₂ = a ∨ z₂ = b ∨ z₂ = c := by rwa [surgery_adj_none_some] at hw₂q
    exact hkey z₁ z₂ x hz₁ hz₂ (fun h => hne12 (congrArg some h))
      hw₁p.symm hw₂p.symm
  · -- p = some x, q = some y
    have hxy : x ≠ y := fun h => hpq (by rw [h])
    rcases w₁ with _ | z₁ <;> rcases w₂ with _ | z₂
    · rfl
    · -- w₁ = none: x, y ∈ {a, b, c}, and z₂ is a `some` common neighbour
      have hx : x = a ∨ x = b ∨ x = c := by rwa [surgery_adj_some_none] at hw₁p
      have hy : y = a ∨ y = b ∨ y = c := by rwa [surgery_adj_some_none] at hw₁q
      exact (hkey x y z₂ hx hy hxy hw₂p hw₂q).elim
    · have hx : x = a ∨ x = b ∨ x = c := by rwa [surgery_adj_some_none] at hw₂p
      have hy : y = a ∨ y = b ∨ y = c := by rwa [surgery_adj_some_none] at hw₂q
      exact (hkey x y z₁ hx hy hxy hw₁p hw₁q).elim
    · rw [surgery_adj_some_some] at hw₁p hw₁q hw₂p hw₂q
      exact congrArg some (hcom' x y z₁ z₂ hxy hw₁p.1 hw₁q.1 hw₂p.1 hw₂q.1)

end Surgery

/-! ## Reusable lower-bound assembly, transport to `Fin (n+1)`, and `f(13) ≥ 4` -/

/-- **Generic witness-to-lower-bound assembly**: a `C₄`-free graph of minimum
degree `≥ 3` on `Fin n` (with `n ≥ 4`) forces `f(n) ≥ 4`.  Extracts the
`sInf` argument used verbatim for `f(10)`, `f(11)`, `f(12)`. -/
theorem four_le_minDegreeForC4_of_witness {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : 3 ≤ G.minDegree) (hC4 : ¬ containsC4 (Fin n) G) :
    4 ≤ minDegreeForC4 n := by
  have hne : {k : ℕ | ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.minDegree ≥ k → containsC4 (Fin n) H}.Nonempty := by
    refine ⟨n - 1, fun H _ hmin => ?_⟩
    rw [eq_top_of_minDegree_ge H hmin]
    exact completeGraph_containsC4 hn
  unfold minDegreeForC4
  refine le_csInf hne (fun k hk => ?_)
  by_contra hk4
  rw [not_le] at hk4
  exact hC4 (hk G (le_trans (by omega : k ≤ 3) hdeg))

/-- The surgered graph, transported from `Option (Fin n)` to `Fin (n + 1)`
along `finSuccEquiv`. -/
def surgeryFin {n : ℕ} (G : SimpleGraph (Fin n)) (a b c : Fin n) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.comap (⇑(finSuccEquiv n)) (surgery G a b c)

instance surgeryFinDecidableRel {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (a b c : Fin n) :
    DecidableRel (surgeryFin G a b c).Adj := fun u v =>
  inferInstanceAs
    (Decidable ((surgery G a b c).Adj (finSuccEquiv n u) (finSuccEquiv n v)))

/-- Degrees only grow under the `finSuccEquiv` transport (they are in fact
equal; the inequality is all that is needed). -/
theorem surgeryFin_degree_ge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (a b c : Fin n) (u : Fin (n + 1)) :
    (surgery G a b c).degree (finSuccEquiv n u) ≤ (surgeryFin G a b c).degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun w => (finSuccEquiv n).symm w)
  · intro w hw
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
    show (surgery G a b c).Adj (finSuccEquiv n u)
      (finSuccEquiv n ((finSuccEquiv n).symm w))
    rw [Equiv.apply_symm_apply]
    exact hw
  · intro w₁ _ w₂ _ h
    exact (finSuccEquiv n).symm.injective h

/-- `C₄`-freeness transports along the `finSuccEquiv` pullback. -/
theorem surgeryFin_not_containsC4 {n : ℕ} (G : SimpleGraph (Fin n))
    (a b c : Fin n) (h : ¬ containsC4 (Option (Fin n)) (surgery G a b c)) :
    ¬ containsC4 (Fin (n + 1)) (surgeryFin G a b c) := by
  rintro ⟨f, hinj, hadj⟩
  exact h ⟨fun i => finSuccEquiv n (f i), (finSuccEquiv n).injective.comp hinj,
    fun i j hij => hadj i j hij⟩

/-- **`f(13) ≥ 4`** — the first rung beyond the counting range, via the
abstract surgery applied to `petersen12` with the configuration
`a = 4, b = 9, c = 7`: the edges `4–9` (spoke) and `9–7` (inner) are
triangle-free, `4 ≁ 7`, and all remaining hypotheses are `12`-vertex kernel
checks.  No `13`-vertex graph is ever `decide`d — the surgery lemmas carry
the verification. -/
theorem four_le_minDegreeForC4_thirteen : 4 ≤ minDegreeForC4 13 := by
  have hab : petersen12.Adj 4 9 := by decide
  have hbc : petersen12.Adj 9 7 := by decide
  have hac : ¬ petersen12.Adj 4 7 := by decide
  have hane : (4 : Fin 12) ≠ 7 := by decide
  have htriab : ∀ z, petersen12.Adj 4 z → petersen12.Adj 9 z → False := by decide
  have htribc : ∀ z, petersen12.Adj 9 z → petersen12.Adj 7 z → False := by decide
  have hcommon := surgery_common_le_one hab hbc hac hane htriab htribc
    petersen12_common_le_one
  have hC4 : ¬ containsC4 (Fin 13) (surgeryFin petersen12 4 9 7) :=
    surgeryFin_not_containsC4 petersen12 4 9 7
      (not_containsC4_of_forall_common_le_one hcommon)
  have hdeg : 3 ≤ (surgeryFin petersen12 4 9 7).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    refine le_trans ?_ (surgeryFin_degree_ge petersen12 4 9 7 u)
    rcases h : finSuccEquiv 12 u with _ | x
    · exact surgery_degree_none (by decide) (by decide) (by decide)
    · exact le_trans (petersen12_degree x)
        (surgery_degree_some (by decide) x)
  exact four_le_minDegreeForC4_of_witness (by norm_num)
    (surgeryFin petersen12 4 9 7) hdeg hC4

/-- **`f(13) ∈ {4, 5}`**: the lower bound is the surgery witness; the upper
bound is the counting bound at `k = 5` (`13 ≤ 5·4`).  Pinning `f(13) = 4`
needs an upper-bound mechanism beyond the cherry count (the true value is `4`
in the literature) — the honest remaining gap. -/
theorem minDegreeForC4_thirteen_mem :
    minDegreeForC4 13 = 4 ∨ minDegreeForC4 13 = 5 := by
  have hle : minDegreeForC4 13 ≤ 5 :=
    minDegreeForC4_le_of_le_mul_pred (by norm_num) (by norm_num)
  have hge := four_le_minDegreeForC4_thirteen
  omega

/-! ## The projective-plane threshold: `f(13) = 4` via the friendship theorem

`n = 13 = 4·3 + 1` sits exactly ONE vertex beyond the reach of the crude cherry
count (`minDegreeForC4_le_of_le_mul_pred` needs `n ≤ k(k−1) = 12`): at `n = 13`
the count `13·C(4,2) = C(13,2) = 78` is EXACTLY tight, so pigeonhole no longer
produces a collision.  What tightness does give is rigidity: a hypothetical
`C₄`-free graph on `13` vertices with minimum degree `4` must be `4`-regular
with every pair of distinct vertices having **exactly one** common neighbour —
the *friendship condition*.  The friendship theorem (Mathlib Archive,
Wiedijk #83: every finite friendship graph has a politician) then produces a
vertex of degree `12`, contradicting `4`-regularity.  Hence `f(13) ≤ 4`, and
with the surgery witness `f(13) ≥ 4` the fourth exact value **`f(13) = 4`** —
the first one pinned beyond the counting range, and precisely the parameter
point of the (nonexistent) friendship configuration attached to a projective
plane of order `3`. -/

section Thirteen

/-- **Converse of the common-neighbour criterion**: a `C₄`-free graph has at
most one common neighbour per pair of distinct vertices (two common
neighbours of `x ≠ y` form the rim `x–v–y–v'–x`). -/
theorem common_le_one_of_not_containsC4 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : ¬ containsC4 V G)
    (x y : V) (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at hv hv'
  exact h (containsC4_of_rim hv.1 hv.2.symm hv'.2 hv'.1.symm hxy hne
    (G.ne_of_adj hv.1).symm (G.ne_of_adj hv.2).symm
    (G.ne_of_adj hv'.1).symm (G.ne_of_adj hv'.2).symm)

/-- **The projective-plane threshold.**  Every graph on `13` vertices with
minimum degree `≥ 4` contains a `4`-cycle.  Cherry-counting is exactly tight
(`13·C(4,2) = C(13,2) = 78`), so a `C₄`-free such graph would be `4`-regular
with every vertex pair having exactly one common neighbour — a friendship
graph; the friendship theorem's politician has degree `12 ≠ 4`. -/
theorem containsC4_of_thirteen_minDegree_four (G : SimpleGraph (Fin 13))
    [DecidableRel G.Adj] (hmin : 4 ≤ G.minDegree) : containsC4 (Fin 13) G := by
  classical
  by_contra hC4
  -- The cherry Finset and the endpoint-pair target, as in
  -- `containsC4_of_card_choose_two_lt`.
  set C : Finset (Σ _ : Fin 13, Finset (Fin 13)) :=
    univ.sigma (fun v => (G.neighborFinset v).powersetCard 2) with hC
  set T : Finset (Finset (Fin 13)) := (univ : Finset (Fin 13)).powersetCard 2 with hT
  have hCcard : C.card = ∑ v : Fin 13, (G.degree v).choose 2 := by
    rw [hC, Finset.card_sigma]
    exact Finset.sum_congr rfl fun v _ => by
      rw [Finset.card_powersetCard, G.card_neighborFinset_eq_degree]
  have hTcard : T.card = 78 := by
    rw [hT, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    decide
  have hmaps : ∀ p ∈ C, p.2 ∈ T := by
    intro p hp
    rw [hC, Finset.mem_sigma] at hp
    rw [hT, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hp.2).2⟩
  -- With no `C₄`, the endpoint pair DETERMINES the centre (two centres over
  -- the same pair are two common neighbours).
  have hcentre : ∀ (v v' : Fin 13) (e : Finset (Fin 13)), (⟨v, e⟩ : Σ _ : Fin 13,
      Finset (Fin 13)) ∈ C → (⟨v', e⟩ : Σ _ : Fin 13, Finset (Fin 13)) ∈ C → v = v' := by
    intro v v' e hp hq
    by_contra hne
    rw [hC, Finset.mem_sigma] at hp hq
    obtain ⟨hsubv, hcard⟩ := Finset.mem_powersetCard.mp hp.2
    obtain ⟨hsubv', -⟩ := Finset.mem_powersetCard.mp hq.2
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hvmem : v ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨((G.mem_neighborFinset v x).mp (hsubv (by simp))).symm,
             ((G.mem_neighborFinset v y).mp (hsubv (by simp))).symm⟩
    have hv'mem : v' ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨((G.mem_neighborFinset v' x).mp (hsubv' (by simp))).symm,
             ((G.mem_neighborFinset v' y).mp (hsubv' (by simp))).symm⟩
    have h2 : 1 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
      Finset.one_lt_card.mpr ⟨v, hvmem, v', hv'mem, hne⟩
    have h1 := common_le_one_of_not_containsC4 hC4 x y hxy
    omega
  -- Injectivity ⟹ `|C| ≤ 78`.
  have hinj : ∀ p₁ p₂ : Σ _ : Fin 13, Finset (Fin 13), p₁ ∈ C → p₂ ∈ C →
      p₁.2 = p₂.2 → p₁ = p₂ := by
    rintro ⟨v, e⟩ ⟨v', e'⟩ hp hq (heq : e = e')
    subst heq
    obtain rfl := hcentre v v' e hp hq
    rfl
  have hCle : C.card ≤ 78 := by
    rw [← hTcard]
    exact Finset.card_le_card_of_injOn (fun p => p.2) hmaps
      (fun p₁ h₁ p₂ h₂ h => hinj p₁ p₂ h₁ h₂ h)
  -- Minimum degree ⟹ `|C| ≥ 78`.
  have hterm : ∀ v : Fin 13, 6 ≤ (G.degree v).choose 2 := by
    intro v
    have h4 : 4 ≤ G.degree v := le_trans hmin (G.minDegree_le_degree v)
    calc 6 = (4 : ℕ).choose 2 := by decide
      _ ≤ (G.degree v).choose 2 := Nat.choose_le_choose 2 h4
  have hCge : 78 ≤ C.card := by
    rw [hCcard]
    calc (78 : ℕ) = ∑ _v : Fin 13, 6 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ v : Fin 13, (G.degree v).choose 2 := Finset.sum_le_sum fun v _ => hterm v
  -- Exact tightness ⟹ `4`-regularity.
  have hsum78 : ∑ v : Fin 13, (G.degree v).choose 2 = 78 := by
    rw [← hCcard]; omega
  have hdeg4 : ∀ v : Fin 13, G.degree v = 4 := by
    intro v
    have h4 : 4 ≤ G.degree v := le_trans hmin (G.minDegree_le_degree v)
    by_contra hne
    have h5 : 5 ≤ G.degree v := by omega
    have h10 : 10 ≤ (G.degree v).choose 2 := by
      calc (10 : ℕ) = (5 : ℕ).choose 2 := by decide
        _ ≤ (G.degree v).choose 2 := Nat.choose_le_choose 2 h5
    have hsplit : (G.degree v).choose 2 +
        ∑ u ∈ univ.erase v, (G.degree u).choose 2
          = ∑ u : Fin 13, (G.degree u).choose 2 :=
      Finset.add_sum_erase univ (fun u => (G.degree u).choose 2) (Finset.mem_univ v)
    have hrest : 72 ≤ ∑ u ∈ univ.erase v, (G.degree u).choose 2 := by
      calc (72 : ℕ) = ∑ _u ∈ univ.erase v, 6 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v),
              Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ ∑ u ∈ univ.erase v, (G.degree u).choose 2 :=
            Finset.sum_le_sum fun u _ => hterm u
    omega
  -- Exact tightness ⟹ surjectivity: every vertex pair is a cherry's endpoint
  -- pair, i.e. has a common neighbour.
  have hsurj := Finset.surj_on_of_inj_on_of_card_le
    (s := C) (t := T) (fun p _ => p.2) (fun p hp => hmaps p hp)
    (fun p₁ p₂ h₁ h₂ h => hinj p₁ p₂ h₁ h₂ h) (by omega)
  -- The friendship condition: every pair of distinct vertices has exactly one
  -- common neighbour.
  have hfriend : Theorems100.Friendship G := by
    intro x y hxy
    have hxyT : ({x, y} : Finset (Fin 13)) ∈ T := by
      rw [hT, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair_eq_two_iff.mpr hxy⟩
    obtain ⟨⟨v, e⟩, hpC, hpe⟩ := hsurj _ hxyT
    have he : e = ({x, y} : Finset (Fin 13)) := hpe.symm
    subst he
    rw [hC, Finset.mem_sigma] at hpC
    obtain ⟨-, hpow⟩ := hpC
    have hsub := (Finset.mem_powersetCard.mp hpow).1
    have hvx : G.Adj x v := ((G.mem_neighborFinset v x).mp (hsub (by simp))).symm
    have hvy : G.Adj y v := ((G.mem_neighborFinset v y).mp (hsub (by simp))).symm
    -- `commonNeighbors` membership is definitionally the pair of adjacencies.
    have hvmemS : v ∈ G.commonNeighbors x y := ⟨hvx, hvy⟩
    -- The goal's `Fintype` instance (Classical, baked into the Archive's
    -- `Friendship` def) differs definitionally from the one synthesized from
    -- `[DecidableRel G.Adj]`.  Prove the count with the synthesized instance,
    -- then bridge with `convert`, which closes the instance mismatch by
    -- `Subsingleton.elim` (Fintype is a subsingleton).
    have hone : Fintype.card {w : Fin 13 // w ∈ G.commonNeighbors x y} = 1 := by
      refine Fintype.card_eq_one_iff.mpr ⟨⟨v, hvmemS⟩, ?_⟩
      rintro ⟨w, hw⟩
      obtain ⟨hwx, hwy⟩ : G.Adj x w ∧ G.Adj y w := hw
      have hcom := common_le_one_of_not_containsC4 hC4 x y hxy
      have hwmem : w ∈ G.neighborFinset x ∩ G.neighborFinset y := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
        exact ⟨hwx, hwy⟩
      have hvmem : v ∈ G.neighborFinset x ∩ G.neighborFinset y := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
        exact ⟨hvx, hvy⟩
      exact Subtype.ext (Finset.card_le_one.mp hcom w hwmem v hvmem)
    convert hone using 2
  -- The friendship theorem: a politician exists — degree `12`, not `4`.
  obtain ⟨v, hv⟩ := Theorems100.friendship_theorem hfriend
  have h12 : G.degree v = 12 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have huniv : G.neighborFinset v = univ.erase v := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
      constructor
      · intro h
        exact ⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩
      · rintro ⟨hne, -⟩
        exact hv w (Ne.symm hne)
    rw [huniv, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin]
  have := hdeg4 v
  omega

/-- **`f(13) ≤ 4`** — the upper half of the fourth exact value, one vertex
beyond the crude counting range. -/
theorem minDegreeForC4_le_four_thirteen : minDegreeForC4 13 ≤ 4 := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_thirteen_minDegree_four G hmin

/-- **The fourth exact value: `f(13) = 4`** — the surgery witness gives
`f(13) ≥ 4`, and the friendship-theorem tightness argument gives
`f(13) ≤ 4`.  This closes the gap flagged in `minDegreeForC4_thirteen_mem`:
the first exact value pinned beyond the counting range `n ≤ k(k−1)`. -/
theorem minDegreeForC4_thirteen : minDegreeForC4 13 = 4 :=
  le_antisymm minDegreeForC4_le_four_thirteen four_le_minDegreeForC4_thirteen

end Thirteen

/-
## Tight points: `f(k(k−1)+1) ≤ k` for every `k ≥ 3`

The `f(13) ≤ 4` argument above is the `k = 4` instance of a uniform
phenomenon.  At the projective-plane parameter `n = k(k−1)+1` the cherry
double-count is *exactly* tight — `C(n,2) = n·C(k,2)` — so a `C₄`-free graph
on `n` vertices with minimum degree `≥ k` would have to be `k`-regular with
every vertex pair sharing exactly one common neighbour: a friendship graph,
whose politician (friendship theorem) has degree `n − 1 = k(k−1) ≠ k`.

This section parameterises the `Thirteen` section over `k`, producing
infinitely many upper bounds one vertex beyond the counting range
`n ≤ k(k−1)` of `minDegreeForC4_le_of_le_mul_pred` — including the new
concrete values `f(21) ≤ 5` and `f(31) ≤ 6`, beyond the exact table
`f(1..13)`.
-/

section TightPoints

/-- **Exact tightness of the cherry count at the projective-plane parameter**:
`C(k(k−1)+1, 2) = (k(k−1)+1) · C(k,2)`.  (Both `Nat.choose 2` halvings are
exact because `k(k−1)` is even.) -/
theorem choose_two_tight (k : ℕ) :
    (k * (k - 1) + 1).choose 2 = (k * (k - 1) + 1) * k.choose 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel,
    Nat.mul_div_assoc _ (two_dvd_mul_pred k), Nat.choose_two_right]

/-- **The tight-point theorem.**  Every graph on `k(k−1)+1` vertices with
minimum degree `≥ k` (for `k ≥ 3`) contains a `4`-cycle.  Cherry-counting is
exactly tight (`choose_two_tight`), so a `C₄`-free such graph would be
`k`-regular with every vertex pair having exactly one common neighbour — a
friendship graph; the friendship theorem's politician has degree
`k(k−1) ≠ k`.  The `Thirteen` section's argument, uniformly in `k`. -/
theorem containsC4_of_tight_minDegree {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin (k * (k - 1) + 1))) [DecidableRel G.Adj]
    (hmin : k ≤ G.minDegree) : containsC4 (Fin (k * (k - 1) + 1)) G := by
  classical
  by_contra hC4
  -- The cherry Finset and the endpoint-pair target, exactly as in the
  -- `Thirteen` section.
  set C : Finset (Σ _ : Fin (k * (k - 1) + 1), Finset (Fin (k * (k - 1) + 1))) :=
    univ.sigma (fun v => (G.neighborFinset v).powersetCard 2) with hC
  set T : Finset (Finset (Fin (k * (k - 1) + 1))) :=
    (univ : Finset (Fin (k * (k - 1) + 1))).powersetCard 2 with hT
  have hCcard : C.card = ∑ v : Fin (k * (k - 1) + 1), (G.degree v).choose 2 := by
    rw [hC, Finset.card_sigma]
    exact Finset.sum_congr rfl fun v _ => by
      rw [Finset.card_powersetCard, G.card_neighborFinset_eq_degree]
  have hTcard : T.card = (k * (k - 1) + 1) * k.choose 2 := by
    rw [hT, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact choose_two_tight k
  have hmaps : ∀ p ∈ C, p.2 ∈ T := by
    intro p hp
    rw [hC, Finset.mem_sigma] at hp
    rw [hT, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hp.2).2⟩
  -- With no `C₄`, the endpoint pair DETERMINES the centre.
  have hcentre : ∀ (v v' : Fin (k * (k - 1) + 1)) (e : Finset (Fin (k * (k - 1) + 1))),
      (⟨v, e⟩ : Σ _ : Fin (k * (k - 1) + 1), Finset (Fin (k * (k - 1) + 1))) ∈ C →
      (⟨v', e⟩ : Σ _ : Fin (k * (k - 1) + 1), Finset (Fin (k * (k - 1) + 1))) ∈ C →
      v = v' := by
    intro v v' e hp hq
    by_contra hne
    rw [hC, Finset.mem_sigma] at hp hq
    obtain ⟨hsubv, hcard⟩ := Finset.mem_powersetCard.mp hp.2
    obtain ⟨hsubv', -⟩ := Finset.mem_powersetCard.mp hq.2
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hvmem : v ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨((G.mem_neighborFinset v x).mp (hsubv (by simp))).symm,
             ((G.mem_neighborFinset v y).mp (hsubv (by simp))).symm⟩
    have hv'mem : v' ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨((G.mem_neighborFinset v' x).mp (hsubv' (by simp))).symm,
             ((G.mem_neighborFinset v' y).mp (hsubv' (by simp))).symm⟩
    have h2 : 1 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
      Finset.one_lt_card.mpr ⟨v, hvmem, v', hv'mem, hne⟩
    have h1 := common_le_one_of_not_containsC4 hC4 x y hxy
    omega
  have hinj : ∀ p₁ p₂ : Σ _ : Fin (k * (k - 1) + 1), Finset (Fin (k * (k - 1) + 1)),
      p₁ ∈ C → p₂ ∈ C → p₁.2 = p₂.2 → p₁ = p₂ := by
    rintro ⟨v, e⟩ ⟨v', e'⟩ hp hq (heq : e = e')
    subst heq
    obtain rfl := hcentre v v' e hp hq
    rfl
  -- Injectivity ⟹ `|C| ≤ n·C(k,2)`.
  have hCle : C.card ≤ (k * (k - 1) + 1) * k.choose 2 := by
    rw [← hTcard]
    exact Finset.card_le_card_of_injOn (fun p => p.2) hmaps
      (fun p₁ h₁ p₂ h₂ h => hinj p₁ p₂ h₁ h₂ h)
  -- Minimum degree ⟹ `|C| ≥ n·C(k,2)`.
  have hterm : ∀ v : Fin (k * (k - 1) + 1), k.choose 2 ≤ (G.degree v).choose 2 :=
    fun v => Nat.choose_le_choose 2 (le_trans hmin (G.minDegree_le_degree v))
  have hCge : (k * (k - 1) + 1) * k.choose 2 ≤ C.card := by
    rw [hCcard]
    calc (k * (k - 1) + 1) * k.choose 2
        = ∑ _v : Fin (k * (k - 1) + 1), k.choose 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ v : Fin (k * (k - 1) + 1), (G.degree v).choose 2 :=
          Finset.sum_le_sum fun v _ => hterm v
  -- Exact tightness ⟹ `k`-regularity.
  have hsum : ∑ v : Fin (k * (k - 1) + 1), (G.degree v).choose 2
      = (k * (k - 1) + 1) * k.choose 2 := by
    rw [← hCcard]
    omega
  have hdegk : ∀ v : Fin (k * (k - 1) + 1), G.degree v = k := by
    intro v
    have hkle : k ≤ G.degree v := le_trans hmin (G.minDegree_le_degree v)
    by_contra hne
    have hk1 : k + 1 ≤ G.degree v := by omega
    have hchoose : k.choose 2 + k ≤ (G.degree v).choose 2 := by
      have hstep : (k + 1).choose 2 = k.choose 2 + k := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
      calc k.choose 2 + k = (k + 1).choose 2 := hstep.symm
        _ ≤ (G.degree v).choose 2 := Nat.choose_le_choose 2 hk1
    have hsplit : (G.degree v).choose 2 +
        ∑ u ∈ univ.erase v, (G.degree u).choose 2
          = ∑ u : Fin (k * (k - 1) + 1), (G.degree u).choose 2 :=
      Finset.add_sum_erase univ (fun u => (G.degree u).choose 2) (Finset.mem_univ v)
    have hrest : (k * (k - 1)) * k.choose 2 ≤
        ∑ u ∈ univ.erase v, (G.degree u).choose 2 := by
      calc (k * (k - 1)) * k.choose 2
          = ∑ _u ∈ univ.erase v, k.choose 2 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v),
              Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, smul_eq_mul]
        _ ≤ ∑ u ∈ univ.erase v, (G.degree u).choose 2 :=
            Finset.sum_le_sum fun u _ => hterm u
    have hmul : (k * (k - 1) + 1) * k.choose 2
        = (k * (k - 1)) * k.choose 2 + k.choose 2 := Nat.succ_mul _ _
    omega
  -- Exact tightness ⟹ surjectivity: every vertex pair has a common neighbour.
  have hsurj := Finset.surj_on_of_inj_on_of_card_le
    (s := C) (t := T) (fun p _ => p.2) (fun p hp => hmaps p hp)
    (fun p₁ p₂ h₁ h₂ h => hinj p₁ p₂ h₁ h₂ h) (by omega)
  -- The friendship condition.
  have hfriend : Theorems100.Friendship G := by
    intro x y hxy
    have hxyT : ({x, y} : Finset (Fin (k * (k - 1) + 1))) ∈ T := by
      rw [hT, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair_eq_two_iff.mpr hxy⟩
    obtain ⟨⟨v, e⟩, hpC, hpe⟩ := hsurj _ hxyT
    have he : e = ({x, y} : Finset (Fin (k * (k - 1) + 1))) := hpe.symm
    subst he
    rw [hC, Finset.mem_sigma] at hpC
    obtain ⟨-, hpow⟩ := hpC
    have hsub := (Finset.mem_powersetCard.mp hpow).1
    have hvx : G.Adj x v := ((G.mem_neighborFinset v x).mp (hsub (by simp))).symm
    have hvy : G.Adj y v := ((G.mem_neighborFinset v y).mp (hsub (by simp))).symm
    have hvmemS : v ∈ G.commonNeighbors x y := ⟨hvx, hvy⟩
    -- Bridge the Classical/synthesized `Fintype` instance mismatch with
    -- `convert`, exactly as in the `Thirteen` section.
    have hone : Fintype.card
        {w : Fin (k * (k - 1) + 1) // w ∈ G.commonNeighbors x y} = 1 := by
      refine Fintype.card_eq_one_iff.mpr ⟨⟨v, hvmemS⟩, ?_⟩
      rintro ⟨w, hw⟩
      obtain ⟨hwx, hwy⟩ : G.Adj x w ∧ G.Adj y w := hw
      have hcom := common_le_one_of_not_containsC4 hC4 x y hxy
      have hwmem : w ∈ G.neighborFinset x ∩ G.neighborFinset y := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
        exact ⟨hwx, hwy⟩
      have hvmem : v ∈ G.neighborFinset x ∩ G.neighborFinset y := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
        exact ⟨hvx, hvy⟩
      exact Subtype.ext (Finset.card_le_one.mp hcom w hwmem v hvmem)
    convert hone using 2
  -- The friendship theorem: a politician exists — degree `k(k−1)`, not `k`.
  obtain ⟨v, hv⟩ := Theorems100.friendship_theorem hfriend
  have hdegBig : G.degree v = k * (k - 1) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have huniv : G.neighborFinset v = univ.erase v := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
      constructor
      · intro h
        exact ⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩
      · rintro ⟨hne, -⟩
        exact hv w (Ne.symm hne)
    rw [huniv, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  have hdeg := hdegk v
  have h2k : k * 2 ≤ k * (k - 1) := Nat.mul_le_mul_left k (by omega)
  omega

/-- **`f(k(k−1)+1) ≤ k` for every `k ≥ 3`** — infinitely many upper bounds at
the projective-plane parameters, each one vertex beyond the counting range
`n ≤ k(k−1)` of `minDegreeForC4_le_of_le_mul_pred`. -/
theorem minDegreeForC4_le_tight {k : ℕ} (hk : 3 ≤ k) :
    minDegreeForC4 (k * (k - 1) + 1) ≤ k := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_tight_minDegree hk G hmin

/-- Sanity check: the `k = 4` instance recovers `f(13) ≤ 4`. -/
example : minDegreeForC4 13 ≤ 4 := by
  simpa using minDegreeForC4_le_tight (k := 4) (by norm_num)

/-- **`f(21) ≤ 5`** — the first bound beyond the exact table `f(1..13)`:
`21 = 5·4+1` is the parameter of the projective plane of order `4`. -/
theorem minDegreeForC4_twentyone_le : minDegreeForC4 21 ≤ 5 := by
  simpa using minDegreeForC4_le_tight (k := 5) (by norm_num)

/-- **`f(31) ≤ 6`**: `31 = 6·5+1`, the parameter of the projective plane of
order `5`. -/
theorem minDegreeForC4_thirtyone_le : minDegreeForC4 31 ≤ 6 := by
  simpa using minDegreeForC4_le_tight (k := 6) (by norm_num)

end TightPoints

/-! ## `f(14) ≥ 4`: one more surgery rung — `f(14) ∈ {4, 5}`

The next lower-bound rung past the projective-plane threshold `f(13) = 4`.
Strategy identical to `f(13) ≥ 4`, one level up: materialise the `13`-vertex
witness as an explicit edge list (`petersen13` — the `a = 4, b = 9, c = 7`
surgery on `petersen12`, i.e. delete the spoke `4–9` and join the new vertex
`12` to `4`, `9`, `7`), certify it by `13`-vertex kernel checks, then apply
the **abstract** surgery with the configuration `a = 0, b = 4, c = 3`:

* the edges `0–4` (outer) and `4–3` (outer) each lie in no triangle — the
  only triangles of `petersen13` are `10–1–6`, `11–3–8`, `12–9–7`, one per
  surgery vertex, and they avoid both edges;
* `0 ≁ 3`, so the surgery hypotheses are met and the surgered graph on
  `14` vertices is `C₄`-free with minimum degree `≥ 3`.

No `14`-vertex graph is ever `decide`d.  The upper counting bound at `k = 5`
(`14 ≤ 5·4`) gives `f(14) ≤ 5`; pinning `f(14) = 4` (the literature value)
needs an upper-bound mechanism beyond the cherry count — `14` is not a tight
point `k(k−1)+1`, so the friendship-theorem argument does not apply.  Honest
result: `f(14) ∈ {4, 5}`. -/

section Fourteen

/-- The twenty-one edges of the `13`-vertex thrice-extended Petersen graph:
`petersen12Edges` with the spoke `(4, 9)` deleted and the new vertex `12`
joined to `4`, `9`, and `7` — the `f(13)` surgery, materialised. -/
def petersen13Edges : List (Fin 13 × Fin 13) :=
  [(1,2), (3,4), (4,0),
   (5,7), (7,9), (9,6), (6,8), (8,5),
   (0,5), (1,6), (2,7), (3,8),
   (10,0), (10,1), (10,6),
   (11,2), (11,3), (11,8),
   (12,4), (12,9), (12,7)]

/-- **A `13`-vertex `C₄`-free graph of minimum degree `3`**: the Petersen
graph after three vertex-adding surgeries.  Vertices `6`, `7`, `8` have
degree `4`; all other vertices have degree `3`. -/
def petersen13 : SimpleGraph (Fin 13) where
  Adj i j := (i, j) ∈ petersen13Edges ∨ (j, i) ∈ petersen13Edges
  symm.symm := fun _ _ h => Or.symm h
  loopless.irrefl := by decide

instance : DecidableRel petersen13.Adj := fun i j =>
  decidable_of_iff ((i, j) ∈ petersen13Edges ∨ (j, i) ∈ petersen13Edges) Iff.rfl

/-- Every vertex of `petersen13` has degree at least `3` — a `13`-vertex
kernel check. -/
theorem petersen13_degree : ∀ v, 3 ≤ petersen13.degree v := by decide

/-- **Every pair of distinct `petersen13` vertices has at most one common
neighbour** — the `13 × 13` kernel check certifying `C₄`-freeness. -/
theorem petersen13_common_le_one : ∀ x y : Fin 13, x ≠ y →
    (petersen13.neighborFinset x ∩ petersen13.neighborFinset y).card ≤ 1 := by
  decide

/-- **`f(14) ≥ 4`** — the abstract surgery applied to `petersen13` with the
configuration `a = 0, b = 4, c = 3`: the edges `0–4` and `4–3` are
triangle-free, `0 ≁ 3`, and all remaining hypotheses are `13`-vertex kernel
checks.  No `14`-vertex graph is ever `decide`d. -/
theorem four_le_minDegreeForC4_fourteen : 4 ≤ minDegreeForC4 14 := by
  have hab : petersen13.Adj 0 4 := by decide
  have hbc : petersen13.Adj 4 3 := by decide
  have hac : ¬ petersen13.Adj 0 3 := by decide
  have hane : (0 : Fin 13) ≠ 3 := by decide
  have htriab : ∀ z, petersen13.Adj 0 z → petersen13.Adj 4 z → False := by decide
  have htribc : ∀ z, petersen13.Adj 4 z → petersen13.Adj 3 z → False := by decide
  have hcommon := surgery_common_le_one hab hbc hac hane htriab htribc
    petersen13_common_le_one
  have hC4 : ¬ containsC4 (Fin 14) (surgeryFin petersen13 0 4 3) :=
    surgeryFin_not_containsC4 petersen13 0 4 3
      (not_containsC4_of_forall_common_le_one hcommon)
  have hdeg : 3 ≤ (surgeryFin petersen13 0 4 3).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    refine le_trans ?_ (surgeryFin_degree_ge petersen13 0 4 3 u)
    rcases h : finSuccEquiv 13 u with _ | x
    · exact surgery_degree_none (by decide) (by decide) (by decide)
    · exact le_trans (petersen13_degree x)
        (surgery_degree_some (by decide) x)
  exact four_le_minDegreeForC4_of_witness (by norm_num)
    (surgeryFin petersen13 0 4 3) hdeg hC4

/-- **`f(14) ∈ {4, 5}`**: the lower bound is the fourth surgery rung; the
upper bound is the counting bound at `k = 5` (`14 ≤ 5·4`).  `14` is not a
tight point `k(k−1)+1`, so the friendship-theorem pinning of `f(13)` does not
extend — closing this gap needs a genuine `ex(n; C₄)` upper-bound mechanism. -/
theorem minDegreeForC4_fourteen_mem :
    minDegreeForC4 14 = 4 ∨ minDegreeForC4 14 = 5 := by
  have hle : minDegreeForC4 14 ≤ 5 :=
    minDegreeForC4_le_of_le_mul_pred (by norm_num) (by norm_num)
  have hge := four_le_minDegreeForC4_fourteen
  omega

end Fourteen

end Erdos85
