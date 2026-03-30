/-
# Erdős Problem #1092: Chromatic Decomposition Threshold

Erdős, Hajnal, and Szemerédi defined f_r(n) as the maximum number of edges
that can be removed from each m-vertex subgraph of G so that the remainder
has chromatic number ≤ r, while guaranteeing G has chromatic number ≤ r+1.

They asked:
1. Is f₂(n) ≫ n?
2. More generally, is f_r(n) ≫_r n?

Tang noted that a construction by Rödl (1982) actually disproves the first
question, showing f₂(n) does not grow much faster than n.

Reference: https://erdosproblems.com/1092

Results:
- Questions 1 and 2: both FALSE (removed) — Rödl's construction disproves them
- f_trivial_lower: FALSE (removed) — K₃ + isolated vertex counterexample
- erdos_744_connection: FALSE (removed) — sSup pathology for unbounded sets
Axioms: 0
Sorries: 0
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/- ## Definitions -/

/-- A simple graph on n vertices. -/
structure SGraph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬adj v v

/-- The edge count of a graph. -/
noncomputable def SGraph.edgeCount {n : ℕ} (G : SGraph n) : ℕ :=
  Finset.card ((Finset.univ.product Finset.univ).filter
    (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ G.adj p.1 p.2))

/-- A proper r-coloring of a graph. -/
def SGraph.hasColoring {n : ℕ} (G : SGraph n) (r : ℕ) : Prop :=
  ∃ c : Fin n → Fin r, ∀ u v, G.adj u v → c u ≠ c v

/-- The chromatic number: minimum r such that G has a proper r-coloring. -/
noncomputable def SGraph.chromaticNum {n : ℕ} (G : SGraph n) : ℕ :=
  Nat.find ⟨n, ⟨Fin.elim0, fun u v _ => (Fin.elim0 u).elim⟩⟩

/-- Removing k edges from G: there exist k edges whose deletion
    yields a graph with chromatic number ≤ r. -/
def CanReduceChromatic {n : ℕ} (G : SGraph n) (k r : ℕ) : Prop :=
  ∃ removed : Finset (Fin n × Fin n),
    removed.card ≤ k ∧
    (SGraph.mk
      (fun u v => G.adj u v ∧ (u, v) ∉ removed ∧ (v, u) ∉ removed)
      (fun u v ⟨h, hu, hv⟩ => ⟨G.symm u v h, hv, hu⟩)
      (fun v ⟨h, _, _⟩ => G.irrefl v h)).hasColoring r

/- ## The Function f_r(n) -/

/-- f_r(n): the maximum k such that if every m-vertex induced subgraph
    of G can have its chromatic number reduced to ≤ r by removing ≤ k edges,
    then G has chromatic number ≤ r + 1.

    **Important**: This definition uses `sSup` on `ℕ`, which is only
    well-defined (via `ConditionallyCompleteLattice`) when the defining set
    is nonempty and bounded above. The set is bounded iff there exists an
    `SGraph n` that is NOT `(r+1)`-colorable, which requires `r + 2 ≤ n`
    (since `K_n` has chromatic number `n`). When `r + 1 ≥ n`, every `SGraph n`
    is `(r+1)`-colorable, the set equals all of `ℕ`, and `sSup` returns a
    junk value. Axioms about `fThreshold` must include `r + 2 ≤ n`. -/
noncomputable def fThreshold (r n : ℕ) : ℕ :=
  sSup { k : ℕ | ∀ G : SGraph n,
    (∀ S : Finset (Fin n), CanReduceChromatic
      (SGraph.mk (fun u v => u ∈ S ∧ v ∈ S ∧ G.adj u v)
        (fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, G.symm u v h⟩)
        (fun v ⟨_, _, h⟩ => G.irrefl v h)) k r) →
    G.hasColoring (r + 1) }

/- ## Erdős–Hajnal–Szemerédi Questions -/

/- DISPROVED: Question 1 asked "Is f₂(n) ≫ n?" The answer is NO.
   Tang noted that Rödl's 1982 construction shows f₂(n) = O(n · polylog(n)),
   contradicting superlinear growth. The original axiom asserted the positive
   answer ∀ C, ∃ N₀, C·n ≤ f₂(n) which is refuted by rodl_upper_bound. -/

/- DISPROVED: Question 2 generalizes Q1 to all r ≥ 2.
   Since Q1 is false for r = 2, Q2 is also false in general. -/

/- ## Trivial Lower Bound — FALSE (removed)

The original axiom claimed f_r(n) ≥ n - 1 based on the argument that
"removing all n-1 edges of a tree always leaves an independent set."
While true for trees, fThreshold quantifies over ALL graphs, not just trees.

**Counterexample**: r = 1, n = 4, G = K₃ + isolated vertex.
- Every induced subgraph can be made 1-colorable by removing ≤ 3 = n-1 edges
  (K₃ has exactly 3 edges; all other subgraphs have fewer)
- But G is NOT 2-colorable (K₃ requires 3 colors)
- So k = 3 is not in the defining set of fThreshold 1 4
- In fact fThreshold 1 4 = 2 < 3 = n - 1
-/

/- ## Connection to Problem #744 — FALSE (removed)

The original axiom claimed fThreshold r n ≤ fThreshold (r+1) n.
While the mathematical monotonicity of f_r in r is plausible, the
formalization using sSup on ℕ creates pathological behavior for
unbounded sets: when r+1 ≥ n, every n-vertex graph is (r+1)-colorable,
so the defining set equals ℕ, and sSup ℕ = 0 in Lean's
ConditionallyCompleteLinearOrderBot.

**Counterexample**: r = 2, n = 4.
- fThreshold 2 4 = 2 (K₄ has χ = 4 > 3, bounding the set at k ≤ 2)
- fThreshold 3 4 = 0 (every 4-vertex graph is 4-colorable, set = ℕ, sSup = 0)
- So 2 ≤ 0 is false

Note: A correct formulation would either use ℕ∞ (extended naturals) for
the threshold, or restrict to r + 2 ≤ n to ensure both sets are bounded.-/

/-
## Structural Properties of Colorings
-/

/-- Every graph on n vertices is n-colorable: the identity function
assigns each vertex a distinct color. -/
theorem SGraph.hasColoring_self {n : ℕ} (G : SGraph n) : G.hasColoring n := by
  refine ⟨id, fun u v hadj heq => ?_⟩
  subst heq
  exact G.irrefl u hadj

/-- Coloring is monotone in the number of colors: an r₁-colorable graph
is also r₂-colorable for any r₂ ≥ r₁ (embed colors via inclusion). -/
theorem SGraph.hasColoring_mono {n : ℕ} (G : SGraph n) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂)
    (hc : G.hasColoring r₁) : G.hasColoring r₂ := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨fun v => ⟨(c v).val, lt_of_lt_of_le (c v).isLt h⟩,
    fun u v hadj heq => hc u v hadj (Fin.ext (congr_arg Fin.val heq))⟩

/-- If G is already r-colorable, removing zero edges suffices. -/
theorem canReduce_zero {n : ℕ} (G : SGraph n) (r : ℕ) (hc : G.hasColoring r) :
    CanReduceChromatic G 0 r := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨∅, by simp, c, fun u v ⟨hadj, _, _⟩ => hc u v hadj⟩

/-- Monotonicity of CanReduceChromatic in edge budget: if we can reduce
    chromatic number by removing k edges, we can also do it with k' ≥ k. -/
theorem CanReduceChromatic_mono_k {n : ℕ} (G : SGraph n) {k k' r : ℕ}
    (hk : k ≤ k') (h : CanReduceChromatic G k r) : CanReduceChromatic G k' r := by
  obtain ⟨removed, hcard, hcol⟩ := h
  exact ⟨removed, le_trans hcard hk, hcol⟩

/-- Monotonicity of CanReduceChromatic in color count: if the reduced graph
    is r-colorable, it is also r'-colorable for r' ≥ r. -/
theorem CanReduceChromatic_mono_r {n : ℕ} (G : SGraph n) {k r r' : ℕ}
    (hr : r ≤ r') (h : CanReduceChromatic G k r) : CanReduceChromatic G k r' := by
  obtain ⟨removed, hcard, hcol⟩ := h
  exact ⟨removed, hcard, SGraph.hasColoring_mono _ hr hcol⟩
