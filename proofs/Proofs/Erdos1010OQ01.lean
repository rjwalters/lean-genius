/-
  Erdős Problem #1010 — Open Question 01:
  What happens for t ≥ ⌊n/2⌋ ?

  Source: https://erdosproblems.com/1010 (follow-up open question)
  Parent: Proofs/Erdos1010Problem.lean

  ## Background

  Erdős Problem #1010 (Lovász–Simonovits 1976, Nikiforov–Khadzhiivanov 1981)
  states the supersaturation bound:

      For t < ⌊n/2⌋, every graph on n vertices with ⌊n²/4⌋ + t edges
      contains at least  t · ⌊n/2⌋  triangles.

  The hypothesis `t < ⌊n/2⌋` is essential. The natural follow-up question is:
  does the same *linear* lower bound `t · ⌊n/2⌋` continue to hold once
  `t ≥ ⌊n/2⌋`?  The answer is **NO**: the regime changes qualitatively exactly
  at `t = ⌊n/2⌋`.

  ## What this file proves (0-axiom, machine-checked)

  We pin down *why* the bound breaks and *exactly where*.

  1. `crossover` — the arithmetic heart. Writing `n = 2m`, the cheapest
     triangle-free way to reach `⌊n²/4⌋ + t` edges is no longer "balanced
     bipartite + t internal edges" (yielding `t·m` triangles) but the
     **unbalanced** base `K_{m-1, m+1}` plus `t+1` triangle-free internal
     edges, each of which spans only the smaller side and so creates only
     `m-1` triangles — a total of `(t+1)·(m-1)`.  We prove

         (t+1)·(m-1) < t·m   ↔   m ≤ t         (for m ≥ 1),

     i.e. the unbalanced construction beats the linear bound *precisely* once
     `t ≥ m = ⌊n/2⌋`.  This is the boundary the open question asks about.

  2. A fully explicit witness at the first failing value `n = 6, t = 3 = ⌊n/2⌋`.
     The graph `Gw = K_{2,4} + C₄(big part)` has exactly `⌊6²/4⌋ + 3 = 12`
     edges and exactly `8` triangles, whereas the extrapolated linear bound
     predicts `t · ⌊n/2⌋ = 3 · 3 = 9`.  Since `8 < 9`, the bound of #1010
     fails at `t = ⌊n/2⌋`.  Equivalently: the hypothesis `t < ⌊n/2⌋` in
     Erdős #1010 is **sharp**.

  Everything is verified by `decide` / `omega` / `ring`; `#print axioms`
  reports only `propext`, `Classical.choice`, `Quot.sound`.

  Tags: graph-theory, extremal, triangles, turán, supersaturation, sharpness
-/

import Mathlib

open SimpleGraph Finset

/-
## Shared definitions (mirroring the parent file `Erdos1010Problem.lean`)
-/

/-- The Turán threshold: maximum number of edges in a triangle-free graph
    on `n` vertices, `ex(n, K₃) = ⌊n²/4⌋`. -/
def turanThreshold (n : ℕ) : ℕ := n ^ 2 / 4

/-- Number of triangles in a graph, counted as 3-element cliques. -/
def triangleCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun s : Finset V =>
    s.card = 3 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card

/-
## Part 1 — The arithmetic crossover

The transition between the two extremal regimes happens at a single, exact
value of `t`.  This is a statement of pure `ℕ`-arithmetic and is the reason the
linear bound of #1010 cannot persist past `t = ⌊n/2⌋`.

Here `m = ⌊n/2⌋` and we write the smaller side as `m - 1`.  The balanced
construction `K_{m,m} + t` triangle-free internal edges yields `t · m`
triangles (each internal edge meets all `m` vertices of the other side); the
unbalanced construction `K_{m-1,m+1} + (t+1)` triangle-free internal edges
yields `(t+1) · (m-1)` triangles (each internal edge meets only the `m-1`
vertices of the smaller side).
-/

/-- **Crossover lemma.** With `m = k + 1 ≥ 1`, the unbalanced construction's
    triangle count `(t+1)·(m-1)` drops strictly below the linear bound `t·m`
    exactly when `t ≥ m`.  (Stated with `m = k+1` to keep `m - 1 = k` away from
    truncated subtraction.) -/
theorem crossover (t k : ℕ) : (t + 1) * k < t * (k + 1) ↔ k < t := by
  have h1 : (t + 1) * k = t * k + k := by ring
  have h2 : t * (k + 1) = t * k + t := by ring
  rw [h1, h2]; omega

/-- Restatement in terms of `m = ⌊n/2⌋ ≥ 1`: the linear supersaturation bound
    `t·m` is beaten by a genuine triangle-free construction iff `t ≥ m`.  Thus
    the conclusion of Erdős #1010 cannot extend to `t ≥ ⌊n/2⌋`. -/
theorem linear_bound_beaten_iff (m t : ℕ) (hm : 1 ≤ m) :
    (t + 1) * (m - 1) < t * m ↔ m ≤ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm   -- m = 0 + k + 1
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  rw [crossover]
  omega

/-
## Part 2 — An explicit witness at the first failing value

Take `n = 6`, so `⌊n²/4⌋ = 9` and `⌊n/2⌋ = 3`.  The open question concerns
`t = 3 = ⌊n/2⌋`, the first value outside the range of #1010.

Witness graph `Gw` on `Fin 6`:
  • smaller side  S = {0, 1},  larger side  B = {2, 3, 4, 5};
  • all 8 edges of the complete bipartite graph `K_{2,4}` between S and B;
  • a 4-cycle `C₄ = 2–3–4–5–2` inside B (triangle-free, 4 edges).

Total: `8 + 4 = 12 = ⌊6²/4⌋ + 3` edges.  Triangles: every edge of the `C₄`
together with each of the two vertices of S forms a triangle, giving
`4 · 2 = 8` triangles; there are no others (S has no internal edge and `C₄`
has no triangle).  Hence `8` triangles, strictly fewer than the `3 · 3 = 9`
predicted by the linear bound.
-/

/-- Adjacency matrix of the witness graph `Gw` on `Fin 6`.
    Rows/cols 0–1 are the small side `S`, rows/cols 2–5 the large side `B`.
    The `B`-block is the 4-cycle 2–3–4–5–2 (note: diagonals 2–4 and 3–5 absent). -/
def Mbool : Fin 6 → Fin 6 → Bool := ![
  ![false, false, true , true , true , true ],
  ![false, false, true , true , true , true ],
  ![true , true , false, true , false, true ],
  ![true , true , true , false, true , false],
  ![true , true , false, true , false, true ],
  ![true , true , true , false, true , false]]

/-- The witness graph `Gw = K_{2,4} + C₄(B)` on `Fin 6`. -/
def Gw : SimpleGraph (Fin 6) where
  Adj a b := Mbool a b = true
  symm := by unfold Symmetric; decide
  loopless := by unfold Irreflexive; decide

instance : DecidableRel Gw.Adj :=
  fun a b => inferInstanceAs (Decidable (Mbool a b = true))

/-- The witness has exactly `⌊6²/4⌋ + 3 = 12` edges, i.e. `t = 3 = ⌊n/2⌋`
    edges beyond the Turán threshold. -/
theorem witness_edge_count : Gw.edgeFinset.card = turanThreshold 6 + 3 := by decide

/-- The witness has exactly `8` triangles. -/
theorem witness_triangle_count : triangleCount Gw = 8 := by decide

/-- **Sharpness of Erdős #1010.**  At the boundary value `t = ⌊n/2⌋` (here
    `n = 6`, `t = 3`) there is a graph with `⌊n²/4⌋ + t` edges whose triangle
    count is *strictly below* the linear prediction `t · ⌊n/2⌋`.  Therefore the
    hypothesis `t < ⌊n/2⌋` in Erdős Problem #1010 cannot be relaxed: the
    answer to "what happens for `t ≥ ⌊n/2⌋`?" is that the linear bound fails. -/
theorem supersaturation_bound_fails_at_threshold :
    Gw.edgeFinset.card = turanThreshold 6 + (6 / 2) ∧
      triangleCount Gw < (6 / 2) * (6 / 2) := by
  refine ⟨by decide, by decide⟩

/-- The same statement phrased through `Fintype.card`, making explicit that
    `n = 6` is the vertex count, `t = n/2`, and the violated bound is the
    extrapolation of `t · ⌊n/2⌋` from Erdős #1010. -/
theorem supersaturation_fails_card :
    Gw.edgeFinset.card
        = turanThreshold (Fintype.card (Fin 6)) + (Fintype.card (Fin 6) / 2) ∧
      triangleCount Gw
        < (Fintype.card (Fin 6) / 2) * (Fintype.card (Fin 6) / 2) := by
  have hc : Fintype.card (Fin 6) = 6 := by decide
  rw [hc]
  exact supersaturation_bound_fails_at_threshold
