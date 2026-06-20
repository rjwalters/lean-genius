/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Turán's Theorem — the Clean `K_{r+1}`-Free Edge Bound Generalizing Mantel

Turán's theorem (1941), the cornerstone of extremal graph theory, states:

> A simple graph on `n` vertices with no clique of size `r + 1` (`CliqueFree (r + 1)`) has at
> most `(1 - 1/r) · n²/2` edges.

Mantel's theorem (the gallery entry `mantel-theorem`) is the special case `r = 2`, giving the
triangle-free bound `⌊n²/4⌋`.

## What Mathlib provides, and what this file adds

`Mathlib.Combinatorics.SimpleGraph.Extremal.Turan` develops the structural side of the theorem.
Concretely it gives:

* `SimpleGraph.CliqueFree.card_edgeFinset_le` — the *exact* bound for an arbitrary `K_{r+1}`-free
  graph, in the bookkeeping form
  `#G.edgeFinset ≤ (n² - (n % r)²)·(r-1)/(2r) + (n % r).choose 2`;
* `SimpleGraph.card_edgeFinset_turanGraph` — the exact edge count of the extremal Turán graph;
* `SimpleGraph.mul_card_edgeFinset_turanGraph_le` — the *clean* bound
  `2r · #(turanGraph n r).edgeFinset ≤ (r-1)·n²`, but **only for the Turán graph itself**.

What is *not* directly in Mathlib is the clean closed form for an **arbitrary** `K_{r+1}`-free
graph — the statement one actually cites as "Turán's theorem". This file assembles it:

* `turan_two_mul_card_edgeFinset_le` : `2r · #G.edgeFinset ≤ (r-1)·n²` for every `K_{r+1}`-free `G`
  (the integer form of `e(G) ≤ (1 - 1/r)·n²/2`);
* `turan_card_edgeFinset_le_rat` : the literal textbook rational bound
  `#G.edgeFinset ≤ (1 - 1/r)·n²/2`.

It then derives the gallery's Mantel bound as the literal `r = 2` corollary, formally linking the
two entries:

* `mantel_four_mul_card_edgeFinset_le` : `4 · #G.edgeFinset ≤ n²` for triangle-free `G`;
* `mantel_card_edgeFinset_le_of_turan` : the floor form `#G.edgeFinset ≤ ⌊n²/4⌋`, re-derived from
  the general theorem rather than from the `r = 2` arithmetic directly.

The bound is sharp: the Turán graph `turanGraph n r` attains the exact count, recorded in
`turan_card_edgeFinset_le_rat_tight`.
-/

open Finset SimpleGraph

namespace TuranEdgeBound

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Turán's theorem (clean integer form).** A `K_{r+1}`-free simple graph on `n` vertices
satisfies `2r · e(G) ≤ (r-1)·n²`. This is the integer reformulation of the textbook bound
`e(G) ≤ (1 - 1/r)·n²/2`.

We chain Mathlib's *exact* bound for `G` (`CliqueFree.card_edgeFinset_le`, whose right-hand side is
literally the edge count of the extremal Turán graph) into Mathlib's *clean* bound for the Turán
graph (`mul_card_edgeFinset_turanGraph_le`). -/
theorem turan_two_mul_card_edgeFinset_le {r : ℕ} (cf : G.CliqueFree (r + 1)) :
    2 * r * G.edgeFinset.card ≤ (r - 1) * (Fintype.card V) ^ 2 := by
  calc
    2 * r * G.edgeFinset.card
        ≤ 2 * r * (turanGraph (Fintype.card V) r).edgeFinset.card := by
          gcongr
          rw [card_edgeFinset_turanGraph]
          exact cf.card_edgeFinset_le
    _ ≤ (r - 1) * (Fintype.card V) ^ 2 := mul_card_edgeFinset_turanGraph_le

/-- **Turán's theorem (textbook rational form).** A `K_{r+1}`-free simple graph on `n` vertices
with `r ≥ 1` satisfies `e(G) ≤ (1 - 1/r)·n²/2`. -/
theorem turan_card_edgeFinset_le_rat {r : ℕ} (hr : 1 ≤ r) (cf : G.CliqueFree (r + 1)) :
    (G.edgeFinset.card : ℚ) ≤ (1 - 1 / r) * (Fintype.card V) ^ 2 / 2 := by
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hr
  have hrne : (r : ℚ) ≠ 0 := ne_of_gt hr0
  have key : (G.edgeFinset.card : ℚ) * (2 * r) ≤ ((r : ℚ) - 1) * (Fintype.card V) ^ 2 := by
    calc
      (G.edgeFinset.card : ℚ) * (2 * r)
          = ((2 * r * G.edgeFinset.card : ℕ) : ℚ) := by push_cast; ring
      _ ≤ (((r - 1) * (Fintype.card V) ^ 2 : ℕ) : ℚ) := by
            exact_mod_cast turan_two_mul_card_edgeFinset_le G cf
      _ = ((r : ℚ) - 1) * (Fintype.card V) ^ 2 := by
            rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_pow]; push_cast; ring
  rw [show (1 - 1 / (r : ℚ)) * (Fintype.card V) ^ 2 / 2
        = ((r : ℚ) - 1) * (Fintype.card V) ^ 2 / (2 * r) by field_simp <;> ring,
      le_div_iff₀ (by positivity)]
  exact key

/-- **Sharpness.** For every `n` and `r ≥ 1` the Turán graph `turanGraph n r` is `K_{r+1}`-free and
its edge count meets the rational bound with the floor rounding, so `turan_card_edgeFinset_le_rat`
cannot be improved in general. -/
theorem turan_card_edgeFinset_le_rat_tight {n r : ℕ} (hr : 1 ≤ r) :
    (turanGraph n r).CliqueFree (r + 1) ∧
      ((turanGraph n r).edgeFinset.card : ℚ)
        ≤ (1 - 1 / r) * (Fintype.card (Fin n)) ^ 2 / 2 :=
  ⟨turanGraph_cliqueFree (by omega), turan_card_edgeFinset_le_rat _ hr (turanGraph_cliqueFree (by omega))⟩

/-! ### Mantel's theorem as the `r = 2` corollary -/

/-- **Mantel's theorem (clean form), as the `r = 2` case of Turán.** A triangle-free
(`K₃`-free) simple graph on `n` vertices satisfies `4 · e(G) ≤ n²`. -/
theorem mantel_four_mul_card_edgeFinset_le (h : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  have := turan_two_mul_card_edgeFinset_le G (r := 2) h
  simpa using this

/-- **Mantel's theorem (floor form), re-derived from Turán.** A triangle-free simple graph on `n`
vertices has at most `⌊n²/4⌋` edges. This recovers the gallery's `mantel_card_edgeFinset_le` from
the general clean bound rather than from the `r = 2` Turán arithmetic. -/
theorem mantel_card_edgeFinset_le_of_turan (h : G.CliqueFree 3) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have := mantel_four_mul_card_edgeFinset_le G h
  omega

end TuranEdgeBound
