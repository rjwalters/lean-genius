/-
Erdős Problem #653 — Elementary Lower-Bound Construction (companion)

Source: https://erdosproblems.com/653

This companion to `Erdos653Problem.lean` supplies the *lower-bound* side that the
main file leaves unproven. The main file states `g(n) ≤ n` and the sharper
`g(n) ≤ n - 1` (theorem `g_le_n_sub_one`), but its only lower bound is the deep
literature axiom `csizmadia_bound` (`g(n) > 0.7n`). Even the trivial lower bound
`g(n) ≥ 1` is only asserted in a docstring, never proved.

This file provides:

* `collinearConfig n` — the explicit `n`-point configuration
  `(0,0), (1,0), …, (n-1,0)` on the x-axis, with `collinearConfig_card` proving
  it has exactly `n` distinct points. This is the reusable construction needed by
  *any* elementary lower bound on `g`.
* `gSet`, `gSet_bddAbove`, `g_eq_sSup` — the supremum set that defines `g`, shown
  bounded above, so `le_csSup` applies.
* `g_ge_one` — the file's first *proved* lower bound: `g(n) ≥ 1` for `n ≥ 1`.
  (Witnessed by any nonempty configuration; needs no distance values.)
* `euclidDist_collinearPoint` — the verified fact that the distance between two
  x-axis points is `|i - j|`. This seeds the deferred sharper bound
  `g(n) ≥ ⌈n/2⌉`, whose remaining combinatorial steps (the distinct distances
  from the i-th collinear point number `max(i, n-1-i)`, giving `⌈n/2⌉` distinct
  R-values overall) are certified numerically in
  `research/problems/erdos-653-oq-01/verify_g_structure.py`.

The open conjecture `g(n) ≥ (1 - o(1))n` is OUT OF SCOPE and untouched here.
-/

import Mathlib.Tactic
import Proofs.Erdos653Problem

namespace Erdos653

open Finset Real

/-- The `n` collinear points `(0,0), (1,0), …, (n-1,0)` on the x-axis. -/
def collinearConfig (n : ℕ) : Finset (Fin 2 → ℝ) :=
  (Finset.range n).image (fun i => ![(i : ℝ), 0])

/-- The collinear configuration has exactly `n` distinct points. -/
theorem collinearConfig_card (n : ℕ) : (collinearConfig n).card = n := by
  unfold collinearConfig
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range n
  · intro a _ b _ hab
    have h0 : (a : ℝ) = (b : ℝ) := by
      have := congrFun hab 0
      simpa using this
    exact_mod_cast h0

/-- For every `n` there exists an `n`-point configuration (the collinear one). -/
theorem collinearConfig_exists (n : ℕ) :
    ∃ S : Finset (Fin 2 → ℝ), S.card = n :=
  ⟨collinearConfig n, collinearConfig_card n⟩

/-- The set of attainable distinct-R-value counts for `n`-point configurations.
`g n` is by definition the supremum of this set. -/
def gSet (n : ℕ) : Set ℕ :=
  { k : ℕ | ∃ S : Finset (Fin 2 → ℝ), S.card = n ∧ numDistinctRValues S = k }

/-- Membership in `gSet` is exactly the existence of a witnessing configuration. -/
theorem mem_gSet {n k : ℕ} :
    k ∈ gSet n ↔
      ∃ S : Finset (Fin 2 → ℝ), S.card = n ∧ numDistinctRValues S = k :=
  Iff.rfl

/-- `g n` is the supremum of `gSet n` (unfolds the definition of `g`). -/
theorem g_eq_sSup (n : ℕ) : g n = sSup (gSet n) := rfl

/-- The attainable-count set is bounded above by `n`: a configuration with `n`
points has at most `n` distinct R-values (`card_image_le`). -/
theorem gSet_bddAbove (n : ℕ) : BddAbove (gSet n) := by
  refine ⟨n, ?_⟩
  intro k hk
  obtain ⟨S, hcard, rfl⟩ := mem_gSet.mp hk
  unfold numDistinctRValues rValueSet
  calc (S.image (distinctDistCount S)).card
      ≤ S.card := Finset.card_image_le
    _ = n := hcard

/-- Any nonempty configuration has at least one distinct R-value. -/
theorem numDistinctRValues_pos {S : Finset (Fin 2 → ℝ)} (hS : S.Nonempty) :
    0 < numDistinctRValues S := by
  unfold numDistinctRValues rValueSet
  exact (hS.image (distinctDistCount S)).card_pos

/-- **First proved lower bound:** `g(n) ≥ 1` for `n ≥ 1`.

The main file asserts this only in a docstring ("Trivial Lower Bound: g(n) ≥ 1");
here it is an actual theorem. Witnessed by `collinearConfig n`, which is nonempty
for `n ≥ 1` and therefore contributes at least one distinct R-value to `gSet n`. -/
theorem g_ge_one (n : ℕ) (hn : 1 ≤ n) : 1 ≤ g n := by
  rw [g_eq_sSup]
  have hne : (collinearConfig n).Nonempty := by
    rw [← Finset.card_pos, collinearConfig_card]; omega
  have hmem : numDistinctRValues (collinearConfig n) ∈ gSet n :=
    mem_gSet.mpr ⟨collinearConfig n, collinearConfig_card n, rfl⟩
  have hpos : 1 ≤ numDistinctRValues (collinearConfig n) := numDistinctRValues_pos hne
  calc 1 ≤ numDistinctRValues (collinearConfig n) := hpos
    _ ≤ sSup (gSet n) := le_csSup (gSet_bddAbove n) hmem

/-- **Distance seed for the `⌈n/2⌉` bound.** The Euclidean distance between two
x-axis points `(i,0)` and `(j,0)` is `|i - j|`. The distinct distances from the
`i`-th collinear point therefore number `max(i, n-1-i)`, and the distinct
R-values across the configuration number `⌈n/2⌉` (certified numerically; the
combinatorial Lean proof is the deferred next step). -/
theorem euclidDist_collinearPoint (i j : ℝ) :
    euclidDist ![i, 0] ![j, 0] = |i - j| := by
  unfold euclidDist
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show ((0 : ℝ) - 0) = 0 by ring, show (0 : ℝ) ^ 2 = 0 by ring, add_zero,
    Real.sqrt_sq_eq_abs]

end Erdos653
