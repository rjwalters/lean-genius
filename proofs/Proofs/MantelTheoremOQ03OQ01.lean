/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Sharpness of the Minimum-Degree Bound in Mantel's Theorem

The minimum-degree corollary of Mantel's theorem (`MantelTheoremOQ03.lean`) states that every
triangle-free (`CliqueFree 3`) simple graph on `n ≥ 1` vertices has a vertex of degree at most
`⌊n/2⌋`. This file certifies that the bound `⌊n/2⌋` is **sharp**: it cannot be lowered.

The witness is the Turán graph `turanGraph n 2`, the balanced complete bipartite graph
`K_{⌈n/2⌉, ⌊n/2⌋}` realized on `Fin n` by the residue-mod-2 partition. We prove:

* `turanGraphTwo_cliqueFree_three` : `turanGraph n 2` is triangle-free.
* `turanTwo_degree_eq` : the degree of a vertex `v` is exactly `⌊n/2⌋` if `v` is even and
  `⌈n/2⌉` if `v` is odd (the size of the *opposite* residue class).
* `turanGraphTwo_minDegree` : the minimum degree of `turanGraph n 2` is exactly `⌊n/2⌋`.
* `turanGraphTwo_forall_degree_ge` : **every** vertex has degree at least `⌊n/2⌋`.

The last statement is the sharpness certificate: a triangle-free graph in which no vertex has
degree below `⌊n/2⌋`, so the threshold in `exists_degree_le_card_div_two` is best possible — it
cannot be replaced by `⌊n/2⌋ − 1`.

## Approach

In `turanGraph n 2` a vertex `v` is adjacent to `w` iff `v % 2 ≠ w % 2`, so the neighbourhood of `v`
is exactly the *opposite* residue class. Counting residues mod 2 in `Fin n`:

* `#{ w : Fin n | w % 2 = 0 } = ⌈n/2⌉ = (n + 1)/2`,
* `#{ w : Fin n | w % 2 = 1 } = ⌊n/2⌋ = n/2`,

which we obtain from `Nat.count` (with `count_succ` + `omega`) and the `Fin.valEmbedding`
bridge between `Finset.univ.filter` over `Fin n` and `Finset.range n`. Since both class sizes are
`≥ ⌊n/2⌋` and the even class achieves `⌊n/2⌋`, the minimum degree is exactly `⌊n/2⌋`.
-/

open Finset SimpleGraph

namespace MantelMinDegreeSharp

/-- Counting `k < n` with `k % 2 = 1` gives `⌊n/2⌋`. -/
lemma count_mod_two_one (n : ℕ) : Nat.count (fun k => k % 2 = 1) n = n / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.count_succ, ih]
    by_cases h : k % 2 = 1
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- Counting `k < n` with `k % 2 = 0` gives `⌈n/2⌉ = (n+1)/2`. -/
lemma count_mod_two_zero (n : ℕ) : Nat.count (fun k => k % 2 = 0) n = (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.count_succ, ih]
    by_cases h : k % 2 = 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- Bridge: the number of `w : Fin n` with `w % 2 = c` equals `Nat.count (· % 2 = c) n`.
Transferred along `Fin.valEmbedding : Fin n ↪ ℕ`, whose image of `univ` is `range n`. -/
lemma card_fin_mod_two (n c : ℕ) :
    (Finset.univ.filter (fun w : Fin n => (w : ℕ) % 2 = c)).card
      = Nat.count (fun k => k % 2 = c) n := by
  rw [Nat.count_eq_card_filter_range, ← congrFun Nat.Iio_eq_range n,
    ← Fin.map_valEmbedding_univ, Finset.filter_map, Finset.card_map]
  rfl

/-- The degree of a vertex `v` in `turanGraph n 2` is the size of the *opposite* residue class:
`⌊n/2⌋` if `v` is even, `⌈n/2⌉ = (n+1)/2` if `v` is odd. -/
theorem turanTwo_degree_eq (n : ℕ) (v : Fin n) :
    (turanGraph n 2).degree v = if (v : ℕ) % 2 = 0 then n / 2 else (n + 1) / 2 := by
  have hcard : (turanGraph n 2).degree v
      = (Finset.univ.filter (fun w : Fin n => (v : ℕ) % 2 ≠ (w : ℕ) % 2)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    congr 1
  rw [hcard]
  by_cases h : (v : ℕ) % 2 = 0
  · rw [if_pos h]
    have heq : (Finset.univ.filter (fun w : Fin n => (v : ℕ) % 2 ≠ (w : ℕ) % 2))
        = (Finset.univ.filter (fun w : Fin n => (w : ℕ) % 2 = 1)) := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [heq, card_fin_mod_two, count_mod_two_one]
  · rw [if_neg h]
    have heq : (Finset.univ.filter (fun w : Fin n => (v : ℕ) % 2 ≠ (w : ℕ) % 2))
        = (Finset.univ.filter (fun w : Fin n => (w : ℕ) % 2 = 0)) := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [heq, card_fin_mod_two, count_mod_two_zero]

/-- `turanGraph n 2` is triangle-free (`CliqueFree 3`). -/
theorem turanGraphTwo_cliqueFree_three (n : ℕ) : (turanGraph n 2).CliqueFree 3 :=
  turanGraph_cliqueFree (by norm_num)

/-- **Every** vertex of `turanGraph n 2` has degree at least `⌊n/2⌋` (for `n ≥ 1`).
This is the sharpness certificate: no vertex drops below the Mantel min-degree threshold. -/
theorem turanGraphTwo_forall_degree_ge (n : ℕ) (v : Fin n) :
    n / 2 ≤ (turanGraph n 2).degree v := by
  rw [turanTwo_degree_eq]
  split <;> omega

/-- **Sharpness of the Mantel minimum-degree bound.** The minimum degree of `turanGraph n 2`
(for `n ≥ 1`) is exactly `⌊n/2⌋`. Combined with `turanGraphTwo_cliqueFree_three`, this exhibits a
triangle-free graph whose minimum degree equals the bound of `exists_degree_le_card_div_two`,
proving that bound cannot be improved. -/
theorem turanGraphTwo_minDegree (n : ℕ) (hn : 0 < n) :
    (turanGraph n 2).minDegree = n / 2 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · -- the even vertex `0` has degree exactly `⌊n/2⌋`, bounding the minimum from above
    have h0 : (turanGraph n 2).degree ⟨0, hn⟩ = n / 2 := by
      rw [turanTwo_degree_eq]; simp
    calc (turanGraph n 2).minDegree
        ≤ (turanGraph n 2).degree ⟨0, hn⟩ := SimpleGraph.minDegree_le_degree _ _
      _ = n / 2 := h0
  · -- every degree is at least `⌊n/2⌋`, bounding the minimum from below
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    exact turanGraphTwo_forall_degree_ge n

/-- Packaged sharpness statement: `turanGraph n 2` is triangle-free **and** has minimum degree
exactly `⌊n/2⌋`, certifying the Mantel min-degree corollary bound is sharp. -/
theorem mantel_minDegree_bound_sharp (n : ℕ) (hn : 0 < n) :
    (turanGraph n 2).CliqueFree 3 ∧ (turanGraph n 2).minDegree = n / 2 :=
  ⟨turanGraphTwo_cliqueFree_three n, turanGraphTwo_minDegree n hn⟩

end MantelMinDegreeSharp
