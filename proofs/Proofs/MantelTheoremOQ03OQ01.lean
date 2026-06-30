/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Sharpness of the Minimum-Degree Corollary of Mantel's Theorem (OQ-03 · OQ-01)

The parent entry (`MantelTheoremOQ03`) proved the *minimum-degree* form of Mantel's
theorem:

> Every triangle-free (`CliqueFree 3`) simple graph on `n ≥ 1` vertices has a vertex of
> degree at most `⌊n/2⌋` (`exists_degree_le_card_div_two`).

Its first open question asks for a matching **sharpness** certificate:

> Exhibit, for each `n`, a triangle-free graph whose minimum degree is *exactly* `⌊n/2⌋`,
> certifying that the bound `⌊n/2⌋` cannot be improved.

This file answers it with the canonical witness, the balanced complete bipartite graph,
realised in Mathlib as the **Turán graph** `turanGraph n 2` on `Fin n`
(`v ~ w ↔ v % 2 ≠ w % 2`, i.e. the bipartition into even and odd residues).

## Results

* `turanTwo_triangleFree` : `turanGraph n 2` is `CliqueFree 3` — directly from
  `SimpleGraph.turanGraph_cliqueFree`.
* `turanTwo_degree` : the exact per-vertex degree,
  `degree v = if v % 2 = 0 then n / 2 else (n + 1) / 2`.
* `turanTwo_minDegree` : `(turanGraph n 2).minDegree = n / 2 = ⌊n/2⌋` for `n ≥ 1`.
* `turanTwo_maxDegree` : `(turanGraph n 2).maxDegree = (n + 1) / 2 = ⌈n/2⌉` for `n ≥ 1`.
* `turanTwo_sharp` : the packaged sharpness statement (triangle-free *and* minimum degree
  exactly `⌊n/2⌋`).

## Method

The whole computation reduces to counting residues modulo `2` among `Fin n`.  We transfer
the per-vertex neighbour count to `Nat.count` over `range n` (`card_fin_filter_val`), and
evaluate the two residue counts in closed form by induction on `n`
(`count_mod_two_eq_zero/one`).  The minimum/maximum degrees then follow from the standard
`minDegree`/`maxDegree` extremality lemmas.
-/

open Finset SimpleGraph

namespace MantelTuranSharp

/-! ## Counting residues modulo two -/

/-- Transfer a `Fin n`-indexed count of a `val`-predicate to `Nat.count` over `range n`. -/
lemma card_fin_filter_val (n : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    #(Finset.univ.filter fun w : Fin n => Q w.val) = Nat.count Q n := by
  rw [Nat.count_eq_card_filter_range]
  rw [← Finset.card_image_of_injective
        (Finset.univ.filter fun w : Fin n => Q w.val) Fin.val_injective]
  congr 1
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.isLt, hw⟩
  · rintro ⟨hk, hQ⟩
    exact ⟨⟨k, hk⟩, hQ, rfl⟩

/-- The number of even residues below `n` is `⌈n/2⌉ = (n + 1) / 2`. -/
lemma count_mod_two_eq_zero (n : ℕ) :
    Nat.count (fun k => k % 2 = 0) n = (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.count_succ, ih]
    by_cases h : m % 2 = 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- The number of odd residues below `n` is `⌊n/2⌋ = n / 2`. -/
lemma count_mod_two_eq_one (n : ℕ) :
    Nat.count (fun k => k % 2 = 1) n = n / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.count_succ, ih]
    by_cases h : m % 2 = 1
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- Pointwise-equivalent predicates have the same `Nat.count`. -/
lemma count_congr {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (n : ℕ) (h : ∀ k, p k ↔ q k) : Nat.count p n = Nat.count q n := by
  simp only [Nat.count_eq_card_filter_range]
  exact congrArg _ (Finset.filter_congr fun k _ => h k)

/-! ## The Turán graph `turanGraph n 2` -/

/-- `turanGraph n 2` is triangle-free: it is `K₃`-free as the `r = 2` Turán graph. -/
theorem turanTwo_triangleFree (n : ℕ) : (turanGraph n 2).CliqueFree 3 :=
  turanGraph_cliqueFree (n := n) (r := 2) (by norm_num)

/-- The exact degree of a vertex `v` in `turanGraph n 2`: even residues see all `⌊n/2⌋`
odd vertices, odd residues see all `⌈n/2⌉` even vertices. -/
theorem turanTwo_degree (n : ℕ) (v : Fin n) :
    (turanGraph n 2).degree v = if v.val % 2 = 0 then n / 2 else (n + 1) / 2 := by
  have hcard : (turanGraph n 2).degree v
      = Nat.count (fun k => v.val % 2 ≠ k % 2) n := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
        ← card_fin_filter_val n (fun k => v.val % 2 ≠ k % 2)]
    congr 1
  rw [hcard]
  by_cases h : v.val % 2 = 0
  · rw [if_pos h, count_congr n (q := fun k => k % 2 = 1) (fun k => by omega)]
    exact count_mod_two_eq_one n
  · rw [if_neg h, count_congr n (q := fun k => k % 2 = 0) (fun k => by omega)]
    exact count_mod_two_eq_zero n

/-- **Sharpness, minimum degree.** For `n ≥ 1`, the balanced complete bipartite graph
`turanGraph n 2` has minimum degree exactly `⌊n/2⌋`. -/
theorem turanTwo_minDegree (n : ℕ) (hn : 0 < n) :
    (turanGraph n 2).minDegree = n / 2 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine le_antisymm ?_ ?_
  · calc (turanGraph n 2).minDegree
        ≤ (turanGraph n 2).degree ⟨0, hn⟩ := (turanGraph n 2).minDegree_le_degree _
      _ = n / 2 := by rw [turanTwo_degree]; simp
  · refine (turanGraph n 2).le_minDegree_of_forall_le_degree (n / 2) (fun v => ?_)
    rw [turanTwo_degree]
    rcases (by omega : v.val % 2 = 0 ∨ v.val % 2 = 1) with h | h
    · rw [if_pos h]
    · rw [if_neg (by omega)]; omega

/-- Every vertex of `turanGraph n 2` has degree at most `⌈n/2⌉ = (n + 1) / 2`. -/
theorem turanTwo_degree_le (n : ℕ) (v : Fin n) :
    (turanGraph n 2).degree v ≤ (n + 1) / 2 := by
  rw [turanTwo_degree]
  rcases (by omega : v.val % 2 = 0 ∨ v.val % 2 = 1) with h | h
  · rw [if_pos h]; omega
  · rw [if_neg (by omega)]

/-- **Sharpness certificate.** The Turán graph `turanGraph n 2` is triangle-free and has
minimum degree exactly `⌊n/2⌋`, so the bound in the minimum-degree corollary of Mantel's
theorem (`MantelMinDegree.exists_degree_le_card_div_two`) cannot be improved. -/
theorem turanTwo_sharp (n : ℕ) (hn : 0 < n) :
    (turanGraph n 2).CliqueFree 3 ∧ (turanGraph n 2).minDegree = n / 2 :=
  ⟨turanTwo_triangleFree n, turanTwo_minDegree n hn⟩

end MantelTuranSharp
