/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Minimum Degree of the General Turán Graph `turanGraph n r` (OQ-03 · OQ-01 · OQ-02)

The parent entry (`MantelTheoremOQ03OQ01`) proved the `r = 2` sharpness certificate for the
minimum-degree corollary of Mantel's theorem: the balanced complete bipartite graph
`turanGraph n 2` is triangle-free and has minimum degree exactly `⌊n/2⌋`.

This file lifts that computation to **every** `r ≥ 1`, certifying sharpness of the Turán
minimum-degree bound `(1 − 1/r)·n` for `K_{r+1}`-free graphs (the parent's third open
question). Recall Mathlib's `turanGraph n r : SimpleGraph (Fin n)` with
`v ~ w ↔ v % r ≠ w % r`, the complete `r`-partite graph whose parts are the residue classes
mod `r` inside `Fin n`. A vertex is adjacent to everyone outside its own residue class, so
its degree is `n` minus the size of that class; the minimum degree lives in the largest
class, residue `0`, of size `⌈n/r⌉ = (n + r − 1)/r`.

## Results

* `turanGraph_degree` : the exact per-vertex degree,
  `degree v = n − #{k < n : k % r = v % r}` (as a `Nat.count`).
* `count_mod_eq_zero` : the residue-class-`0` size, `#{k < n : k % r = 0} = (n + r − 1)/r`.
* `count_mod_le_zero` : residue class `0` is the largest, `#{k < n : k % r = j} ≤ #{k < n :
  k % r = 0}`, via the injection `k ↦ k − j`.
* `turanGraph_minDegree` : `(turanGraph n r).minDegree = n − ⌈n/r⌉` for `n, r ≥ 1`.
* `turanGraph_minDegree_sharp` : the packaged sharpness certificate (`K_{r+1}`-free *and*
  minimum degree exactly `n − ⌈n/r⌉`).
* `turanGraph_minDegree_bound` : the `(1 − 1/r)·n` bound in cleared-denominator form,
  `r · minDegree ≤ (r − 1)·n`.
* `turanTwo_specialization` : `r = 2` recovers the parent's `⌊n/2⌋`.

## Method

The graph-theoretic scaffolding mirrors the parent `r = 2` file: transfer the per-vertex
neighbour count to `Nat.count` over `range n` (`card_fin_filter_val`), then read off the
minimum degree from the `minDegree` extremality lemmas. The only genuinely new content is
the general residue-class-size arithmetic: the closed form for class `0` (induction on `n`
via `Nat.succ_div`) and the antitonicity of class size in the residue (an explicit injection
`k ↦ k − j` on the counting `Finset`s).
-/

open Finset SimpleGraph

namespace MantelTuranGeneral

/-! ## Counting residues modulo `r` -/

/-- Transfer a `Fin n`-indexed count of a `val`-predicate to `Nat.count` over `range n`.
(Reused verbatim from the parent `r = 2` file.) -/
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

/-- The size of residue class `0` modulo `r` inside `Fin n`: `#{k < n : k % r = 0} =
⌈n/r⌉ = (n + r − 1)/r`. Proved by induction on `n` using `Nat.succ_div`. -/
lemma count_mod_eq_zero (r n : ℕ) (hr : 0 < r) :
    Nat.count (fun k => k % r = 0) n = (n + r - 1) / r := by
  induction n with
  | zero =>
    simp only [Nat.count_zero]
    symm
    exact Nat.div_eq_of_lt (by omega)
  | succ m ih =>
    rw [Nat.count_succ, ih]
    have e1 : m + 1 + r - 1 = (m + r - 1) + 1 := by omega
    rw [e1, Nat.succ_div]
    have hcond : (r ∣ (m + r - 1) + 1) ↔ (m % r = 0) := by
      have e2 : (m + r - 1) + 1 = m + r := by omega
      rw [e2, Nat.dvd_iff_mod_eq_zero, Nat.add_mod_right]
    simp only [hcond]

/-- **Residue class `0` is the largest.** For any residue `j`, the class `{k < n : k % r = j}`
injects into `{k < n : k % r = 0}` via `k ↦ k − j` (each such `k` satisfies `k ≥ k % r = j`,
so `k − j = r·(k/r)` is a multiple of `r`), whence its size is bounded by that of class `0`. -/
lemma count_mod_le_zero (r n j : ℕ) :
    Nat.count (fun k => k % r = j) n ≤ Nat.count (fun k => k % r = 0) n := by
  simp only [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card_of_injOn (fun k => k - j)
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hkn, hkj⟩ := hk
    refine ⟨by omega, ?_⟩
    have hdm := Nat.div_add_mod k r
    have hsub : k - j = r * (k / r) := by omega
    rw [hsub]
    exact Nat.mul_mod_right r (k / r)
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hja : j ≤ a := ha.2 ▸ Nat.mod_le a r
    have hjb : j ≤ b := hb.2 ▸ Nat.mod_le b r
    simp only at hab
    omega

/-! ## The general Turán graph `turanGraph n r` -/

/-- **Exact per-vertex degree.** A vertex `v` in `turanGraph n r` is adjacent to every vertex
outside its own residue class, so `degree v = n − #{k < n : k % r = v % r}`. -/
theorem turanGraph_degree (n r : ℕ) (v : Fin n) :
    (turanGraph n r).degree v = n - Nat.count (fun k => k % r = v.val % r) n := by
  have key : (turanGraph n r).degree v + Nat.count (fun k => k % r = v.val % r) n = n := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
        ← card_fin_filter_val n (fun k => k % r = v.val % r)]
    have hadj : (Finset.univ.filter ((turanGraph n r).Adj v))
        = Finset.univ.filter (fun w : Fin n => v.val % r ≠ w.val % r) :=
      Finset.filter_congr (fun w _ => by rw [turanGraph_adj])
    have hnegeq : (Finset.univ.filter (fun w : Fin n => w.val % r = v.val % r))
        = Finset.univ.filter (fun w : Fin n => ¬ (v.val % r ≠ w.val % r)) :=
      Finset.filter_congr (fun w _ => by constructor <;> intro h <;> omega)
    rw [hadj, hnegeq, Finset.filter_card_add_filter_neg_card_eq_card,
        Finset.card_univ, Fintype.card_fin]
  omega

/-- **Sharpness, minimum degree, general `r`.** For `n ≥ 1` and `r ≥ 1`, the Turán graph
`turanGraph n r` has minimum degree exactly `n − ⌈n/r⌉ = n − (n + r − 1)/r`, attained on the
residue class `0`. -/
theorem turanGraph_minDegree (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (turanGraph n r).minDegree = n - (n + r - 1) / r := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine le_antisymm ?_ ?_
  · calc (turanGraph n r).minDegree
        ≤ (turanGraph n r).degree ⟨0, hn⟩ := (turanGraph n r).minDegree_le_degree _
      _ = n - Nat.count (fun k => k % r = (⟨0, hn⟩ : Fin n).val % r) n :=
            turanGraph_degree n r _
      _ = n - (n + r - 1) / r := by
            have h0 : (⟨0, hn⟩ : Fin n).val % r = 0 := by simp
            rw [h0, count_mod_eq_zero r n hr]
  · refine (turanGraph n r).le_minDegree_of_forall_le_degree (n - (n + r - 1) / r) (fun v => ?_)
    rw [turanGraph_degree n r v]
    have hle : Nat.count (fun k => k % r = v.val % r) n ≤ (n + r - 1) / r := by
      calc Nat.count (fun k => k % r = v.val % r) n
          ≤ Nat.count (fun k => k % r = 0) n := count_mod_le_zero r n (v.val % r)
        _ = (n + r - 1) / r := count_mod_eq_zero r n hr
    exact Nat.sub_le_sub_left hle n

/-- **Sharpness certificate for the parent's third open question.** `turanGraph n r` is
`K_{r+1}`-free and its minimum degree `n − ⌈n/r⌉` witnesses that the `(1 − 1/r)·n`
minimum-degree bound for `K_{r+1}`-free graphs cannot be improved. -/
theorem turanGraph_minDegree_sharp (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (turanGraph n r).CliqueFree (r + 1)
      ∧ (turanGraph n r).minDegree = n - (n + r - 1) / r :=
  ⟨turanGraph_cliqueFree hr, turanGraph_minDegree n r hn hr⟩

/-- The minimum degree realises the `(1 − 1/r)·n` bound: in cleared-denominator form,
`r · minDegree ≤ (r − 1)·n`. Equivalently `minDegree = n − ⌈n/r⌉ ≤ (1 − 1/r)·n`. -/
theorem turanGraph_minDegree_bound (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    r * (turanGraph n r).minDegree ≤ (r - 1) * n := by
  rw [turanGraph_minDegree n r hn hr, Nat.mul_sub, Nat.sub_one_mul]
  have hdm := Nat.div_add_mod (n + r - 1) r
  have hlt : (n + r - 1) % r < r := Nat.mod_lt _ hr
  have hge : n ≤ r * ((n + r - 1) / r) := by omega
  exact Nat.sub_le_sub_left hge (r * n)

/-- **Consistency with the parent.** For `r = 2`, the general formula
`n − ⌈n/2⌉ = ⌊n/2⌋` recovers `turanTwo_minDegree`. -/
theorem turanTwo_specialization (n : ℕ) (hn : 0 < n) :
    (turanGraph n 2).minDegree = n / 2 := by
  rw [turanGraph_minDegree n 2 hn (by norm_num)]
  omega

end MantelTuranGeneral
