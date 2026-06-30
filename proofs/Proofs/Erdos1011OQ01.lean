import Mathlib

/-
# Erdős Problem #1011 (OQ-01) — Mantel's Theorem: the Triangle (r = 2) Case, Axiom-Free

## Lineage

This is an open-question descendant of `Erdos1011Problem.lean`, which studies
`f_r(n)`, the minimal edge count forcing a triangle in an `n`-vertex graph of
chromatic number ≥ r. The parent file *axiomatizes* the known small cases,
including the triangle base case as

  `axiom turan_theorem` :  (the extremal edge count for triangle-free graphs).

The base case is **Mantel's theorem** (1907), the `r = 2` instance of Turán's
theorem: a triangle-free graph on `n` vertices has at most `⌊n²/4⌋` edges, and
this is sharp (the complete bipartite graph `K_{⌊n/2⌋,⌈n/2⌉}`, i.e. the Turán
graph `turanGraph n 2`, attains it).

Mathlib 4.26.0 now contains the full Turán machinery
(`Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`). This file uses it to
**discharge the parent's `turan_theorem` axiom for the triangle case**: every
statement below is a theorem with 0 axioms / 0 sorries, derived from
`SimpleGraph.CliqueFree.card_edgeFinset_le` and `card_edgeFinset_turanGraph`.

A triangle is a 3-clique, so "triangle-free" is `G.CliqueFree 3`, and the
relevant Turán parameter is `r = 2` (an `(r+1) = 3`-clique-free graph).

## What is proved here (self-contained, Mathlib-only)

* `triangleFree_card_edgeFinset_le` : Mantel's bound `#edges ≤ n² / 4`.
* `four_mul_card_edgeFinset_le`      : the cleared-denominator form `4·#edges ≤ n²`.
* `turanGraph_two_triangleFree`      : the Turán graph `turanGraph n 2` is triangle-free.
* `card_edgeFinset_turanGraph_two`   : its exact edge count `(n² − (n%2)²)/4`.
* `mantel_sharp_even`                : for **even** `n`, `turanGraph n 2` is a
                                        triangle-free graph with exactly `n²/4`
                                        edges — so Mantel's bound is sharp.

## Honest scope

The hard work — Turán's theorem itself — lives in Mathlib. The contribution of
this file is to *connect* that machinery to the exact triangle statement the
Erdős #1011 development needs, specializing the general Turán bound to `r = 2`,
simplifying the binomial/modular correction terms, and exhibiting the matching
extremal graph for even `n`. This converts one of the parent's five axioms (the
triangle base case) into a machine-checked theorem.

Adapted from erdosproblems.com lineage (Apache 2.0 License).
-/

open Finset Fintype SimpleGraph

namespace Erdos1011Mantel

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Mantel's theorem.** A triangle-free graph (no `3`-clique) on `n` vertices
has at most `⌊n²/4⌋` edges. This is the `r = 2` case of Turán's theorem; it is
the triangle base case axiomatized in the parent Erdős #1011 file, here proved. -/
theorem triangleFree_card_edgeFinset_le (hG : G.CliqueFree 3) :
    G.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  have h := hG.card_edgeFinset_le (r := 2)
  set n := Fintype.card V with hn
  have hmod : n % 2 ≤ 1 := by omega
  have hchoose : (n % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [hchoose, add_zero] at h
  -- `h : G.edgeFinset.card ≤ (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2)`
  refine h.trans ?_
  norm_num
  exact Nat.div_le_div_right (Nat.sub_le _ _)

/-- The cleared-denominator form of Mantel's theorem: `4·#edges ≤ n²`. -/
theorem four_mul_card_edgeFinset_le (hG : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ Fintype.card V ^ 2 := by
  have h := triangleFree_card_edgeFinset_le hG
  calc 4 * G.edgeFinset.card
      ≤ 4 * (Fintype.card V ^ 2 / 4) := by exact Nat.mul_le_mul_left _ h
    _ ≤ Fintype.card V ^ 2 := Nat.mul_div_le _ _

/-- The Turán graph `turanGraph n 2` (a balanced complete bipartite graph) is
triangle-free. -/
theorem turanGraph_two_triangleFree (n : ℕ) : (turanGraph n 2).CliqueFree 3 :=
  turanGraph_cliqueFree (by norm_num)

/-- Exact edge count of the triangle-free extremal graph `turanGraph n 2`. -/
theorem card_edgeFinset_turanGraph_two (n : ℕ) :
    (turanGraph n 2).edgeFinset.card = (n ^ 2 - (n % 2) ^ 2) / 4 := by
  have h := card_edgeFinset_turanGraph (n := n) (r := 2)
  have hmod : n % 2 ≤ 1 := by omega
  have hchoose : (n % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [hchoose, add_zero] at h
  rw [h]; norm_num

/-- **Sharpness of Mantel's theorem for even `n`.** When `n` is even, the Turán
graph `turanGraph n 2` is triangle-free and has exactly `n²/4` edges, so the
bound `triangleFree_card_edgeFinset_le` cannot be improved. -/
theorem mantel_sharp_even (n : ℕ) (hn : Even n) :
    (turanGraph n 2).CliqueFree 3 ∧
      (turanGraph n 2).edgeFinset.card = n ^ 2 / 4 := by
  refine ⟨turanGraph_two_triangleFree n, ?_⟩
  rw [card_edgeFinset_turanGraph_two]
  have : n % 2 = 0 := Nat.even_iff.mp hn
  rw [this]; norm_num

end Erdos1011Mantel
