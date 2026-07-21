# Knowledge Base: erdos-89-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session (researcher-1, 2026-07-20) — first machine-checked theorems (axiom-free)

Created `proofs/Proofs/Erdos89WIP01.lean` (6 theorems, 0 sorry, 0 axiom;
host-verified `bin/lake env lean` exit 0, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` on all — no `sorryAx`, no `ofReduceBool`). The
scaffold `Erdos89Problem.lean` proved facts *about the conjecture* (Guth–Katz
consistency) but nothing about the counting objects; this adds their structure.

- `dist_pos_of_ne` — `p ≠ q ⟹ 0 < ‖p − q‖` (`norm_pos_iff` + `sub_ne_zero`).
- `distinctDistances_eq_image` — the definitional `filter (· > 0)` is redundant:
  every off-diagonal pair already has positive distance, so
  `distinctDistances S = S.offDiag.image (dist · ·)` (`Finset.filter_true_of_mem`).
- `numDistinctDistances_le_offDiag` — `≤ |S|·(|S|−1)` (`card_image_le`,
  `Finset.offDiag_card`, `Nat.mul_sub_one`).
- `numDistinctDistances_eq_zero_of_card_le_one` — degenerate floor.
- `one_le_numDistinctDistances_of_two_le_card` — `2 ≤ |S| ⟹ ≥ 1`
  (`Finset.one_lt_card` gives a distinct pair; its distance is a member).
- `minDistinctDistances_le_of_card_eq` — `g(n) ≤ numDistinctDistances S` for any
  `n`-point `S` (`Nat.sInf_le`), the grid-upper-bound membership hook.

### Verification
Parent `Erdos89Problem.lean` fresh-built to olean host-side (Mathlib-only, v4.31,
docker-free), child compiled against it. Exit 0, no warnings.

### Next Steps
- Sharpen to `≤ S.card.choose 2` via distance symmetry.
- Formalize the `√n × √n` grid upper bound feeding `minDistinctDistances_le_*`,
  giving a concrete `g(n) = O(n)` ceiling.
- Connect `singlePointConjecture` (Problem #604) to the global count.

## Session (researcher-1, 2026-07-20 #2) — sharp choose-2 ceiling

Added `numDistinctDistances_le_choose_two` — `numDistinctDistances S ≤
S.card.choose 2`, the sharp unordered-pair ceiling (halves the crude
`|S|·(|S|−1)` bound from session #1). This was the first listed Next Step.

Key idea (identical to erdos-98-wip-01): the custom `Erdos89.dist p q = ‖p−q‖`
is symmetric via `norm_sub_rev`, so it factors as `g ∘ Sym2.mk.uncurry` with
`g = Sym2.lift ⟨fun a b => dist a b, norm_sub_rev⟩`. Then
`S.offDiag.image (dist ·.1 ·.2) = (S.offDiag.image Sym2.mk.uncurry).image g`
(`Finset.image_image`), and `Sym2.card_image_offDiag S` counts the off-diagonal
`Sym2` image as `S.card.choose 2`.

Host-verified `bin/lake env lean Proofs/Erdos89WIP01.lean` exit 0, no warnings;
`#print axioms numDistinctDistances_le_choose_two` = `[propext, Classical.choice,
Quot.sound]`. Now 7 theorems, 0 sorry, 0 axiom.

### Next Steps (unchanged)
- Formalize the `√n × √n` grid upper bound feeding `minDistinctDistances_le_*`
  for a concrete `g(n) = O(n)` ceiling.
- Guth–Katz `Ω(n/log n)` lower bound stays an imported assumption.

## Session (researcher-1, 2026-07-20 #3) — first linear upper bound g(n) ≤ n−1

Added the file's **first non-quadratic upper bound** on Erdős's function:
`minDistinctDistances_le_pred : minDistinctDistances n ≤ n - 1`. Prior sessions
bounded `g(n)` above only by the worst-case `n.choose 2` (quadratic); this pins
the linear ceiling that (together with monotonicity) shows `g` grows at most
linearly. The truth is `Θ(n/√(log n))`, so `n − 1` is a correct non-sharp ceiling.

Construction (all axiom-free, host-verified `bin/lake env lean` exit 0,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):
- `apPoint i := !₂[(i:ℝ), 0]` — the collinear AP along the x-axis.
- `dist_apPoint : Erdos89.dist (apPoint i) (apPoint j) = |(i:ℝ) − j|`. Since the
  gallery `dist` is `‖·−·‖`, rewrite `← dist_eq_norm` to the metric, then
  `EuclideanSpace.dist_eq` + `Fin.sum_univ_two`; the y-coordinate term vanishes
  (`sub_self`/`abs_zero`/`zero_pow`), leaving `√(|i−j|²) = |i−j|`
  (`Real.sqrt_sq_eq_abs`, `abs_abs`).
- `apPoint_injective` via `dist_apPoint` (distance 0 ⟹ equal indices), so
  `apSet_card : (apSet n).card = n`.
- `apSet_distinctDistances_subset` — every distance `|a−b|` (a,b<n, a≠b) equals
  `((a:ℤ)−b).natAbs ∈ [1, n−1]` (`Nat.cast_natAbs` bridges `|(a:ℝ)−b|` to the nat;
  bounds by `omega` — omega handles `Int.natAbs`), so the distance set embeds in
  `(Finset.Icc 1 (n−1)).image (↑·)`, of card `≤ n−1`.

Gotcha: inside `namespace Erdos89`, bare `dist` is `Erdos89.dist` (= ‖·−‖), NOT
the metric — `EuclideanSpace.dist_eq` needs `_root_.dist`, reached via
`← dist_eq_norm`. `Nat.cast_natAbs` (NOT `Int.cast_natAbs`, which does not exist)
is the `(n.natAbs : α) = |↑n|` bridge.

Now 20 theorems, 0 sorry, 0 axiom.

### Next Steps
- Sharpen toward `Θ(n/√(log n))` via the `√n × √n` grid — DEEP (needs the
  number-theoretic count of distinct distances in a square integer grid).
- Guth–Katz `Ω(n/log n)` lower bound stays an imported assumption.
