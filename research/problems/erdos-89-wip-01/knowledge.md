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
