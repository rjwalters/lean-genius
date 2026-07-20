# Knowledge Base: erdos-98-wip-01

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

Created `proofs/Proofs/Erdos98WIP01.lean` (5 theorems, 0 sorry, 0 axiom;
host-verified `bin/lake env lean` exit 0, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` on all — no `sorryAx`, no `ofReduceBool`). The
scaffold `Erdos98Problem.lean` had only definitions; this file proves the first
structural facts about `numDistinctDistances` and `h`.

The **counting envelope** that any analysis of `h(n)` sits inside:

- `numDistinctDistances_le_offDiag` — `numDistinctDistances P ≤ n·(n−1)`. A
  positive distance forces `P i ≠ P j` (`dist_pos`), hence `i ≠ j`, so the
  distinct positive distances embed into `Finset.image f univ.offDiag`; count via
  `Finset.offDiag_card` and `Nat.mul_sub_one`.
- `numDistinctDistances_eq_zero_of_le_one` — degenerate floor `n ≤ 1 ⟹ 0`.
- `one_le_numDistinctDistances_of_injective` — for injective `P`, `2 ≤ n ⟹ ≥ 1`
  (exhibit indices `0 ≠ 1`, distinct images, positive distance).
- `InGeneralPosition.injective` — general position ⟹ injective (first conjunct).
- `h_le_of_inGeneralPosition` — `h n ≤ numDistinctDistances P` via `Nat.sInf_le
  ⟨P, hgp, rfl⟩`: every general-position configuration is an upper-bound witness
  for the minimum. This is the membership hook every known upper-bound
  construction (Pach `n^{log₂3}`, Erdős–Füredi–Pach `n·exp(c√log n)`) supplies.

### Verification
Parent `Erdos98Problem.lean` fresh-built to olean host-side (Mathlib-only, v4.31,
docker-free), then child compiled against it. Exit 0, no warnings.

### Next Steps
- Sharpen the upper envelope to `numDistinctDistances P ≤ n.choose 2` using the
  symmetry `dist (P i) (P j) = dist (P j) (P i)` (image over `{i < j}` pairs).
- A lower bound beyond `1`: the elementary Erdős pigeonhole `≥ √(n − 3/4) − 1/2`
  distinct distances (needs the max-degree-of-a-distance argument) would be the
  first genuinely superconstant floor.
