# Pompeiu's Theorem (pompeiu-theorem-oq-01)

**Status:** COMPLETED — build-verified 0 sorries / 0 axioms.

## Statement
For an equilateral triangle `ABC` and an arbitrary point `P`, the distances `PA, PB, PC`
satisfy the triangle inequality (they are side lengths of a possibly degenerate triangle).

## Proof Summary
Model points as complex numbers. The entire argument rests on one algebraic identity:

    (P-A)(B-C) + (P-B)(C-A) + (P-C)(A-B) = 0     (pure `ring` fact for any 4 complex numbers)

The three summands therefore form a closed vector triangle in ℂ. Three complex numbers
summing to zero have norms obeying the triangle inequality (`norm_le_of_add_eq_zero`, one line
via `norm_add_le` + `norm_neg`). Taking norms gives `PA·s ≤ PB·s + PC·s` where `s` is the
common side length of the equilateral triangle (`norm_mul` splits each product); cancelling the
positive `s` yields `PA ≤ PB + PC`. The other two inequalities follow by cyclic relabelling.

## Files
- `proofs/Proofs/PompeiuTheoremOQ01.lean` (96 lines, 4 theorems, 0 defs)
- `src/data/proofs/pompeiu-theorem-oq-01/{meta.json,annotations.json}`
- Registered in `proofs/Proofs.lean`

## Key Lemmas
- `pompeiu_identity` — the closed-triangle identity (ring)
- `norm_le_of_add_eq_zero` — zero sum ⟹ triangle inequality on norms
- `pompeiu_dist_le` — single inequality PA ≤ PB + PC
- `pompeiu_triangle_inequalities` — all three, by cyclic symmetry

## Session 2026-06-16 (Session 1) — FRESH, COMPLETED
Picked from clean plane-geometry pool. Numerically verified identity + inequality in Python,
wrote the Lean proof, docker-build green `[3062/3062]` after fixing a left-/right-associativity
mismatch in the zero-sum hypothesis. Registered + gallery data. PR opened.

## Possible Follow-ups (not pursued)
- Degeneracy characterization: equality (degenerate triangle) iff `P` lies on the circumcircle.
- Generalization to the inequality form of Ptolemy for non-equilateral triangles (weighted
  distances `PA·a, PB·b, PC·c`).
