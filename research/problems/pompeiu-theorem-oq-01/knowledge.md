# Pompeiu's Theorem (pompeiu-theorem-oq-01)

## Problem
For an equilateral triangle `ABC` and any point `P` in its plane, the three
distances `PA`, `PB`, `PC` satisfy the triangle inequality (they are the side
lengths of a possibly-degenerate triangle). Degenerate iff `P` lies on the
circumcircle of `ABC`.

## Status: COMPLETED (0 sorry / 0 axiom, build-verified)

## Approach (complex numbers)
Vertices `a, b, c` and point `p` as complex numbers. Everything follows from the
hypothesis-free polynomial identity

  (p - a)(b - c) + (p - b)(c - a) + (p - c)(a - b) = 0     -- `ring`

Isolating the `a`-term and taking norms:

  ‖p - a‖·‖b - c‖ ≤ ‖p - b‖·‖c - a‖ + ‖p - c‖·‖a - b‖     -- `norm_add_le`, `norm_mul`

Equilateral hypothesis ‖a-b‖ = ‖b-c‖ = ‖c-a‖ lets the common side length cancel
(`le_of_mul_le_mul_right` when positive; degenerate a=b=c case handled directly),
giving dist p a ≤ dist p b + dist p c. Cyclic permutation of the core lemma gives
the other two inequalities.

## Files
- `proofs/Proofs/PompeiuTheorem.lean` — 3 theorems, 0 def, 0 axiom, 0 sorry, 81 lines
  - `pompeiu_identity` (hypothesis-free Lagrange three-term identity)
  - `pompeiu_dist` (core inequality)
  - `pompeiu` (full: all three cyclic triangle inequalities)
- `src/data/proofs/pompeiu-theorem-oq-01/meta.json` — gallery entry

## Key facts
- The identity is the SAME three-term Lagrange identity as Ptolemy's inequality;
  Pompeiu is the equilateral specialization.
- Equality (degenerate triangle) ⇔ P on circumcircle = Ptolemy equality case.
- Mathlib v4.26.0: use `‖·‖` / `dist_eq_norm` / `norm_mul` / `norm_add_le`
  (avoid `Complex.abs`, which has churned). `norm_mul` works since ℂ is a
  NormedField.

## Sessions
### 2026-06-16 (Session 1, researcher-10) — FRESH, COMPLETED
- Formalized from scratch via the complex Lagrange identity. Build-verified
  (docker, 0/0). Registered in Proofs.lean + gallery meta.json.

## Possible follow-ups
- Biconditional equality characterization (P on circumcircle ⇔ degenerate).
- Regular n-gon analogue.
