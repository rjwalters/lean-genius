# Complete Hurwitz's Theorem (WIP): the even-case impossibility sorry

## Source

- **Parent proof**: `hurwitz-theorem-oq-03` (`proofs/Proofs/HurwitzTheorem.lean`)
- **Type**: work-in-progress / completion
- **Category**: extension
- **Tractability**: challenging

## Problem Statement

`HurwitzTheorem.lean` proves Hurwitz's theorem with the impossibility direction
(no `n`-square identity for `n ∉ {1,2,4,8}`) fully discharged for **odd** `n` but
left as a single `sorry` for the **even** non-admissible case (`n` even, `n ∉ {2,4,8}`).
The blocker is the minimal-faithful-representation dimension of the Clifford algebra
`Cl(0,n-1)`, which needs Bott periodicity + Artin–Wedderburn — not in Mathlib.

## Progress (researcher-14, 2026-07-05)

Isolated and **verified** the elementary determinant engine that extends the argument
one residue class further: `proofs/Proofs/HurwitzTheoremOQ03WIP01.lean`
(gallery `hurwitz-theorem-oq-03-wip-01`, `verified`, 0 sorry / 0 axiom).

**Key theorem** (`anticommuting_invertible_forces_even`): over any field with `2 ≠ 0`,
two anticommuting invertible matrices force even dimension.

This closes, in principle, the `n ≡ 2 (mod 4)` sub-case; the residual `n ≡ 0 (mod 4)`,
`n ∉ {4,8}` remains genuinely blocked on Clifford theory.

## Remaining Steps (to close the `n ≡ 2 mod 4` sub-case in `HurwitzTheorem.lean`)

1. Define the product `P = M₁ ⋯ M_{n-1}` over the existing `crossMat` family.
2. Prove `P` commutes with each `Mᵢ` (uses `n-1` even minus the `i`-th factor → even
   number of anticommuting swaps).
3. Prove `P² = -I` for `n ≡ 2 (mod 4)` (sign `(-1)^{(n-1)n/2}` is `-1` iff `n ≡ 2 mod 4`).
4. Complexify `ℝⁿ` via `P` (module over `ℂ` of complex dim `n/2`, odd) and invoke
   `HurwitzOQ03WIP01.no_anticommuting_complex_structures_of_odd` over `ℂ`.
5. The remaining `n ≡ 0 (mod 4)` case still needs Clifford representation theory.
