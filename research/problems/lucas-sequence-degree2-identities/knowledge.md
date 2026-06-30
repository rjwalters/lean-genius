# Lucas Sequence Degree-2 Identities

**Slug:** `lucas-sequence-degree2-identities`
**Status:** COMPLETED (verified, 0 axioms, 0 sorries)
**Lean file:** `proofs/Proofs/LucasSequenceDegree2Identities.lean`

## Problem

The gallery's degree-2 Fibonacci/Lucas algebra (`FibonacciIdentitiesOQ02OQ01OQ01` and
children) is entirely the `(P,Q) = (1,−1)` instance of the general theory of Lucas
sequences `U_n(P,Q)`, `V_n(P,Q)`. Goal: formalize the **master degree-2 identity**

  `V_n² − (P²−4Q)·U_n² = 4·Q^n`

over `ℤ` for arbitrary parameters `P, Q`, recovering the gallery's
`L_n² − 5·F_n² = 4·(−1)ⁿ` and the Pell relation as instances.

## Session 2026-06-28 (Session 1) — FRESH, COMPLETED

**Outcome:** completed. New 0-axiom verified gallery entry.

### What I did
- Confirmed the gap: the gallery has only the specific Fibonacci/Lucas pair (and Pell
  separately); no general two-parameter `U_n(P,Q)`, `V_n(P,Q)` with the `V²−DU²=4Q^n`
  master identity.
- Defined `U`, `V : ℤ → ℤ → ℕ → ℤ` and proved, all over `ℤ`, no Binet/`√D`:
  - `V_eq`: `V_n = 2·U_{n+1} − P·U_n` (two-step induction via consecutive-pair strengthening).
  - `U_quad`: `U_{n+1}² − P·U_n·U_{n+1} + Q·U_n² = Q^n` (single induction; the form is a
    `Q`-eigenvector of the recurrence — step is `linear_combination Q * ih`).
  - `U_cassini`: `U_{n+1}² − U_{n+2}·U_n = Q^n` (Lucas-sequence Cassini, from `U_quad`).
  - `V_sq_sub_D_U_sq`: the master identity, via `rw [V_eq]; linear_combination 4 * U_quad`.
  - `fib_lucas_instance` (1,−1)→D=5, `pell_instance` (2,−1)→D=8.
- Built clean in Docker: `✔ Built Proofs.LucasSequenceDegree2Identities`. 12 theorems,
  2 defs, 0 sorries, kernel `decide` only (no `native_decide`).

### Key findings / techniques
- **Eliminate-then-invariant** architecture: the companion relation `V_eq` removes `V`,
  so the whole degree-2 identity reduces to the single invariant quadratic form on `U`.
- The quadratic form `U_{n+1}² − P U_n U_{n+1} + Q U_n²` is multiplied by exactly `Q` per
  recurrence step ⇒ equals `Q^n` by a one-line induction. This is the engine; it is also
  the Lucas-sequence Cassini determinant.
- `linear_combination` discharges both the inductive step and the final algebraic collapse.

### Files modified
- `proofs/Proofs/LucasSequenceDegree2Identities.lean` (new, 174 lines)
- `proofs/Proofs.lean` (import added)
- `src/data/proofs/lucas-sequence-degree2-identities/{meta.json,annotations.json,index.ts}` (new)
- `research/registry.json` (entry added)

### Next steps / follow-up open questions
- General doubling formulas `U_{2n} = U_n·V_n`, `V_{2n} = V_n² − 2·Q^n` over arbitrary `(P,Q)`.
- Bilinear addition laws `2·U_{m+n} = U_m·V_n + U_n·V_m`, `2·V_{m+n} = V_m·V_n + D·U_m·U_n`,
  and `gcd(U_n, V_n) ∣ 2` when `Q` is a unit, derived from the master identity.
