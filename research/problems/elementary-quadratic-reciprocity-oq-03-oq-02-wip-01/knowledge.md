# Knowledge: Kronecker Symbol WIP Completion

## Result (2026-07-07)

**Target 1 — full second-argument multiplicativity — is proven and machine-verified**
in `proofs/Proofs/ElementaryQuadraticReciprocityOQ03OQ02.lean` (0 sorries, 0 axioms,
builds under Mathlib v4.26).

New declarations:
- `kronecker_eq_sign_jacobi (a n : ℤ) (hn : n ≠ 0)` — normal form:
  `kronecker a n = (if n < 0 then kroneckerNeg1 a else 1) * jacobiSym a n.natAbs`.
- `kroneckerNeg1_sq` (private) — `kroneckerNeg1 a * kroneckerNeg1 a = 1`.
- `kronecker_mul_right (a m n : ℤ) (hmn : m * n ≠ 0)` — `(a/mn) = (a/m)(a/n)`.
- `kronecker_mul_right_odd` retained as the `ℕ`-typed odd-modulus corollary.

## Key insights

- **`jacobiSym.mul_right'` needs only nonzero moduli, not oddness.** The prior
  session assumed the general even/negative case required supplementary laws
  `(2/n)`, `(-1/n)`. That is true for the *classical* Kronecker symbol, but this
  file's `kronecker` definition routes the whole modulus through `jacobiSym |n|`,
  so multiplicativity is immediate from `jacobiSym.mul_right' a (b₁≠0) (b₂≠0)`.
- **Normal-form trick.** The three special-modulus branches (`n = 0, ±1`) obstruct
  a direct `split_ifs` when the three `kronecker` calls have *different* moduli
  (`m*n`, `m`, `n`). Collapsing each to `sign(n)·J(a||n|)` first makes the
  remaining case analysis purely about signs.
- **Sign multiplicativity** across a nonzero product: the only nontrivial case is
  `m<0, n<0` (then `m*n>0`), where the two sign characters must cancel — handled
  by `kroneckerNeg1_sq` (a value in `{±1}` squares to 1).
- **Scope caveat (honesty).** At even moduli the file's symbol equals Jacobi's
  value at 2, NOT the classical mod-8 character `kronecker2` (which is defined in
  the file but never wired into `kronecker`). So `kronecker_mul_right` is
  multiplicativity of the symbol *as defined* — it coincides with the classical
  Kronecker symbol at all odd moduli and at `n = ±1`. Status kept `wip`.
- **Build gotcha:** local Docker builds of this file SIGSEGV/exit-135 on the
  `#print axioms` commands (stack overflow); the origin/main version always
  *replays* its cached olean so the crash only appears once the file is edited.
  Commented the `#print axioms` block out; the file otherwise builds in ~2s.

## Open work

1. Refine `kronecker` to use `kronecker2` at the 2-adic part (→ classical symbol
   at even moduli), then re-prove `kronecker_mul_right` for the refined def.
2. Target 2: generalized quadratic reciprocity for arbitrary fundamental
   discriminants — supplementary laws + Gauss sums.
