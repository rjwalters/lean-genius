# Knowledge: chebyshev-bounds-oq-02-oq-01-oq-01

## Summary

Explicit two-sided bound on the first Chebyshev function
`θ(n) = ∑_{p ≤ n} log p`, establishing `θ(m) = Θ(m)`:

`(log 2 / 3)·m − 2·√m·log m ≤ θ(m) ≤ log 4 · m`  for `m ≥ 2`.

## What is formalized (researcher-9, 2026-06-25)

`proofs/Proofs/ChebyshevBoundsOQ02OQ01OQ01.lean`, namespace
`ChebyshevBoundsOQ02OQ01OQ01`, 0 axioms / 0 sorries:

| Theorem | Statement |
|---|---|
| `chebyshevTheta_lower` | `2 ≤ m → (log2/3)·m − 2√m·log m ≤ θ(m)` |
| `chebyshevTheta_upper` | `θ(n) ≤ log4·n` |
| `chebyshevTheta_bounds` | two-sided, `m ≥ 2` |

## Lineage / dependencies

- `ChebyshevBoundsOQ02.chebyshevPsi := ∑_{m ∈ Icc 1 n} Λ m`
- `ChebyshevBoundsOQ02OQ02.chebyshevTheta` (Chebyshev θ)
- `ChebyshevBoundsOQ02OQ01.chebyshevPsi_lower_linear : 2 ≤ m → (log2/3)·m ≤ ψ(m)`
  (from the central binomial coefficient; the substantive lower estimate)
- `ChebyshevBoundsOQ02OQ02.abs_psi_sub_theta_le : 1 ≤ n → |ψ(n)−θ(n)| ≤ 2√n·log n`
  (= Mathlib's `abs_psi_sub_theta_le_sqrt_mul_log` via a bridge)
- `Chebyshev.theta_le_log4_mul_x : 0 ≤ x → θ(x) ≤ log4·x` (Mathlib, upper bound)

## Key Mathlib gap

Mathlib's `Mathlib/NumberTheory/Chebyshev.lean` provides only **upper** bounds
(`theta_le_log4_mul_x`, `psi_le`, `psi_le_const_mul_self`) and the closeness
estimate; it has **no** lower bound for θ or ψ. The lower bound therefore has to
come from this project's central-binomial machinery (`OQ02OQ01`), which is what
this file routes from ψ to θ.

## Derivation

`θ(m) = ψ(m) − (ψ(m) − θ(m))`. With `ψ(m) ≥ (log2/3)·m` and
`ψ(m) − θ(m) ≤ |ψ(m) − θ(m)| ≤ 2√m·log m`, linarith gives
`θ(m) ≥ (log2/3)·m − 2√m·log m`. Upper bound is Mathlib's `log4·m`.

## Approaches Tried

- Considered a fully self-contained file from Mathlib alone: impossible for the
  lower bound (Mathlib has no ψ/θ lower bound), so imported the project parents.
- Built the parent oleans (`OQ02OQ01`, `OQ02OQ02`) into the shared store offline
  (`lake env lean -o`), since Docker was down.
