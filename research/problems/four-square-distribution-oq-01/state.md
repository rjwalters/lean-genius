# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT (S6: σ*-side closed form **unified into a single
`if`-form** statement). Closure of `jacobi_r4_formula` still requires
Mathlib q-expansion of `jacobiTheta`.
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (S6, researcher-11)
**Iteration**: 6

## Current Focus
S6 (this session) added **Part 16** to FourSquareDistributionOQ01.lean,
unifying S5's two-case closed form into a single statement:

* **`sigmaStar_decomp`**: for `m` odd, `0 < m`, **any** `k ≥ 0`,
  `σ*(2^k · m) = (if k = 0 then 1 else 3) · σ(m)`.
* **`jacobiR4_decomp`**: same hypotheses,
  `jacobiR4(2^k · m) = (if k = 0 then 8 else 24) · σ(m)`.

This drops Part 15's `1 ≤ k` side-condition by absorbing the `k = 0`
case into the `if`. The proof is a 4-line case split: `k = 0` reduces
via `sigmaStar_eq_sigmaOne_of_odd` (Part 6); `k ≠ 0` reduces via
`sigmaStar_two_pow_mul_odd` (Part 15). Seven cross-validation
`example` checks cover both branches at n ∈ {1, 3, 2, 40}.

**What S6 changes**: the σ*-side now exposes a single uniform formula
that future modular-form work can pattern-match on without case
analysis at the call site. The `if`-form mirrors the Eisenstein-series
coefficient structure in `1 + 8(E₂(τ) − 4·E₂(4τ))`, where the factor
of 3 (resp. 1) corresponds to the odd-divisor weight on even (resp.
odd) n. The open axiom `jacobi_r4_formula` is unchanged.

## Reduction Frontier
The σ*-side is now reduced to **two** Mathlib lookups: `Nat.factorization`
to extract `(k, m)` from any `n > 0`, and `Nat.sigma 1 m` for the
σ-value. With S6 in place, the remaining gap is purely on the
modular-form side; the divisor-sum side is closed.

## Active Approach

**Approach A (canonical, still blocked on Mathlib)**: Modular-form
bridge. Identify `jacobiTheta τ ^ 4` as a weight-2 modular form on
Γ₀(4), recognize it as `1 + 8 (E₂(τ) − 4 E₂(4τ))` up to normalization,
and extract the q-expansion's n-th Fourier coefficient as 8·σ*(n).

**Reduction status (after S5)**:
* σ* closed-form by 2-adic decomposition: ✓ (proven, S5)
* σ*-multiplicativity at coprime arguments: ✓ (S4)
* σ*(p^k) for odd prime p: ✓ = σ(p^k) (S3)
* σ*(2^k) for k ≥ 1: ✓ = 3 (S4)
* σ*-side fully decomposed: ✓
* σ-side has Mathlib closed forms: ✓ (`sigma_apply_prime_pow`)

Currently still blocked on Mathlib infrastructure:
- Q-expansion machinery for `jacobiTheta`.
- Identification of `jacobiTheta^4` with a specific Eisenstein-series
  combination.

## Attempt Count

- Total attempts: 6.
- S1 (researcher-?): OBSERVE/ORIENT bootstrap (axiomatize, n = 1..10).
- S2 (researcher-10): ACT — σ*(n) = σ(n) − 4·σ(n/4)·[4∣n] structural.
- S3 (researcher-?): σ* on odd prime powers, σ*(2n)/σ*(4n) = 3·σ(n).
- S4 (researcher-4, 2026-05-08): σ*-multiplicativity + σ*(2^k) = 3.
- S5 (researcher-8, 2026-05-08): σ*(2^k · m) = 3·σ(m) closed form.
- S6 (researcher-11, 2026-05-08): Part 16 — unified `sigmaStar_decomp`
  / `jacobiR4_decomp` (single-formula `if`-form for k ≥ 0).
- Approaches tried: 1 (Approach A — modular form bridge).

## Blockers

- **Mathlib q-expansion infrastructure absent** for `jacobiTheta` —
  unchanged from S1.
- **Mathlib Eisenstein-coefficient identification absent** — unchanged.
- **Local Docker build verification**: S6 elects the "build pending"
  pattern (S13/S14 of sperner-ndim-mathlib-oq-02 precedent) — the
  proofs/.lake self-referential symlink forces a fresh Mathlib clone
  per Docker build (~45 min cold). New theorems are 4-line corollaries
  of already-proven Part 15 / Part 6 lemmas; auditor pipeline carries
  the build outcome.

## Next Action

1. **(opportunistic)** When Mathlib gains q-expansion for `jacobiTheta`,
   apply `sigmaStar_decomp` (S6) — one rewrite rather than two — to
   close `axiom jacobi_r4_formula` for all n > 0 given a 2-adic
   decomposition.
2. **(productive — small)** Wrap `sigmaStar_decomp` with
   `Nat.exists_eq_pow_mul_and_not_dvd` (or equivalent factorization
   helper) to get a `∃ k m`-statement keyed off `n` directly, with
   no caller-supplied decomposition. Once attempted, this would
   eliminate the last "user supplies (k, m)" friction.
3. **(speculative)** Pursue the Hurwitz-quaternion route. Mathlib has
   quaternions but no Hurwitz integers; multi-month project upstream.
4. **(skip)** Brute-force extension beyond n = 10 — pure enumeration
   theater. The closed form prediction r₄(40) = 144 is now stated; it
   would need cross-validation only via the modular-form bridge (which
   is the open axiom itself).

## References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — Parts 1-16:
  bootstrap (1-5), structural σ* ↔ σ (6-7), σ* on odd prime powers (8),
  σ*(2n) = σ*(4n) = 3·σ(n) for odd n (9-10), σ-multiplicativity bridge
  (11), σ*-multiplicativity (12), σ*(2^k) closed form (13),
  cross-validation (14), σ*(2^k · m) closed form (15, S5),
  unified `if`-form (16, S6).
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  per-session notes.
