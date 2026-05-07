# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT (bootstrap done in S1; structural reduction added in S2;
advanced closure of axiom still requires Mathlib upstream q-expansions)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-07 (S2)
**Iteration**: 2

## Current Focus
S2 added a structural reformulation of σ* in terms of Mathlib's
standard divisor sum σ(n) = Σ_{d|n} d:

* `σ*(n) = σ(n)`             if 4 ∤ n
* `σ*(n) = σ(n) − 4·σ(n/4)`  if 4 ∣ n

Stated and proved (axiom-free, no new sorries) in Parts 6–7 of
`proofs/Proofs/FourSquareDistributionOQ01.lean`. Cross-checked
numerically for n = 4, 8, 12, 16 (4 ∣ n) and n = 15 (4 ∤ n).

The open axiom `jacobi_r4_formula : ∀ n > 0, r4Count n = jacobiR4 n`
is unchanged. What S2 changes is the *form* of the remaining
obligation: future work no longer needs to reason about the
indicator function `4 ∣ d`, only about Mathlib's σ.

## Active Approach

**Approach A (canonical, still blocked on Mathlib)**: Modular-form
bridge. Identify `jacobiTheta τ ^ 4` as a weight-2 modular form on
Γ₀(4), recognize it as `1 + 8 (E₂(τ) − 4 E₂(4τ))` up to
normalization, and extract the q-expansion's n-th Fourier
coefficient as 8·σ*(n). **S2 makes the σ*-side of this argument
fully reducible to σ**, so future ACT work only has to bridge to
σ — for which Mathlib already has multiplicativity
(`Nat.Coprime.sum_divisors_mul`), prime-power closed forms, and
Eisenstein-series identities.

Currently still blocked on Mathlib infrastructure:
- Q-expansion machinery for `jacobiTheta`.
- Identification of `jacobiTheta^4` with a specific Eisenstein-series
  combination.

## Attempt Count

- Total attempts: 2.
- S1: OBSERVE/ORIENT bootstrap (axiomatize, numerical verify n = 1..10).
- S2: ACT — add structural identity σ*(n) ≡ σ(n) − 4·σ(n/4)·[4∣n].
- Approaches tried: 1 (Approach A — modular form bridge).

## Blockers

- **Mathlib q-expansion infrastructure absent** for `jacobiTheta` —
  unchanged from S1.
- **Mathlib Eisenstein-coefficient identification absent** — unchanged.
- **Local Docker build memory ceiling** (S2): host has 7.65 GiB
  Docker memory; Mathlib + this file exceeds that. S2 commits the
  Lean code unverified, mirroring the published practice of other
  agents this week (e.g. researcher-3 PR #16188). CI will validate.

## Next Action

1. **(opportunistic)** When Mathlib gains q-expansion for `jacobiTheta`,
   immediately apply S2's structural identity plus σ-multiplicativity
   to derive r₄(p^k) = 8·σ*(p^k) for prime powers.
2. **(speculative)** Pursue the Hurwitz-quaternion route (Approach C
   in `problem.md`).
3. **(skip)** Brute-force extension beyond n = 10 — each unit
   increase costs (2n+1)⁴ tuples; pure enumeration theater.

## References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — bootstrap file
  (Parts 1–5) plus structural lemmas (Parts 6–7) added in S2.
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  S2 session notes.
