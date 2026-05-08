# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT (bootstrap S1; structural reduction S2; σ* on odd prime
powers + σ*(2n)/σ*(4n) for odd n in S3; σ*-multiplicativity at coprime
arguments + σ*(2^k) closed form in S4. Closure of `jacobi_r4_formula`
still requires Mathlib q-expansion of `jacobiTheta`.)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (S4)
**Iteration**: 4

## Current Focus
S4 (this session) added the **multiplicative structure** of σ*:

* **`sigmaStar_mul_of_coprime`**: σ*(mn) = σ*(m)·σ*(n) for `gcd(m,n) = 1`.
* **`sigmaStar_two_pow`**: σ*(2^k) = 3 for `k ≥ 1`.

Combined with Part 8's `sigmaStar_prime_pow_of_odd_prime` (σ*(p^k) =
σ(p^k) for odd prime p), σ* is now **completely characterised** by its
values on prime-power arguments — exactly mirroring the multiplicative
theory of σ in Mathlib's `ArithmeticFunction.IsMultiplicative.sigma`.

For n = 2^a · ∏ p_i^{e_i} with the p_i odd:
```
σ*(n) = σ*(2^a) · ∏ σ*(p_i^{e_i})
      = (1 if a = 0; 3 if a ≥ 1) · ∏ σ(p_i^{e_i}).
```
The proof routes σ-multiplicativity (Mathlib's
`ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime`) through
the Part 6 structural identity σ*(n) + 4·σ(n/4)·[4∣n] = σ(n).

The open axiom `jacobi_r4_formula : ∀ n > 0, r4Count n = jacobiR4 n`
is unchanged. **What S4 changes is the form of the remaining
obligation**: future work can now compute σ*(n) by prime-power
decomposition without re-deriving any structural arithmetic.

## Active Approach

**Approach A (canonical, still blocked on Mathlib)**: Modular-form
bridge. Identify `jacobiTheta τ ^ 4` as a weight-2 modular form on
Γ₀(4), recognize it as `1 + 8 (E₂(τ) − 4 E₂(4τ))` up to normalization,
and extract the q-expansion's n-th Fourier coefficient as 8·σ*(n).

**Reduction status (after S4)**:
* σ*-multiplicativity at coprime arguments: ✓ (proven, S4)
* σ*(p^k) for odd prime p: ✓ = σ(p^k) (S3)
* σ*(2^k) for k ≥ 1: ✓ = 3 (S4)
* σ*-side fully decomposes via prime-power: ✓
* σ-side has Mathlib closed forms: ✓ (`sigma_apply_prime_pow`)

Currently still blocked on Mathlib infrastructure:
- Q-expansion machinery for `jacobiTheta`.
- Identification of `jacobiTheta^4` with a specific Eisenstein-series
  combination.

## Attempt Count

- Total attempts: 4.
- S1 (researcher-?): OBSERVE/ORIENT bootstrap (axiomatize, n = 1..10).
- S2 (researcher-10): ACT — σ*(n) = σ(n) − 4·σ(n/4)·[4∣n] structural.
- S3 (researcher-?): σ* on odd prime powers, σ*(2n)/σ*(4n) = 3·σ(n).
- S4 (researcher-4, 2026-05-08): σ*-multiplicativity + σ*(2^k) = 3.
- Approaches tried: 1 (Approach A — modular form bridge).

## Blockers

- **Mathlib q-expansion infrastructure absent** for `jacobiTheta` —
  unchanged from S1.
- **Mathlib Eisenstein-coefficient identification absent** — unchanged.
- **Local Docker build memory ceiling** (S2-S4): host has 7.65 GiB
  Docker memory; Mathlib + this file may exceed that. S4 attempts a
  6 GB Docker build with concurrency to other lean4 containers; CI
  will validate definitively.

## Next Action

1. **(opportunistic)** When Mathlib gains q-expansion for `jacobiTheta`,
   immediately apply S4's σ*-multiplicativity to reduce r₄(n) = 8·σ*(n)
   to a prime-power calculation per p ∈ primes(n).
2. **(productive)** Prove r₄(2^k) = 24 for k ≥ 1 (numerically confirmed
   at k = 1, 2, 3 in n = 2, 4, 8 cases) using σ*(2^k) = 3 and the
   target identity. Doesn't close the axiom but cross-validates a
   prediction.
3. **(speculative)** Pursue the Hurwitz-quaternion route (Approach C
   in `problem.md`). Mathlib has quaternions but no Hurwitz integers;
   building Hurwitz arithmetic is a multi-month project.
4. **(skip)** Brute-force extension beyond n = 10 — each unit increase
   costs (2n+1)⁴ tuples; pure enumeration theater.

## References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — Parts 1-14:
  bootstrap (1-5), structural σ* ↔ σ (6-7), σ* on odd prime powers (8),
  σ*(2n) = σ*(4n) = 3·σ(n) for odd n (9-10), σ-multiplicativity bridge
  (11), σ*-multiplicativity (12), σ*(2^k) closed form (13),
  cross-validation (14).
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  per-session notes.
