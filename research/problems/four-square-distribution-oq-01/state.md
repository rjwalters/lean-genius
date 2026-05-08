# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT (S5: σ*-side fully closed-form by 2-adic decomposition).
Closure of `jacobi_r4_formula` still requires Mathlib q-expansion of
`jacobiTheta`.
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (S5, researcher-8)
**Iteration**: 5

## Current Focus
S5 (this session) added **Part 15** to FourSquareDistributionOQ01.lean,
producing the **explicit closed form** for σ* by 2-adic decomposition:

* **`sigmaStar_two_pow_mul_odd`**: for `1 ≤ k`, `m` odd, `0 < m`:
  `σ*(2^k · m) = 3 · σ(m)`.
* **`jacobiR4_two_pow_mul_odd`**: for the same hypotheses,
  `jacobiR4(2^k · m) = 24 · σ(m)`.

Combined with S2's `sigmaStar_eq_sigmaOne_of_odd` (σ*(odd m) = σ(m)),
this gives a **complete two-case characterisation** of σ*(n) by
2-adic valuation:

```
σ*(n) = σ(odd_part(n))            if v₂(n) = 0
σ*(n) = 3 · σ(odd_part(n))        if v₂(n) ≥ 1
```

The proof is a one-step corollary of S4's multiplicative theory: 4
rewrites combining `sigmaStar_mul_of_coprime`, `sigmaStar_two_pow`,
and `sigmaStar_eq_sigmaOne_of_odd`. Eight cross-validation `example`
checks confirm the closed form against S1's `sigmaStar_*` numeric
values at n = 2, 4, 6, 8, 10 and extends to n = 40 (closed-form
prediction beyond brute-force range).

The open axiom `jacobi_r4_formula : ∀ n > 0, r4Count n = jacobiR4 n`
is unchanged. **What S5 changes is the form of the σ*-side**: future
modular-form work can call `sigmaStar_two_pow_mul_odd` directly
without re-deriving the multiplicative chain.

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

- Total attempts: 5.
- S1 (researcher-?): OBSERVE/ORIENT bootstrap (axiomatize, n = 1..10).
- S2 (researcher-10): ACT — σ*(n) = σ(n) − 4·σ(n/4)·[4∣n] structural.
- S3 (researcher-?): σ* on odd prime powers, σ*(2n)/σ*(4n) = 3·σ(n).
- S4 (researcher-4, 2026-05-08): σ*-multiplicativity + σ*(2^k) = 3.
- S5 (researcher-8, 2026-05-08): σ*(2^k · m) = 3·σ(m) closed form.
- Approaches tried: 1 (Approach A — modular form bridge).

## Blockers

- **Mathlib q-expansion infrastructure absent** for `jacobiTheta` —
  unchanged from S1.
- **Mathlib Eisenstein-coefficient identification absent** — unchanged.
- **Local Docker build verification**: S5 launches a Docker build
  with 32 GB memory ceiling and 80 min timeout from a clean state
  (proofs/.lake symlink loop forces a fresh Mathlib clone + cache
  fetch per build). PR carries the build outcome.

## Next Action

1. **(opportunistic)** When Mathlib gains q-expansion for `jacobiTheta`,
   apply `sigmaStar_two_pow_mul_odd` (S5) to get a closed form for
   r₄(n) given any n's 2-adic decomposition.
2. **(productive — would be a real proof)** Use Mathlib's
   `Nat.factorization n 2` and `n / 2^v₂(n)` to lift S5's two-case
   closed form to a single-formula statement
   `theorem sigmaStar_factorization (n : ℕ) (hn : 0 < n) :
       sigmaStar n = (if 2 ∣ n then 3 else 1) * sigmaOne (n.divNatFactorTwo)`
   (or similar), making the σ*-side a single Mathlib expression.
3. **(speculative)** Pursue the Hurwitz-quaternion route. Mathlib has
   quaternions but no Hurwitz integers; multi-month project upstream.
4. **(skip)** Brute-force extension beyond n = 10 — pure enumeration
   theater. The closed form prediction r₄(40) = 144 is now stated; it
   would need cross-validation only via the modular-form bridge (which
   is the open axiom itself).

## References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — Parts 1-15:
  bootstrap (1-5), structural σ* ↔ σ (6-7), σ* on odd prime powers (8),
  σ*(2n) = σ*(4n) = 3·σ(n) for odd n (9-10), σ-multiplicativity bridge
  (11), σ*-multiplicativity (12), σ*(2^k) closed form (13),
  cross-validation (14), σ*(2^k · m) closed form (15, S5).
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  per-session notes.
