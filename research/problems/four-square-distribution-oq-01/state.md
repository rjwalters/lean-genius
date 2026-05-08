# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT
**Phase note**: S12: Part 22 — `jacobiR4(p^k) = 8·σ(p^k)` and
`r4Count(p^k) = 8·σ(p^k)` for odd prime `p` and arbitrary `k ≥ 0`.
Generalizes Part 21's `jacobiR4_odd_prime` / `r4Count_odd_prime`
(k = 1 case) by inlining Part 8's `sigmaStar_prime_pow_of_odd_prime`.
With Part 15's pure 2-power closed form and Part 12's σ*-multiplicativity,
this pins jacobiR4(n) explicitly on every prime power. Closure of
`jacobi_r4_formula` still requires the multiplicative bridge from
r4Count to jacobiR4 (atomic-axiom route — see S11) or Mathlib
q-expansion of `jacobiTheta` / `E₂`.
**Path**: full
**Since**: 2026-05-08T21:33:45+03:00
**Last Updated**: 2026-05-08 (S12, researcher-11; build pending)
**Iteration**: 12

## Current Focus
S12 (this session) adds **Part 22** to FourSquareDistributionOQ01.lean:
the odd-prime-POWER closed forms

* **`jacobiR4_prime_pow_of_odd_prime`**: for odd prime `p` and `k ≥ 0`,
  `jacobiR4(p^k) = 8·σ(p^k)` (axiom-free).
* **`r4Count_prime_pow_of_odd_prime`**: for odd prime `p` and `k ≥ 0`,
  `r4Count(p^k) = 8·σ(p^k)` (uses `jacobi_r4_formula`).

Plus four explicit `sigmaOne_*` numerical theorems (σ(9), σ(25), σ(27),
σ(49)) and seven `example`-form cross-validations including the n = 9
match against Part 1's `jacobiR4_9 = 104`, n = 27 (first odd-prime
cube), and n ∈ {25, 49} extending beyond Part 1's brute-force envelope
n ≤ 10. Net: +91 lines, +6 named theorems, 0 new axioms, 0 sorries.

Coverage: Part 22 generalizes Part 21's k = 1 odd-prime case
(`jacobiR4_odd_prime`) by chaining through Part 8
(`sigmaStar_prime_pow_of_odd_prime`) and the definition
`jacobiR4 = 8·σ*`. Combined with Part 15's pure 2-power closed form
(`jacobiR4_two_pow_mul_odd`) and Part 12's σ*-multiplicativity, this
pins `jacobiR4(n)` explicitly on every prime power. The general case
n = ∏ pᵢ^{kᵢ} reduces to a chain via multiplicativity.

S11 had two parallel branches (Part 21 = `r4Count_eight_le` /
`r4Count_pos` / `eight_dvd_r4Count` / `sigmaStar_odd_prime` /
`jacobiR4_odd_prime` / `r4Count_odd_prime` lower-bound cluster, merged
in PR #17395; an atomic-axiom decomposition `jacobi_r4_formula_from_atomic`
proposed in PR #17388, build pending). S10 (researcher-10) had landed
the multiplicativity bridge `jacobiR4_mul_of_coprime` /
`r4Count_mul_of_coprime` / `r4Count_two_pow_mul_odd` (PR #17359).

S9 (researcher-11) had added **Part 19** (`r4Count_factorization_form`)
to FourSquareDistributionOQ01.lean, exposing `r4Count n` directly in the
Eisenstein-coefficient closed form that the modular-form derivation
of Jacobi's theorem produces. Combines `jacobi_r4_formula` (Part 5)
with `jacobiR4_factorization_form` (S8) in a 1-line `rw`. PR #17347
adds 66 lines (1 theorem + 4 cross-validation examples), 0 axioms,
0 sorries.

S8 (researcher-10) had added **Part 18** to FourSquareDistributionOQ01.lean,
lifting S7's existential form to a constructive n-keyed expression using
Mathlib's `ord_compl[2] n` notation (the odd part of `n`,
`= n / 2 ^ n.factorization 2`):

* **`sigmaStar_factorization_form`**: for `0 < n`,
  `σ*(n) = (if 2 ∣ n then 3 else 1) · σ(ord_compl[2] n)`.
* **`jacobiR4_factorization_form`**: companion identity with constants
  24/8 (since jacobiR4 = 8·σ*).

The proof rewrites `n` as `2 ^ n.factorization 2 · ord_compl[2] n` via
`Nat.ord_proj_mul_ord_compl_eq_self`; applies S6 `sigmaStar_decomp` with
`Nat.ord_compl_pos` and `Nat.not_dvd_ord_compl Nat.prime_two`; and
case-splits the `if k = 0` vs `if 2 ∣ n` via
`Nat.Prime.dvd_iff_one_le_factorization`. Four `example` cross-checks at
n ∈ {1, 9, 40} demonstrate the closed form on σ* and jacobiR4.

**What S8 changes (relative to S7)**: S7 callers had to extract `(k, m)`
from an existential and supply them downstream; S8 expresses both
σ*(n) and jacobiR4(n) directly as `n`-indexed terms, single-line rewrites
using a single Mathlib notation `ord_compl[2]`. The closed form is now
keyed off the parity of `n` alone, which is the form that Eisenstein
coefficients on Γ₀(4) take in the canonical proof. The open axiom
`jacobi_r4_formula` is unchanged.

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

- Total attempts: 12.
- S1 (researcher-?): OBSERVE/ORIENT bootstrap (axiomatize, n = 1..10).
- S2 (researcher-10): ACT — σ*(n) = σ(n) − 4·σ(n/4)·[4∣n] structural.
- S3 (researcher-?): σ* on odd prime powers, σ*(2n)/σ*(4n) = 3·σ(n).
- S4 (researcher-4, 2026-05-08): σ*-multiplicativity + σ*(2^k) = 3.
- S5 (researcher-8, 2026-05-08): σ*(2^k · m) = 3·σ(m) closed form.
- S6 (researcher-11, 2026-05-08): Part 16 — unified `sigmaStar_decomp`
  / `jacobiR4_decomp` (single-formula `if`-form for k ≥ 0).
- S7 (researcher-10, 2026-05-08): Part 17 —
  `sigmaStar_exists_decomp_of_pos` / `jacobiR4_exists_decomp_of_pos`
  (existential closed form keyed off `n`).
- S8 (researcher-10, 2026-05-08): Part 18 —
  `sigmaStar_factorization_form` / `jacobiR4_factorization_form`
  (constructive n-keyed closed form using `ord_compl[2] n`).
- S9 (researcher-11, 2026-05-08): Part 19 —
  `r4Count_factorization_form` (r4Count side Eisenstein-coefficient
  closed form `(if 2 ∣ n then 24 else 8)·σ(ord_compl[2] n)`,
  1-line corollary of `jacobi_r4_formula` + S8).
- S10 (researcher-?, 2026-05-08, PR #17359): Part 20 —
  `jacobiR4_mul_of_coprime` / `r4Count_mul_of_coprime` /
  `r4Count_two_pow_mul_odd` (multiplicativity bridge for `jacobiR4`
  and `r4Count` at coprime arguments, deriving from
  `sigmaStar_mul_of_coprime` and `jacobi_r4_formula`).
- S11 (researcher-?, 2026-05-08, PR #17395): Part 21 —
  `sigmaStar_pos` / `sigmaStar_one_le` / `eight_dvd_jacobiR4` /
  `jacobiR4_eight_le` / `jacobiR4_pos` / `r4Count_eight_le` /
  `r4Count_pos` / `eight_dvd_r4Count` / `sigmaStar_odd_prime` /
  `jacobiR4_odd_prime` / `r4Count_odd_prime` (positivity,
  8-divisibility, and odd-prime k = 1 closed forms).
- S11.alt (researcher-?, 2026-05-08, PR #17388 build pending):
  alternative Part 21 — `jacobi_r4_formula_from_atomic` (axiom-free
  reduction of Jacobi's formula to three elementary `r4Count` facts:
  odd case, pure-2-power case, coprime multiplicativity).
- S12 (researcher-11, 2026-05-08): Part 22 —
  `jacobiR4_prime_pow_of_odd_prime` / `r4Count_prime_pow_of_odd_prime`
  (closed form on odd prime POWERS for arbitrary `k ≥ 0`,
  generalizing S11's k = 1 case).
- Approaches tried: 1 (Approach A — modular form bridge).

## Blockers

- **Mathlib q-expansion infrastructure absent** for `jacobiTheta` —
  unchanged from S1.
- **Mathlib Eisenstein-coefficient identification absent** — unchanged.
- **Local Docker build verification**: S7 continues the "build pending"
  pattern (precedent: S6, sperner-ndim-mathlib-oq-02 S13/S14) — the
  proofs/.lake self-referential symlink forces a fresh Mathlib clone
  per Docker build (~45 min cold). The S7 additions are 7-line wrappers
  on already-proven S6 lemmas plus one Mathlib lookup
  (`Nat.exists_eq_pow_mul_and_not_dvd`); auditor pipeline carries the
  build outcome.

## Next Action

1. **(opportunistic, σ*-side AND r4Count-side closed)** When Mathlib
   gains q-expansion for `jacobiTheta` / `EisensteinSeries.E₂`, apply
   `r4Count_factorization_form` (S9) directly — the LHS of the
   modular-form identity `θ⁴ = 1 + 8·(E₂(τ) − 4·E₂(4τ))` matches
   `r4Count` at q^n by definition; the RHS evaluates at q^n to
   `(if 2 ∣ n then 24 else 8)·σ(ord_compl[2] n)` (closed form already
   proven). Two q-coefficient extractions plus this corollary close
   `jacobi_r4_formula`. No σ*-side intermediation needed.
2. **(productive, modular-form side, NEW STRUCTURAL DECOMPOSITION)**
   Bootstrap two atomic axioms targeting Mathlib roadmap:
   (a) `theta_pow_four_qExpansion : (1/(2π)) ∫ θ⁴ e^{-2πinτ} dτ = r4Count n`
       (definitional bridge between integer counting and q-coefficient).
   (b) `theta4_eq_eisenstein : θ⁴ = 1 + 8·(E₂(τ) − 4·E₂(4τ))`
       (the Jacobi-1834 modular-form identity).
   With (a) + (b) + Mathlib's `EisensteinSeries.E2_qExpansion`,
   `r4Count_factorization_form` (S9) closes `jacobi_r4_formula`.
   This decomposition is more atomic than the current single broad
   axiom and each piece is on a known Mathlib roadmap.
3. **(elementary, hard)** Direct combinatorial proof of
   `r4Count(2n) = 3·r4Count(n)` for odd n via the pairing bijection
   `(a,b,c,d) ↦ ((a+b)/2, (a-b)/2, (c+d)/2, (c-d)/2)` (~300-500 lines
   in Lean). Combined with σ*-multiplicativity, would close all
   prime-power cases except odd primes. Speculative.
4. **(speculative)** Hurwitz-quaternion route — Mathlib has
   quaternions but no Hurwitz integers; multi-month project upstream.
5. **(skip)** Brute-force extension beyond n = 10 — pure enumeration
   theater.

## References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — Parts 1-22:
  bootstrap (1-5), structural σ* ↔ σ (6-7), σ* on odd prime powers (8),
  σ*(2n) = σ*(4n) = 3·σ(n) for odd n (9-10), σ-multiplicativity bridge
  (11), σ*-multiplicativity (12), σ*(2^k) closed form (13),
  cross-validation (14), σ*(2^k · m) closed form (15, S5),
  unified `if`-form (16, S6), n-keyed existential decomp (17, S7),
  constructive `ord_compl[2]`-keyed closed form (18, S8),
  r4Count Eisenstein-coefficient form (19, S9), multiplicativity
  bridge for jacobiR4 / r4Count (20, S10), positivity / 8-divisibility
  / odd-prime corollary (21, S11), odd-prime-power closed form
  (22, S12).
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  per-session notes.
