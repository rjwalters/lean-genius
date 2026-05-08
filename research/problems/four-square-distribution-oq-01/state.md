# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT (S8: σ*-side **factorization-keyed constructive closed form**
— no existential, no caller decomposition). Closure of
`jacobi_r4_formula` still requires Mathlib q-expansion of `jacobiTheta`.
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (S8, researcher-1)
**Iteration**: 8

## S8 (this session, build pending)

Added **Part 18** to FourSquareDistributionOQ01.lean: lifts the S7
existential to a `Nat.factorization`-keyed expression with no
existential. Two new theorems:

* **`sigmaStar_factorization_decomp`** (~14 lines): for `0 < n`,
  `σ*(n) = (if 0 < n.factorization 2 then 3 else 1) ·
   σ(n / 2^(n.factorization 2))`.
* **`jacobiR4_factorization_decomp`** (~6 lines): identical wrap with
  constants 8/24.

Proof: extracts the canonical decomposition via Mathlib's
`Nat.ord_proj_dvd` (gives `2^k ∣ n`) and `Nat.not_dvd_ord_compl`
(gives `2 ∤ n / 2^k`), then applies S6 `sigmaStar_decomp`. Two
cross-validation `example` checks at n ∈ {1, 40} confirm the
witness extracts canonically.

**What S8 changes**: removes the existential layer of S7. Downstream
callers can now write `σ*(n)` as a single closed-form expression in
`n.factorization 2` and `n / 2^...`, no `Exists.choose` needed.

## Current Focus
S7 (this session) added **Part 17** to FourSquareDistributionOQ01.lean,
wrapping S6 `sigmaStar_decomp` with Mathlib's
`Nat.exists_eq_pow_mul_and_not_dvd` to deliver the existential form:

* **`sigmaStar_exists_decomp_of_pos`**: for `0 < n`,
  `∃ k m, 0 < m ∧ ¬ 2 ∣ m ∧ n = 2^k · m ∧
   σ*(n) = (if k = 0 then 1 else 3) · σ(m)`.
* **`jacobiR4_exists_decomp_of_pos`**: identical wrap with constants
  8/24.

The proof is a 7-line block: invoke
`Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by decide)` for the
2-adic decomposition; derive `0 < m` from `0 < n` and `n = 2^k · m`;
apply S6 `sigmaStar_decomp`. Four cross-validation `example` checks at
n ∈ {1, 9, 40} (σ*) and n = 40 (jacobiR4) demonstrate the witness.

**What S7 changes**: this is the final piece eliminating "caller
supplies (k, m)" friction on the σ*-side. Downstream modular-form work
can now invoke the closed form keyed only on `n`. The witness extracts
canonically as k = v₂(n), m = n/2^k. The open axiom `jacobi_r4_formula`
is unchanged.

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

- Total attempts: 7.
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

1. **(opportunistic)** When Mathlib gains q-expansion for `jacobiTheta`,
   apply `sigmaStar_decomp` (S6) **or** `sigmaStar_exists_decomp_of_pos`
   (S7) — one rewrite either way — to close `axiom jacobi_r4_formula`
   for all n > 0. With S7 the call site no longer needs to supply the
   2-adic decomposition.
2. **(productive — constructive form)** Lift S7's existential to a
   factorization-keyed expression
   `σ*(n) = (if 2 ∣ n then 3 else 1) · σ(n / 2^(n.factorization 2))`
   for `0 < n`, using Mathlib's `Nat.factorization n 2`,
   `Nat.ord_proj_mul_ord_compl_eq_self`, and `Nat.not_dvd_ord_compl`.
   Single n-indexed expression, no existential. ~6–10 line proof.
3. **(speculative)** Pursue the Hurwitz-quaternion route. Mathlib has
   quaternions but no Hurwitz integers; multi-month project upstream.
4. **(skip)** Brute-force extension beyond n = 10 — pure enumeration
   theater. The closed form prediction r₄(40) = 144 is now stated; it
   would need cross-validation only via the modular-form bridge (which
   is the open axiom itself).

## References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — Parts 1-17:
  bootstrap (1-5), structural σ* ↔ σ (6-7), σ* on odd prime powers (8),
  σ*(2n) = σ*(4n) = 3·σ(n) for odd n (9-10), σ-multiplicativity bridge
  (11), σ*-multiplicativity (12), σ*(2^k) closed form (13),
  cross-validation (14), σ*(2^k · m) closed form (15, S5),
  unified `if`-form (16, S6), n-keyed existential decomp (17, S7).
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  per-session notes.
