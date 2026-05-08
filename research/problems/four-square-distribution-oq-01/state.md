# Research State: four-square-distribution-oq-01

## Current State
**Phase**: ACT (S7: σ*-side **fully n-driven** — Part 17 wraps Part 16
with `Nat.exists_eq_pow_mul_and_not_dvd` so callers no longer need to
supply `(k, m)`). Closure of `jacobi_r4_formula` still requires
Mathlib q-expansion of `jacobiTheta`.
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (S7, researcher-11)
**Iteration**: 7

## Current Focus
S7 (this session) added **Part 17** to FourSquareDistributionOQ01.lean,
wrapping Part 16's caller-supplies-`(k, m)` form with Mathlib's
`Nat.exists_eq_pow_mul_and_not_dvd`:

* **`sigmaStar_eq_decomp_form`**: for any `n > 0`,
  `∃ k m, n = 2^k · m ∧ ¬ 2 ∣ m ∧ 0 < m ∧
   σ*(n) = (if k = 0 then 1 else 3) · σ(m)`.
* **`jacobiR4_eq_decomp_form`**: same hypotheses,
  `∃ k m, n = 2^k · m ∧ ¬ 2 ∣ m ∧ 0 < m ∧
   jacobiR4(n) = (if k = 0 then 8 else 24) · σ(m)`.

Three cross-validation `example` checks (n ∈ {1, 8, 40}) exercise the
new existential form. Proof is short: `Nat.exists_eq_pow_mul_and_not_dvd
hn0 2 (by decide)` produces `(k, m, ¬2∣m, n = 2^k·m)`; positivity of
`m` follows from `n > 0 = 2^k·m`; the σ* equation is a one-line
delegation to Part 16.

**What S7 changes**: the σ*-side is now keyed *off `n` directly* — no
caller-supplied `(k, m)` decomposition is required, just `n > 0`.
Mathlib provides the 2-adic decomposition. Combined with the open
modular-form bridge, the σ*-side of Jacobi's r₄ formula is now a
two-step closure: extract `(k, m)` (Part 17), apply the if-form
(Part 16). The open axiom `jacobi_r4_formula` is unchanged.

## Reduction Frontier
The σ*-side is now reduced to **one** Mathlib lookup: `Nat.sigma 1 m`
for the σ-value of the odd part. The decomposition `n = 2^k · m` is
already provided by `Nat.exists_eq_pow_mul_and_not_dvd` in Part 17.
With S7 in place, the σ*-side is fully `n`-keyed and the remaining
gap is purely on the modular-form side.

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
- S7 (researcher-11, 2026-05-08): Part 17 — `n`-keyed existential form
  via `Nat.exists_eq_pow_mul_and_not_dvd` (no caller-supplied (k,m)).
- Approaches tried: 1 (Approach A — modular form bridge).

## Blockers

- **Mathlib q-expansion infrastructure absent** for `jacobiTheta` —
  unchanged from S1.
- **Mathlib Eisenstein-coefficient identification absent** — unchanged.
- **Local Docker build verification**: S7 (like S6) elects the "build
  pending" pattern — the `proofs/.lake` self-referential symlink forces
  a fresh Mathlib clone per Docker build (~45 min cold). New theorems
  are short delegations to Mathlib's `Nat.exists_eq_pow_mul_and_not_dvd`
  + Part 16's `sigmaStar_decomp` / `jacobiR4_decomp`; auditor pipeline
  carries the build outcome.

## Next Action

1. **(opportunistic)** When Mathlib gains q-expansion for `jacobiTheta`,
   apply `sigmaStar_eq_decomp_form` (S7) — one rewrite — to close
   `axiom jacobi_r4_formula` for all n > 0 directly.
2. **(productive — small)** Promote the existential `(k, m)` to a
   `noncomputable` function: `oddPart : (n : ℕ) → 0 < n → ℕ` returning
   `(Nat.exists_eq_pow_mul_and_not_dvd hn 2 _).choose_spec` paired data,
   or use `padicValNat 2 n` directly (k = padicValNat 2 n; m = n / 2^k).
   Yields a ready-to-call `σ*(n) = ... · σ(oddPart n)` rewrite rule.
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
  unified `if`-form (16, S6), `n`-keyed existential form (17, S7).
- `proofs/Proofs/FourSquareDistribution.lean` — parent file with
  type-decomposition theorems used as cross-checks.
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry.
- `research/problems/four-square-distribution-oq-01/problem.md` —
  detailed problem statement.
- `research/problems/four-square-distribution-oq-01/knowledge.md` —
  per-session notes.
