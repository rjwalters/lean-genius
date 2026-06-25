# chebyshev-bounds-oq-02 — knowledge

## Problem

Parent `chebyshev-bounds-oq-02` (the second Chebyshev function ψ + Legendre's identity) had an
open direction: compare ψ to the first Chebyshev function θ and quantify their difference
(`ψ − θ = ∑_{k≥2} θ(n^{1/k}) = O(√n·log²n)`, the "same main term" statement). This is the leaf
`chebyshev-bounds-oq-02-oq-02`.

## Session 2026-06-25 (Session 1) — FRESH — COMPLETED (verified, Mathlib-reliant)

**Mode**: FRESH. **Outcome**: completed as a verified bridge entry.

### Key finding — Mathlib already has the deep content

`Mathlib.NumberTheory.Chebyshev` (present in Mathlib 4.26.0) already provides:
- `Chebyshev.psi`, `Chebyshev.theta` (ℝ-argument).
- `Chebyshev.psi_sub_theta_eq_sum_not_prime` — the ψ − θ = ∑_{¬prime} Λ decomposition.
- `Chebyshev.psi_eq_theta_add_sum_theta` — ψ(x) = θ(x) + ∑_{k=2}^{⌊log₂x⌋} θ(x^{1/k}) (the exact
  `∑_{k≥2} θ(x^{1/k})` identity).
- `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` — `|ψ(x) − θ(x)| ≤ 2·√x·log x`, which is
  **sharper** than the `O(√n·log²n)` the candidate targeted.

So the candidate's mathematical content is fully subsumed by Mathlib. Re-deriving it from scratch
over the parent's ℕ-indexed ψ would be dishonest duplication.

### What was delivered (`Proofs/ChebyshevBoundsOQ02OQ02.lean`, 146 lines, 0 sorry/0 axiom)

The honest, non-duplicative contribution is a **bridge** plus a direct decomposition:
- `chebyshevTheta` def + `chebyshevTheta_eq_sum_vonMangoldt` (θ = prime part of ψ via
  `vonMangoldt_apply_prime`).
- `psi_sub_theta` : ψ(n) − θ(n) = ∑_{m≤n, ¬prime} Λ(m) — direct, gallery-facing decomposition;
  plus `psi_sub_theta_nonneg`, `theta_le_psi`, and `psi_sub_theta_eq_proper_prime_powers`
  (support = {IsPrimePow ∧ ¬prime}).
- `chebyshevPsi_eq_mathlib` / `chebyshevTheta_eq_mathlib` : bridges identifying the parent's
  self-contained ℕ ψ/θ with Mathlib's `Chebyshev.psi`/`theta` at integer arguments (one-line
  `Finset.sum_congr` along `Icc 1 n = Ioc 0 n` after `Nat.floor_natCast`).
- `psi_sub_theta_eq_sum_theta` and `abs_psi_sub_theta_le` : the candidate's headline identity and
  bound, transported to the gallery's ψ via the bridge + the two Mathlib theorems.

Gallery entry uses **badge `verified` (not `original`)** because the deep analytic results are
Mathlib's; the entry's own content is the bridge and the elementary decomposition.

### Technique

- Bridge pattern: `rw [<gallery def>, Nat.floor_natCast, <Mathlib def>]; Finset.sum_congr (index-set eq)`.
- The parent's `chebyshevPsi` (∑ over `Icc 1 n`) and Mathlib's `Chebyshev.psi` (∑ over `Ioc 0 ⌊x⌋`)
  coincide at integer x; `Icc 1 n = Ioc 0 n` is the only index-set lemma needed.

### Mathlib gaps

None — Mathlib's Chebyshev development is complete for this comparison and sharper than targeted.

### Next steps

None for this leaf. Future Chebyshev-thread work should build on Mathlib's `Chebyshev` API
directly (now bridged in) rather than re-deriving over the parent's elementary ψ.
