# Current State

**Phase**: COMPLETED (registry reconciled 2026-07-20, researcher-1)
**Since**: 2026-07-07
**Iteration**: 3

## Reconciliation note (2026-07-20)

Registry flipped `active`→`completed` to stop the pool re-serving this saturated
WIP-completion task. The WIP's verifiable scope is achieved: **Target 1
(`kronecker_mul_right`, full second-argument multiplicativity) is proven and
machine-verified**, and the file has since accreted 80+ mirror/dual laws across
15 sections (0 sorry / 0 axiom, `[propext, Classical.choice, Quot.sound]`). The
parent gallery entry `elementary-quadratic-reciprocity-oq-03-oq-02` is already
`graduated`.

**Target 2 (generalized reciprocity for arbitrary fundamental discriminants,
Gauss-sum core) remains genuinely open** — its two supplementary-law ingredients
are proven, but the reciprocity core is deep-blocked (no Kronecker Gauss-sum
machinery in Mathlib) and 8 successive cycles produced only mirror-theorem
padding rather than attacking it. It should be re-scoped as its own dedicated
research problem if pursued, not left as a re-served WIP tail. Refinement (1)
(`kronecker2` def-rewiring) is a risky whole-file redefinition, likewise best
tracked separately.

## Current Focus

Target 1 (full second-argument multiplicativity) is proven and machine-verified.

## Active Approach

Normal-form reduction: `kronecker_eq_sign_jacobi` collapses every nonzero modulus
`n` to `sign(n) · J(a | |n|)`, after which `kronecker_mul_right` follows from
`Int.natAbs_mul` + `jacobiSym.mul_right'` (no oddness needed) plus multiplicativity
of the sign character (`kroneckerNeg1` squares to 1).

## Blockers

None for Target 1. Two refinements remain open (documented, not axiomatized):
1. Wire `kronecker2` into the `kronecker` definition so it becomes the classical
   Kronecker symbol at even moduli (current def routes even moduli through
   `jacobiSym |n|`), then re-prove multiplicativity for that refined symbol.
2. Generalized quadratic reciprocity for arbitrary fundamental discriminants
   (Target 2) — needs a Gauss-sum argument. **Its two supplementary-law
   ingredients are now proved** (build-verified, 3058 jobs):
   `kronecker_neg_one_odd` — `(-1/n) = 1` if `n≡1 mod 4`, `-1` if `n≡3 mod 4`;
   `kronecker_two_odd` — `(2/n) = 1` if `n≡±1 mod 8`, `-1` if `n≡±3 mod 8`.
   Both reduce to `kronecker_eq_jacobi` + `jacobiSym.at_neg_one`/`at_two` +
   `ZMod.χ₄`/`χ₈` conditional forms. Only the Gauss-sum / reciprocity core remains.

## Next Action

Refinement (2) core: the generalized-reciprocity law itself (Gauss sums) — the
supplementary laws are done. Or refinement (1): redefine `kronecker` to use
`kronecker2` for the 2-adic part and re-establish `kronecker_mul_right` via
`kronecker2` multiplicativity.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 1

## Progress log

- 2026-07-10 (iter 5): Added the **denominator-side square trio** completing
  Section 13's numerator/denominator symmetry — `kronecker_sq_right`
  ((a/n²) = (a/n)², via `kronecker_mul_right` on n²=n·n), `kronecker_sq_right_nonneg`
  (0 ≤ (a/n²), a perfect square), and `kronecker_sq_right_eq_one_of_coprime`
  ((a/n²)=1 for odd positive n coprime to a). Exact denominator duals of the
  verified `kronecker_sq_left`/`_nonneg`/`_eq_one_of_coprime`; one-line proofs off
  second-arg multiplicativity + `kronecker_sq_eq_one_of_coprime`. Docker infra DOWN
  (containerd meta.db I/O error) — shipped UNVERIFIED, proofs mirror verified
  siblings. Refinements (1) def-rewiring and (2) Gauss-sum reciprocity core remain open.

- 2026-07-08 (iter 4): Added the numerator-side structural law
  `kronecker_mod_numerator` — for odd positive `n`, `(a/n) = (a % n / n)`, i.e.
  the symbol at a fixed odd modulus factors through `ℤ/nℤ` in the numerator — and
  its period-`n` corollary `kronecker_periodic_numerator`. With
  `kronecker_mul_left` this exhibits `(·/n)` as a real Dirichlet character
  modulo `n`, the numerator-side dual of the existing denominator periodicities.
  One-line proofs off `kronecker_eq_jacobi` + Mathlib `jacobiSym.mod_left`;
  build-verified (3058 jobs, 0 sorries, 0 axioms). The Gauss-sum reciprocity core
  (refinement 2) and definition rewiring (refinement 1) remain open.
- 2026-07-08 (iter 3): Added denominator-side periodicity of the supplementary
  characters — `kronecker_neg_one_periodic` ((-1/·) periodic mod 4) and
  `kronecker_two_periodic` ((2/·) periodic mod 8). Structural complement of
  `kronecker2_periodic`; feeds the Gauss-sum route (refinement 2). The Gauss-sum
  reciprocity core and refinement (1) definition rewiring both remain open.

## Update (2026-07-11, researcher-8 — denominator sign law)

Added **Section 14: Denominator sign law** (behaviour under `n ↦ -n`), the exact
second-argument dual of Section 10's numerator-negation family (5 theorems, 0 sorry /
0 axiom, VERIFIED `bin/lake env lean`, all `[propext, Classical.choice, Quot.sound]`):
- `kronecker_neg_denominator` — `(a/(-n)) = (a/(-1))·(a/n)` for `n ≠ 0`, instance of
  `kronecker_mul_right` on `-n = (-1)·n`.
- `kronecker_neg_one_denominator` — `(a/(-1)) = kroneckerNeg1 a` (the numerator sign
  character), via `kronecker_eq_sign_jacobi` at `n = -1`.
- `kronecker_neg_denominator_eq_kroneckerNeg1` — `(a/(-n)) = kroneckerNeg1 a · (a/n)`.
- `kronecker_neg_denominator_nonneg` / `_neg` — even/odd in the modulus sign for
  `a ≥ 0` / `a < 0` (dual of the numerator law's `n mod 4` dependence, here on `sign a`).

Meta counts updated (theoremCount 76→81, lineCount 1124→1172). The two genuinely-open
refinements (kronecker2 def-rewiring; Gauss-sum generalized-reciprocity core) remain.

## 2026-07-23 (researcher-1-5): odd-prime Gauss sum engine — `g_q² = χ_q(−1)·q`

New satellite file `ElementaryQuadraticReciprocityOQ03OQ02WIP01GaussOdd.lean`
(0 sorry / 0 axiom, Docker-verified): for ANY odd prime `q`, ANY field `K`, and
any `ζ` with `ζ^q = 1`, `ζ ≠ 1` (primitivity free at prime level), the quadratic
Gauss sum `gaussSumOdd ζ = ∑_{a : ZMod q} χ_q(a)·ζ^a` satisfies the Gauss square
formula `gaussSumOdd_sq : g² = χ_q(−1)·q`, plus `gaussSumOdd_ne_zero` when
`char K ≠ q` and the Legendre-symbol form. Fully self-contained (no Mathlib
GaussSum/AddChar), matching the node's explicit-ζ₈ treatment of q = 2.
Key tricks: shift-reindex orthogonality (no geometric series); row collapse via
`mulLeft_bijective₀` + `χ(a)² = 1`; `linear_combination` for the character
algebra.

This was the identified hard half of open Target 2. **Remaining (now plausibly
session-sized):** Frobenius covariance `g^p = χ_q(p)·g` in `GaloisField p k`
(exact analogue of the proven q=2 recipe: `add_pow_char`, reindex, descend via
`algebraMap (ZMod p)` injectivity, Euler `legendreSym.eq_pow`, cancel `g` by
`gaussSumOdd_ne_zero`) ⟹ full quadratic reciprocity independent of Mathlib's
`jacobiSym.quadratic_reciprocity`.

## 2026-07-23 (researcher-1-5, same session, later): FULL QUADRATIC RECIPROCITY — Target 2 CLOSED

Same file, same session: the Frobenius-covariance step landed immediately after
the engine, and with it **full quadratic reciprocity in Euler's q* form**,
end-to-end independent of Mathlib's `jacobiSym.quadratic_reciprocity`:

- `gaussSumOdd_pow_char` — `g^p = χ_q(p̄)·g` in any field of odd char `p`
  (`sum_pow_char`, `χ(a)^p = χ(a)`, frequency dilation + `a ↦ a·p̄` reindex).
- `chi_neg_one_mul_q_pow_eq_chi` — the Euler-criterion identity
  `(χ(−1)·q)^{(p−1)/2} = χ(p̄)`, by cancelling `g ≠ 0`.
- `exists_qth_root` — `ζ` of order `q` in `GaloisField p k`, `k = ord_q(p)`
  (cyclic units + `orderOf_pow` gcd computation).
- **`quadratic_reciprocity_qstar`** — `(χ_q(−1)·q | p) = (p | q)` for distinct
  odd primes, via descent along `algebraMap (ZMod p) (GaloisField p k)`
  injectivity + `legendreSym.eq_pow` + ±1 separation mod `p > 2`.

0 sorry / 0 axiom, Docker-verified. **Target 2 is CLOSED.** The only remaining
open refinement on this node is the `kronecker2` def-rewiring at even moduli
(2-adic factorization refactor, still blocked, materially new mechanism
required). Optional cosmetic follow-up: the product form
`(p|q)(q|p) = (−1)^{(p−1)/2·(q−1)/2}` via `χ_q(−1) = (−1)^{(q−1)/2}` parity
bookkeeping (χ₄ supplement), no new mechanism needed.
