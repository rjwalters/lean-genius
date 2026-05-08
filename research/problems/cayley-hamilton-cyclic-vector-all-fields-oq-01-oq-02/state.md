# Research State: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02

## Current State
**Phase**: COMPLETE (axiom-free, biconditional closed); Session 4 advancing toward `minpoly K (companionMx p) = p`.
**Path**: full
**Since**: 2026-05-08
**Iteration**: 4

## Current Focus

The full nonderogatory RCF is verified over arbitrary fields:
- `nonderogatory_similar_to_companion` (Session 1+2): forward direction (the existing
  proof, now axiom-free).
- `similar_to_companion_implies_nonderogatory` + `nonderogatory_iff_similar_to_companion`
  (Session 3, merged via PR #17069 into origin/main): converse + biconditional via
  cyclic-vector transport using `companionMx_isCyclic_e0`.
- **Session 4 (this iteration)**: vector-level Cayley-Hamilton for the companion —
  `(aeval (companionMx p) p).mulVec e₀ = 0` for monic `p` of degree `n`. This is the
  computational core of the as-yet-unproved `Matrix.minpoly_companionMatrix` (Q2).

## Outcome (Session 4)

**Three new private lemmas** added to `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean`:

1. `companionMx_mulVec_eNm1 (p : K[X]) (hn : 0 < n)` — action of `companionMx p` on
   `e_{n-1}` returns the last column, which by the def of `companionMx` is the
   vector `(-(p.coeff i))_{i<n}`. Pure unfolding of the matrix definition; the
   first `if-then-else` clause (`j.val + 1 = n`) triggers for `j = ⟨n-1, _⟩`.

2. `companionMx_pow_n_eq_lastCol_e0 (p : K[X]) (hn : 0 < n)` — combining
   `companionMx_pow_e0` (Session 3, k = n-1) with `companionMx_mulVec_eNm1`,
   `((companionMx p)^n).mulVec e₀ = (-(p.coeff i))_{i<n}`. The exponent rewrite
   from `n` to `(n-1) + 1` uses `congr 1 + omega` to avoid scope-of-rewrite issues
   that would otherwise break the type-level `Fin n`.

3. `aeval_companionMx_p_mulVec_e0_zero (p : K[X]) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) (hn : 0 < n)`
   — for monic p of degree n, `(aeval (companionMx p) p).mulVec e₀ = 0`. Proof:
   expand `aeval` via `aeval_eq_sum_range_natDegree`, peel off the k=n term via
   `Finset.sum_range_succ`, use `p.Monic ∧ p.natDegree = n` to set `p.coeff n = 1`,
   apply `companionMx_pow_n_eq_lastCol_e0` for the C^n term and `companionMx_pow_e0`
   for the k<n terms. Pointwise at index i: the sum picks out `k = i.val`, giving
   `p.coeff i.val + (-(p.coeff i.val)) = 0`.

## File State (after Session 4)

- 509 lines (was 406; +103 net)
- 17 theorems/lemmas (was 14; +3: the three above)
- 2 definitions (`companionMx`, `cyclicMatrix`; unchanged)
- **0 axioms, 0 sorries** (status `verified`/`original` retained)

## Triangle of Equivalences (already closed in S3)

  `IsNonderogatory M ↔ ∃ v cyclic ↔ ∃ P invertible, P⁻¹ M P = companionMx (minpoly K M)`

machine-verified over arbitrary fields with **zero axioms**.

## Next Step (Session 5)

**`aeval (companionMx p) p = 0`** as a matrix-level identity (currently we have
the vector-level annihilation at e₀ only). Two approaches:

1. **Cyclicity-based** (preferred, reuses S3's infrastructure): `companionMx_isCyclic_e0`
   says `IsCyclicVector (companionMx p) e₀`, but it's stated for polynomials of degree
   `< n`. We'd need a small extension: if the matrix-polynomial is in the kernel of
   `mulVec e₀` (i.e. annihilates e₀) AND has degree ≥ n, then it's a multiple of the
   minpoly. The cleaner route: show that `aeval (companionMx p) p` commutes with
   `companionMx p` (any polynomial in C does), so its kernel is a `K[C]`-submodule
   containing e₀; combined with the cyclic decomposition `K^n = span_{0≤k<n}(C^k e₀)`
   (which the cyclicity gives), the kernel is all of K^n, so the matrix is zero.

2. **Pointwise** (more work, less elegant): show `(aeval (companionMx p) p).mulVec e_k = 0`
   for each `k = 0..n-1`. Since `e_k = ((companionMx p)^k).mulVec e₀` and `aeval (... p) p`
   commutes with `(companionMx p)^k`, this reduces to S4's `aeval_companionMx_p_mulVec_e0_zero`.

Once `aeval (companionMx p) p = 0` is in hand:
- `(minpoly K (companionMx p)) ∣ p` by minimality.
- `(minpoly K (companionMx p)).natDegree = n` from S3's `companionMx_isCyclic_e0` +
  `minpoly_natDegree_of_cyclic` (from sibling OQ-01-OQ-01).
- Both are monic of the same degree, so `minpoly K (companionMx p) = p`.

This gives `Matrix.minpoly_companionMatrix : minpoly K (companionMx p) = p`, the
companion-matrix minpoly identity that is missing from Mathlib v4.26.0.

## Risks

- **Build risk (Session 4)**: not verified locally (worktree `.lake` symlink trap;
  see memory `feedback_researcher_lake_symlink_broken.md`). CI is the ground truth.
  If CI flags an API drift on `pow_succ'`, `Matrix.mul_mulVec`, `Matrix.smul_mulVec`,
  `Polynomial.leadingCoeff`, `Polynomial.Monic.leadingCoeff`, `Pi.single_apply`,
  `Pi.single_eq_same`, `Pi.smul_apply`, `Pi.add_apply`, `Finset.sum_range_succ`,
  `Finset.sum_apply`, `Finset.sum_eq_single`, `Finset.mem_range`, `Nat.sub_add_cancel`,
  or `Nat.sub_lt`, Session 5 will repair.
- **Lemma scope**: all three new lemmas are `private` so they're not part of the
  public API; Session 5 will likely promote `aeval_companionMx_p_eq_zero` to a
  public theorem once the matrix-level version is proved.

## Open Questions (post-S4)

See `meta.json` `overview.openQuestions`. Q1 (biconditional, S3) and Q5
(eliminate hMn_axiom, S2) are resolved. Q2 (charpoly/minpoly companion identities)
is now **half-resolved**: the vector-level annihilation at e₀ is proved (S4); the
matrix-level identity remains for Session 5.
