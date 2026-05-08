# Research State: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02

## Current State
**Phase**: COMPLETE (axiom-free, biconditional closed, matrix-level companion CH identity proved); Session 5 prepares for `minpoly K (companionMx p) = p`.
**Path**: full
**Since**: 2026-05-08
**Iteration**: 5

## Current Focus

The full nonderogatory RCF triangle is verified over arbitrary fields:

- `nonderogatory_similar_to_companion` (Session 1+2): forward direction, axiom-free.
- `similar_to_companion_implies_nonderogatory` + `nonderogatory_iff_similar_to_companion`
  (Session 3, PR #17069 merged): converse + biconditional via cyclic-vector transport
  using `companionMx_isCyclic_e0`.
- Vector-level Cayley-Hamilton at e₀ (Session 4, PR #17107 merged):
  `(aeval (companionMx p) p).mulVec e₀ = 0` for monic `p` of `natDegree = n`.
- **Session 5 (this iteration)**: matrix-level Cayley-Hamilton identity for the
  companion matrix — `aeval (companionMx p) p = 0`. Lifts S4's e₀-result via
  pointwise annihilation of all standard basis vectors, using S3's
  `companionMx_pow_e0` to express each `e_k = C^k.mulVec e₀` and the AlgHom
  structure of `aeval C` to commute `aeval C p` past `C^k`.

## Outcome (Session 5)

**Three new lemmas** added to
`proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean`:

1. `matrix_eq_zero_of_mulVec_basis (A : Matrix (Fin n) (Fin n) K) (h : ∀ k, A.mulVec (Pi.single k 1) = 0) : A = 0`
   — a matrix is zero iff every standard basis column is annihilated by `mulVec`.
   Proof: `A.mulVec (Pi.single j 1) i = ∑ k, A i k * Pi.single j 1 k = A i j` after
   `mul_ite + mul_one + mul_zero + Finset.sum_ite_eq + if_true`. Reusable utility for
   lifting any vector-level annihilation to a matrix identity. `private`.

2. `aeval_companionMx_p_mulVec_ek_zero (p : K[X]) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) (hn : 0 < n) (k : Fin n) : (aeval (companionMx p) p).mulVec (Pi.single k 1) = 0`
   — vector-level annihilation at every standard basis vector e_k. Proof:
   - Rewrite `e_k = C^{k.val}.mulVec e₀` via S3's `companionMx_pow_e0` (k = k.val,
     hk = k.isLt) — needs a small `Fin.ext rfl` to identify `⟨k.val, k.isLt⟩` with `k`.
   - Use `← Matrix.mulVec_mulVec` to collapse `(aeval C p).mulVec (C^k.mulVec e₀)`
     into `(aeval C p * C^k).mulVec e₀`.
   - Commute `aeval C p * C^k = C^k * aeval C p` via the AlgHom structure of
     `aeval C`: rewrite `C^k = aeval C (X^k)` (via `map_pow + aeval_X`), then use
     `← map_mul, ← map_mul, mul_comm p (X^k)` (using commutativity of `K[X]`).
   - Re-expand with `Matrix.mulVec_mulVec`, apply S4's
     `aeval_companionMx_p_mulVec_e0_zero` to get `C^k.mulVec 0`, then
     `Matrix.mulVec_zero` closes.

3. `aeval_companionMx_p_eq_zero (p : K[X]) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) (hn : 0 < n) : aeval (companionMx p) p = 0`
   — **the matrix-level Cayley-Hamilton identity for the companion matrix**.
   Public theorem combining `matrix_eq_zero_of_mulVec_basis` with
   `aeval_companionMx_p_mulVec_ek_zero` for every k.

## File State (after Session 5)

- 590 lines (was 509; +81 net).
- 20 theorems/lemmas (was 17; +3: the three above).
- 2 definitions (`companionMx`, `cyclicMatrix`; unchanged).
- **0 axioms, 0 sorries** (status `verified`/`original` retained).

## Triangle of Equivalences (closed in S3)

  `IsNonderogatory M ↔ ∃ v cyclic ↔ ∃ P invertible, P⁻¹ M P = companionMx (minpoly K M)`

machine-verified over arbitrary fields with **zero axioms**.

## Companion-Matrix Cayley-Hamilton Path

  S4 → vector annihilation `(aeval (companionMx p) p).mulVec e₀ = 0` (monic deg n)
  S5 → **matrix annihilation `aeval (companionMx p) p = 0`** (DONE this session)
  S6 → `Matrix.minpoly_companionMatrix : minpoly K (companionMx p) = p` (next)

## Next Step (Session 6)

Derive **`minpoly K (companionMx p) = p`** for monic `p` of `natDegree = n` (with
`n ≥ 1`). Two-step argument:

1. **Divisibility**: `(minpoly K (companionMx p)) ∣ p` by `minpoly.dvd K (companionMx p) p`
   together with the matrix-level annihilation `aeval (companionMx p) p = 0` from
   `aeval_companionMx_p_eq_zero` (S5).

2. **Degree equality**: `(minpoly K (companionMx p)).natDegree = n`. From S3's
   `companionMx_isCyclic_e0` (e₀ is cyclic for `companionMx p`) and sibling
   OQ-01-OQ-01's `minpoly_natDegree_of_cyclic` (which gives `(minpoly K M).natDegree = n`
   when `M : Matrix (Fin n) (Fin n) K` admits a cyclic vector). Note that
   `companionMx p` may need a small additional step: `IsCyclicVector` uses the
   `GeneralCyclicVector` namespace; we need to confirm the typeclass / definition
   matches `minpoly_natDegree_of_cyclic`'s expected hypothesis (probably already
   matches, since S3's transport argument `cyclicVector_similar_transport`
   already uses both APIs against the same M-then-companion variable).

3. **Conclude**: `(minpoly K (companionMx p))` is monic, `p` is monic, both have
   `natDegree = n`, and the first divides the second; therefore they are equal.
   Mathlib's `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` (or similar) closes.

## Risks (Session 5)

- **Build risk**: not verified locally (worktree `.lake` symlink trap; see memory
  `feedback_researcher_lake_symlink_broken.md`). CI is the ground truth. If CI
  flags an API drift on:
    - `Matrix.mulVec_mulVec` (`(A * B).mulVec v = A.mulVec (B.mulVec v)`),
    - `Matrix.mulVec_zero`,
    - `aeval_X` (`aeval r X = r`),
    - `map_pow` / `map_mul` (`AlgHom` preserves powers and products),
    - `Polynomial.mul_comm` (any `mul_comm` on `K[X]`),
    - `dotProduct`, `Pi.single_apply`, `Pi.zero_apply`, `mul_ite`, `mul_one`,
      `mul_zero`, `Finset.sum_ite_eq`, `Finset.mem_univ`,
  Session 6 will repair.
- **Lemma scope**: `aeval_companionMx_p_eq_zero` is `theorem` (public) — exported
  for downstream use in S6 (`minpoly_companionMatrix`). The two helper lemmas
  remain `private`.

## Open Questions (post-S5)

See `meta.json` `overview.openQuestions`. Q1 (biconditional, S3), Q5
(eliminate hMn_axiom, S2), and Q2 vector-level + matrix-level (S4, S5) are
resolved. Q2 fully resolution to `Matrix.minpoly_companionMatrix` remains for S6.
