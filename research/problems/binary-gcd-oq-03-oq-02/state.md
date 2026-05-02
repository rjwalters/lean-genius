# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 4

## Current Focus

Pursuing the **size-reduction lemma** `hgcdMatrix_size_reduction`
(currently a `True` placeholder in `BinaryGcdOQ03OQ02.lean` PART VI).
The 4-step proof plan is:

1. **Step 1** ✅ (Session 3, 2026-05-02): Matrix-vector invariant.
   `lehmerCofactors_invariant`: the row-vector relation
   `(a₀, b₀) · M = (current pair)` is preserved by `lehmerCofactors`
   in the row convention. PART V.5 of `BinaryGcdOQ03OQ02.lean`.
2. **Step 2a** ✅ (Session 3, 2026-05-02): Residue monotonicity.
   `lehmerCofactors_invariant_le`: combines (1) with the bound
   `max ahat' bhat' ≤ max ahat bhat`. PART V.5.
3. **Step 2b** ⏳ (next session): Cramer-inversion entry bound on
   the cofactor matrix. From the row-vector invariant and `det M
   = ±1`, invert to bound each entry of M.
4. **Step 3** ⏳: Perturbation bound between `(a, b) · M` and the
   top-half-truncated `(aHi · 2^shift, bHi · 2^shift) · M`.
5. **Step 4** ⏳: Compose Steps 2b + 3 + 2a to close
   `hgcdMatrix_size_reduction` with explicit constants.

Concurrently: bit-complexity claim O(M(n)·log n) remains genuinely
blocked on Mathlib (no fast multiplication, no bit-complexity model).

## Active Approach

**Correctness layer + size-reduction infrastructure** (additive to
the merged Path A from Session 2).

* Session 2 (2026-05-01) merged via PR #14389: correctness layer
  for `hgcdMatrix` (det ±1, GCD preservation), 0 sorries, 1
  placeholder for size reduction.
* Session 3 (2026-05-02) added PART V.5 to the merged file: 8
  theorems for the matrix-vector invariant + residue monotonicity,
  with a convention-finding docstring explaining why these need to
  be stated in the row convention rather than the column-action
  `apply` used by `cofactor_apply_gcd`.

The merged file's column-convention `apply` is correct for the
det-based theorems but is **not** the right operator for stating
size reduction. Session 3's PART V.5 introduces the row-convention
relation directly without redefining `apply`, keeping the merged
correctness layer untouched.

## Blockers

* **Step 2b (next-session focus)**: Cramer-inversion entry bound on
  cofactor matrix. Self-contained — no Mathlib gap.
* **Bit complexity (C)**: genuinely blocked on Mathlib infrastructure.
  Documented in `BinaryGcdOQ03OQ02.lean` PART VII; not a blocker on
  (A) correctness or (B) size reduction.
* **PR #14097**: prior researcher branch with the same lemmas in a
  divergent file structure. State CONFLICTING; should be closed as
  superseded by this session's PR.

## Next Action

1. **Session 4**: Cramer-inversion entry bound. The row-vector
   relation `(a₀, b₀) · M = (ahat', bhat')` from
   `lehmerCofactors_invariant` plus `det M = ±1` gives
   `(a₀, b₀) = (ahat', bhat') · M⁻¹` where
   `M⁻¹ = ⟨δ, -β, -γ, α⟩ / det M`. Bound each entry of `M⁻¹` by
   `max a₀ b₀ / max ahat' bhat'`; combine with residue monotonicity
   (`max ahat' bhat' ≤ max ahat bhat`) for the entry bound on M.
2. **Session 5**: Perturbation bound on the truncated top-half
   input. The Lehmer step is computed on `(aHi, bHi) =
   (a >> shift, b >> shift)`; we need to bound the "low-bit"
   contribution to the full-precision result.
3. **Session 6**: Close `hgcdMatrix_size_reduction` using Steps
   2a + 2b + 3.

## Attempt Counts

- Total attempts: 3 (Sessions 1, 2, 3)
- Approaches tried:
  - Path A (fuel-indexed correctness): succeeded, merged in Session 2
  - Row-convention size-reduction infra: in progress (Session 3 added
    Steps 1 + 2a)
