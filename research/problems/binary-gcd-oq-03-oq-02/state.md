# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 4

## Current Focus

Proving the **size-reduction lemma** `hgcdMatrix_size_reduction` — the
only sorry remaining in `proofs/Proofs/BinaryGcdOQ03OQ02.lean`. The
Session-3 (2026-05-01) work corrected a cofactor-convention mismatch
that would have made the lemma *false as previously stated*; the
lemma is now well-typed against the actual Lehmer-reduced pair.

Quantitative target:

```
bitsize (max (applyToNat (hgcdMatrix fuel a b) a b).1
             (applyToNat (hgcdMatrix fuel a b) a b).2)
  ≤ bitsize (max a b) / 2 + (hgcdThreshold + 2)
```

where `applyToNat M a b = (a·M.α + b·M.γ, a·M.β + b·M.δ)` (row
convention; see "Active Approach").

## Active Approach

**Correctness-only formalization** as recommended by Session 1.

* Session 2 (2026-05-01) put down the skeleton: `hgcdMatrix`,
  det-unit, gcd preservation, and the size-reduction lemma stated
  with `sorry`.
* Session 3 (2026-05-01) discovered and fixed a cofactor-convention
  mismatch:

  `lehmerCofactors` in `BinaryGcdOQ03.lean` accumulates the cofactor
  matrix in the **row-vector** convention: each Lehmer step
  `S_k = ⟨0, 1, 1, -q⟩` *right*-multiplies the accumulator
  (`M' = M · S_k`), so the maintained invariant is
  `(a₀, b₀) · M = (current pair)`.

  The previous Session-2 `applyToNat` used `M.apply` (column-vector
  product `M · (a, b)ᵀ`). This is *not* the row product
  `(a, b) · M`; the two differ as soon as `M.β ≠ M.γ`, which happens
  whenever Lehmer runs ≥ 2 steps with different quotients.

  Concrete counterexample (now a `native_decide` test in the file):
  for `(a, b) = (1000, 300)`, Lehmer on the top half `(31, 9)` builds
  `M = ⟨1, -2, -3, 7⟩`. Row-apply gives `(100, 100)` — reduced;
  column-apply gives `(400, 900)` — *larger* than the input. Both
  preserve gcd `100`, but only row-apply realises the half-bitsize
  reduction the size-reduction lemma claims.

  Fix in Session 3:

  - `applyToNat` rewritten to `(a·M.α + b·M.γ, a·M.β + b·M.δ)`.
  - `hgcdMatrix` recursive composition swapped from
    `M_rec.mul M_top` to `M_top.mul M_rec`, so that
    `(a, b) · (M_top · M_rec)` reads "apply top first, then recurse"
    in row convention.
  - `hgcdMatrix_apply_gcd` restated with the row product on the
    left-hand side; the proof reduces to `gcd_cofactor_eq` applied
    to the relabelled coefficients
    `(α, β, γ, δ) ← (M.α, M.γ, M.β, M.δ)` (det condition is
    symmetric under the swap `β ↔ γ`).
  - `hgcdMatrix_det_unit` updated to feed
    `mul_unit_of_unit_of_unit` in the new argument order.
  - File-level docstring and `applyToNat` docstring document the
    convention and the worked counterexample.

The two correctness theorems remain mechanical given the existing
cofactor-matrix machinery. The size-reduction lemma is the genuinely
new content, and its statement is now well-aligned with the actual
algorithm semantics.

## Blockers

* **Size reduction proof** requires an entry bound on
  `lehmerCofactors`: each entry of the accumulated matrix should be
  at most roughly `2^(fuel+1)`. This Lehmer entry-bound lemma does not
  appear to exist either in Mathlib or in `BinaryGcdOQ03.lean`, and
  must be proved inline.
* **Bit complexity (C)** remains genuinely blocked: Mathlib has no
  bit-complexity model and no fast multiplication. This is documented
  in `BinaryGcdOQ03OQ02.lean` Part V; not a blocker on (A) and (B).

## Next Action

1. Prove the Lehmer accumulator entry bound:
   `(lehmerCofactors fuel ahat bhat M).α ≤ ... bound ...` (and
   analogous for β, γ, δ). Likely by induction on fuel using
   `lehmerInnerStep_det` and the explicit step form
   `euclidStepMatrix q = ⟨0, 1, 1, -q⟩`.
2. Combine the entry bound with Cramer's rule (inverse of a
   unimodular matrix has the same entry bound up to sign) to bound
   `applyToNat (hgcdTopHalfStep a b) a b` by
   `2^(bitsize(max a b)/2 + 2)`.
3. Iterate the half-reduction twice (once at the top level, once in
   the recursive call) to close `hgcdMatrix_size_reduction`.
4. Once size reduction is proved, replace the explicit-fuel
   definition with a `WellFounded.fix` definition (lexicographic
   on `bitsize`).

## Attempt Counts

* Total attempts: 2 (Session 2 — skeleton; Session 3 — convention fix)
* Current approach attempts: 2
* Approaches tried: 1 (HGCD as Lehmer-step composition with explicit
  fuel; row-vector cofactor convention)
