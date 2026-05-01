# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 6

## Current Focus

Proving the **size-reduction lemma** `hgcdMatrix_size_reduction` — the
only sorry remaining in `proofs/Proofs/BinaryGcdOQ03OQ02.lean`. The
Session-3 (2026-05-01) work corrected a cofactor-convention mismatch
that would have made the lemma *false as previously stated*; the
lemma is now well-typed against the actual Lehmer-reduced pair.
Session 4 (2026-05-01) added the **matrix-vector invariant** for
`lehmerCofactors` — the foundational lemma underpinning the entry-
bound argument, which is Step 2 in the multi-step proof plan.

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

* Session 4 (2026-05-01) executed Step 1 of the next-action plan:
  the matrix-vector invariant for `lehmerCofactors`.

  Three new theorems in a new PART IV of `BinaryGcdOQ03OQ02.lean`
  (parts V/VI/VII renumbered):

  - `lehmerInnerStep_invariant`: per-step invariant. Given a "ghost
    original pair" `(a₀, b₀)` consistent with the current state
    `(ahat, bhat, M)` via `(a₀, b₀) · M = (ahat, bhat)`, the
    relation persists across one `lehmerInnerStep`. Proof unfolds
    `lehmerInnerStep`, splits on the two `if` branches, then
    discharges using `h_inv₁ - q · h_inv₂` plus `Nat.div_add_mod`.

  - `lehmerCofactors_invariant`: existential multi-step version.
    Inductive on `fuel`, applying the per-step lemma in the
    successor case via `match hstep : lehmerInnerStep ahat bhat M
    with` (the same destructuring pattern used in the existing
    `lehmerCofactors_det_unit` proof).

  - `lehmerCofactors_id_apply_eq`: specialisation to `M = id` and
    ghost pair = input pair. Direct corollary.

The two correctness theorems remain mechanical given the existing
cofactor-matrix machinery. The size-reduction lemma is the genuinely
new content, and its statement is now well-aligned with the actual
algorithm semantics. Step 1 (invariant) is done; Step 2a (residue
monotonicity) is done as of Session 5; Step 2b (entry bound via
Cramer inversion) and Step 3 (perturbation analysis) remain.

* Session 5 (2026-05-02) executed Step 2a of the next-action plan:
  residue monotonicity for `lehmerCofactors`.

  Four new theorems extending PART IV of `BinaryGcdOQ03OQ02.lean`:

  - `lehmerInnerStep_residue_le`: per-step bound. A successful
    `lehmerInnerStep` returns `ahat' = bhat` and `bhat' < bhat`.
    Proof follows the `lehmerInnerStep_det` pattern: unfold the
    definition, two `split at h <;> simp_all` calls eliminate the
    `if` chain, and `omega` handles `ahat % bhat < bhat`.

  - `lehmerInnerStep_max_le`: corollary. `max ahat' bhat' ≤
    max ahat bhat`.

  - `lehmerCofactors_invariant_le`: strengthens
    `lehmerCofactors_invariant` (Session 4) with the residue bound
    `max ahat' bhat' ≤ max ahat bhat`. Same induction structure as
    the parent, threading `lehmerInnerStep_max_le` through each
    recursive step via transitivity.

  - `lehmerCofactors_id_apply_le`: specialisation to `M = id` and
    ghost pair = input pair. Combined statement: row-applying the
    accumulated cofactor matrix to `(ahat, bhat)` yields a Euclidean-
    residue pair whose max is bounded by `max ahat bhat`.

  This gives the residue-side bound used in the size-reduction
  argument. The remaining piece (Step 2b) is a Cramer-inversion
  bound on the cofactor entries: from
  `a₀ M.α + b₀ M.γ = ahat'` and `a₀ M.β + b₀ M.δ = bhat'` with
  `det M = ±1`, Cramer gives the entries in terms of `(a₀, b₀)`
  and `(ahat', bhat')`. With residue monotonicity providing
  `(ahat', bhat') ≤ (ahat, bhat)` componentwise (in max), this
  closes the entry bound.

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

1. ✅ **Done in Session 4**: Matrix-vector invariant
   (`lehmerCofactors_invariant`).

2a. ✅ **Done in Session 5**: Residue monotonicity
    (`lehmerCofactors_invariant_le`, `lehmerCofactors_id_apply_le`).

2b. **Cramer-inversion entry bound** (next-session focus). From
   `lehmerCofactors_id_apply_le` we have
   `(ahat, bhat) · M = (ahat', bhat')` with `max ahat' bhat' ≤
   max ahat bhat` and `det M = ±1`. Cramer's rule gives
   `ahat = ±(δ · ahat' - β · bhat')` and `bhat = ±(α · bhat' -
   γ · ahat')`, from which one extracts entry bounds in terms of
   `(ahat, bhat)`. Care is needed on degenerate residue values
   (e.g. `bhat' = 0`). The Lean version will likely state the
   bound `|α|, |γ| ≤ ahat` (and `|β|, |δ| ≤ bhat`) on a generic
   non-degenerate run, then handle the degenerate case separately.

3. **Perturbation analysis**: combine the entry bound with
   `applyToNat M a b = (a · M.α + b · M.γ, a · M.β + b · M.δ)` and
   the decomposition `a = aHi · 2^shift + aLo` (similar for `b`)
   to bound the residual by `2^shift · (residue(aHi, bHi) +
   |M.α| + |M.γ|)`.

4. **Iterate** the half-reduction (top-half + recursive call)
   to close `hgcdMatrix_size_reduction`.

5. Once size reduction is proved, replace the explicit-fuel
   definition with a `WellFounded.fix` definition (lexicographic
   on `bitsize`).

## Attempt Counts

* Total attempts: 4 (Session 2 — skeleton; Session 3 — convention fix;
  Session 4 — matrix-vector invariant; Session 5 — residue monotonicity)
* Current approach attempts: 4
* Approaches tried: 1 (HGCD as Lehmer-step composition with explicit
  fuel; row-vector cofactor convention)
