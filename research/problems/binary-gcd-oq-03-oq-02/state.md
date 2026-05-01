# Current State

**Phase**: ACT
**Since**: 2026-05-01
**Iteration**: 3

## Current Focus

Proving the **size-reduction lemma** `hgcdMatrix_size_reduction` —
the only sorry remaining in `proofs/Proofs/BinaryGcdOQ03OQ02.lean`.

Quantitative target:

```
bitsize (max (applyToNat (hgcdMatrix fuel a b) a b).1
             (applyToNat (hgcdMatrix fuel a b) a b).2)
  ≤ bitsize (max a b) / 2 + (hgcdThreshold + 2)
```

## Active Approach

**Correctness-only formalization** as recommended by Session 1.
Session 2 (2026-05-01) executed the recommendation:

1. Defined `hgcdMatrix : ℕ → ℕ → ℕ → CofactorMatrix` (recursive HGCD
   with explicit fuel; two recursive calls composed via
   `CofactorMatrix.mul`).
2. Proved `hgcdMatrix_det_unit` — the matrix is unimodular (det = ±1).
3. Proved `hgcdMatrix_apply_gcd` — applying it preserves `Nat.gcd`.
4. Stated `hgcdMatrix_size_reduction` with the precise quantitative
   bound (sorry, deferred).
5. Documented the bit-complexity claim (C) as a Mathlib infrastructure
   gap in a Part-V comment.

The two correctness theorems were essentially mechanical given the
existing `BinaryGcdOQ03.lean` cofactor-matrix machinery. The
size-reduction lemma is the genuinely new content.

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

* Total attempts: 1 (Session 2 — skeleton + det/gcd theorems)
* Current approach attempts: 1
* Approaches tried: 1 (HGCD as Lehmer-step composition with
  explicit fuel)
