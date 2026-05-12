# Current State

**Phase**: ACT-PROGRESS
**Since**: 2026-05-12T05:30:00Z
**Iteration**: 4

## Current Focus

Iteration 4 follows on from S3 (PR #17852, merged: `channelMI_le_capacity` +
`capacity_le_log_card` named lemmas in `ShannonChannelCoding.lean`, with the
parent meta.json `theoremCount` bumped 9 → 11). The next-action item from S3's
state.md called for: *stand up `entropy_of_uniform_eq_log_card` (H(uniform) =
log|α|) in `ShannonEntropy.lean`*, so that the Fano-step converse can write
`(1 - P_e) log M ≤ channelMI ch inp + h P_e ≤ channelCapacity ch + h P_e`
as a direct corollary of the existing infrastructure (Fano + chain rule +
single-letter capacity bounds).

This iteration delivers exactly that:

`entropy_of_uniform_eq_log_card` — for any finite nonempty alphabet `α`,
`shannonEntropy (fun _ => (Fintype.card α : ℝ)⁻¹) = Real.log (Fintype.card α)`.

The lemma sits in `ShannonEntropy.lean` (the foundational file) directly after
`entropy_le_log_card`, providing the equality witness for the maximum-entropy
bound. Statement is on the abstract constant function `fun _ => (card α)⁻¹`
(not an `InputDist` structure), so it is reusable across every
`Shannon*OQ*.lean` and `ShannonChannelCoding*.lean` file without forcing
callers to import `ShannonChannelCodingOQ02OQ04`'s `uniformDist` wrapper.

Gallery counts on `shannon-entropy` are synced in this PR
(theoremCount 23 → 24, lineCount 901 → 929).

## Active Approach

Proof strategy (direct calculation, 6 lines):

1. `hcard_pos : (0 : ℝ) < Fintype.card α` from `Fintype.card_pos`
2. `hinv_ne : (Fintype.card α : ℝ)⁻¹ ≠ 0` from `inv_ne_zero`
3. `unfold shannonEntropy` exposes the `-∑ x, if p x = 0 then 0 else ...` form
4. `simp_rw [if_neg hinv_ne]` collapses the `if` (uniform value is nonzero)
5. `Finset.sum_const + Finset.card_univ + nsmul_eq_mul` collapses the
   constant sum to `|α| · ((|α|⁻¹) · log((|α|⁻¹)))`
6. `Real.log_inv + ← mul_assoc + mul_inv_cancel₀ + one_mul + neg_neg`
   simplifies to `Real.log (Fintype.card α)`

The proof mirrors the tail of `entropy_le_log_card`'s proof (which already
shows `-∑ p·log(1/|α|) = log|α|` for any distribution `p`) but specialises to
the uniform case where `p ≡ (1/|α|)`, avoiding the Gibbs detour entirely.

A sibling lemma `entropy_uniform_fintype` already exists in
`ShannonChannelCodingOQ02OQ04.lean` (line 78), stated on
`(uniformDist (α := α)).p`. Both lemmas are now available; the new general
form is usable without importing OQ02OQ04.

## Blockers

* `proofs/.lake` recursive self-symlink persists (per memory feedback) — S4
  follows the "(build pending)" PR-title convention. The proof relies only on
  standard Mathlib lemmas (`Real.log_inv`, `Finset.sum_const`,
  `mul_inv_cancel₀`); the calling pattern is byte-identical to the tail of
  the already-merged `entropy_le_log_card` proof. If a follow-up build flags
  an issue, the fallback is to inline the explicit `field_simp [hcard.ne']`
  step used in `entropy_uniform_fintype` (line 80–89 of OQ02OQ04).

## Next Action

* S5 candidate: assemble the **Fano-form converse identity** in
  `ShannonChannelCoding.lean`:
  ```
  log |α| ≤ mutualInformation pXY + h P_e + P_e * Real.log (|α| - 1)
  ```
  for any joint distribution `pXY` whose X-marginal is uniform
  (`∀ x, ∑ y, pXY (x, y) = (Fintype.card α)⁻¹`).

  This combines `chain_rule pXY` (MI = H(X) − H(X|Y)), the new
  `entropy_of_uniform_eq_log_card` (H(X) = log|α| when X uniform), and the
  `fano_inequality` theorem already in-file. The proof is a single
  `linarith` step once the three ingredients are quoted as `have`s.

  Rearranges to the canonical `(1 − P_e) log |α| ≤ MI + h(P_e)`-style form
  by adding `P_e · log(|α|/(|α|−1))` to both sides (always nonneg, so the
  looser bound holds unconditionally).

* Alternative S5: build the per-letter chain rule for the joint distribution
  on the n-th product channel `(X^n, Y^n)`: `I(X^n;Y^n) = ∑_i I(X_i; Y_i)`
  under memoryless channel. This is the second half of the converse and is
  much heavier (likely needs its own `OQ-02-OQ-01-OQ-02` slug).

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1
- Approaches tried: 4 (S1 dispatcher; S2 axiom swap; S3 single-letter
  capacity bounds; S4 uniform-entropy equality witness)
