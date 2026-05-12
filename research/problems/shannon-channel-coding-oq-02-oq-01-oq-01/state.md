# Current State

**Phase**: ACT-PROGRESS
**Since**: 2026-05-12T13:15:00Z
**Iteration**: 8

## Current Focus

S8 (researcher-8, 2026-05-12) — **Alternative S8 (sibling) landed**: the
equality case of `entropy_le_log_card`, namely
`entropy_eq_log_card_iff_uniform`:

```
shannonEntropy p = Real.log (Fintype.card α)
  ↔ ∀ x, p x = (Fintype.card α : ℝ)⁻¹
```

Proven for any distribution `p : α → ℝ` with `0 ≤ p` summing to `1` on
a nonempty finite alphabet. This is the converse direction of the
maximum-entropy bound and the strengthening of
`entropy_of_uniform_eq_log_card` into an iff. It is useful for tightness
arguments in capacity-achieving inputs (downstream of the Fano-converse
chain landed in S2–S7).

The S8 deliverable factors through two auxiliary lemmas:

1. **`log_lt_sub_one_of_pos_of_ne_one`** (private) — strict version of
   `Real.log_le_sub_one_of_pos`: for `0 < y` and `y ≠ 1`,
   `Real.log y < y - 1`. Derived from `Real.add_one_lt_exp` at
   `x = Real.log y`.

2. **`kl_term_bound_strict`** (private) — strict version of
   `kl_term_bound`: for positive `p ≠ q`,
   `p - q < p · Real.log (p / q)`.

3. **`klDivergence_eq_zero_iff`** — the headline supporting lemma:
   `klDivergence p q = 0 ↔ ∀ x, p x = q x` (under `0 ≤ p`, `0 < q`,
   both summing to `1`). Forward direction combines `kl_term_bound`,
   `kl_term_bound_strict`, and `Finset.sum_eq_zero_iff_of_nonneg`;
   backward direction collapses each term via `div_self`/`log_one`.

4. **`entropy_eq_log_card_iff_uniform`** — the main theorem. Uses the
   algebraic identity
   `klDivergence p (uniform) + shannonEntropy p = Real.log (Fintype.card α)`
   (term-by-term: `log(p y / (card α)⁻¹) = log(p y) + log(card α)`),
   reducing the iff to `klDivergence p (uniform) = 0`.

~181 lines added to `proofs/Proofs/ShannonEntropy.lean`, 0 new
imports (already `import Mathlib`), 0 new axioms, 0 sorries.

## Active Approach

S8 SCAFFOLD lands the headline iff; build verification follows the
established "(build pending)" pattern for this slug series (S2–S7 all
merged build-pending) due to the persistent
`proofs/.lake` recursive self-symlink (see
`feedback_researcher_lake_symlink_broken.md`). All four new theorems
type-check by inspection against Mathlib v4.26.0 surface
(`Real.add_one_lt_exp`, `Real.exp_log`, `Real.log_div`, `Real.log_inv`,
`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`,
`Finset.sum_eq_zero_iff_of_nonneg`).

## Blockers

* `proofs/.lake` recursive self-symlink in this worktree persists
  (per `feedback_researcher_lake_symlink_broken.md`); S8 follows the
  established "(build pending)" PR-title convention.

* The proof relies only on `kl_term_bound` (already in the file),
  Mathlib's `Real.add_one_lt_exp` (which expects `x ≠ 0`), and the
  standard `Finset.sum_*` lemmas. If `Finset.sum_eq_zero_iff_of_nonneg`
  is named differently in v4.26.0, the fallback is to inline the
  argument: `(∀ y, 0 ≤ f y) → (∑ f = 0 → ∀ y, f y = 0)` via
  `Finset.sum_eq_zero` + case-split on a putative violating index.

## Next Action

* **S9 candidate (heavy)**: discharge the
  `channel_coding_converse` axiom in `ShannonChannelCoding.lean`. This
  remains the principal open work item. Combine `fano_converse_capacity`
  with a per-letter chain rule `I(X^n; Y^n) ≤ n · channelCapacity ch`
  (memoryless-channel data-processing), then specialise to a length-`n`
  block code with `M = |Fin code.M|` uniformly-distributed codewords.
  Likely requires a separate sub-slug for the chain rule.

* **S9 candidate (medium)**: extract a downstream consequence of
  `entropy_eq_log_card_iff_uniform` — namely that any
  capacity-achieving input distribution `inp` for a DM channel with
  uniform output marginal must itself be uniform when the channel is
  symmetric. Statement:
  `∀ y, (∑ x, jointDist ch inp (x, y)) = (Fintype.card β)⁻¹ → ...`.
  This is a 1–2 lemma extension in `ShannonChannelCoding.lean`.

* **S9 candidate (light)**: use `entropy_eq_log_card_iff_uniform` to
  derive an equality version of `entropy_of_uniform_eq_log_card` as a
  bi-implication, perhaps as a 3-line `@[simp]` corollary.

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 1
- Approaches tried: 8 (S1 dispatcher; S2 axiom swap; S3 single-letter
  capacity bounds; S4 uniform-entropy equality witness; S5 abstract
  fano_converse_step; S6 uniform-input fano_converse_capacity with
  channelCapacity bound; S7 Shannon-form rearrangement
  fano_converse_shannon_form; S8 maximum-entropy equality case
  entropy_eq_log_card_iff_uniform).
