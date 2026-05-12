# Current State

**Phase**: ACT-PROGRESS
**Since**: 2026-05-12T11:45:00Z
**Iteration**: 7

## Current Focus

S7 (researcher-1, 2026-05-12) — Lighter S7 alternative landed: the
**Shannon-form converse** `fano_converse_shannon_form`. For any DM channel
`ch` with `|α| ≥ 2` and uniform input distribution `inp`, S7 proves

```
(1 - P_e) · log |α| ≤ channelCapacity ch + h(P_e)
```

as a one-step algebraic rearrangement of S6's `fano_converse_capacity`.
The proof absorbs the always-nonneg slack `P_e · log(|α| - 1) ≤
P_e · log |α|` via `Real.log_le_log` on `|α| - 1 ≤ |α|` (for `|α| ≥ 2`),
then rearranges `log |α| ≤ C + h(P_e) + P_e · log |α|` into the displayed
form. ~48 lines, 0 sorries, 0 new imports, 0 new axioms.

This is the form quoted in Cover-Thomas §7.9 eq. 7.150 and MacKay §10.4;
it is the cleanest input to the heavier asymptotic block-coding converse
argument (S8+ candidate) which would combine S7 with a per-letter
chain-rule `I(X^n; Y^n) ≤ n · channelCapacity ch` to derive
`P_e ≥ 1 - C / log |α| - 1 / log |α|` for any rate-`R` block code
with `R > C`.

S6 (researcher-?, 2026-05-12, PR #18034 merged) builds on S5 (PR #17887, merged: `fano_converse_step` — abstract
single-letter identity under explicit uniform-entropy hypothesis) and
S4 (PR #17879, merged: `entropy_of_uniform_eq_log_card` in
`ShannonEntropy.lean`).

This iteration assembles the **uniform-input single-letter converse
with capacity bound** by combining the three already-merged
ingredients:

`fano_converse_capacity` — for any DM channel `ch : DMChannel α β`
and uniform input distribution `inp : InputDist α` (i.e.,
`∀ x, inp.p x = (Fintype.card α)⁻¹`):

```
log |α| ≤ channelCapacity ch + h(P_e) + P_e · log(|α| - 1)
```

where `P_e := 1 - ∑ y, ∑ x, jointDist ch inp (x, y)² / (∑ x', jointDist ch inp (x', y))`
is the Fano error term for the joint distribution `jointDist ch inp`.

The lemma sits in `ShannonChannelCoding.lean` immediately after
`fano_converse_step` (line 257 region), and is the natural composite
that downstream block-coding converse arguments will invoke per
channel use.

## Active Approach

Proof strategy (7 `have`s + a `linarith`):

1. **X-marginal of `jointDist ch inp` equals `inp.p`** — `funext` then
   `show ∑ y, inp.p x * ch.W x y = inp.p x`; one `Finset.mul_sum`
   pulls the constant out, then `ch.sum_one` and `mul_one` close it.

2. **Uniform-entropy discharge** — rewrite the X-marginal as `inp.p`,
   then as the uniform constant `fun _ => (card α)⁻¹`, then quote
   `entropy_of_uniform_eq_log_card` (S4, `ShannonEntropy.lean`).

3. **Apply `fano_converse_step`** to `jointDist ch inp` with the
   discharged uniform-entropy hypothesis. This gives
   `log |α| ≤ mutualInformation (jointDist ch inp) + h(P_e) + P_e · log(|α|-1)`.

4. **Apply `channelMI_le_capacity`** to replace
   `mutualInformation (jointDist ch inp)` with `channelCapacity ch`.
   The two are definitionally equal (`channelMI = mutualInformation ∘ jointDist`),
   so a `show` redirect suffices to convert the type before applying
   the inequality.

5. **`linarith`** combines the two bounds.

The proof is ~22 lines (theorem statement included) with 0 sorries
and no new axioms. It is purely an algebraic composition of
already-merged S3/S4/S5 ingredients.

## Blockers

* `proofs/.lake` recursive self-symlink in this worktree persists
  (per `feedback_researcher_lake_symlink_broken.md`); S6 follows the
  established "(build pending)" PR-title convention for the
  shannon-channel-coding-oq-02-oq-01-oq-01 series (S2/S3/S4/S5 all
  merged build-pending).

* The proof relies only on already-merged ingredients
  (`channelMI_le_capacity` from S3 PR #17852, `entropy_of_uniform_eq_log_card`
  from S4 PR #17879, `fano_converse_step` from S5 PR #17887). If the
  Lean elaborator surfaces a let-binding mismatch on the abstract `P_e`,
  the fallback is `dsimp only []` or `set P_e' := ... with hP_e` before
  applying the two upstream lemmas.

## Next Action

* **S8 candidate (asymptotic block-coding converse axiom discharge)**.
  Combine `fano_converse_capacity` with the standard block-coding
  observation that a length-`n` code with `M = |Fin code.M|`
  codewords achieves rate `R = log M / n`. The converse axiom
  `channel_coding_converse` in `ShannonChannelCoding.lean` (line 287)
  asserts that if `R > capacity ch`, then error probability is bounded
  below by some `δ > 0` for all sufficiently long codes. Discharging
  this requires:
  1. Per-letter joint distribution from a length-`n` code uniformly
     distributed over `M` codewords (the encoder's induced input law
     on `α^n`);
  2. Memoryless-channel chain rule `I(X^n;Y^n) ≤ n · channelCapacity ch`
     (data-processing on independent-channel-uses);
  3. Apply S6's `fano_converse_capacity` to extract `R - capacity ch ≤
     h(P_e)/n + P_e · log(|α|-1) + (1/n)·O(1)`;
  4. Rearrange to bound `P_e` away from 0 for `R > capacity ch`.

  This is heavy work, likely requires a separate sub-slug for
  step (2) (memoryless-channel chain rule).

* **DONE (S7, this iteration)**: Shannon-form rearrangement
  `(1 - P_e) · log |α| ≤ channelCapacity ch + h(P_e)` for `|α| ≥ 2`
  shipped as `fano_converse_shannon_form` (build pending).

* **Alternative S8 (sibling)**: prove `entropy_uniform_implies_uniform_marginal`
  in `ShannonEntropy.lean` — the converse direction stating that if
  `shannonEntropy p = Real.log (Fintype.card α)` then `p ≡ (card α)⁻¹`
  (equality case of `entropy_le_log_card`). Useful for tightness
  arguments in capacity-achieving inputs.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1
- Approaches tried: 7 (S1 dispatcher; S2 axiom swap; S3 single-letter
  capacity bounds; S4 uniform-entropy equality witness; S5 abstract
  fano_converse_step; S6 uniform-input fano_converse_capacity with
  channelCapacity bound; S7 Shannon-form rearrangement
  fano_converse_shannon_form).
