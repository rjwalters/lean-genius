# Current State

**Phase**: ACT-PROGRESS
**Since**: 2026-05-12T04:45:00Z
**Iteration**: 3

## Current Focus

Iteration 3 follows on from S2 (PR #17796, merged: axiom `fano_inequality`
discharged into a theorem via the `FanoFromConditionalEntropy` dispatcher).
The next-action item from S2's state.md asked: *can `channel_coding_converse`
be discharged via the new `fano_inequality` theorem combined with a
data-processing-inequality lemma already in the gallery?* The full
asymptotic converse is multi-step (Fano + chain rule + uniform-X entropy +
sub-additivity for the block extension `(X^n, Y^n)`), so this iteration
contributes the **single-letter capacity bounds** that sit underneath any
Fano-style converse, exposing them as named lemmas in
`ShannonChannelCoding.lean`:

1. `channelMI_le_capacity` — for every input distribution `inp`,
   `channelMI ch inp ≤ channelCapacity ch`. Proof: `le_csSup` against the
   `BddAbove` witness `Real.log (Fintype.card β)` supplied by the existing
   `channelMI_le_log_card`.
2. `capacity_le_log_card` — `channelCapacity ch ≤ Real.log (Fintype.card β)`
   when `[Nonempty α]`. Proof: `csSup_le` against the same uniform-`log|β|`
   bound, nonempty witness via the point-mass `inp₀` already used in
   `capacity_nonneg`.

Together with `capacity_nonneg`, this localises every DMChannel `α → β` to
capacity in the closed interval `[0, log|β|]` (proof-level, not only at
the definition level).

Gallery-entry counts on the parent slug `shannon-channel-coding` are synced
in this PR (theoremCount 9 → 11, lineCount 233 → 275, assumptions string
extended).

## Active Approach

The two new theorems mirror the proof skeleton of `capacity_nonneg` (already
in-file) modulo a duality flip (`le_csSup_of_le` ↔ `le_csSup` for the lower
bound; `csSup_le` for the upper bound). The same `BddAbove` witness and
nonempty witness are reused unchanged.

These are explicitly named so that the next iteration's Fano-step converse
can write `(1 - P_e) * Real.log M ≤ channelMI ch inp + h P_e ≤ channelCapacity ch + h P_e`
in two trivial `linarith` steps once an `entropy_of_uniform_eq_log_card`
lemma is in place.

## Blockers

* `proofs/.lake` recursive self-symlink persists (per memory feedback) — S3
  follows the "(build pending)" PR-title convention. Both new lemmas are
  syntactic transcriptions of standard Mathlib `csSup`/`le_csSup` calling
  conventions and should compile without metavariable strands; if a follow-up
  build flags an issue, the fallback is to inline the `BddAbove` witness as
  a named `have` before each `apply`, mirroring `capacity_nonneg`.

## Next Action

* Mechanic / audit pass: verify any sibling meta.json that still cites
  9-theorem counts on `shannon-channel-coding` (parent slug now bumped to
  11; the OQ-02-OQ-01 / OQ-02 / OQ-04 / etc. sub-galleries describe their
  own proof files and should not need an update).
* S4 candidate: stand up `entropy_of_uniform_eq_log_card` (H(uniform) =
  log|α|) in `ShannonEntropy.lean` (or here, if it's easier as a special
  case of an existing entropy_le_log_card with equality witness), so that
  the Fano-step converse `(1 - P_e) log M ≤ channelMI ch inp + h P_e`
  becomes a direct corollary of the now-named `channelMI_le_capacity`
  combined with `fano_inequality` + chain rule.
* Alternative S4: build the `IndepWith` / DPI-style lemma for the joint
  `(X^n, Y^n)` extension under a memoryless channel — this is the second
  half of the converse but requires an asymptotic `nR ≤ I(X^n;Y^n)` chain
  rule which is much heavier and likely needs its own `OQ-02-OQ-01-OQ-02`
  slug.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 3 (S1 dispatcher; S2 axiom swap; S3 single-letter
  capacity bounds)
