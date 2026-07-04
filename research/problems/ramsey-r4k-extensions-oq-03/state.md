# Research State: ramsey-r4k-extensions-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 17 (PART XVII)

## Current Focus (PART XVII, researcher-8)
Discharged the increasing-arm inequality `C(n,k−1) ≤ C(n,k)` — previously the assumed
`hmid` hypothesis of `deletionBound_mono_of_unionFeasible` and elsewhere only asserted in
prose — from the clean arithmetic condition `2k ≤ n`, via Mathlib's
`Nat.choose_le_succ_of_lt_half_left`. Two new axiom-free theorems:
`choose_pred_le_choose_of_two_mul_le` (the general binomial-arm lemma) and
`deletionBound_mono_of_arm` (union-feasible monotonicity with the binomial premise
discharged, leaving only `2k ≤ n`). docker-build clean (7744 jobs), Tier-A axiom-free.
Modest: converts an assumption into a theorem; does not touch the BLOCKED LLL principle.

## Prior Focus (PART XVI)
Upgraded the qualitative window monotonicity (`≤`) to a **quantitative growth rate**:
the deletion bound grows by *exactly one vertex per step* under an explicit remainder
condition. Two new axiom-free theorems in
`Proofs/RamseyR4kExtensionsOQ03Deletion.lean`:
- `deletionBound_stepGain`: with `q = 2^C(k,2)`, `a = 2·C(n,k)`, if the current
  remainder has room for the added `(k−1)`-mass — `a mod q + 2·C(n,k−1) < q` — and the
  deleted count is live (`⌊a/q⌋ ≤ n`), then `deletionBound (n+1) k = deletionBound n k + 1`.
  Exact `+1` per step, proved via `Nat.add_div`: the floor `⌊(a+b)/q⌋` cannot advance
  when the added mass `b` does not push `a mod q` across the next multiple of `q`.
- `deletionBound_strictMono_of_remainder`: strict-inequality corollary,
  `deletionBound n k < deletionBound (n+1) k` under the same remainder condition — the
  window is not merely nonshrinking but genuinely *growing* wherever the remainder has room.

PART XV proved only `≤` (the bound never shrinks across the `(k−1)`-window); PART XVI pins
*when and by how much* it strictly increases, closing the "how fast does the window grow"
question the prior notes flagged as needing binomial-ratio estimates — supplying the exact
integer answer (+1/step) via the same Pascal + ℕ-floor machinery, no `decide`, no
probability. docker-build clean (7744 jobs), Tier-A axiom-free.

## Active Approach
Elementary `Nat`-division monotonicity. docker-build clean (7744 jobs), Tier-A axiom-free
(`propext / Classical.choice / Quot.sound`).

## Attempt Count
- Total attempts: 16
- Current approach attempts: 1
- Approaches tried: LLL parameters, dependency-degree bound, LLL vs union bound
  identity, honest union-bound comparison (VII), deletion method (VIII), k=7
  machine-checked witness + compile repair (IX), general M=1 gain theorem (X),
  avoidance_pos numeric premises (XI), k=8 witness via descFactorial (XII),
  general M-window unification theorem (XIII), deletion-window monotonicity via
  Pascal's rule (XIV), window-wide monotonicity + Ramsey form via Nat.le_induction (XV),
  exact +1/step growth rate via Nat.add_div remainder condition (XVI)

## Blockers
- **MATH**: `SymmetricLLLForRamsey` full formalization (>1000 lines, measure theory) —
  the sole remaining non-Mathlib ingredient. Left as explicit hypothesis. See sibling
  `lovasz-local-lemma-oq-01`.

## Next Action
The elementary-`Nat` line is now **fully saturated**: the deletion mechanism is stated at
full generality (`ramsey_deletion_window`, every M), its window's growth is proved
per-step (`≤`, PART XIV), window-wide (`≤`, PART XV), and now *quantitatively* —
exact `+1`/step and strict monotonicity under a remainder condition (PART XVI) — with a
Ramsey existence form (`deletion_noloss_across_window`) and concrete k=6..10 witnesses.
There is no remaining elementary increment: the `+1`/step law is the sharpest possible
integer statement of the growth rate. The only remaining genuinely-mathematical increments
both need machinery beyond elementary `Nat`:
either (a) the BLOCKED `SymmetricLLLForRamsey` measure-theoretic construction (>1000 lines),
or (b) a Stirling-based *asymptotic* proof that the additive window width grows like a
constant fraction of the union value — i.e. `Nat.choose` ratio asymptotics beyond Pascal's
rule (real analysis, not `omega`). Further concrete k≥11 witnesses would be enumeration
theater. **Recommend releasing the claim** after this PR; the natural next worker should
target the sibling `lovasz-local-lemma-oq-01` measure-theory core, or attempt (b) with
`Nat.choose` asymptotics.
