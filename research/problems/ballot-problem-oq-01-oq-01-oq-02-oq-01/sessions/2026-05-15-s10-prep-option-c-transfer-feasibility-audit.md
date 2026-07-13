# S10 PREP — Option C (two-sided bounded) transfer feasibility audit (doc-only)

**Researcher**: researcher-6
**Date**: 2026-05-15 (UTC 2026-05-16T~05:10Z)
**PR**: (this PR)
**Phase**: PREP cleanup (doc-only)
**Iteration**: 12 → 13 (PREP doc-only bump)
**Lake SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
**Predecessor**: S9 PREP §-Recommended Next PREP (PR #19340, researcher-8, merged) explicitly
asks for "Option C transfer sketch — adapt S7 PREP §3's mixed-down
recipe to the broader alphabet, identifying which Path B lemmas
survive vs need re-proving. Estimated 200-300 LOC doc-only."

## §0 Scope

This S10 PREP **scopes down** the S9 PREP recommendation by 30-50%:
instead of attempting a full 200-300 LOC transfer sketch, it ships a
~120 LOC **feasibility audit** that:

1. (§1) Restates the Option C target shape vs Path B's mixed-down alphabet.
2. (§2) Classifies each Path B lemma in `BallotProblemOQ01OQ01OQ02OQ01.lean`
   as TRANSFERABLE-AS-IS, MINOR-ADAPTATION, or NEEDS-REPROOF.
3. (§3) Identifies the **zero-step obstruction** as the single load-bearing
   distinction Option C makes.
4. (§4) Proposes a 3-route plan (alphabet-filter, alphabet-extend, multiset
   bijection) for the zero-step.
5. (§5) Refines LOC + Docker iter forecast.
6. (§6) Defers full transfer sketch to S11 PREP (single-route).

## §1 Target shape

**Option C** (per S8 PREP §4.3 / S9 PREP §-Most natural next ACT):

```
∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1
```

For `l : List ℤ`, this means each element is in `{-m, -m+1, ..., -1, 0, 1}`.

**Path B** (already shipped, `step_in_one_pos_mixed_neg_card_eq` at L446):

```
∀ x ∈ l, x = 1 ∨ ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)
```

For `l : List ℤ`, this means each element is in `{-m, -m+1, ..., -1, 1}` — **strictly missing `0`**.

**The Option C / Path B delta is precisely `0`**: Path B's alphabet has no zero step; Option C's does.

## §2 Path B lemma transfer classification

Each lemma in `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` part
"Path B (S7 ACT)" (L313–L470) classified for Option C transfer:

| Lemma | Line | Hypothesis | Option C transfer | LOC delta |
|---|---|---|---|---|
| `levelPosB` (private def) | 337 | none beyond `l : List ℤ` | **AS-IS** | 0 |
| `levelPosB_mem` | 343 | none | **AS-IS** | 0 |
| `levelPosB_le` | 348 | none | **AS-IS** | 0 |
| `levelPosB_prefixSum_le` | 351 | none | **AS-IS** | 0 |
| `levelPosB_max` | 355 | none | **AS-IS** | 0 |
| `levelPosB_lt` | 360 | `(n : ℤ) < l.sum` | **AS-IS** | 0 |
| `levelPosB_right` | 368 | none | **AS-IS** | 0 |
| `levelPosB_eq` (private) | 379 | `∀ x ∈ l, x = 1 ∨ ∃ k…` | **NEEDS-REPROOF** (Option C `hmem` reshape + zero case) | +20-40 |
| `goodRotations_card_ge_pathB` | 405 | as above | **MINOR-ADAPTATION** (signature change, body essentially unchanged) | +5 |
| `step_in_one_pos_mixed_neg_card_eq` | 446 | as above | **AS-IS structurally** (just renamed) | +2 |
| `step_in_one_pos_mixed_neg_card_bound` | 456 | as above + `1 ≤ m` | **AS-IS structurally** (just renamed) | +2 |

**Summary**: 7/11 lemmas transfer verbatim or with a 1-token `hmem`
rewrite. **The single load-bearing reproof is `levelPosB_eq`** —
specifically the `helem : l[levelPosB l n] = 1` step (lines 388–396).

## §3 The zero-step obstruction

The `helem` proof in `levelPosB_eq` works as follows (L388–396):

```lean
have helem : l[levelPosB l n] = (1 : ℤ) := by
  rcases hmem l[levelPosB l n] (List.getElem_mem hj_lt) with h1 | ⟨k, _, _, hx_eq⟩
  · exact h1                       -- x = 1: done
  · exfalso                        -- x = -k for some k ∈ [1, m]: contradicts hj1_gt
    have hstep : prefixSum l (levelPosB l n + 1) = prefixSum l (levelPosB l n) + l[levelPosB l n]
    rw [hstep, hx_eq] at hj1_gt
    linarith [show (0 : ℤ) ≤ (k : ℤ) from Int.natCast_nonneg k]
```

For Option C, the `rcases` on `hmem` becomes a single conjunctive
hypothesis `-m ≤ x ∧ x ≤ 1`. The case analysis becomes a three-way
split:

- `x = 1` ⟹ done (as before).
- `-m ≤ x ≤ -1` ⟹ same `linarith` contradiction (as before).
- **`x = 0`** ⟹ `prefixSum l (levelPosB l n + 1) = prefixSum l (levelPosB l n)`, which **does NOT exceed** `minPrefixSum l + n`, contradicting the definition of `levelPosB l n` as the *rightmost* such index.

The zero-case proof requires a different argument: not a `linarith`
on `hj1_gt`, but a contradiction via `levelPosB_max` (the maximality
of `levelPosB l n` in the `Finset.filter`). The step from
`prefixSum l (levelPosB l n) ≤ minPrefixSum l + n` to
`prefixSum l (levelPosB l n + 1) ≤ minPrefixSum l + n` (since
`l[levelPosB l n] = 0`) shows `levelPosB l n + 1` is also in the
filter, contradicting `levelPosB l n + 1 > levelPosB l n =`
maximum.

This is a **~10-20 LOC** addition to `levelPosB_eq`'s body, not a
fundamental restructuring.

## §4 Three-route plan for the zero-case

### Route A — alphabet-filter (RECOMMENDED for S11 ACT)

Define `l' := l.filter (· ≠ 0)`, prove
`(goodRotations l).card = (goodRotations l').card` via a bijection on
"good rotations" (zeros don't affect prefix-sum reachability or
strict minimality), then apply Path B's `step_in_one_pos_mixed_neg_card_eq`
to `l'` (whose alphabet is now Path B's).

**Pros**: maximally reuses Path B; the alphabet-filter bijection is a
clean 30-50 LOC lemma that's reusable.

**Cons**: requires proving `(goodRotations l).card = (goodRotations
(l.filter (· ≠ 0))).card` — likely 50-80 LOC, non-trivial because
`goodRotations` is a `Finset.filter` over `Finset.range l.length`, not
on `l` directly.

**LOC estimate**: 80-120 LOC.

### Route B — alphabet-extend (lift `levelPosB_eq` body directly)

Adapt `levelPosB_eq` directly per §3's three-way split. No filter
bijection.

**Pros**: surgical, minimal infrastructure addition.

**Cons**: the `levelPosB_eq` body grows by ~20 LOC; the rest of Path
B's chain (lower bound, equality, slack) needs corresponding
adjustments to handle the larger `Finset.range l.sum.toNat` (since
zero steps don't change `l.sum`, the count target is unchanged but
the bijection argument shifts).

**LOC estimate**: 60-100 LOC.

### Route C — multiset bijection (heaviest)

Reframe `goodRotations` via a multiset / index-set construction that
naturally handles zero steps (e.g. work with `l.attach.filter
goodRotationP`). Probably overkill for this slug.

**LOC estimate**: 150-250 LOC.

**Recommended route**: **Route B** for S11 ACT (surgical, reuses
existing infrastructure, lowest LOC). Route A as fallback if zero-case
proof in Route B turns out to require deeper restructuring.

## §5 LOC + Docker iter forecast

| Quantity | Forecast |
|---|---|
| New file content (S11 ACT, Route B) | +60-100 LOC |
| Parent-file build job count after S11 ACT | 3062 (S7 ACT baseline) ± 0-5 |
| Docker iters to verify S11 ACT | 1-3 (zero-case `linarith` may need 1-2 tweaks) |
| New imports needed | none (alphabet-extend stays inside `BallotProblemOQ01OQ01OQ02OQ01.lean`) |

## §6 Forward — S11 PREP / S11 ACT recommendation

**Recommended order**:

1. **S11 PREP (single-route, ~150-200 LOC doc-only)**: Detailed
   skeleton for Route B — full body of `levelPosB_eq_optionC` with
   zero-case proof, full sketch of how `goodRotations_card_ge_pathB`
   transfers, full sketch of `step_in_one_pos_pm_card_eq` (Option C
   variant). Bearer audit for any new lemmas in
   `Mathlib.Data.Int.Order.Basic` etc.
2. **S11 ACT (~60-100 LOC)**: Implement Route B per S11 PREP.
3. **(optional) S12 BUILD-VERIFY**: Docker build confirmation.

**Defer past S11**: zero-tolerant counting refinements (`m=0` /
`m=1` edge cases), `l.length`-only-zeros corner case, full Option C
spec amendment to `problem.md` L93 (currently scope-limited to
Option A per S9 PREP §4.1).

## §7 Conflict-free guarantees

This PREP is **doc-only**: 1 new file in `sessions/`, plus minimal
state.md head + JSON `currentState` updates.

- 0 Lean edits
- 0 parent-file edits  
- 0 problem.md / knowledge.md edits
- 0 gallery / meta.json edits
- 0 cross-slug impact (companion file is fully encapsulated by namespace
  `BallotMJumpCycleLemma`)
- No conflict with OPEN-DIRTY PR #19015 (S6 ACT; content already on
  main; S9 PREP §5.1 recommends close-without-merge by doctor)
- No conflict with any other open PR on slug at PREP authoring
  (`gh pr list --repo rjwalters/lean-genius --search
  "ballot-problem-oq-01-oq-01-oq-02-oq-01 in:title" --state open`
  returns only #19015)

## §8 Iteration bookkeeping

- Phase: PREP cleanup (unchanged)
- Iteration: 12 → 13
- Sorries: unchanged
- Axioms: unchanged
- Theorems: unchanged
- LOC: unchanged

**Cycle**: ~25 min (orient + parent-file Path B inventory + 3-route audit + memo).
