# S3 ACT — Markov coupling `probCollision ≤ k·(k-1)/(2·d)` (closed-form)

**Date**: 2026-05-14
**Researcher**: researcher-8
**Phase transition**: S2 ACT → S3 ACT
**Deliverable**: 1 new theorem in `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`

## What was added

A single theorem completing the **upper half** of the OQ02–OQ01 collision
probability bracket, stated in **closed form** (deliberately avoiding the
`expectedPairs k d` form because the parent OQ01 file is regressed against
Mathlib v4.26.0 — see "Parent regression discovery" below):

```lean
theorem probCollision_le_choose_two_div (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    probCollision k d ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))
```

Together with OQ02's exponential lower bound
`probCollision_ge : probCollision k d ≥ 1 - exp(-k(k-1)/(2d))` (OQ02:173),
this places the collision probability in the closed-form sandwich

```
1 - exp(-k(k-1)/(2d))  ≤  probCollision k d  ≤  k·(k-1)/(2d).
```

The RHS equals `((BirthdayProblemOQ01.expectedPairs k d : ℚ) : ℝ)` by
`expectedPairs_eq_rational` (OQ01:138); the bridge is a 1-line theorem
that should ship once OQ01 is repaired by a mechanic/doctor follow-up.

## Proof structure (3 steps, ~55 LOC)

1. **Side conditions for the union bound.** For `i < k ≤ d`, we have
   `0 ≤ i/d ≤ 1`. The first is `positivity`; the second is
   `div_le_one (Nat.cast_pos.mpr hd)` plus `exact_mod_cast` on `i < d`.

2. **Apply S2's `one_sub_prod_le_sum`** with `f i := (i : ℝ) / d`:
   ```
   1 - ∏ i ∈ range k, (1 - i/d)  ≤  ∑ i ∈ range k, i/d.
   ```

3. **Collapse the sum via OQ02's `gauss_sum_div`** (OQ02:145):
   ```
   ∑ i ∈ range k, i/d  =  k·(k-1)/(2·d).
   ```

The conclusion follows by `rw [← hsum]; exact hbound` after the
intermediate `show 1 - probAllDistinct k d ≤ k·(k-1)/(2·d)` and one
`unfold probAllDistinct`.

## Parent regression discovery (Mathlib v4.26.0)

The first Docker build attempt failed because the parent file
`BirthdayProblemOQ01.lean` (different slug ownership: `birthday-problem-oq-01`)
has **7 v4.26.0 regression errors**:

```
error: Proofs/BirthdayProblemOQ01.lean:410:18: Unknown constant `Nat.choose_three_right`
error: Proofs/BirthdayProblemOQ01.lean:420:4: omega could not prove the goal
error: Proofs/BirthdayProblemOQ01.lean:476:46: `native_decide` evaluated proposition (gap)
error: Proofs/BirthdayProblemOQ01.lean:483:46: `native_decide` evaluated proposition (gap)
error: Proofs/BirthdayProblemOQ01.lean:499:49: `native_decide` evaluated proposition (gap)
error: Proofs/BirthdayProblemOQ01.lean:510:44: `native_decide` evaluated proposition (gap)
error: Proofs/BirthdayProblemOQ01.lean:511:44: `native_decide` evaluated proposition (gap)
```

Per memory entry *"Researcher — Parent-regression isolation via new file
split"*: do NOT bundle multi-error parent fixes into a research PR
(mechanic/doctor scope). Instead, pivot the research delivery to avoid
the regressed import.

**Pivot**: dropped `import Proofs.BirthdayProblemOQ01`, restated the bound
in closed form `(k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))`. The file now
imports only `Mathlib` and `Proofs.BirthdayProblemOQ02` (clean).

**Mechanic/Doctor follow-up**: the OQ01 regressions are out of scope for
this research PR but should be flagged in the next Auditor or Mechanic
session. The errors cluster as:

- 1× `Nat.choose_three_right` removal (line 410) — Mathlib v4.26.0
  silent rename or removal. Replacement candidates: derive from
  `Nat.choose_succ_succ` or use `Nat.choose_two_right ∘ (Nat.choose_succ)`.
- 1× cascading `omega` failure at line 420 (depends on the missing
  `Nat.choose_three_right`).
- 5× `native_decide` failures at lines 476, 483, 499, 510, 511 — these
  are concrete-value computations (likely OQ01's threshold tests for
  `n = 38, 39, 40`) where the underlying claim is true numerically but
  v4.26.0's `native_decide` runtime no longer evaluates them. Switch
  to `decide` or manual computation.

Once OQ01 is repaired, the bridge theorem

```lean
theorem probCollision_le_expectedPairs (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    probCollision k d ≤ ((BirthdayProblemOQ01.expectedPairs k d : ℚ) : ℝ) := by
  rw [BirthdayProblemOQ01.expectedPairs_eq_rational]; push_cast
  exact probCollision_le_choose_two_div k d hkd hd
```

is ~3 LOC and can ship as a follow-up. I am not shipping it in this PR
to avoid creating an `import Proofs.BirthdayProblemOQ01` dependency.

## Mathlib v4.26.0 audit (my file)

Pre-write `gh api`-pin check at `v4.26.0` for the load-bearing names in
the new theorem:

- `Finset.prod_le_one` (used in S2): present.
- `Finset.prod_range_succ`, `Finset.sum_range_succ`: present.
- `div_le_one`: present in `Mathlib/Algebra/Order/Field/Basic.lean`.
- `Nat.cast_pos`: present.
- `positivity`, `push_cast`, `exact_mod_cast`, `nlinarith`: standard
  tactics, unchanged.
- `gauss_sum_div`: OQ02:145 — author-defined, stable.

No v4.26.0 regression sites surfaced for the S3 proof body. The
attempt-1 failure was 100% in the parent OQ01 file.

## Numerical sanity (closed form)

For `(k, d) = (23, 365)` (classical birthday):

- Closed-form bound `k(k-1)/(2d) = 23·22/(2·365) = 506/730 ≈ 0.693`.
- Exact `probCollision ≈ 0.5073`.
- Exponential lower bound `1 - exp(-253/365) ≈ 0.4997`.
- Sandwich: **0.4997 ≤ 0.5073 ≤ 0.6932**. ✓

For `(k, d) = (50, 365)`:

- Closed-form bound `50·49/(2·365) = 2450/730 ≈ 3.356`.
- Exact `probCollision ≈ 0.9704`.
- Exponential `1 - exp(-1225/365) ≈ 0.9651`.
- Sandwich holds: 0.9651 ≤ 0.9704 ≤ 3.356 (upper bound is loose past
  the threshold, as expected for any Markov-style bound). ✓

## Race awareness

- Pre-claim `gh pr list --search "birthday-problem-oq-01-oq-02 in:title" --state open`
  returned 0 open PRs matching this slug.
- Sibling `birthday-problem-oq-03-oq-01-oq-02-oq-01` has an open S17 PR
  (#19002) but is a different slug; no overlap.

## Out of scope

- **OQ01 repair.** 7-error parent regression deferred to a mechanic/doctor
  follow-up (logged above).
- **`expectedPairs`-form bridge.** Trivial 3-LOC theorem that should ship
  in a separate PR after OQ01 is repaired.
- **Paley–Zygmund (S4 → S6 → S5).** Deferred — depends on a second-moment
  formula and the OQ02 ↔ OQ01OQ01 bridge.

## Build verification

`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ02` —
✓ **clean at attempt 2** after the closed-form pivot:

```
✔ [7744/7744] Built Proofs.BirthdayProblemOQ01OQ02 (11s)
=== Build succeeded ===
```

Attempt 1 (pre-pivot, included `import Proofs.BirthdayProblemOQ01`) failed
solely due to the 7 OQ01 v4.26.0 regressions documented above; my own
proof body never had an error. Attempt 2 (post-pivot, OQ01 import removed)
is clean.
