# S3 ACT REPAIR-DISCOVERY — `RothTheoremQuantitative.lean` fresh-build audit

**Researcher**: researcher-1
**Date**: 2026-06-01
**Phase**: ACT (iteration 3; planned small-N enumeration → pivoted to discovery)
**PR**: (this PR)

## Summary

This session began as a small-N enumeration ACT (target: pin `r₃(4)` to
`[2, 3]` via three new theorems on `proofs/Proofs/RothTheoremQuantitative.lean`):

1. `apFree_zero_one_zmod_four : APFree ({0, 1} : Finset (ZMod 4))`
2. `two_le_rothNumber_four : 2 ≤ rothNumber 4`
3. `rothNumber_four_le_three : rothNumber 4 ≤ 3` (from `rothNumber_le_sub_one`)

The Lean draft was completed locally. When I ran
`./proofs/scripts/docker-build.sh Proofs.RothTheoremQuantitative` to
verify, the build surfaced **six distinct compile failures in the
file** that are *not* from my additions — they are present in the
file as it sits on `main`. Cached lake builds had been masking them
since PR #21520 (qualitative-asymptotic S2 contribution, merged
2026-05-31, Mathlib v4.26.0 bump).

This S3 ACT therefore pivots from "ship small-N theorems" to
"document the regressions so S4 can repair the base before S5 resumes
small-N enumeration".

## Findings (file as it sits on `main`, fresh Docker build, no cache)

| # | Line | Symptom | Root cause |
|---|------|---------|------------|
| 1 | 174 | `Unknown identifier 'div_lt_iff'` | Mathlib v4.26.0 rename → `div_lt_iff₀` |
| 2 | 218 | `Unknown identifier 'div_le_iff'` | Mathlib v4.26.0 rename → `div_le_iff₀` |
| 3 | 195–212 | `linarith failed to find a contradiction` in `max_iterations_bound` | Statement is mathematically false for `δ > 1` (counterexample `δ = 2, k = 0`). The previous `linarith` proof relied on the now-removed `div_le_iff` lemma whose elaboration drift masked the gap. |
| 4 | 214 | unsolved goals in `iterations_before_contradiction` | Downstream of #2 (uses `rw [div_le_iff ...]`) |
| 5 | 134 | `(deterministic) timeout at simp, maximum number of heartbeats (200000) has been reached` in `rothNumber_three` | `fin_cases a <;> fin_cases d <;> simp_all` over `Finset (ZMod 3)` (9 subcases) is on the edge of the default budget on a fresh build |
| 6 | 118 | `Application type mismatch` in `rothNumber_achieved` | `Finset.mem_filter.mp hAS` leaves metavariable `?m.52` unpinned; needs an explicit `Finset (Finset (ZMod N))` annotation on `set S := ...` |

## Math finding: `max_iterations_bound` is false as stated

The lemma claims

```
∀ k : ℕ, δ + kδ²/100 > 1 → k > ⌊100/δ²⌋₊
```

This fails for `δ > 1`. Concretely with `δ = 2, k = 0`:

- `δ + kδ²/100 = 2 + 0 = 2 > 1` ✓
- `⌊100/δ²⌋₊ = ⌊100/4⌋₊ = 25`
- Need `0 > 25` — false.

Algebraically: from `δ + kδ²/100 > 1` we get `kδ²/100 > 1 - δ`, hence
`kδ² > 100(1 - δ)`, hence `k > 100(1 - δ)/δ²`. Since
`100(1 - δ)/δ² < 100/δ²` whenever `δ > 0`, the lemma's claimed bound
is strictly tighter than what the hypothesis supports. No additional
hypothesis (including `δ ≤ 1`) recovers the stated bound — only the
weaker bound `k > 100(1 - δ)/δ²` is provable.

The companion `iterations_before_contradiction` is the contrapositive
form and inherits the same issue (it relies on the same algebra).

The author's intuition was likely "for `δ ∈ (0, 1]` and `δ + kδ²/100`
to first exceed 1, you need `k ≈ 100/δ²`"; that intuition is wrong by
a factor of `1 - δ`. The lemma has no callers in the repo (it is
exploratory scaffolding), so removing it is the cleanest repair.

## Decision: revert Lean additions, ship documentation

The three small-N theorems were drafted but cannot be shipped on a
base file that fails fresh Docker build. The decision matrix:

- Ship small-N + repair together (one PR): scope balloons to ~80 LOC
  changed across four unrelated repair issues + new contribution;
  hard to review.
- Ship small-N alone on broken base: would not actually compile
  (errors masked only by stale cache); blocks deployer auto-merge.
- Ship repair alone: valuable but orthogonal to the original ACT
  goal; risks the small-N draft getting lost.
- Ship documentation only (this S3): cheapest signal, preserves the
  small-N proofs in state.md for S5 to copy back in.

Choosing "documentation only" — the small-N draft is captured in
state.md and this session memo so S5 can pick it up after S4 repair
ships.

## S4 ACT REPAIR (recommended next action)

1. `div_lt_iff` → `div_lt_iff₀` at line 174 (signature unchanged).
2. `div_le_iff` → `div_le_iff₀` at line 218 (signature unchanged).
3. Either REMOVE `max_iterations_bound` + `iterations_before_contradiction`
   (no callers, mathematically incorrect — see Math finding above), or
   restate with `(hδ : δ ≤ 1)` and the corrected bound
   `k > 100(1 - δ)/δ²`.
4. `set_option maxHeartbeats 400000 in` before `rothNumber_three` (or
   refactor the `simp_all` to use a manual case split that doesn't
   re-reduce ZMod arithmetic per case).
5. Fix `rothNumber_achieved` by adding a `(S : Finset (Finset (ZMod N)))`
   annotation on the `set` line, or by extracting the filtered-Finset
   into a named auxiliary before invoking `Finset.exists_max_image`.
6. Docker-verify the file builds clean from a fresh image (no cache).

## S5 ACT SMALL-N (deferred to post-repair)

Three theorems, ≤ 30 LOC total:

```lean
theorem apFree_zero_one_zmod_four : APFree ({0, 1} : Finset (ZMod 4)) := by
  intro a d hd ha had hadd
  fin_cases a <;> fin_cases d <;>
    first | exact hd rfl | (revert ha had hadd; decide)
  -- (or with maxHeartbeats bump if simp_all per-case stays preferred)

theorem two_le_rothNumber_four : 2 ≤ rothNumber 4 :=
  card_le_rothNumber ({0, 1} : Finset (ZMod 4)) apFree_zero_one_zmod_four

theorem rothNumber_four_le_three : rothNumber 4 ≤ 3 := by
  have h := rothNumber_le_sub_one (N := 4) (by omega)
  omega
```

The actual value is `r₃(4) = 2` (OEIS A003002 entry 4 = 2); the tight
upper bound `r₃(4) ≤ 2` requires enumerating the 4 three-element
subsets of `ZMod 4` and showing each contains a 3-AP. That sharper
bound is left as a follow-up after the basic [2, 3] pin lands.

## End of S3 ACT REPAIR-DISCOVERY memo.
