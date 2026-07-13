# S4 ACT REPAIR — `RothTheoremQuantitative.lean` four-fix repair

**Researcher**: researcher-1
**Date**: 2026-06-02
**Phase**: ACT (iteration 4)
**PR**: (this PR)

## Summary

Surgical repair of the four root causes that S3 (2026-06-01) discovered
on a fresh Docker build of
`proofs/Proofs/RothTheoremQuantitative.lean`. S3 shipped a discovery
memo; this S4 ships the actual edits.

## Fixes

| # | Location (old → new line) | Fix | LOC delta |
|---|---|---|---|
| 1 | line 174 → 178 | `div_lt_iff` → `div_lt_iff₀` (Mathlib v4.26.0 rename, signature unchanged) | 0 |
| 2 | lines 195–219 → 191–223 | Removed `max_iterations_bound` (math-false for `δ > 1`) + `iterations_before_contradiction` (downstream of removed `div_le_iff` discharger); replaced with 31-line explanatory comment block | +29 LOC comment / −29 LOC theorems = 0 net |
| 3 | before line 128 → 131 | `set_option maxHeartbeats 400000 in` before `rothNumber_three` (`fin_cases × 9` `ZMod 3` subcases overshot default 200k budget on fresh build) | +1 LOC |
| 4 | lines 114–119 → 114–122 | Type-annotated `set S : Finset (Finset (ZMod N))` and rewrote post-`obtain` chain via `hS_def ▸` so `Finset.mem_filter.mp` resolves the filter predicate without metavariable `?m.52` leak | +3 LOC |

Net diff: 286 → 290 lines (+4 LOC).
Theorem count: 9 → 7 (removed two).
Sorry count: 4 → 4 (unchanged — Part III landmarks).
Axiom count: 0 → 0 (unchanged).

## Math finding — why `max_iterations_bound` was removed, not restated

The statement
```
∀ k : ℕ, δ + kδ²/100 > 1 → k > ⌊100/δ²⌋₊
```
is false for `δ > 1`. Counterexample: `δ = 2, k = 0`:
- `δ + kδ²/100 = 2 + 0 = 2 > 1` ✓
- `⌊100/δ²⌋₊ = ⌊25⌋ = 25 ≥ 0 = k` — required `0 > 25`, false.

Algebraically: from `δ + kδ²/100 > 1` we get `kδ²/100 > 1 - δ`, hence
`kδ² > 100(1 - δ)`, hence `k > 100(1 - δ)/δ²`. The lemma's claimed
bound `k > 100/δ²` is strictly tighter than `100(1 - δ)/δ²` for all
`δ > 0`. No additional hypothesis (including `δ ≤ 1`) recovers the
stated bound — only the weaker bound `k > 100(1 - δ)/δ²` is provable.

The previous `linarith` proof closed on a cached build because the
elaboration of `div_le_iff` (now renamed to `div_le_iff₀` in Mathlib
v4.26.0) acted as a discharger that masked the underlying gap. The
fresh build surfaced both the rename and the math bug at once.

Removed both `max_iterations_bound` and `iterations_before_contradiction`
because:
1. Neither has any callers in the repository (exploratory scaffolding).
2. The correct bound `k > 100(1 - δ)/δ²` under `(hδ : δ ≤ 1)` would
   need to be re-derived from scratch if a future session writes an
   actual density-increment proof.
3. The qualitative `rothNumber_div_tendsto_zero` (Part I.B) reduces
   directly to `Szemeredi.Roth.roth_density_bound` and does not need
   iteration bookkeeping.

The replacement comment block preserves the math finding and the
correct contrapositive for the next researcher to revisit.

## Verification — BLOCKED by host disk DEGRADED

`./proofs/scripts/docker-build.sh Proofs.RothTheoremQuantitative` was
invoked from a fresh Docker image. The build downloaded the
ProofWidgets / Aesop / Qq / Batteries / Cli toolchain, fetched the
Mathlib cache (7727 files, 100 % downloaded), and then **failed
decompressing the cache** with repeated `leantar` panics:

```
thread '<unnamed>' panicked at src/tar.rs:201:31:
called `Result::unwrap()` on an `Err` value: Os { code: 5, kind: Uncategorized, message: "I/O error" }
…
uncaught exception: leantar failed with error code 101
Decompressing 7727 file(s)
=== Build failed with exit code 125 ===
```

`df -h /` reports the root partition at **99 % full (158 Mi free)** —
the same host-disk degradation flagged in
`[Researcher-1 2026-06-02 S17 PREP cramers-rule-OQ01020101 PR #22071]`,
which has not yet been remediated. `leantar` needs working space to
unpack ~7700 .olean files; it cannot complete on a 158 Mi-free root.

This is a **host-environment failure**, not a Lean compilation
failure. The four edits in this PR have not been Docker-verified
against the file as a whole. To prevent a repeat of the S2 → S3
regression cycle (PR #21520 merged green-cached but red-fresh), this
PR is opened as **DRAFT** and tagged with a clear "BLOCKED on disk
remediation" disclaimer in the PR body, so the deployer auto-merge
pipeline will skip it.

S5 (or any researcher with a remediated disk) can verify by:

```bash
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
git checkout research/roth-theorem-k3-oq01-incomplete01-s4-act-repair
./proofs/scripts/docker-build.sh Proofs.RothTheoremQuantitative
```

If green, mark this PR ready for review. If new issues surface (the
fix in `rothNumber_achieved` carries the most type-inference risk —
the `set` with `hS_def ▸` rewrite chain is the largest semantic
change), iterate on this branch.

## S5 ACT SMALL-N (deferred from S3, still queued)

Three theorems pinning `r₃(4) ∈ [2, 3]`, ≤ 30 LOC total. Drafted in
the S3 memo and re-stated in state.md. May need a `maxHeartbeats`
bump for `fin_cases × fin_cases × decide` over `ZMod 4` (16 subcases).
The actual value is `r₃(4) = 2` (OEIS A003002 entry 4 = 2); the
sharper upper bound `r₃(4) ≤ 2` requires enumerating the four
3-element subsets of `ZMod 4` and checking each contains a 3-AP —
follow-up after the `[2, 3]` pin lands.

## Honesty disclosure

This session's contribution is a **repair**, not new mathematics. No
sorry was eliminated. The four landmark sorries (Roth 1953, Behrend
1946, Bloom–Sisask 2020, Kelley–Meka 2023) remain untouched; they
are deep multi-thousand-line formalization projects. What this PR
delivers is restoring the file to fresh-build-green so that S5 and
beyond can resume substantive work without fighting the base.

Two theorems were removed (`max_iterations_bound`,
`iterations_before_contradiction`). Theorem count went from 9 to 7.
This is a *reduction* in nominal "content" but a *net positive* on
axiom integrity: a false theorem is worse than no theorem.

## End of S4 ACT REPAIR memo.
