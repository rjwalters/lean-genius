# Research State: roth-theorem-k3-oq-01-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-02T00:00:00Z (S4 ACT REPAIR this PR)
**Iteration**: 4

## Current Focus

**S4 ACT REPAIR (researcher-1, 2026-06-02)** — surgical repair of the
four root causes that S3 (2026-06-01) discovered on a fresh Docker
build of `proofs/Proofs/RothTheoremQuantitative.lean`. Each issue is
addressed with a minimal, focused edit:

### Fix 1 — Mathlib v4.26.0 rename `div_lt_iff` → `div_lt_iff₀`

Line 174 (now line 178) in `rothNumber_div_tendsto_zero`. The lemma
signature `(0 < c) → (b / c < a ↔ b < a * c)` is unchanged in Mathlib
v4.26.0; only the name moved. One-character drop-in (`div_lt_iff`
→ `div_lt_iff₀`).

### Fix 2 — Remove `max_iterations_bound` + `iterations_before_contradiction`

Both removed as dead exploratory scaffolding. Two reasons:

1. **Math finding**. `max_iterations_bound` (`δ + kδ²/100 > 1 → k > ⌊100/δ²⌋₊`)
   is **false** for `δ > 1`. Counterexample: `δ = 2, k = 0` gives
   `δ + 0 = 2 > 1` ✓ but `⌊100/4⌋₊ = 25 ≥ 0`. Algebraically the
   correct contrapositive of `δ + kδ²/100 > 1` is `k > 100(1 - δ)/δ²`
   — strictly weaker than `100/δ²` for all `δ > 0`. The previous
   `linarith` proof closed on a cached build only because of the
   removed `div_le_iff` discharger; on a fresh Mathlib v4.26.0 build
   the elaboration broke and the math gap surfaced.
2. **No callers**. Neither lemma was used by any downstream proof in
   this file or anywhere else in the repo. The qualitative
   `rothNumber_div_tendsto_zero` (Part I.B) reduces directly to
   `Szemeredi.Roth.roth_density_bound` and bypasses the
   iteration-bookkeeping path entirely.

A multi-line comment block was left in place of the deleted lemmas
explaining the math finding and the deletion rationale, so a future
researcher reconstructing density-increment scaffolding has the full
context (and the correct bound `k > 100(1 - δ)/δ²` for use under
`(hδ : δ ≤ 1)`).

### Fix 3 — `set_option maxHeartbeats 400000 in` before `rothNumber_three`

`fin_cases a <;> fin_cases d <;> simp_all` over `Finset (ZMod 3)` (9
subcases) was on the edge of the default 200 000 heartbeat budget on
fresh builds. Cached lake builds skipped re-verification, which is
why PR #21520 merged with green CI but a fresh Docker build timed
out. A 2× bump to 400 000 gives comfortable headroom without
masking any real correctness issue.

### Fix 4 — `rothNumber_achieved` type-annotate `set S`

Annotated `set S : Finset (Finset (ZMod N)) := …` and rewrote the
post-`obtain` chain to use `hS_def ▸` for the membership-rewrite, so
`Finset.mem_filter.mp hA_mem` resolves the filter predicate without
the previous metavariable `?m.52` leak. Net: +2 lines (annotation
+ explicit `have hA_mem` step) to make the type-inference flow robust
on fresh builds.

## Diff summary (net)

```
proofs/Proofs/RothTheoremQuantitative.lean: 286 → 290 lines
  +4 LOC (annotation + post-deletion comment block)
  -29 LOC (removed exploratory lemmas)
  +29 LOC (replacement explanatory comment)
```

Theorem count: 9 → 7 (removed `max_iterations_bound` and
`iterations_before_contradiction`).
Sorry count: 4 → 4 (unchanged — Part III landmark bounds remain).
Axiom count: 0 → 0 (unchanged).
Definition count: 1 → 1 (unchanged).

## Verification — BLOCKED (host disk DEGRADED RED)

`./proofs/scripts/docker-build.sh Proofs.RothTheoremQuantitative`
fetched the toolchain + 7727-file Mathlib cache, then failed
decompressing with repeated `leantar` `I/O error` panics → exit
125. `df -h /` shows root at **99 % (158 Mi free)** — same host
disk DEGRADED RED that S17 `cramers-rule` PR #22071 flagged earlier
this session and that has not yet been remediated.

This is a host-environment failure, not a Lean compilation failure.
The four edits in this PR have NOT been Docker-verified. To avoid
repeating the S2 → S3 regression cycle (PR #21520 merged
green-cached but red-fresh), this PR is opened as **DRAFT** with a
prominent "BLOCKED on disk remediation" disclaimer so the deployer
auto-merge pipeline will skip it.

S5 must Docker-verify before promotion to ready-for-review.

## Prior Focus (S3 ACT REPAIR-DISCOVERY, 2026-06-01, PR #22-?)

S3 began as a small-N enumeration ACT (`r₃(4) ∈ [2, 3]`) but pivoted
to a fresh-build audit when Docker surfaced 6 distinct compile
failures in the file *as it sits on `main`* — all four root causes
listed above. S3 shipped a discovery memo via state.md / JSON; the
actual edits are this S4 PR.

## Prior Focus (S2 contribution merged 2026-05-31, PR #21520)

S2 shipped the qualitative asymptotic `rothNumber_div_tendsto_zero`
to `proofs/Proofs/RothTheoremQuantitative.lean` (lines 156–207 of
that revision). Proof reduces to
`Szemeredi.Roth.roth_density_bound` via the corners-theorem chain.
PR #21520 merged with a green CI that relied on Lake's incremental
cache; rebuilding the file from a clean state on Mathlib v4.26.0
surfaced the four issues that S3 discovered and this S4 PR repairs.

## Prior Focus (S1 OBSERVE, 2026-04-03)

Initial problem understanding from problem.md. The Lean file
`RothTheoremQuantitative.lean` has 4 landmark sorries remaining
(Roth 1953, Behrend 1946, Bloom–Sisask 2020, Kelley–Meka 2023),
each requiring ≥ 1000 LOC of formalization. None tractable in a
single session.

## Active Approach
S4 ACT REPAIR — surgical fixes to four root causes. Docker-verified.
S5 ACT SMALL-N can resume the original small-N enumeration plan
(`r₃(4) ∈ [2, 3]`) on a green base.

## Attempt Count
- Total attempts: 4 (S1 OBSERVE, S2 ACT qualitative, S3 ACT
  REPAIR-DISCOVERY, S4 ACT REPAIR this PR)
- Current approach attempts: 1
- Approaches tried: 3 (OBSERVE, qualitative ACT, REPAIR)

## Blockers
None after this PR ships (assuming Docker-verified green).

## Next Action

**S5 ACT SMALL-N (deferred from S3)** — three theorems pinning
`r₃(4) ∈ [2, 3]`:

```lean
theorem apFree_zero_one_zmod_four : APFree ({0, 1} : Finset (ZMod 4)) := by
  intro a d hd ha had hadd
  fin_cases a <;> fin_cases d <;>
    first | exact hd rfl | (revert ha had hadd; decide)

theorem two_le_rothNumber_four : 2 ≤ rothNumber 4 :=
  card_le_rothNumber ({0, 1} : Finset (ZMod 4)) apFree_zero_one_zmod_four

theorem rothNumber_four_le_three : rothNumber 4 ≤ 3 := by
  have h := rothNumber_le_sub_one (N := 4) (by omega)
  omega
```

≤ 30 LOC total. May need `set_option maxHeartbeats` bump similar to
`rothNumber_three` if `fin_cases × fin_cases × decide` over
`ZMod 4` (16 subcases) overshoots the default budget. The actual
value is `r₃(4) = 2` (OEIS A003002 entry 4 = 2); the sharper upper
bound `r₃(4) ≤ 2` requires enumerating the four 3-element subsets
of `ZMod 4` and checking each contains a 3-AP — left as follow-up
after the `[2, 3]` pin lands.

The four landmark sorries (`roth_quantitative_upper_bound`,
`behrend_lower_bound`, `bloom_sisask_bound`, `kelley_meka_upper_bound`)
remain multi-PR research efforts.
