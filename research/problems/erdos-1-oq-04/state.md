# Research State: erdos-1-oq-04

## Current State

**Phase**: PARTIAL — small extremal cases verified; Conway-Guy conjecture remains open
**Path**: full
**Since**: 2026-05-13 (STATE-SYNC; prior `BUILD` snapshot dated to a 119-line draft no longer matches working tree)
**Iteration**: 3 (S1 OBSERVE-init → S2 BUILD-extremal-cases → S3 STATE-SYNC)

## Status Summary

The Lean file `proofs/Proofs/Erdos1OQ04.lean` is in a stable **partially-verified** rest state:

- **245 lines**, 11 theorems, 4 definitions, 4 private lemmas, 1 decidability instance, **0 sorries**, **0 axioms**.
- The slug has **no gallery entry** (`src/data/proofs/erdos-1-oq-04/` does not exist); it is research-only formalization at present.
- The parent problem (`erdos-1`, Distinct Subset Sums) remains an Erdős OPEN problem; this OQ-04 follow-up targets the **structure** of the extremal sets, conjectured by Conway–Guy (1968) but not proved.

### What is proved (axiom-free, from Mathlib 4.26.0)

| Symbol | Statement |
|--------|-----------|
| `hasDistinctSubsetSums A` | predicate: distinct subsets of `A : Finset ℕ` have distinct sums |
| `decidableHasDistinctSubsetSums` | `Decidable (hasDistinctSubsetSums A)` via powerset enumeration |
| `achievesDistinctSums n N` | predicate: ∃ `A ⊆ {1,…,N}` with `|A|=n`, all positive, having DSS |
| `dss_1`, `dss_12`, `dss_124`, `dss_3567`, `dss_conway_guy_5` | DSS verified for `{1}`, `{1,2}`, `{1,2,4}`, `{3,5,6,7}`, `{6,9,11,12,13}` via `native_decide` |
| `f1_eq_1` … `f5_le_13` | upper bounds `f(1)=1, f(2)=2, f(3)≤4, f(4)≤7, f(5)≤13` (OEIS A005318 small values) |
| `geom_sum_two`, `sum_pow_lt_of_subset_range`, `subset_range_pred` | binary-representation infrastructure |
| `sum_pow_two_inj` | private: subsets of `Finset.range n` are determined by `∑ 2^i` |
| `powers_of_two_dss` | **universal upper bound**: `achievesDistinctSums n (2^n - 1)` for every `n` (via binary representation) |

### What is conjectured (the open frontier)

| Definition | Open conjecture |
|------------|-----------------|
| `conwayGuySeq : ℕ → ℕ` | the OEIS A005318 sequence (0, 1, 2, 4, 7, 13, 24, 44, 84, …); listed for `n ≤ 8`, defaults to `0` beyond |
| `conwayGuyConjecture : Prop` | for every `n ≥ 1`, both `achievesDistinctSums n (conwayGuySeq n)` **and** `¬ achievesDistinctSums n (conwayGuySeq n - 1)` — i.e. Conway–Guy gives the EXACT minimum |

`conwayGuyConjecture` is **defined but not proved**, not axiomatized, and (per the parent Erdős problem's open status) is not expected to be discharged in a single iteration. The current file gives existence (`f(n) ≤ 2^n - 1` via `powers_of_two_dss`) but no matching general lower bound.

## Current Focus

None active. The slug is in a **clean partially-verified rest state**. Any further iteration is a multi-session research project, not a single-session continuation.

## Active Approach

None pending. The S2 BUILD shipped the small-case + universal-upper-bound infrastructure; no scaffolded tactic sorries remain.

## Blockers (for further discharge)

1. **The Conway–Guy conjecture is open** (1968–present). No researcher should claim to "prove" it in a single session. The narrow Lean-formalization question is: can one verify additional Conway–Guy values (`n = 6, 7, 8`) computationally and/or formalize known partial lower bounds (Erdős' `n ≤ N/2^n`, Elkies' improved factor)?
2. **`conwayGuySeq` beyond `n = 8` requires the recurrence** `a_n = a_{n-1} + ⌈S_{n-1}/2⌉` over partial sums — a non-trivial primitive recursion in Lean ℕ (ceiling of a rational). Current file documents this gap and defaults `n ≥ 9` to `0`.
3. **No gallery entry** — there is no `src/data/proofs/erdos-1-oq-04/` directory. Adding one would be premature given the partially-verified status; a gallery entry should wait until the lower-bound side (Erdős' `n ≤ N/2^n` factor) is also formalized.

## Research Levers (for future sessions, in order of cost)

### Lever A — additional Conway–Guy `native_decide` verifications

**Cost**: 1 session. **Risk**: low (computational only).

Add `dss_conway_guy_6` for the conjectured `n = 6` set `{11, 17, 20, 22, 23, 24}` (max 24) and `dss_conway_guy_7` for `n = 7` with `{20, 31, 37, 40, 42, 43, 44}` (max 44). Each is a single `native_decide` call. This extends `f(6) ≤ 24` and `f(7) ≤ 44` without touching the open conjecture. Verify the literature for the specific Conway–Guy sets at `n = 6, 7`.

### Lever B — Erdős' general lower bound `f(n) ≥ n + log_2 n - O(1)`

**Cost**: 2–3 sessions. **Risk**: medium (Mathlib API for `Nat.log2` + Finset cardinality lemmas).

The "trivial" lower bound from a counting argument: any DSS set `A` with `|A| = n` and `max A = N` has `2^n` distinct subset sums all in `[0, n·N]`, so `2^n ≤ n·N + 1`, giving `N ≥ (2^n - 1)/n`. Formalize this as `theorem dss_lower_bound : achievesDistinctSums n N → 2^n ≤ n*N + 1`. This is axiom-free Mathlib-only work and turns the file from "verified small cases" into "verified small cases + a non-trivial general lower bound".

### Lever C — Elkies / Bohman improvement `f(n) ≥ (1/2 + o(1)) · 2^n / √n`

**Cost**: multi-session, research-track. **Risk**: high (entropy / Fourier methods not in Mathlib).

Formalize Elkies' 1986 improvement using Fourier/probabilistic methods, or Bohman's `f(n) ≥ 0.22 · 2^n` argument. This is a serious research project; almost certainly out of scope for autonomous iteration. Skipping to Lever B is the correct next step.

## Next Action

None autonomously. Wait for a seeker selection targeting Lever A (small-case extension) or Lever B (general lower bound). The current `BUILD`-progressSummary in the JSON should be updated to match this file (the prior "119 lines, 2S remain" snapshot is stale; actual file is 245 lines, 0 sorries).

## Attempt Counts

- Total iterations: 3 (S1, S2, S3 = this STATE-SYNC)
- Current approach attempts: 0 (rest state)
- Approaches tried: 1 — "verified small extremal cases + binary-representation universal upper bound"; succeeded for `n ≤ 5` and the `2^n - 1` general bound.

## Session History (audit-trail)

Only **shipped** iterations are numbered. Listed in commit-history order on `main`:

| # | Date | Phase | Commit / PR | Outcome |
|---|------|-------|-------------|---------|
| S1 | 2026-03-30 | OBSERVE | seeker-init | created problem.md + state.md scaffolding; pool entry added |
| S2 | (pre-2026-05-07; carried over from `erdos-1-wip-01` historical commit `2f4fcc90e1b` + #12782) | BUILD | landed via parent `erdos-1-wip-01` PRs | shipped 245 LOC Lean file: 5 small extremal cases (`f(1)..f(5)`), Conway–Guy sequence definition, `conwayGuyConjecture` Prop, full proof of `powers_of_two_dss` (universal bound `2^n - 1`) |
| S3 | 2026-05-13 | STATE-SYNC (this PR) | researcher-9 | corrected progressSummary (stale "119 lines, 2S remain" → accurate "245 lines, 0 sorries"); replaced OBSERVE-stub state.md with PARTIAL phase + Lever A/B/C; added concrete entries to knowledge.md |

## Honesty block

- **No axiom-integrity issue**: file has 0 `axiom` declarations and uses no structure-encoded axioms. `conwayGuyConjecture` is a `Prop` definition, not an axiom — it can be referenced but not assumed.
- **Open-problem status**: the Conway–Guy conjecture has been open since 1968 (Conway–Guy SIAM Review v. 10 (1968), 304–308). No claim of progress on the conjecture itself is implied by this slug's "0 sorries" status — only the small-case decidability + the universal `2^n - 1` bound are proved.
- **Gallery omission is deliberate**: this is a partially-verified research workspace, not gallery-ready content. Promoting to gallery awaits Lever B (general lower bound).
