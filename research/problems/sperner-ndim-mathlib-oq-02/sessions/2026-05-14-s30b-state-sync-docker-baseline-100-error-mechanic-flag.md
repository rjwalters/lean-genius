# S30b STATE-SYNC — Docker baseline reveals 100+ errors; mechanic-scope flag

**Session**: 2026-05-14, researcher-12
**Mode**: STATE-SYNC (no Lean ACT; documents build state to halt PREP-on-PREP chain)
**Slug**: sperner-ndim-mathlib-oq-02
**Status**: ACT-blocked at parent-file level; mechanic-scope intervention required

## 0. TL;DR

Docker-build of `proofs/Proofs/SpernerFreudenthalSimplex.lean` on origin/main
**fails with 100+ errors** (capped at 100 by `maxErrors`; 103 raw error
records in the log, spanning 56 distinct line numbers from line 73 through
line 1093). The parent file has been silently broken on origin/main since
**~2026-05-08** (per state.md: "parent file build broken on origin/main since
2026-05-08 at `t1_ne_t2`/`diagonal_in_t1_iff` post-Mathlib drift") and
**20 merged "(build pending)" PRs** plus **3 still-open "(build pending)" PRs**
have accumulated on top of an unbuildable parent — exactly the
`feedback_researcher_build_pending_slug_series_silent_parent_regression`
pattern.

This session does **no Lean ACT** — the right move is to halt further PREPs
on this slug and ship an error inventory for the mechanic agent to consume.

**Build log**: `.loom/logs/researcher-12-sperner-freud-baseline.log`
(captured 2026-05-14 ~04:30 UTC from origin/main).

## 1. Build-pending PR chain count

```
$ gh pr list -R rjwalters/lean-genius \
    --search "sperner-ndim-mathlib-oq-02 in:title build pending" \
    --state merged --limit 30 | wc -l
20
$ gh pr list -R rjwalters/lean-genius \
    --search "sperner-ndim-mathlib-oq-02 in:title" \
    --state open --limit 10 | wc -l
3
```

Open: #17621 (S25-prep), #17571 (S23), #17984 (S28-prep). All marked
"(build pending)". All conflict-likely against any actual repair.

## 2. Error inventory (top 7 distinct line:col + class)

Captured via:
```
$ grep "^error: Proofs/SpernerFreudenthalSimplex" \
    .loom/logs/researcher-12-sperner-freud-baseline.log \
    | sed -E 's/^error: .*\.lean:([0-9]+):([0-9]+): /\1:\2 /' \
    | awk '!a[$1]++' | head -7
```

| # | line:col | error class | likely cause (Mathlib v4.26.0 surface) |
|---|----------|-------------|----------------------------------------|
| 1 | 73:84 | `unsolved goals` after `linarith [hv.2, Finset.sum_eq_zero ...]` | `Finset.sum_eq_zero` API drift (signature or import location); `linarith`'s usable-fact filter narrowed |
| 2 | 77:18, 77:44 | `don't know how to synthesize implicit argument s` / `Failed to infer binder type` | function-arg-binder-type inference strictened for anonymous lambdas without explicit `(i : Fin _)` |
| 3 | 116:36, 118:7–118:55 | cascade of `don't know how to synthesize placeholder` (12 errors at line 118 alone) on `Finset.min'_mem _ _` | `Finset.min'_mem` argument-pattern stricter; needs explicit `(colorSet v fv).Nonempty` instance arg |
| 4 | 135:23 | `Type mismatch` | concrete to be diagnosed by mechanic |
| 5 | 171:10, 232:10, 234:10 | `rewrite failed: Did not find an occurrence of the pattern` | several `rw [...]` patterns now non-syntactically-matching after Mathlib normalization change |
| 6 | 226:71, 227:81, 308:4, 310:62, 1068:2, 1085:10 (×6) | `omega could not prove the goal: No usable constraints found` / `a possible counterexample: a ≥ 0` | `omega`'s usable-fact discovery narrowed: needs `have :=` to materialize hypotheses before invocation |
| 7 | 348:20 (×6 nested + cascade) | `Tactic cases failed with a nested error` | `cases` on `Fin (n+1)` or sigma-product no longer auto-elaborates the motive; needs explicit `cases ... with | ...` |

**Total error count**: 103 errors recorded in the log; `maxErrors = 100`
ceiling reached at line 1093:8 → **the actual error count past line 1093 is
unknown without rebuilding with higher `maxErrors`**.

**Spread**: 56 distinct line numbers between 73 and 1093 (≈ 33% of the
~3417-line file's source lines, weighted toward the front half).

**Estimated mechanic effort**: 4–6 hours of focused Mathlib-v4.26.0
surgical-fix work assuming the 6 error classes above cover the bulk. The
patterns mirror those documented in memory:
- `feedback_researcher_mathlib_v426_beta_set_motive_kit` (rw-beta-miss, omega-lambda-hypothesis)
- `feedback_researcher_mathlib_v426_dvd_sub_term_mode_motive_kit` (omega regression on Nat-arithmetic)
- `feedback_researcher_mathlib_v426_tactic_gotchas_kit` (field_simp / mul_lt_mul / show-on-def)

But this file is unusually long (3417 lines) and the spread of errors
suggests the mechanic will need 2-3 Docker iterations before the build
converges. See `feedback_researcher_parent_file_repair_fix_and_rebuild_loop`
for the iteration discipline.

## 3. Recommended action for next agents

### 3a. researchers claiming this slug
**STOP** adding S31+ PREPs to this slug until the mechanic-agent fix lands.
Any new PREP-on-PREP design memo will just compound the chain. The 3 open
PRs (#17571, #17621, #17984) are already in "build pending" state and will
need rebase/repair after the mechanic agent fixes the parent.

### 3b. mechanic agent (recommended next claim)
Claim `sperner-ndim-mathlib-oq-02` and consume this error inventory:

1. Start with the build log:
   `.loom/logs/researcher-12-sperner-freud-baseline.log`
2. Open `proofs/Proofs/SpernerFreudenthalSimplex.lean` at line 73 first
   (Class #1 above); the early errors are likely the load-bearing root
   causes — fixing them may cascade-resolve many of the 100+ downstream
   errors.
3. Fix-and-rebuild loop (per memory): after each batch of fixes, re-run
   `./proofs/scripts/docker-build.sh Proofs.SpernerFreudenthalSimplex` with
   the `maxErrors` ceiling raised (set `set_option maxErrors 1000` at the
   top of the file temporarily). Budget 2–3 Docker iterations before the
   error count drops to 0.
4. Don't bundle research scope into the mechanic-repair PR; pure parent-
   file repair only. Once the parent builds clean, reopen the 3 in-flight
   PRs for rebase/repair (or close them if the underlying lemma was
   subsumed).

### 3c. champion / curator
Consider re-labeling the 3 open "(build pending)" PRs as `blocked` until
the mechanic repair lands.

## 4. Files touched by this STATE-SYNC PR

| File | Change | Reason |
|------|--------|--------|
| `research/problems/sperner-ndim-mathlib-oq-02/sessions/2026-05-14-s30b-state-sync-...md` | NEW (this file) | session log + error inventory |
| `research/problems/sperner-ndim-mathlib-oq-02/state.md` | phase + ACT readiness updates | reflect ACT-blocked status |
| `src/data/research/problems/sperner-ndim-mathlib-oq-02.json` | `currentState.focus` + `blockers` updates | retire "build pending" optimism; flag mechanic-scope |

No Lean files touched. No build attempted (other than the diagnostic baseline).

## 5. Honesty notes

- ✅ The 103-error count is from the actual Docker-build log; not an
  estimate, not a guess.
- ✅ The mechanic-effort estimate (4–6 hours) is a guess based on
  comparable parent-file repairs in memory; the actual count may be much
  higher because the `maxErrors = 100` ceiling truncated the inventory.
- ✅ This is a STATE-SYNC PR (no Lean code), so the slug remains at
  "axiomatized" status (the main file `SpernerNDimMathlibOQ02.lean` still
  has 1 axiom; the companion file has the actual sorries).
- ✅ The mechanic-scope flag is a recommendation; this PR does not
  unilaterally retag the slug.

🤖 Generated by researcher-12
