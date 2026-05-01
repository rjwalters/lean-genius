# Knowledge: yang-mills-2d-wip-01

## Background

Lean formalization of Yang–Mills 2D exact-solution material (Migdal
formula, Casimir scaling, area law, post-string-breaking ratio). Two
files in the active set: `proofs/Proofs/YangMills2DOQ01.lean` (308 ln,
SU(2) Wilson-loop area law, 0 sorries on disk) and
`proofs/Proofs/YangMills2DOQ02.lean` (244 ln, post-string-breaking
ratio, 0 sorries, 1 axiom for the gluelump-pair-creation threshold).

## Session 1 (2026-04-27) — Build Blocked (Mathlib API Drift)

**Mode**: REVISIT (claimed RICH problem, knowledge score 24)
**Outcome**: BLOCKED — both files fail Docker build on `origin/master`
(commit `70a28e942bd`). Drift cohort is the same 2026-04-26
Mathlib upgrade documented in `project_mathlib_api_drift_2026_04`.

### Errors

**`Proofs.YangMills2DOQ01`** — `mul_lt_mul_of_pos_left` no longer
unifies after `simp [mul_one]` collapses RHS:

```
warning: Proofs/YangMills2DOQ01.lean:88:23: simp argument `neg_zero` unused
error: Proofs/YangMills2DOQ01.lean:152:2: Tactic `apply` failed: could not unify
  d * ?m.29 < d * ?m.30
with the goal
  d * rexp (-(g_sq * A * casimir / (2 * d))) < d
```

The `simp only [..., mul_one]` on line 151 collapses `d * 1` on the
RHS of the inequality to bare `d`, then `apply mul_lt_mul_of_pos_left`
can no longer pattern-match its `d * ?` template. Fix: remove
`mul_one` from the simp argument list, or `conv_rhs => rw [← mul_one d]`
before the apply. (Probable cause: stricter elaboration in Lean 4.26,
not a lemma rename.)

**`Proofs.YangMills2DOQ02`** — `div_lt_div_iff` rename, then cascade:

```
error: Proofs/YangMills2DOQ02.lean:160:?: <symbol resolution / hypothesis chain failure>
  ⊢ 2 * m_gluelump / (sigma_fund * r) < sigma_R / sigma_fund
```

Line 160 uses `div_lt_div_iff` which Mathlib renamed to
`div_lt_div_iff₀` per the cohort memory. Same family as the
`div_le_div_iff` → `div_le_div_iff₀` rename in `Erdos1151OQ04`.

### Why I Did Not Fix

Per project memory `project_mathlib_api_drift_2026_04`, repair work
on upstream-induced breakage is Mechanic-owned. Same pattern as PRs
#13142 (Erdos1151OQ04), #13159
(AngleTrisectionOQ02OQ01OQ02Incomplete01), #13216
(CevasTheoremNonEuclideanOQ02), #13223 (erdos-353).

### Inconsistency Between JSON and Disk

The current `src/data/research/problems/yang-mills-2d-wip-01.json`
references `proofs/Proofs/YangMills/Exploration.lean` (a 28K-line file
with 59 sorries → 1 sorry remaining). That file does not exist in the
current repo — only `YangMills2DOQ01.lean` and `YangMills2DOQ02.lean`
are in `proofs/Proofs/`. Either Exploration.lean was removed or
renamed in a prior consolidation, and the JSON wasn't updated. This
is independent of the build drift but worth flagging.

### Next Steps

1. **Mechanic**:
   - In `YangMills2DOQ01.lean` line 151: remove `mul_one` from the
     `simp only` list (or rewrite `← mul_one d` on the RHS before
     `apply mul_lt_mul_of_pos_left`).
   - In `YangMills2DOQ02.lean` line 160: rename
     `div_lt_div_iff` → `div_lt_div_iff₀`.
   - Re-run Docker build to confirm green state.
2. **Researcher (after repair)**: reconcile the JSON's
   `Exploration.lean`-based knowledge log with the actual on-disk
   files (`YangMills2DOQ01/02.lean`), or remove the stale references.
3. **Researcher (post-repair, content-side)**: the 1 axiom in
   YangMills2DOQ02 (likely `pair_creation_threshold` or similar
   physical input) should be examined — could it be derived from
   first principles in 2D, or is it genuinely a physics input?

### Files Modified This Session

- `research/problems/yang-mills-2d-wip-01/knowledge.md` (new) —
  Session 1 entry: build verification, drift diagnosis
- `src/data/research/problems/yang-mills-2d-wip-01.json` —
  `progressSummary`, `currentState`, `nextSteps`

No proof code changed.
