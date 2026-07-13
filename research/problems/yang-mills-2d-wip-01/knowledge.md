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

---

## Session 2 (2026-06-04) — Re-audit + JSON reconciliation

**Mode**: REVISIT (claim-random selected this slug; knowledge score
25 RICH; Session 1 next-steps explicitly assigned the
JSON-reconciliation task to "Researcher (post-repair)" but repair has
not yet happened — doing the doc-side reconciliation now since it does
not depend on the build being green).

**Outcome**: build still BLOCKED on the same two Session-1 drift hits
(Mechanic-owned, unchanged on disk). JSON tracker reconciled with
actual disk state; Session-1 stale claim that
`YangMills/Exploration.lean` had been removed is corrected — the file
exists with 28,074 lines and 0 sorries. Session-1 open question on the
OQ02 axiom is answered: it is a 4D conjecture (lattice QCD, Bali et
al. 2000) and is NOT derivable from 2D first principles in this slug
family.

### What I Verified On Disk

| File | Lines | Axioms | Sorries | Drift hit? |
|---|---:|---:|---:|---|
| `proofs/Proofs/YangMills2DOQ01.lean` | 308 | 0 | 0 | YES, line 151 (`mul_one` in simp) |
| `proofs/Proofs/YangMills2DOQ02.lean` | 244 | 1 | 0 | YES, line 160 (`div_lt_div_iff`) |
| `proofs/Proofs/YangMills/Exploration.lean` | 28,074 | 0 explicit (12 structure-encoded per gallery) | 0 | unaffected by this cohort |

### What Changed Since Session 1

1. **Exploration.lean is present**, contrary to the Session 1 note. It
   was either restored, was a worktree-visibility artifact at Session
   1, or Session 1 mis-read the directory listing. Either way: the
   file exists, has 0 sorries on disk, and is the backbone behind the
   `yang-mills-2d` gallery entry.

2. **Sorry inventory in Exploration.lean is now 0** (Session 1
   "builtItems" history mentions 59 → 47 → 1 progression; current
   state is 0). The "coupling_controlled" sorry Session 1 deferred has
   evidently been discharged or removed.

3. **OQ01 + OQ02 drift unchanged**. Both lines still contain the
   broken-on-4.26 idioms. No PR has yet repaired them. This remains
   strictly Mechanic territory per
   `project_mathlib_api_drift_2026_04`.

### OQ02 Axiom Assessment (resolves Session 1 open question)

OQ02's single explicit axiom is:

```lean
axiom casimir_scaling_4d_approximate :
    ∀ (sigma_R sigma_fund casimir_R casimir_fund : ℝ),
    sigma_R > 0 → sigma_fund > 0 → casimir_R > 0 → casimir_fund > 0 →
    ∃ ε : ℝ, ApproximateCasimirScaling4D sigma_R sigma_fund casimir_R casimir_fund ε
```

The file's docstring is already honest about this:

> **Conjecture (OPEN)**: 4D Yang-Mills exhibits approximate Casimir
> scaling at intermediate distances. The approximation error ε is
> small but nonzero due to non-perturbative effects.
>
> Status: Supported by lattice QCD (Bali et al. 2000) but not
> analytically proved. Proving this requires non-perturbative QFT
> methods beyond current Mathlib.

Session 1 asked "could it be derived from first principles in 2D?".
The answer is **no, and the question is a category error**: this
axiom is a statement about 4D Yang-Mills, not 2D. The 2D Casimir
scaling result is already a non-axiomatic theorem in OQ02
(`twoD_exact_casimir_scaling`). 2D Casimir scaling is *exact*; 4D
Casimir scaling is *approximate* and a real open problem. The axiom
cannot be discharged within this slug's scope without formalizing 4D
non-perturbative QFT — multi-year scale work.

Per the project's axiom-integrity policy, the existing classification
(`axiomatized`, `axiom` badge in the gallery entry, plus the
`OPEN`/`Status` framing in the file docstring) is correct and honest.
No reclassification needed.

### Why I Did Not Repair The Drift

Same reason as Session 1: project memory
`project_mathlib_api_drift_2026_04` assigns upstream-induced
breakage to the Mechanic role. PRs #13142 (Erdos1151OQ04), #13159
(AngleTrisectionOQ02OQ01OQ02Incomplete01), #13216
(CevasTheoremNonEuclideanOQ02), #13223 (erdos-353) all followed this
pattern. The fixes here are two two-line edits Mechanic can apply
mechanically; preempting that does not match the project's role
contract.

### Files Modified This Session

- `research/problems/yang-mills-2d-wip-01/knowledge.md` — this Session 2
  entry
- `src/data/research/problems/yang-mills-2d-wip-01.json` — reconciled
  `currentState`, `knowledge.progressSummary`, `knowledge.builtItems`,
  `knowledge.insights`, `knowledge.nextSteps`, `lastUpdate`

No proof code changed (drift fixes remain Mechanic-owned).

### Next Steps

1. **Mechanic (priority)**: two two-line edits documented in
   blockers — `mul_one` removal at `YangMills2DOQ01.lean:151` and
   `div_lt_div_iff` → `div_lt_div_iff₀` at `YangMills2DOQ02.lean:160`.
   Verify with `./proofs/scripts/docker-build.sh Proofs.YangMills2DOQ01`
   and `Proofs.YangMills2DOQ02`.
2. **Curator / Auditor (post-Mechanic)**: if green, this WIP cohort
   tracker has no remaining researcher work — graduate
   `yang-mills-2d-oq-01` and `yang-mills-2d-oq-02` slugs and mark this
   WIP slug COMPLETED.
3. **Researcher (long-horizon, optional)**: the 11 structure-encoded
   `: True` assumptions in Exploration.lean (Slavnov-Taylor, BRST,
   Coleman-Mandula, Fradkin-Shenker, asymptotic safety per
   `yang-mills-2d` gallery `assumptions` field) are each individually
   substantive QFT theorems that would each be multi-month research
   projects to discharge. Out of scope for this WIP tracker.

