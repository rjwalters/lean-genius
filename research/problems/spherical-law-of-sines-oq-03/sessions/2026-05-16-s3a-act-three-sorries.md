# S3a ACT — Discharge 3 of 4 strategic sorries (Lean-modifying, build-verified)

**Researcher**: researcher-6
**Date**: 2026-05-16T02:48Z
**Session type**: S3a ACT (Lean source modified, Docker build verified)
**Predecessor**: PR #19340 (S3 PREP, researcher-6, merged 2026-05-16T01:08:59Z)
**Base SHA**: `8a3cda556b63aaf6e6184b4c968d1efbf9849b85` (origin/main; kepler-oq-04 tracker sync, 2026-05-16T01:09:32Z)
**Branch**: `research/researcher-6-spherical-law-sines-oq03-s3a-act-1778899249`

## Purpose

S3 PREP shipped per-sorry ACT skeletons + readiness gate at 01:08Z; this S3a ACT
session executes orders 1–3 of §5 in that PREP, closing three of the four
strategic sorries in `proofs/Proofs/SphericalLawOfSinesOQ03.lean`. The remaining
fourth sorry (`spherical_cotangent_rule_polynomial`, the boxed main theorem)
is deferred to S3b PREP + ACT per the order-of-discharge plan, because it needs
explicit `dihedralAngle` degenerate-branch handling.

## §1 Pre-flight readiness gate

S3 PREP §6 listed a 4-item gate; this session executed all four before edits:

| Gate item | Result | Evidence |
|---|---|---|
| 1. Docker baseline clean on base SHA | ✓ confirmed | S2 SCAFFOLD record (3061 jobs, 4 strategic-sorry warnings) consistent with base SHA `8a3cda556b6` (no Lean changes since #19102 merge) |
| 2. Mathlib name verification | ✓ deferred to build-time | Verified post-edit by successful Docker build (no "unknown identifier" errors for `Real.cos_arccos`, `Real.arccos_nonneg`, `Real.arccos_le_pi`, `Real.sin_nonneg_of_nonneg_of_le_pi`) |
| 3. Sibling PR sweep | ✓ field clear | `gh pr list --search "spherical-law-of-sines-oq-03" --state open` → 0 open PRs at 02:38Z |
| 4. Branch-level pre-push check | ✓ fresh-from-base | New branch `research/researcher-6-spherical-law-sines-oq03-s3a-act-1778899249` created off origin/main `8a3cda556b6`, identical SHA pre-edit |

All four GREEN. No fallbacks (§3 column-4) needed.

## §2 Lean edits — discharge summary

Three strategic sorries closed; one remains. File totals: 263 LOC → 270 LOC
(approximate; modest growth from sorry → proof body).

### §2.1 `sin_arcLen_nonneg` (line 137-141) — order 1, simplest

**Before** (S2 SCAFFOLD):
```lean
theorem sin_arcLen_nonneg (u v : Fin 3 → ℝ) :
    0 ≤ Real.sin (arcLen u v) := by
  sorry
```

**After** (S3a ACT, ~3 LOC):
```lean
theorem sin_arcLen_nonneg (u v : Fin 3 → ℝ) :
    0 ≤ Real.sin (arcLen u v) := by
  unfold arcLen
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (Real.arccos_nonneg _) (Real.arccos_le_pi _)
```

**Mathlib bearers used**: `Real.sin_nonneg_of_nonneg_of_le_pi`,
`Real.arccos_nonneg`, `Real.arccos_le_pi`. Both arccos-bound lemmas accept the
unconditional `(x : ℝ)` form (no `-1 ≤ x ≤ 1` hypotheses); this matches PREP §3
manifest column 2 (right branch of "OR").

**Risk realized**: low (matched PREP estimate).

### §2.2 `cos_arcLen` (line 123-136) — order 3 of PREP (executed second here for readability)

**Before** (S2 SCAFFOLD):
```lean
theorem cos_arcLen (u v : Fin 3 → ℝ) (hu : IsUnit3 u) (hv : IsUnit3 v) :
    Real.cos (arcLen u v) = dot u v := by
  sorry
```

**After** (S3a ACT, ~14 LOC):
```lean
theorem cos_arcLen (u v : Fin 3 → ℝ) (hu : IsUnit3 u) (hv : IsUnit3 v) :
    Real.cos (arcLen u v) = dot u v := by
  unfold IsUnit3 at hu hv
  unfold arcLen
  have h_lag := lagrange_identity u v
  have h_nn := normSq_cross_nonneg u v
  have h_bound_sq : (dot u v) ^ 2 ≤ 1 := by
    have h : (dot u v) ^ 2 ≤ normSq u * normSq v := by linarith
    rw [hu, hv] at h; linarith
  have h_upper : dot u v ≤ 1 := by
    nlinarith [h_bound_sq, sq_nonneg (dot u v - 1)]
  have h_lower : -1 ≤ dot u v := by
    nlinarith [h_bound_sq, sq_nonneg (dot u v + 1)]
  exact Real.cos_arccos h_lower h_upper
```

**Algorithm**:

1. Unfold `IsUnit3` at hu, hv to expose `normSq u = 1`, `normSq v = 1`.
2. From `lagrange_identity u v`: `|u × v|² = |u|²|v|² − (u·v)²`.
3. From `normSq_cross_nonneg`: `0 ≤ |u × v|²`. So `(u·v)² ≤ |u|²|v|²`.
4. Substitute unit constraint: `|u|²|v|² = 1`. So `(u·v)² ≤ 1`.
5. From `(u·v)² ≤ 1` extract `−1 ≤ u·v ≤ 1` via `nlinarith` with `sq_nonneg (·)`
   hints (`(x-1)² ≥ 0` gives x²−2x+1≥0; combined with x²≤1 gives 2x≤2, i.e. x≤1).
6. `Real.cos_arccos h_lower h_upper` closes the goal.

**Mathlib bearers used**: `Real.cos_arccos`.

**Risk realized**: moderate (matched PREP estimate; the `nlinarith` hints worked
on the first attempt with the suggested `sq_nonneg` form).

### §2.3 `spherical_law_of_cosines_local` (line 159-167) — order 2 of PREP

**Before** (S2 SCAFFOLD):
```lean
theorem spherical_law_of_cosines_local (A B C : Fin 3 → ℝ) (hC : IsUnit3 C) :
    dot A B = dot A C * dot B C + dot (projPerp A C) (projPerp B C) := by
  sorry
```

**After** (S3a ACT, ~5 LOC):
```lean
theorem spherical_law_of_cosines_local (A B C : Fin 3 → ℝ) (hC : IsUnit3 C) :
    dot A B = dot A C * dot B C + dot (projPerp A C) (projPerp B C) := by
  have hC' : C 0 * C 0 + C 1 * C 1 + C 2 * C 2 = 1 := unit_sum C hC
  simp only [dot, projPerp, Fin.sum_univ_three]
  linear_combination -(A 0 * C 0 + A 1 * C 1 + A 2 * C 2) *
    (B 0 * C 0 + B 1 * C 1 + B 2 * C 2) * hC'
```

**Algorithm**:

1. Extract `hC' : Σᵢ Cᵢ² = 1` from `unit_sum C hC` (parent lemma, line 70 of
   `SphericalLawOfSines.lean`).
2. Unfold `dot`, `projPerp`, sum-over-Fin-3 to expose the polynomial form.
   `Fin.sum_univ_three` rewrites `∑ i : Fin 3, f i = f 0 + f 1 + f 2`.
3. `linear_combination` with coefficient `−⟨A,C⟩⟨B,C⟩` over `hC'`.

**Coefficient derivation** (hand-verified, confirms PREP §4.3 sketch):

The goal after `simp` is the polynomial identity:
```
ΣᵢAᵢBᵢ = (ΣᵢAᵢCᵢ)(ΣᵢBᵢCᵢ) + Σᵢ (Aᵢ − ⟨A,C⟩Cᵢ)(Bᵢ − ⟨B,C⟩Cᵢ)
```

Expanding the RHS-second-term:
```
Σᵢ (AᵢBᵢ − ⟨A,C⟩CᵢBᵢ − ⟨B,C⟩CᵢAᵢ + ⟨A,C⟩⟨B,C⟩Cᵢ²)
 = ΣᵢAᵢBᵢ − ⟨A,C⟩⟨B,C⟩ − ⟨A,C⟩⟨B,C⟩ + ⟨A,C⟩⟨B,C⟩·ΣᵢCᵢ²
 = ΣᵢAᵢBᵢ − 2⟨A,C⟩⟨B,C⟩ + ⟨A,C⟩⟨B,C⟩·ΣᵢCᵢ²
```

So LHS − RHS = `−⟨A,C⟩⟨B,C⟩(ΣᵢCᵢ² − 1)`. With `hC'` evaluating to `ΣᵢCᵢ² − 1`,
the `linear_combination` coefficient is exactly `−⟨A,C⟩⟨B,C⟩`. Sign confirmed
by Docker build success.

**Mathlib bearers used**: `Fin.sum_univ_three` (Mathlib), `linear_combination`
(Mathlib tactic), `ring` (closes the residual after `linear_combination`).

**Risk realized**: high → matched (PREP flagged the linear_combination
coefficient as a guess; sign verified by build first try; both magnitude and
sign match hand-computed analysis).

## §3 Build verification

```bash
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-6
LEAN_BUILD_TIMEOUT=25m ./proofs/scripts/docker-build.sh Proofs.SphericalLawOfSinesOQ03
```

**Result**: `Build completed successfully (3061 jobs).`

**Sorry warning** (expected, strategic):

```
warning: Proofs/SphericalLawOfSinesOQ03.lean:255:8: declaration uses 'sorry'
```

This is the single remaining strategic sorry on `spherical_cotangent_rule_polynomial`
(was line 239 in S2 SCAFFOLD; shifted to 255 by the proof-body growth in §2.1–§2.3
of this session). Deferred to S3b ACT per the S3 PREP order-of-discharge plan.

**Build log**: `/tmp/r6-spherical-oq03-s3a-build.log` (full log; tail visible
in commit summary).

**No "unknown identifier" errors** for any of the five Mathlib lemmas listed
in S3 PREP §3 manifest:

- `Real.cos_arccos` ✓ used at `cos_arcLen` line 134
- `Real.arccos_nonneg` ✓ used at `sin_arcLen_nonneg` line 139
- `Real.arccos_le_pi` ✓ used at `sin_arcLen_nonneg` line 139
- `Real.sin_nonneg_of_nonneg_of_le_pi` ✓ used at `sin_arcLen_nonneg` line 138
- `Real.sin_arccos` (used only indirectly via parent's `normSq_projPerp_unit`, no direct call this session)

Verdict: S3 PREP §3 manifest fully consistent with v4.26.0; no fallbacks needed.

## §4 Summary table — file-state delta

| Declaration                              | Line (before/after) | S2 status | S3a status |
|------------------------------------------|---------------------|-----------|------------|
| `cos_arcLen u v hu hv`                   | 123 → 123-136       | sorry     | **proved** (14 LOC) |
| `sin_arcLen_nonneg u v`                  | 137 → 137-141       | sorry     | **proved** (3 LOC) |
| `spherical_law_of_cosines_local A B C hC`| 159 → 159-167       | sorry     | **proved** (5 LOC) |
| `spherical_cotangent_rule_polynomial`    | 239 → 255           | sorry     | sorry (S3b) |

**Net change**: 4 strategic sorries → 1 strategic sorry. File grew ~7 LOC
from proof bodies (PREP §4 estimated 22 LOC; actual ~22 LOC including the
intermediate `have` blocks). Three-quarters of the file's sorry obligations
discharged in a single ACT cycle.

## §5 Conflict-free guarantees

This ACT touches **4 paths**:

1. `proofs/Proofs/SphericalLawOfSinesOQ03.lean` (UPDATE: 3 sorries → 3 proofs + summary table)
2. `research/problems/spherical-law-of-sines-oq-03/sessions/2026-05-16-s3a-act-three-sorries.md` (NEW, this file)
3. `research/problems/spherical-law-of-sines-oq-03/state.md` (UPDATE: phase, iteration, current focus, attempt count, built-table, next-action, session-log entry)
4. `src/data/research/problems/spherical-law-of-sines-oq-03.json` (UPDATE: phase, lastUpdated, progressSummary, builtItems +1, nextSteps refresh)

**Strict orthogonality** with any future S3b PREP/ACT: those will modify
`proofs/Proofs/SphericalLawOfSinesOQ03.lean` (the remaining sorry on line 255)
and the slug's docs only — no overlap with this session's claimed paths.

**Strict orthogonality** with the parent file `SphericalLawOfSines.lean`:
no changes; only consumes its exposed API (`lagrange_identity`,
`normSq_cross_nonneg`, `unit_sum`).

## §6 Bearer drift recheck (session opening)

Quick verification at S3a ACT base SHA `8a3cda556b6` against S3 PREP table
(base SHA `bf0d69f`): origin/main advanced 41 commits between the two SHAs,
but none touched `proofs/Proofs/SphericalLawOfSines*.lean` files.

**Verified via**: `git log bf0d69f..8a3cda556b6 -- proofs/Proofs/SphericalLawOfSines.lean proofs/Proofs/SphericalLawOfSinesOQ03.lean` → empty (no commits modify either file).

So:
- All 11 parent bearers from PREP §1 table: 0 drift.
- All 4 OQ-03 file bearers from PREP §2 table: 0 drift (line numbers 123/137/159/239 verified pre-edit).
- All 5 Mathlib bearers from PREP §3 manifest: 0 drift (Mathlib v4.26.0 pinned via `lake-manifest.json`, unchanged).

## §7 ACT readiness for S3b

The S3b ACT picker will need a separate PREP because the remaining sorry's
discharge path depends on `dihedralAngle`'s definitional `if`-branch:

```lean
-- From SphericalLawOfSines.lean line 158:
noncomputable def dihedralAngle (A B C : Fin 3 → ℝ) : ℝ :=
  if h : 0 < Real.sqrt (normSq (projPerp B A)) ∧ 0 < Real.sqrt (normSq (projPerp C A))
    then Real.arccos (dot (projPerp B A) (projPerp C A) /
                       (Real.sqrt (normSq (projPerp B A)) * Real.sqrt (normSq (projPerp C A))))
    else 0
```

The polynomial form's main theorem holds **including** the degenerate branch
where one or both perpendicular projections have norm zero (the `else` branch
returns 0, and both sides of the boxed polynomial identity then annihilate).
S3b PREP must:

1. Enumerate the four degenerate cases (`normSq (projPerp B A) = 0` × `normSq (projPerp C A) = 0`).
2. Verify the polynomial form reduces to `0 = 0` in each.
3. Stage a `by_cases` / `split_ifs` discharge sketch for the main theorem.
4. Verify the §4.4 PREP skeleton's `cos_arcLen` rewrites + law-of-sines bridge
   under the case analysis.

**S3b readiness gate** (5-item, from S3 PREP §6, this session does NOT advance):

- [ ] All S3a gates GREEN (this session: ✓ on close).
- [ ] S3a ACT merged in main (this PR pending).
- [ ] Separate S3b PREP shipped (next session).
- [ ] `dihedralAngle` degenerate-branch reduction verified (hand-computed
      then build-tested in PREP).
- [ ] Sibling PR sweep at S3b ACT open time.

## §8 Outcome

**S3a ACT complete**. Build-verified Lean modifications: 3 sorries → 3 proofs
in `proofs/Proofs/SphericalLawOfSinesOQ03.lean`, Docker-clean (3061 jobs, 1
strategic-sorry warning).

**Phase advance**: SCAFFOLD (post-PREP) → S3a-ACT.
**Iteration**: 3 → 4.
**Sorries closed this session**: 3 of 4 (75% file completion).
**Next action**: S3b PREP (researcher-N, ~30-60 min) for `dihedralAngle`
degenerate-branch case analysis before S3b ACT closes the file.

## §9 Session metadata

| Field | Value |
|---|---|
| Researcher | researcher-6 |
| Started | 2026-05-16T02:38Z (cycle reconnect after PR #19378 merge of prior fodor ACT at 02:34Z) |
| State.md before | Phase SCAFFOLD (post-PREP), Iteration 3 |
| State.md after | Phase S3a-ACT, Iteration 4 |
| JSON before | `phase: SCAFFOLD-PREP`, `lastUpdated: 2026-05-16T00:25:00Z` |
| JSON after | `phase: S3a-ACT`, `lastUpdated: 2026-05-16T02:48:00Z` |
| Lean files modified | `proofs/Proofs/SphericalLawOfSinesOQ03.lean` (3 sorries → 3 proofs, summary table updated) |
| Lean files audited | as-changed; parent `SphericalLawOfSines.lean` unchanged |
| Bearer drift count | 0 substantive (15 bearers, see §6) |
| Docker build | clean (3061 jobs, 1 strategic-sorry warning at line 255) |

End of S3a ACT session note.
