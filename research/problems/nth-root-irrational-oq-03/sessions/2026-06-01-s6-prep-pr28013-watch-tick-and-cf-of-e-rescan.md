# S6 PREP — PR #28013 watch tick + CF-of-e Mathlib rescan + S5c build re-verify

**Researcher**: researcher-1 (claim id `researcher-6368`)
**Date**: 2026-06-01T05:10Z
**Phase**: PREP (S6 watch tick + drift recheck)
**Iteration**: 7
**Scope**: doc-only

## 1. Mission

State.md (post-S5d, 2026-05-16) names two **passive** continuations:

> **Path B (passive)**: continue S6 watch on Mathlib PR #28013. Threshold 168h,
> current 91h, margin ~77h. Re-check at next slug claim.

> **Path C (active, high ROI)**: apply S5c's `rat_approx_bounded_den_finite` +
> `irrational_liouvilleWith_two` reusable template to a sibling slug with an
> analogous `LiouvilleWith 2 (specific-irrational)` axiom.

This iteration performs the Path B watch tick (16 days after S5d), re-scans
Mathlib master for any new CF-of-e content (S5d's `e_continued_fraction_pattern`
blocker), and re-verifies the S5c-shipped infrastructure still builds clean at
origin/main HEAD `8bf8a7b3552`. Path C is **declined** this session — see §5
for the empirical reason (no other Lean files in `proofs/Proofs/` carry a
`LiouvilleWith p (specific-irrational)` axiom).

## 2. Lake SHA verification

`proofs/lake-manifest.json` at HEAD `8bf8a7b3552`:

| field      | value                                              |
|------------|----------------------------------------------------|
| `inputRev` | `v4.26.0`                                          |
| `rev`      | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`         |

**0 drift** from S5c PREP / S5c ACT / S5d PREP records. The project pin has not
moved in 16 days.

## 3. S5c-era build re-verify (RECOVERING-phase recheck)

Per memory `feedback_recovering_phase_resolves_silently_under_docker.md`, pre-
2026-05-31 RECOVERING/build-pending slugs often build clean now. The slug's
primary Lean targets:

| target                       | result                  |
|------------------------------|-------------------------|
| `Proofs.ETranscendentalOQ03` | **3072/3072 jobs ✓**    |
| `Proofs.eTranscendental`     | replayed from cache ✓   |

Command:
```
LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03
```
Output (tail):
```
⚠ [3071/3072] Replayed Proofs.eTranscendental
⚠ [3072/3072] Replayed Proofs.ETranscendentalOQ03
Build completed successfully (3072 jobs).
=== Build succeeded ===
```

**Verdict**: clean. S5c's `irrational_liouvilleWith_two` + `rat_approx_bounded_den_finite`
remain build-verified at HEAD. 0 bearer drift across the 16-day interval.

### 3.1 Deprecation linter warnings — same as S5c records

```
warning: Proofs/eTranscendental.lean:5: 'Mathlib.Data.Real.Irrational' has been deprecated
warning: Proofs/eTranscendental.lean:6: 'Mathlib.Data.Complex.ExponentialBounds' has been deprecated
warning: Proofs/ETranscendentalOQ03.lean:6: 'Mathlib.Data.Real.Irrational' has been deprecated
```

These are linter warnings (not errors). Same 3 deprecation warnings noted in
S5c ACT §3 (2026-05-16). The replacement imports are:
- `Mathlib.Data.Real.Irrational` → `Mathlib.NumberTheory.Real.Irrational`
- `Mathlib.Data.Complex.ExponentialBounds` → `Mathlib.Analysis.Complex.ExponentialBounds`

Out of S6 scope (doc-only watch tick). Flagged as a follow-up `mechanic`-class
cleanup PR — touches 2 files, 3 lines, no semantic change.

## 4. PR #28013 watch tick (16-day delta)

### 4.1 Status snapshot

| field             | value (2026-06-01)                                   | delta vs S5d (2026-05-16) |
|-------------------|------------------------------------------------------|---------------------------|
| `state`           | open                                                 | unchanged                 |
| `merged`          | false                                                | unchanged                 |
| `draft`           | false                                                | unchanged                 |
| `mergeable`       | true                                                 | unchanged                 |
| `mergeable_state` | blocked                                              | unchanged (review-gated)  |
| `head_sha`        | `5abb7c68488b527e4d7ecf5d7bbe085db8d2a388`           | **CHANGED** from `3bafffe27908…` |
| `updated_at`      | `2026-05-29T07:22:48Z`                               | **+17 days fresher**      |
| `additions`       | 1040                                                 | (unrecorded at S5d)       |
| `deletions`       | 64                                                   | (unrecorded at S5d)       |
| `comments`        | 9 issue + 24 review                                  | (unrecorded at S5d)       |

### 4.2 Recent commits (since S5d era, head→tip)

Sampled `gh api repos/.../pulls/28013/commits?per_page=100&page=3` (paginated
tail):

```
2025-12-30 .. 2026-01-04   cleanup, yamls, liftFinsupp, module, Indicator.lean, Gal( / )
2026-04-08                 cleanup
2026-04-08                 Merge branch 'master' into transcendental
2026-04-20                 Merge branch 'master' into transcendental + to_dual fix
2026-04-27                 suggestions, -`public`, Merge branch 'master' into transcendental
2026-05-08                 Merge branch 'master' into pr/28013; lint; cleanup; fix
2026-05-29                 Merge branch 'master' into transcendental   ← MOST RECENT
```

**Pattern**: between S5d (2026-05-16) and now (2026-06-01) the PR received
exactly **one** activity — the `2026-05-29` merge-from-master. No new
substantive commits since `2026-05-08` (the prior `lint/cleanup/fix` cluster).
The merge SHA change `3bafffe27908` → `5abb7c68488` is mechanical (rebase on
master), not new mathematical content.

### 4.3 Staleness calculus

S5d watch tick recorded `~90.93h` stale vs threshold `168h` (margin `~77h`).

Recomputed at 2026-06-01T05:10Z:

```
hours since last updated_at = (2026-06-01T05:10Z) − (2026-05-29T07:22:48Z)
                            = 69.8h
```

**Below threshold** (168h). Margin grew rather than shrank because the
2026-05-29 merge reset the clock. The PR is therefore "warm" — author/maintainer
activity within the past 3 days, well below the S5d-recorded staleness threshold
that would trigger a "consider scoping local re-prove" decision.

### 4.4 Verdict

- **No upstream merge of #28013**: `axiom hermite_lindemann` discharge (S6) remains
  gated. mergeable_state `blocked` typically means awaiting required reviews; 24
  review comments + 9 issue comments suggests active review backlog.
- **Watch-loop cadence**: next tick at next claim of this slug. Staleness is now
  decreasing-by-default each day until the next maintainer push.
- **No promote-to-local-reprove signal**: 69.8h stale is well below the 168h
  threshold; far from the "consider scoping" decision boundary.

## 5. Path C re-evaluation (sibling slug template re-use)

S5d PREP recommended applying `irrational_liouvilleWith_two` + the slice-
finiteness helper to a sibling slug with an analogous axiom. This session
empirically checked that recommendation:

### 5.1 LiouvilleWith / liouvilleWith axiom scan across `proofs/Proofs/`

```
grep -rn "axiom.*[Ll]iouvilleWith" /Users/rwalters/GitHub/lean-genius/proofs/Proofs/
→ proofs/Proofs/ETranscendentalOQ03.lean:247: axiom e_not_liouvilleWith_gt_two ...
```

**Result**: exactly one such axiom across the whole `proofs/Proofs/` tree, and
it is in the *same file* as the just-shipped `irrational_liouvilleWith_two` —
i.e. there is no sibling slug carrying an analogous `LiouvilleWith 2 (specific-
irrational)` axiom that could be discharged by the template.

### 5.2 Sibling slug Liouville candidates

S5d PREP suggested `pi-transcendental-oq-*` and `ln-2-irrationality-*` as
candidates. Empirical check:

- `PiTranscendental.lean` exists (457 LOC). Contains `axiom lindemann_theorem`
  at line 125. **No `LiouvilleWith`-related axioms.** The irrationality measure
  of π is unknown (2 ≤ μ(π) ≤ 7.10), so a `LiouvilleWith 2 π` proof is
  immediately available (π is irrational → `irrational_liouvilleWith_two _
  Real.pi_irrational`), but **no such axiom exists in any file** to discharge.
- No `LnTwo*.lean` or `LogTwo*.lean` or `Liouville*.lean` (other than
  `LiouvilleTheorem.lean` / `LiouvilleTheoremOQ04.lean`, both unrelated to
  irrationality measure of specific irrationals) carry the target axiom shape.

**Verdict**: Path C has **no actionable target** at this time. The template is
correct and reusable, but the analogous-axiom slot is empty across the whole
repo. Future enrichment or research work could **add** new `LiouvilleWith 2
(specific-irrational)` consequence theorems to other slugs (using the template),
but that is enricher/curator-scope generative work, not axiom-reduction
researcher work.

## 6. CF-of-e Mathlib master rescan

S5d PREP verdict (2026-05-16): "**CF expansion of e (Euler's [2;1,2k,1] pattern)
is completely absent from Mathlib**", confirmed via 3 independent code searches
+ full tree filter.

### 6.1 16-day delta — Mathlib master path commits

```
GET repos/leanprover-community/mathlib4/commits
    ?path=Mathlib/Algebra/ContinuedFractions&since=2026-05-16T00:00:00Z
```

| date         | sha       | message (truncated)                                 |
|--------------|-----------|-----------------------------------------------------|
| `2026-06-01` | fc937127  | doc: add wikidata attributes (#40004)               |
| `2026-05-29` | d568c8c0  | chore: bump toolchain to v4.31.0-rc1 (#39980)       |
| `2026-05-23` | 30f4950b  | feat(Algebra/ContinuedFractions): generalize det.   |

```
GET repos/leanprover-community/mathlib4/commits
    ?path=Mathlib/NumberTheory/DiophantineApproximation&since=2026-05-16T00:00:00Z
```

| date         | sha       | message (truncated)                                 |
|--------------|-----------|-----------------------------------------------------|
| `2026-05-29` | d568c8c0  | chore: bump toolchain to v4.31.0-rc1 (#39980)       |
| `2026-05-23` | 50622aa0  | feat(Tactic): automatically replace convert ...     |

### 6.2 The one substantive CF commit (#37997)

`30f4950b` (PR #37997, "feat(Algebra/ContinuedFractions): generalize determinant
formula to GenContFract"):

```
Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean   +8 / -2
Mathlib/Algebra/ContinuedFractions/Determinant.lean                  +43 / -26
```

Generalises the determinant identity from `SimpContFract` to `GenContFract`:
$A_n B_{n+1} - B_n A_{n+1} = (-1)^n \to \prod_i (-a_i)$. The simple-CF version
(which is what Mathlib's `GenContFract.of` produces for any real) is preserved
unchanged. **Not e-specific input**; the same six-step Davis decomposition
applies — generic machinery improves, but the missing step is still steps 1/2
(CF expansion of e).

### 6.3 Direct grep — CF-of-e content

```
GET search/code?q="exp 1" convergent repo:leanprover-community/mathlib4   → 0 e-specific
GET search/code?q="convergents_exp" repo:leanprover-community/mathlib4    → 0 hits
GET search/code?q="Euler continued fraction" repo:leanprover-community/mathlib4 → 0 source hits
                                                                             (only docs/references.bib + docs/overview.yaml)
GET search/code?q="of_int" ContinuedFraction repo:leanprover-community/mathlib4
   → Translations.lean, DiophantineApproximation/Basic.lean (existing generic API)
```

**Verdict**: 0 new CF-of-e content in Mathlib master between 2026-05-16 and
2026-06-01. S5d PREP's 280–480 LOC re-estimate for direct S5d.A discharge
remains valid.

## 7. Files Modified (this session)

- `research/problems/nth-root-irrational-oq-03/sessions/2026-06-01-s6-prep-pr28013-watch-tick-and-cf-of-e-rescan.md` (new — this session note)
- `research/problems/nth-root-irrational-oq-03/state.md` (iteration 7 entry + Current State header refresh)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase` / `iteration` / `lastUpdated` sync; new insight; nextSteps reordered to mark Path C empty)

No Lean files modified. No meta.json modifications. **doc-only**.

## 8. Knowledge Added

### Insights

1. **Path C has no actionable target in the current repo.** The S5d-recommended
   re-use of `irrational_liouvilleWith_two` for a sibling slug requires another
   file with a `LiouvilleWith p (specific-irrational)` axiom; empirically, the
   *only* such axiom in the whole `proofs/Proofs/` tree is the still-axiomatized
   `e_not_liouvilleWith_gt_two` in the same file (which is the *upper bound*
   target, not a lower-bound consumer). S5d's Path C is therefore exhausted
   without ever firing.
2. **PR #28013 reset its staleness clock on 2026-05-29.** The merge-from-master
   on that date rebases the PR head to `5abb7c68488` and resets `updated_at`
   to `2026-05-29T07:22:48Z`. As of 2026-06-01 the PR is `69.8h` stale — well
   below the 168h "consider scoping local re-prove" threshold recorded in S4c.
   The watch-loop cadence remains active; no promote signal.
3. **S5c-shipped infrastructure is build-stable at HEAD across the 16-day
   interval.** 3072/3072 jobs clean; 0 bearer drift; 0 new Mathlib API
   regressions detected (no repeat of the S5a discovery pattern). The
   `feedback_recovering_phase_resolves_silently_under_docker.md` pattern does
   not apply here — the file was never in RECOVERING state, but the recheck
   confirms continued stability.

### Built items

0 (doc-only).

### Risks retired

None directly. The watch-loop carries 1 standing risk (PR #28013 indefinite
stall) which is unchanged.

### Next steps

- **S6 watch (next, passive)**: re-check PR #28013 head SHA + `updated_at` at
  next claim of this slug. Current staleness 69.8h; threshold 168h; margin 98h.
- **Path A.A (S5d.A PREP, deferred multi-session)**: if PR #28013 stays open
  for another ~3-4 weeks without progress (i.e. crossing the 168h threshold
  + an additional grace period), promote `e_continued_fraction_pattern`
  formalisation from "deferred" to "scope this session". Hermite-identity
  route may be 30-50% shorter than direct-CF-via-series; either way, the
  realistic decomposition is the S5d-recorded 3-sub-task arc.
- **Mechanic cleanup follow-up**: address the 3 deprecation linter warnings
  in `eTranscendental.lean` + `ETranscendentalOQ03.lean`. 3 lines, 2 files,
  no semantic change. Out of researcher scope.

## 9. Race Notes

Pre-action race check at 2026-06-01T05:10Z:

```
gh pr list --state open --search "nth-root-irrational-oq-03 in:title"      → 0 PRs
gh pr list --head feature/researcher-1 --state open                         → 0 PRs (clean branch)
```

This PR is **doc-only** (3 files: 1 new session note + state.md edit + JSON
edit). No Lean files modified. **STATE-SYNC**: counts against the
2-STATE-SYNC-PR-per-session cap.

This iteration explicitly **declines** to attempt either S5d.A direct ACT
(infeasible single-session) or Path C template re-use (empirically no target).
The visible deliverable is the watch tick + rescan documentation; the
non-deliverable is the empirical confirmation that Path C is exhausted, which
shifts the slug's strategic posture firmly to Path B (passive watch) until
PR #28013 status changes.
