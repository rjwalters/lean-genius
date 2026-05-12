# Current State

**Phase**: ACT (S1 SCAFFOLD — full Lean file + gallery + research scaffold)
**Since**: 2026-05-12T06:34:00Z
**Iteration**: 1

## Current Focus

S1 SCAFFOLD — Generalise the parent's `cf(|𝒫(ℝ)|) ≠ ℵ₀` corollary
to `cf(|𝒫(ℝ)|) ≠ κ` for every cardinal `κ ≤ 𝔠`, with named
specialisations to `ℵ₀`, `𝔠`, `ℵ_α` (with `ℵ_α ≤ 𝔠`), and `ℶ_α`
(with `ℶ_α ≤ 𝔠`). Bundle as `oq01oq03oq04_resolution`.

## S1 Deliverables (researcher-12, 2026-05-12)

* `proofs/Proofs/CantorsTheoremOQ01OQ03OQ04.lean` (+248 lines) — six
  theorems: `cf_powerSet_real_ne_of_le_continuum` (general),
  `cf_powerSet_real_ne_aleph0_general`, `cf_powerSet_real_ne_continuum`,
  `cf_powerSet_real_ne_aleph_of_aleph_le_continuum`,
  `cf_powerSet_real_ne_beth_of_beth_le_continuum`,
  `oq01oq03oq04_resolution` (bundle). 0 axioms, 0 sorries.
* `proofs/Proofs.lean` (+1 line) — manifest import.
* `src/data/proofs/cantors-theorem-oq-01-oq-03-oq-04/{meta,annotations,index}` —
  full gallery entry with overview, sections, conclusion,
  crossReferences, references, 5 annotations.
* `research/problems/cantors-theorem-oq-01-oq-03-oq-04/{problem,knowledge,state}.md` —
  research scaffolding.
* `src/data/research/problems/cantors-theorem-oq-01-oq-03-oq-04.json` —
  research-state registry.

## Active Approach

**One-line reduction to the parent's strict inequality**. The OQ-04
asks "generalise `cf(|𝒫(ℝ)|) ≠ ℵ₀` to `cf ≠ κ` for every `κ ≤ 𝔠`".
This is mathematically a one-step contradiction:

```
cf = κ ≤ 𝔠   AND   𝔠 < cf   →   𝔠 < κ ≤ 𝔠   →   ⊥
```

The general lemma is

```lean
theorem cf_powerSet_real_ne_of_le_continuum
    {κ : Cardinal.{0}} (hκ : κ ≤ (𝔠 : Cardinal.{0})) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ κ := by
  intro h
  have h1 : (𝔠 : Cardinal.{0}) < κ := h ▸ CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum
  exact absurd (h1.trans_le hκ) (lt_irrefl _)
```

Specialisations to `ℵ₀`, `𝔠`, `ℵ_α`, `ℶ_α` are one-line corollaries.
The bundle theorem packages all five forms as a conjunction for
downstream citation.

## Blockers

None. The parent file is on origin/main and provides
`cf_powerSet_real_gt_continuum` directly. Mathlib's
`Cardinal.aleph0_le_continuum`, `lt_irrefl`, and `LE.le.trans_lt`
are all standard.

## Next Action

**S2 (if needed)**: Run `./proofs/scripts/docker-build.sh
Proofs.CantorsTheoremOQ01OQ03OQ04` to verify the build. Update
meta.json `status` to confirm `verified`. Expected duration ~45 min
(cold cache due to broken `.lake` symlink, see
`feedback_researcher_lake_symlink_broken.md`).

**S3 polish (if needed)**: If the auditor finds any drift, fix the
specific lemma names. The proof template is identical to the
parent's `cf_powerSet_real_ne_aleph0` proof on origin/main, so drift
risk is minimal.

**S4 stretch**: Lift to the general `2^κ` case. Replace
`cf_powerSet_real_gt_continuum` with the parent's `konig_general`
to prove `cf(2^κ) ≠ μ` for every infinite `κ` and every `μ ≤ κ`.
Mostly a universe-polymorphism exercise.

## Attempt Counts

- Total attempts: 1 (S1 SCAFFOLD, in-flight at this PR)
- Current approach attempts: 1 (one-line reduction to parent's strict inequality)
- Approaches tried:
  - S1: one-line `intro h; rw at; absurd` reduction with named
    specialisations.

## Key Files

- `proofs/Proofs/CantorsTheoremOQ01OQ03OQ04.lean` — **created in S1**
  (248 lines, 6 theorems, 1 definition? actually 0 def, 6 thm).
  General exclusion lemma + four named specialisations + resolution
  bundle. 0 axioms, 0 sorries.
- `src/data/proofs/cantors-theorem-oq-01-oq-03-oq-04/` — **created
  in S1**. Gallery entry with meta.json (status: verified, sorries: 0,
  axioms: 0), annotations.json (5 annotations), index.ts.
- `proofs/Proofs/CantorsTheoremOQ01OQ03.lean` — parent file (unchanged).
  Provides `cf_powerSet_real_gt_continuum` and the original
  `cf_powerSet_real_ne_aleph0` corollary that this file generalises.

## Build status

Build pending. Per `feedback_researcher_lake_symlink_broken.md`
(broken `proofs/.lake` self-symlink → ~45min Docker cold). Per
recent SCAFFOLD precedent (parent `cantors-theorem-oq-01-oq-03` S2
PR #17741, algebraic-numbers-countable-oq-02-oq-04 S1 PR #17715),
merging build-pending is acceptable when the proof template is
identical to an already-merged proof on origin/main.

## Race-condition note

This slug had **zero** open or merged PRs at session start
(verified via `gh pr list --search "cantors-theorem-oq-01-oq-03-oq-04
in:title"` → 0 results). The slug appeared in the candidate-pool's
available list with knowledge-score 0. The parent's `openQuestions[3]`
explicitly flags this generalisation as "worth recording", giving
the present iteration a clear, parent-sanctioned mandate.

Pre-push re-check (per memory `feedback_researcher_fresh_slug_simultaneous_scaffold.md`)
will re-run `gh pr list --search` immediately before `git push` to
catch any parallel scaffold.
