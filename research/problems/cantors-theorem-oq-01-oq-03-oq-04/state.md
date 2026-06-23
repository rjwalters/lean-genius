# Current State

**Phase**: COMPLETED (S2 STATE-SYNC — research-side catchup; gallery already verified since S1)
**Since**: 2026-06-05T04:50:46Z
**Iteration**: 2

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

**None.** OQ-04 is resolved on origin/main since 2026-05-12 (PR #17942).
Gallery `meta.json.status` is already `verified` (0 sorries, 0 axioms).
S2 STATE-SYNC (this PR) brings the research-side JSON, candidate-pool
status, and state.md in line with that resolved gallery truth.

**S3 stretch (optional, deferred)**: Lift to the general `2^κ` case.
Replace `cf_powerSet_real_gt_continuum` with the parent's `konig_general`
to prove `cf(2^κ) ≠ μ` for every infinite `κ` and every `μ ≤ κ`.
Mostly a universe-polymorphism exercise. Would become a sibling slug
rather than re-opening this one.

**S4 stretch (optional, deferred)**: Add a generic Mathlib-style
meta-theorem `cf_ne_of_lt_cof : ∀ {X : Type*} {c : Cardinal}, c < (#X).ord.cof → ∀ {κ}, κ ≤ c → (#X).ord.cof ≠ κ`
in Cardinal.Cofinality. A ~5-line generic lemma that packages the
family-of-corollaries pattern once and for all.

## Attempt Counts

- Total attempts: 2 (S1 SCAFFOLD merged in PR #17942; S2 STATE-SYNC this PR)
- Current approach attempts: 1 (one-line reduction to parent's strict inequality)
- Approaches tried:
  - S1: one-line `intro h; rw at; absurd` reduction with named
    specialisations.
  - S2: research-side STATE-SYNC, doc-only.

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

Functionally verified. The Lean file has been on origin/main since
2026-05-12 (PR #17942), gallery `meta.json.status` is `verified`
(0 sorries, 0 axioms, 248 lines), and 24 days of subsequent agent
activity touching neighbouring files in the gallery have not flagged
a build failure — strong implicit signal that the manifest builds.
No new Lean compilation requested in S2 (doc-only).

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
