# Research State: buffons-needle-oq-01-oq-04

## Current State
**Phase**: ORIENT (S1 OBSERVE complete; ready for S2 ACT)
**Path**: full
**Since**: 2026-04-05T19:30:47-07:00
**Iteration**: 2
**Last Updated**: 2026-05-31T23:50:00Z (S1 OBSERVE, researcher-1)

## S1 OBSERVE Summary (2026-05-31, researcher-1)

**Mode**: OBSERVE (doc-only — populates `problem.md` (placeholder → full content), `knowledge.md` (placeholder → S1 findings), and shortlists S2 ACT candidates). No `.lean` edits.

### Deliverable

* `problem.md` — formal statement, plain-language framing, known-results table, S2 candidate shortlist (3 candidates, recommended = Approach A).
* `knowledge.md` — bearer table at Mathlib v4.26.0, S2 ACT translation lemma sketch, sibling-file overview, citations.
* `state.md` (this file) — phase OBSERVE → ORIENT, iteration 1 → 2.

### Key findings

1. **The slug's open question is structurally a corollary of the direct parent `buffons-needle-oq-01`.** `BuffonsNeedleOQ01.buffon_smooth_of_contDiff` already proves $\mathbb{E}[\text{crossings}] = 2 \cdot \operatorname{arcLength}(\gamma) / (\pi d)$ for any C¹ planar curve. Applying it to a closed C¹ parametrisation of $\partial K$ for a C¹-smooth convex body $K$ gives **Buffon's coin** in one step.
2. **The only new analytic content needed** is a 10–15 LOC lemma "for $K$ convex compact and $\ell$ a line, $|\partial K \cap \ell| \le 2$, with equality iff $\ell \cap \operatorname{int}(K) \ne \emptyset$". Mathlib v4.26.0 has no direct bearer for this; will be a hand-rolled local lemma using `Convex.segment_subset` and supporting-line API from `Mathlib.Analysis.Convex.Topology`.
3. **Estimated total LOC for S2 ACT**: 50–80 (translation lemma 10–15, parametrisation setup 15–20, application of `buffon_smooth_of_contDiff` ~5, ancillary 10–20). 0 new axioms, 0 sorries (Approach A is a structural corollary).

### Why this matters

This slug is the **most tractable of the four `conclusion.openQuestions`** of the parent `buffons-needle-oq-01`. The other three (Cauchy-Crofton random-line measure, hyperplane arrangements in ℝⁿ, Lipschitz boundary extension) all require substantial new Mathlib infrastructure; this one reuses an already-shipped 0-axiom-0-sorry bearer. Closing it advances the BuffonsNeedle chain to **5 of 11 files at the `OQ01-OQ-(01..04)` level** (currently only OQ-01, OQ-02 exist as direct children).

### Race disclosure

* **No open PRs on slug.** `gh pr list --search "buffons-needle-oq-01-oq-04 in:title" --state open` → `[]` (verified 2026-05-31T23:50Z).
* **No existing `BuffonsNeedleOQ01OQ04.lean` file.** The sibling-named `BuffonsNeedleOQ01OQ01OQ04.lean` (568 LOC) is at a DIFFERENT chain position (OQ01-OQ01-OQ04, not OQ01-OQ04). S2 ACT creates a fresh file.

### Honest-status block

Zero new mathematics; pure literature-survey + bearer-audit OBSERVE iteration. No Lean files modified. The chain status (5 axioms, 5 sorries across the 11-file BuffonsNeedle chain) is unchanged. Open question status unchanged (S2 ACT not yet run).

## Current Focus
S1 OBSERVE complete. Ready for S2 ACT (Approach A — Buffon's coin via C¹ boundary parametrisation).

## Active Approach
**Approach A** (recommended for S2 ACT): create `proofs/Proofs/BuffonsNeedleOQ01OQ04.lean` proving Buffon's coin for C¹-smooth convex bodies by reducing to `buffon_smooth_of_contDiff` (the parent's main theorem). 50–80 LOC, 0 axioms, 0 sorries.

**Alternates** (less tractable):
* (B) Strict Buffon's coin for a disk of radius $r$ — direct probability computation, ~30 LOC; less general.
* (C) Cauchy mean-width formula for general convex bodies — ~150–250 LOC; requires substantial new Mathlib infrastructure.

## Attempt Count
- Total attempts: 1 (this S1 OBSERVE)
- Current approach attempts: 0
- Approaches tried: 1 (S1 OBSERVE survey)

## Blockers
None for Approach A. The `buffon_smooth_of_contDiff` bearer is 0-axiom-0-sorry and live in `BuffonsNeedleOQ01.lean`. The translation lemma is small and uses standard Mathlib `Convex.*` API.

## Next Action
**S2 ACT (Approach A)**: create `proofs/Proofs/BuffonsNeedleOQ01OQ04.lean` with:

1. Local translation lemma: $|\partial K \cap \ell| \le 2$ for convex compact $K$ and line $\ell$, with equality iff $\ell$ cuts the interior. ~10–15 LOC.
2. Closed C¹ boundary parametrisation type / hypotheses ($\gamma : [0, p] \to \partial K$, $\gamma(0) = \gamma(p)$, $\operatorname{ContDiff} \mathbb{R}\ 1\ \gamma$, image of $\gamma$ = $\partial K$). ~15–20 LOC.
3. Main theorem: $\mathbb{E}[\text{lines cutting }K] = \operatorname{perimeter}(K) / (\pi d)$, derived from `buffon_smooth_of_contDiff` via the translation lemma. ~5 LOC.
4. Docker build verification: `./proofs/scripts/docker-build.sh Proofs.BuffonsNeedleOQ01OQ04`.

Estimated effort: 3–4 hours (a single S2 ACT session with claim TTL 90 min).

Also: create `src/data/proofs/buffons-needle-oq-01-oq-04/` gallery directory with `meta.json`, `index.ts`, `annotations.json` once the Lean file is built and verified.
