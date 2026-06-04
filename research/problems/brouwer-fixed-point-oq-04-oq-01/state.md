# Research State: brouwer-fixed-point-oq-04-oq-01

## Current State
**Phase**: ORIENT (blocked on upstream Mathlib foundations; tracking)
**Path**: track-upstream
**Since**: 2026-05-29 (S29 ORIENT first established blocker structure)
**Last Updated**: 2026-06-03 (S30 Mathlib UHC upstream survey)
**Iteration**: 2 (S29 ORIENT + S30 upstream survey; no ACT iterations to date)

## Current Focus

Tracking Mathlib upstream for the absent foundational bearers identified
by S29's 4-axiom dependency map: Kakutani's fixed point theorem, Berge's
maximum theorem. S30 (this session) confirmed:

* **Pinned v4.26.0**: still lacks upper-hemicontinuity (UHC) predicate
  API and Berge / Kakutani theorems.
* **Mathlib head-of-tree**: UHC predicate API merged 2026-01-09 (PR
  #33626); active development continues (open PRs #38601, #39116).
* **Kakutani fixed point theorem**: no Mathlib activity anywhere.

## Active Approach

**Track upstream Mathlib**. No single-session formalization is feasible
for the foundational bearers (Berge ~300–500 LOC, Kakutani ~500–1500
LOC, both Mathlib-style PRs not gallery work). The only in-file action
available is the `kakutani_product_simplex` → `kakutani_finite_dim`
consolidation (~150–300 LOC, multi-build), and S29 deemed it not
worth attempting without `kakutani_finite_dim` first being discharged
upstream.

## Lean file state (verified at S30 author time)

* `proofs/Proofs/BrouwerFixedPointOQ04OQ01.lean`: 296 LOC, **2 axioms**
  (`kakutani_product_simplex` line 220, `bestResponse_uhc` line 178),
  **0 sorries**.
* Upstream chain: `kakutani_finite_dim` (in `BrouwerFixedPointOQ04OQ03.lean:69`)
  and `kakutani_fixed_point_axiom` (in `BrouwerFixedPointOQ04.lean:170`) bring
  the total axioms-the-slug-depends-on to 4.

## Attempt Count
- Total attempts: 2 (S29 ORIENT, S30 upstream survey — both doc-only)
- Current approach attempts: 2 (track-upstream)
- Approaches tried: 1 (track-upstream)

## Blockers

1. **Mathlib pinned v4.26.0 lacks UHC API**. Resolvable by a pinned-
   Mathlib bump past PR #33626's merge commit
   `04b964fb1e93c79c62e1d7d6f584890a79c640bd` (2026-01-09). Not under
   this slug's control — needs a global gallery-side decision.

2. **Mathlib lacks Berge's maximum theorem** (UHC argmax over compact
   convex domains). Even on head-of-tree where the UHC predicate
   exists, the actual theorem is custom work. Mathlib PR #39116
   (Michael's selection theorem) is adjacent but not identical.

3. **Mathlib lacks Kakutani's fixed point theorem**. 0 PRs upstream.
   Building on top of Brouwer is a known argument but Mathlib-style
   PR territory (~500–1500 LOC), not single-session work.

## Next Action

**Re-survey Mathlib upstream every ~30 days, anchored to 2026-07-03.**
Trigger an ACT iteration on the slug only if one of:

* A Mathlib PR appears for Kakutani's fixed point theorem (any
  framing — direct on Brouwer, via Knaster-Kuratowski-Mazurkiewicz,
  or via Berge composition).
* A Mathlib upgrade in `proofs/lake-manifest.json` past 2026-01-09
  brings in the UHC predicate API (PR #33626). At that point, the
  `bestResponse_uhc` axiom becomes a non-foundational consolidation
  task and is worth a fresh ORIENT.
* Gallery-side activity touches `BrouwerFixedPointOQ04.lean`,
  `BrouwerFixedPointOQ04OQ03.lean`, or
  `BrouwerFixedPointOQ04OQ01.lean`.

**Honest scope guard** (per S29 §"Honest classification" and S30 §"Honest
scope assessment"): do NOT add further Nash / game-theory theorems
on top of the existing scaffold; that deepens scaffolding without
reducing the axiom base (cf. Axiom Integrity Policy).

## Session log

* **S29** (2026-05-29, researcher-1) — ORIENT: 4-axiom dependency map
  + "BLOCKED for single-session work" classification. PR #20972.
* **S30** (2026-06-03, researcher-1) — ORIENT: Mathlib upstream survey
  for UHC + Kakutani + Berge. Correction to S29's "Mathlib lacks UHC"
  generalization (true on pinned v4.26.0 but false on head-of-tree
  since 2026-01-09 PR #33626 merged). This PR (see session file
  `2026-06-03-s30-mathlib-uhc-upstream-survey.md`).
