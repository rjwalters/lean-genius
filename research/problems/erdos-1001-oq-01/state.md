# Current State

**Phase**: OBSERVE
**Since**: 2026-05-13 (S1)
**Iteration**: 1

## Session 1 — S1 OBSERVE (researcher-10, 2026-05-13)

**Deliverable.**  Initial survey of `erdos-1001-oq-01` "Explicit formula
for `limitValue(A, c)` outside the EST regime".  Substantive
upgrade of `problem.md` (155 → ~210 lines) and new `knowledge.md`
(~190 lines).  Phase advanced `NEW → OBSERVE`.

**Key findings.**

1. **The main goal is genuinely open in the literature.**  Outside the
   EST regime `A ≥ c/(1+c²)`, Farey approximation intervals overlap
   and the leading correction is the **Boca–Cobeli–Zaharescu (2001)
   pair-correlation density** of Farey fractions.  This produces an
   *implicit integral* characterisation, not a closed-form elementary
   function — so the OQ-01 main goal is unlikely to be fully closed at
   significance/tractability `(6, 6)`.  Revised classification
   (problem.md) to `(significance=6, tractability=4)`.

2. **Two tractable sub-goals decompose the OQ.**
   - **Sub-goal A** (`limit_at_est_boundary`): explicit formula at the
     boundary `A = c/(1+c²)`.  Closable by continuity argument +
     `tendsto_nhds_unique`; +20-40 LOC, possibly +1 axiom.
   - **Sub-goal B** (`limit_tendsto_one_as_A_infty`): saturation
     limit as `A → ∞`.  Closable by monotone+bounded tendsto + a
     measure-fill claim; +30-60 LOC, possibly +1 axiom.

3. **Mathlib has no Farey-fraction infrastructure at v4.26.0.**  Three
   `gh api search/code` queries for `Farey`, `threeDistance`,
   `FareyFraction` against pinned SHA `2df2f015` returned 0 hits in
   `Mathlib/`.  Closing the main goal (BCZ-explicit form) requires
   substantial upstream contribution: `Mathlib.NumberTheory.Farey`
   (Stern–Brocot tree, gap bound, cardinality formula, three-distance
   theorem) and downstream `Mathlib.NumberTheory.FareyPairCorrelation`
   (BCZ density).  Both flagged as **Mathlib-gap sub-questions** in
   knowledge.md.

**Net.**  +1 file (`knowledge.md`, ~190 LOC).  Substantive rewrite of
`problem.md` (formal statement, classification, theoretical setup,
three obstacles, Mathlib API map, decomposition, references).  State
update from `Phase: NEW / Iteration: 1 / Active Approach: None yet`
to `Phase: OBSERVE / Iteration: 1 / Active Approach: tendsto_nhds_unique-
based sub-goal closure`.  0 Lean files modified.  0 sorries / 0 axiom
changes.

**Race-safety note (pre-claim, 2026-05-13 ~11:17 UTC).**
`gh pr list --search "erdos-1001-oq-01 in:title" --state all` → 0 hits.
Sibling slug PRs exist (oq-02, oq-02-oq-01, oq-03) but none touch
oq-01.  Clean fresh-slug S1.

**Next action (S2).**  Sub-goal A (`limit_at_est_boundary`).  Add to
`Proofs/Erdos1001Problem.lean` (or a new companion
`Proofs/Erdos1001OQ01.lean` to avoid touching the parent):

```lean
-- Option 1: axiomatise continuity, prove boundary by left-limit
axiom limitValue_continuous_at_boundary (c : ℝ) (hc : c > 1) :
    ContinuousAt (fun A => limitValue A c) (estBoundary c)

theorem limit_at_est_boundary (c : ℝ) (hc : c > 1) :
    limitValue (estBoundary c) c = f (estBoundary c) c := by
  -- Use continuity + EST regime on a left-neighbourhood of estBoundary c
  sorry  -- ~20-30 LOC
```

Or, **Option 2** (cleaner, no continuity axiom):

```lean
axiom est_extends_to_boundary (c : ℝ) (hc : c > 1) :
    Tendsto (fun N => S N (estBoundary c) c) atTop
            (nhds (f (estBoundary c) c))

theorem limit_at_est_boundary (c : ℝ) (hc : c > 1) :
    limitValue (estBoundary c) c = f (estBoundary c) c := by
  have hboundary : estBoundary c > 0 := estBoundary_pos c (by linarith)
  exact tendsto_nhds_unique
    (limit_convergence (estBoundary c) c hboundary hc)
    (est_extends_to_boundary c hc)
```

Option 2 (3-line proof body, 1 axiom) is the preferred S2 design — it
mirrors `limit_in_est_regime` exactly.  Note the axiom is a genuine
research-level claim: extending the EST regime to its boundary requires
either a deeper analysis of EST's proof or a continuity-of-`S`-in-`A`
argument; either way the axiom captures a meaningful fact.

After S2, S3 attempts Sub-goal B (saturation).  S4+ awaits Farey
infrastructure.

## Active Approach

`tendsto_nhds_unique`-based sub-goal closure.  Each sub-goal (A: boundary,
B: saturation) becomes a 3-line proof body once an appropriate
`tendsto`-statement (axiom or theorem) is in place.  The pattern is
identical to the parent's `limit_in_est_regime` (lines 205-209).

## Blockers

- **Main goal** (`limit_outside_est_regime`): blocked by absence of
  `Mathlib.NumberTheory.Farey` infrastructure at v4.26.0.  Deferred
  to S4+ / spawn sibling OQs.
- **Sub-goal A** (S2): no blocker; needs S2 to write the boundary
  tendsto axiom or continuity bridge.
- **Sub-goal B** (S3): no blocker; needs S3 to write the saturation
  density claim.

## Next Action

**S2 (any researcher):** Sub-goal A boundary case.  See "Next action"
above for the Option 2 design.  Estimated +20-40 Lean lines in either
`Erdos1001Problem.lean` (single-file edit) or a new
`Erdos1001OQ01.lean` companion (preferred for clean separation; mirrors
the `Erdos1001OQ02.lean` pattern that already exists).  Build
verification required.

## Attempt Counts

- Total attempts: 1 (S1 survey, this session)
- Current approach attempts: 1
- Approaches tried: 1 (tendsto_nhds_unique-based sub-goal decomposition;
  the alternative direct-BCZ-formula route is noted but deferred)

## Open files

- `problem.md` — full theoretical setup: parent context, three
  obstacles (BCZ pair correlation, Farey Mathlib gap, Kesten–Sós
  axiomatisation), Mathlib API map, sub-goal decomposition,
  references to BCZ 2001 / Xiong–Zaharescu 2006 / Boca 2008.
- `knowledge.md` — S1 session note: parent file's 18-row symbol
  table, Mathlib audit at SHA `2df2f015`, three insights, two
  Mathlib-gap sub-questions, race-safety check.

## S1 Deliverable

S1 is **survey-only** (Tier-B fresh-slug S1 OBSERVE):

- 0 new theorems
- 0 new sorries
- 0 axiom changes (the parent's `erdos_szusz_turan` and `kesten_sos`
  remain the only axioms in the family)
- 0 Lean files modified

Produced:
- `problem.md` substantively rewritten (formal statement, two sub-goals,
  three obstacles, Mathlib API map, references).
- `knowledge.md` new — S1 session note with concrete API names,
  obstacle-by-obstacle resolution sketches, S2-S4 plan.
- `state.md` (this file) advancing phase NEW → OBSERVE.

S2 will touch `proofs/Proofs/Erdos1001Problem.lean` (single-file edit)
or create `proofs/Proofs/Erdos1001OQ01.lean` (companion; preferred).
