# S2 STATE-SYNC — mechanic-PR #15759 single-delta absorb + state.md bootstrap from template

**Slug**: erdos-347
**Phase (before/after)**: OBSERVE/ACT (JSON top/currentState mismatched) → COMPLETED (top-level + currentState unified)
**Iteration**: 1 → 2
**Predecessor**: mechanic PR [#15759](https://github.com/rjwalters/lean-genius/pull/15759) (2026-05-04, T-12d, gallery meta.json lineCount/theoremCount fix; did NOT touch research JSON leanFiles[0])
**Researcher**: researcher-1
**Date**: 2026-05-16
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

---

## §1. Why S2 fires (template bootstrap + mechanic single-delta absorb)

erdos-347 was in an unusual triply-inconsistent state:

1. **state.md = bare template** (Phase=NEW, Iter=1, "Begin problem exploration", Active Approach=None yet, Total attempts=0) — never updated from 2026-01-13 seeker-init.
2. **JSON populated incrementally** via batched session work (`top-level phase=OBSERVE`, `currentState.phase=ACT`, `knowledge.progressSummary "BUILD: Added 4 structural API lemmas ... Theorems 3->7"`, 8 builtItems + 8 insights, `leanFiles[0]` populated with `lineCount=126 / theoremCount=7`).
3. **Mechanic PR #15759 (2026-05-04)** fixed gallery `meta.json` `lineCount 125→195` + `theoremCount 7→13` — but did NOT propagate to research JSON `leanFiles[0]` (same-named fields drifted; remained at 126/7).

Additionally, between the JSON's `lastUpdate: 2026-03-30` and now, **6 more theorems** were added to `Erdos347Problem.lean` (lines 132-194: `countIn_mono`, `countIn_le`, `hasDensity_one_of_superset`, `erdos347_range_density_one`, `subsetSums_cofiniteImage_subset`, `erdos347_cofinite_density_via_superset` — density infrastructure + axiom consequences). `knowledge.{progressSummary,builtItems}` still reflected the 7-theorem state.

S2 absorbs all three drifts in a single doc-only PR.

---

## §2. Drift inventory (12 JSON fields + state.md full bootstrap + sessions/ bootstrap)

| # | Path | Before | After | Source-of-truth |
|---|------|--------|-------|------------------|
| 1 | `.phase` | `"OBSERVE"` | `"COMPLETED"` | gallery `status: axiomatized`, badge: axiom |
| 2 | `.currentState.phase` | `"ACT"` | `"COMPLETED"` | gallery + state.md alignment |
| 3 | `.currentState.iteration` | `1` | `2` | this S2 |
| 4 | `.currentState.focus` | `"Axiom elimination + bug fix complete"` (terse) | S2 catchup explanation w/ full bootstrap context | residual-drift description |
| 5 | `.currentState.nextAction` | `"Begin problem exploration."` (template) | `"None — slug COMPLETED-axiomatized-stable..."` | reflects actual state |
| 6 | `.currentState.attemptCounts.total` | `0` | `1` | this S2 |
| 7 | `.currentState.attemptCounts.approachesTried` | `0` | `1` | structural infrastructure + axiomatization |
| 8 | `.knowledge.progressSummary` | "BUILD: Added 4 structural API lemmas...Theorems 3->7" | Full COMPLETED-axiomatized-stable summary | actual file + gallery |
| 9 | `.knowledge.builtItems` | 8 items (theorems 1-7 + bug fix note) | 14 items (added 6 for theorems 8-13) | added density infrastructure + axiom consequences |
| 10 | `.leanFiles[0].lineCount` | `126` | `195` | `wc -l Erdos347Problem.lean = 195` + gallery `lineCount: 195` + mechanic PR #15759 |
| 11 | `.leanFiles[0].theoremCount` | `7` | `13` | `grep -c '^theorem ' = 13` + gallery `theoremCount: 13` + mechanic PR #15759 |
| 12 | `.lastUpdate` | `"2026-03-30T14:20:00.000Z"` | `"2026-05-16T19:10:00Z"` | now (~47d stale) |

state.md edits (full bootstrap from template):
- Phase NEW→COMPLETED
- Added Last Updated line
- Added 4-row Session Ledger
- Replaced "Initial exploration of the problem" focus with full COMPLETED-axiomatized-stable summary (8 defs, 1 axiom, 13 theorems detailed)
- Replaced "None yet" Active Approach with "None — slug is axiomatized-stable"
- Replaced "Begin problem exploration" Next Action with "None at this slug level. Discharging `erdos347_affirmative` would require ~1000s LOC Tao-van Doorn..."
- Total attempts 0→1

sessions/ bootstrap: created `sessions/` dir (was absent), this is the first memo.

---

## §3. Axiom-integrity calibration

Per CLAUDE.md axiom-integrity-policy:
- `erdos347_affirmative : ErdosProblem347` is a single explicit `axiom` declaration (line 78), recording the **affirmative answer** (Tao-van Doorn construction).
- 8 definitions in the file are computational definitions (`subsetSums`, `countIn` noncomputable, `HasDensity`, `IsMonotone`, `HasRatioLimit`, `IsCofiniteSubseq`, `cofiniteImage`, `ErdosProblem347`) — none are def-encoded Prop assumptions. `ErdosProblem347` is a `def : Prop := ∃ a, ...` packaging the existential statement (not an assumption itself; assumption is in the `axiom` that consumes it).
- Gallery `axiomCount: 1` + `badge: axiom` + `status: axiomatized` ✅ correct.
- Total assumption count: 1 (matches gallery).

S2 does NOT propose any gallery `status`/`badge`/`axiomCount` change — those are aligned.

---

## §4. Bearer / Lean-file stability

**No re-spot-check.** Lean file is in its post-#15759 state:
- 195 LOC, 8 defs, 1 axiom (erdos347_affirmative), 13 theorems (all proved), 0 sorries

Mathlib bearers used in proofs (carry-forward at SHA `2df2f0150c…`):
- `Finset.card_le_card`, `Finset.filter_subset_filter`, `Finset.card_filter_le`, `Finset.card_Icc` (in `countIn_mono`, `countIn_le`)
- `div_le_div_right`, `div_le_one_of_le`, `abs_sub_comm`, `abs_of_nonneg` (in `hasDensity_one_of_superset`)
- `Set.range_id`, `Function.comp_id`, `strictMono_id` (in `isCofiniteSubseq_id`, `erdos347_range_density_one`)

All Mathlib stable since 2026-03-30 JSON last-update. Carry-forward verdict: GREEN.

---

## §5. Readiness gate restatement

| Gate | Status | Notes |
|------|--------|-------|
| A. Lean file | ✅ GREEN | 195 LOC, 1 axiom, 13 theorems, 0 sorries; final since pre-#15759 |
| B. Gallery meta.json | ✅ GREEN | status=axiomatized, badge=axiom, sorries=0, axiomCount=1, theoremCount=13, lineCount=195 |
| C. Research JSON | ✅ GREEN (post-S2) | Was RED (leanFiles[0] drifted + knowledge subset stale at 7-theorem state); S2 absorbs 12-field drift |
| D. state.md | ✅ GREEN (post-S2) | Bootstrapped from template; Phase=COMPLETED, Iter=2, Session Ledger present |
| E. knowledge.md | ✅ GREEN (carry-forward) | Auto-generated stub from erdosproblems.com scrape (2026-01-13); contains LaTeX problem statement + tags; no domain edits needed |
| F. Sessions dir | ✅ GREEN (post-S2) | Bootstrapped w/ this memo |
| G. Mathlib SHA | ✅ STABLE | `2df2f0150c…` unchanged |
| H. Docker / build | N/A | Doc-only PR, no Lean changes |

---

## §6. Trap transfer

| Item | Pre-S2 status | S2 disposition |
|------|---------------|---------------|
| state.md bare template | LEFT (4+ months since seeder-init) | DISCHARGED → full bootstrap |
| sessions/ dir absent | LEFT | DISCHARGED → bootstrapped |
| JSON top-level `phase: OBSERVE` + `currentState.phase: ACT` mismatch | LEFT | DISCHARGED → both → COMPLETED |
| `leanFiles[0].lineCount: 126` (vs gallery 195) | LEFT 12d since mechanic | DISCHARGED → 195 |
| `leanFiles[0].theoremCount: 7` (vs gallery 13) | LEFT 12d since mechanic | DISCHARGED → 13 |
| `knowledge.progressSummary` "Theorems 3->7" | LEFT 47d | DISCHARGED → COMPLETED summary w/ 13 theorems |
| `knowledge.builtItems` missing items 8-13 | LEFT 47d | DISCHARGED → appended 6 items |
| `currentState.nextAction: "Begin problem exploration"` | LEFT (template) | DISCHARGED → "None — slug COMPLETED" |
| `lastUpdate: 2026-03-30` (47d stale) | LEFT | DISCHARGED → 2026-05-16 |
| `problem.md` "Problem statement not found" or similar | N/A (problem.md has LaTeX statement) | n/a |
| `knowledge.md` body | N/A (auto-generated stub OK) | LEFT |
| Discharge of `erdos347_affirmative` axiom | N/A | LEFT (~1000s LOC Tao-van Doorn = new sub-slug seeker job) |
| Tier mismatch JSON `tier: A` vs `problem.md tier: B` | N/A | LEFT (not S2 scope; possible later mechanic fix) |

---

## §7. Explicit non-actions (10 items)

S2 deliberately does NOT:
1. Touch `proofs/Proofs/Erdos347Problem.lean` (file final since pre-#15759)
2. Touch `src/data/proofs/erdos-347/meta.json` (already correct per #15759)
3. Touch `src/data/proofs/erdos-347/annotations.json`
4. Touch `problem.md` (LaTeX problem statement present and accurate)
5. Touch `knowledge.md` body (auto-generated stub; no domain edits needed)
6. Touch `proofs/lake-manifest.json` (Mathlib pin unchanged)
7. Run `lake build` / Docker (doc-only PR; never run direct `lake build` per CLAUDE.md DANGER; Docker daemon hung per host snapshot)
8. Run `pnpm build` (mechanic-pnpm-build memory: regenerates ALL research JSONs via research:enrich; would clobber my targeted edit)
9. Re-walk Mathlib bearers (SHA stable; carry-forward GREEN per §4; SHA-stable busywork)
10. Discharge the `erdos347_affirmative` axiom (~1000s of LOC Tao-van Doorn = new sub-slug `erdos-347-oq-01` seeker job, NOT this slug's STATE-SYNC scope)

---

## §8. Picker decision matrix

| Branch | Trigger | Why not chosen here |
|--------|---------|---------------------|
| Release without PR (long-stale slug) | template state.md + sessions/ absent + no activity ≥6 weeks + no single-delta + host 3-RED INFRA | NOT met: there IS a single-delta to absorb (mechanic PR #15759 fix; research JSON still drifted 12d later); leaving it = perpetual future claim-random rediscovery |
| PREP | stage paste-ready ACT skeleton | NOT applicable: slug axiomatized-stable, no next ACT planned |
| ACT | build-pending Lean edit | NOT applicable: no Lean changes needed |
| STATE-SYNC (this S2) | mechanic single-delta + template state.md bootstrap + knowledge subset rewrite | ✅ MATCH |
| 13-field rewrite (OBSERVE-predecessor variant) | predecessor OBSERVE memo with contradictory findings | NOT applicable: no OBSERVE predecessor |
| 8-field smaller-followup (sqrt2 pattern) | predecessor standalone STATE-SYNC ≤7d ago | NOT applicable: no predecessor STATE-SYNC; this is the FIRST STATE-SYNC for this slug |
| 12-field knowledge-error fix (erdos-1138 pattern) | predecessor batched ≥7d w/ JSON contradicting gallery | PARTIAL MATCH: mechanic predecessor 12d ago + JSON contradicting gallery, but additional template-bootstrap scope makes this richer than pure pattern |

This case is closest to **erdos-1138 pattern** (12-field knowledge rewrite + leanFiles fix vs gallery ground-truth) but extended w/ state.md template bootstrap + 6-builtItems append for the 6 newer theorems.

---

## §9. Honesty calibration

What this PR **is**:
- A 3-file doc-only fix bringing state.md + JSON into agreement with actual Lean file + gallery meta.json + mechanic PR #15759's intent.
- A template-bootstrap of state.md (Phase NEW → COMPLETED, Iter 1→2, Session Ledger + Focus/Next-Action populated).
- A first-memo bootstrap of `sessions/`.
- An append of 6 builtItems for theorems added since 2026-03-30 JSON last update.

What this PR is **not**:
- Not a discharge of the `erdos347_affirmative` axiom (Tao-van Doorn construction).
- Not a re-formalization or refactor of any Lean code.
- Not a gallery status/badge change.
- Not a re-build of the Lean file.
- Not a problem.md / knowledge.md / annotations.json rewrite.
- Not a tier-mismatch fix (JSON tier=A vs problem.md tier=B; out of scope).

Cost of NOT shipping: future claim-random sees template state.md ("Phase: NEW, Begin problem exploration") + drifted JSON leanFiles[0] (126/7 vs gallery 195/13), spends investigative cycles re-discovering the COMPLETED status.

---

## §10. References

- Mechanic PR (gallery fix; this S2 absorbs): [#15759](https://github.com/rjwalters/lean-genius/pull/15759) — `fix(erdos-347): correct lineCount 125→195, theoremCount 7→13` (merged 2026-05-04T16:23:02Z)
- Research substantive PRs (earlier batched): [#8386](https://github.com/rjwalters/lean-genius/pull/8386), [#8390](https://github.com/rjwalters/lean-genius/pull/8390) (Reynolds API + structural lemmas)
- Lean file: `proofs/Proofs/Erdos347Problem.lean` (195 LOC, 1 axiom `erdos347_affirmative`, 13 theorems, 0 sorries) @ Mathlib `2df2f0150c…` (v4.26.0)
- Affirmative solution provenance: ebarschkis on erdosproblems.com #347 (Tao-van Doorn construction): perturbed powers of 2 with controlled redundancy survives cofinite deletion
- Forward path: discharge `erdos347_affirmative` axiom = candidate sub-slug `erdos-347-oq-01` (not yet created — seeker job if pool wants to materialize)
