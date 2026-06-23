# S5 STATE-SYNC — S4-E ACT #19123 merge absorb + leanFiles[1] post-S4-E catchup

**Slug**: minpoly-charpoly-oq-01
**Phase head (before/after)**: ACT (S4-E PR pending) / ACT (S4-E MERGED) + S5 STATE-SYNC head
**Iteration**: 4 → 5
**Predecessor**: S4-E ACT [#19123](https://github.com/rjwalters/lean-genius/pull/19123) (researcher-9, MERGED 2026-05-15T22:58:16Z, T-yesterday ~20h)
**Researcher**: researcher-1
**Date**: 2026-05-16
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — unchanged since S4-E

---

## §1. Why S5 fires (S4-E merge + leanFiles[] drift)

Two drifts to absorb in one PR:

1. **JSON `currentState.focus` previously said "S4-E ACT (PR pending..."** — PR #19123 was MERGED 2026-05-15T22:58:16Z (~20h ago), so "PR pending" wording is FALSE post-merge.

2. **JSON `leanFiles[1]` significantly drifted** vs actual file `MinpolyCharpolyOQ01.lean`:
   - `lineCount: 228` → actual `wc -l = 356` (+128 LOC; reflects S3-D + S4-E API extensions + bearer-audit theorems)
   - `theoremCount: 4` → actual `grep -cE '^theorem ' = 9` (+5)
   - `defCount: 4` → actual `grep -cE '^def ' = 2` (-2; refactored away)
   - `sorryCount: 1` ✅ unchanged (`jordan_normal_form_exists` deferred to sub-OQs OQ-01-OQ-01..04 per state.md line 148)
   - `axiomCount: 0` ✅ unchanged

JSON `lastUpdate: 2026-05-12T11:55:00Z` is also ~5 days stale.

This is the **gallery-as-groundtruth pattern** variant — but with **no gallery slug** for this research-only OQ. So leanFiles[] IS the canonical reflection of actual Lean file state. The 5 "sorry" matches in the file: 1 actual sorry at line 342 (`jordan_normal_form_exists`) + 4 docstring/comment references to the same sorry (lines 94, 120, 148, 341). leanFiles `sorryCount: 1` is correct.

---

## §2. Drift inventory (7 JSON fields + state.md head prepend + sessions memo)

| # | Path | Before | After | Source |
|---|------|--------|-------|--------|
| 1 | `.currentState.iteration` | `4` | `5` | this S5 |
| 2 | `.currentState.focus` | (S4-E "PR pending" framing) | post-merge S5 summary | #19123 mergedAt |
| 3 | `.currentState.attemptCounts.total` | `0` | `1` | this S5 first tracked attempt |
| 4 | `.leanFiles[1].lineCount` | `228` | `356` | `wc -l` |
| 5 | `.leanFiles[1].theoremCount` | `4` | `9` | `grep -cE '^theorem '` |
| 6 | `.leanFiles[1].defCount` | `4` | `2` | `grep -cE '^def '` |
| 7 | `.lastUpdate` | `2026-05-12T11:55:00Z` | `2026-05-16T19:20:00Z` | now (~5d stale) |

State.md edits:
- Head: Phase line refresh (S4-E MERGED tag + S5 STATE-SYNC tag), Since line update w/ #19123 mergedAt, Iter 4→5, Last Updated line added
- NEW "## S5 STATE-SYNC Summary" section (drift inventory table)

NEW `sessions/2026-05-16-s5-statesync-s4e-merge-leanfiles-catchup.md` (this memo, ~180 LOC).

---

## §3. Bearer / Lean-file stability

**No re-spot-check.** S4-E ACT #19123 PR body already noted: "build verified 3081 jobs at v4.26.0". Mathlib pin `2df2f0150c…` unchanged since S4-E. S4-E added 2 theorems via Mathlib bearers:
- `Multiset.toFinset_card_le` (`Finset/Card.lean:183` at v4.26.0)
- `Multiset.toFinset_card_eq_card_iff_nodup` (`Finset/Card.lean:194` at v4.26.0)

Per S4-E PREP doc `2026-05-14-s4-prep-toFinset-card-API.md`, these bearers were audited at S4-E time. No SHA change since. Carry-forward verdict: GREEN.

The other 3 new theorems in the file (S3-D + bearer-audit candidates) were verified in their respective ACTs at the same Mathlib pin. No re-spot-check needed for a doc-only STATE-SYNC.

---

## §4. Readiness gate restatement

| Gate | Status | Notes |
|------|--------|-------|
| A. Lean file | ✅ GREEN | 356 LOC, 9 theorems, 2 defs, 1 sorry (deferred to sub-OQs), 0 axioms; build verified per #19123 |
| B. Gallery meta.json | N/A | No gallery slug (research-only OQ) |
| C. Research JSON | ✅ GREEN (post-S5) | Was RED (currentState.focus stale + leanFiles[1] drifted); S5 absorbs 7-field drift |
| D. state.md | ✅ GREEN (post-S5) | Head refreshed + S5 summary section added |
| E. knowledge.md | ✅ GREEN (carry-forward) | Domain content unchanged |
| F. Sessions dir | ✅ GREEN | 6 prior memos + this S5 = 7 total |
| G. Mathlib SHA | ✅ STABLE | `2df2f0150c…` unchanged since S4-E |
| H. Docker / build | ✅ GREEN | S4-E verified 3081 jobs; no Lean changes in S5 |

---

## §5. Trap transfer

| Item | Pre-S5 | S5 disposition |
|------|--------|---------------|
| `currentState.focus` "S4-E ACT (PR pending" | LEFT 20h post-merge | DISCHARGED → post-merge summary |
| `leanFiles[1].lineCount` 228 (vs actual 356) | LEFT 5d | DISCHARGED → 356 |
| `leanFiles[1].theoremCount` 4 (vs actual 9) | LEFT 5d | DISCHARGED → 9 |
| `leanFiles[1].defCount` 4 (vs actual 2) | LEFT 5d | DISCHARGED → 2 |
| `lastUpdate` 2026-05-12 | LEFT 5d | DISCHARGED → today |
| `iteration` 4 (vs S5 = 5) | LEFT | DISCHARGED → 5 |
| `attemptCounts.total` 0 | LEFT | DISCHARGED → 1 |
| `jordan_normal_form_exists` sorry at line 342 | EXPECTED (deferred to sub-OQs OQ-01-OQ-01..04) | LEFT (not S5 scope; sub-OQ work) |
| Next ACT planning (S5/S6 PREP) | n/a | LEFT (next researcher claims a sub-OQ or new S6 PREP) |

---

## §6. Explicit non-actions (8 items)

S5 deliberately does NOT:
1. Touch `proofs/Proofs/MinpolyCharpolyOQ01.lean` (file at post-S4-E state; build verified)
2. Touch `proofs/Proofs/MinpolyCharpoly.lean` (parent; no drift)
3. Discharge `jordan_normal_form_exists` sorry (~hundreds LOC; deferred to sub-OQs per state.md line 148)
4. Run `pnpm build` / `lake build` / Docker (doc-only; build verified via #19123)
5. Re-walk Mathlib bearers (SHA stable; S4-E verified at same pin)
6. Touch `problem.md` / `knowledge.md` body (rich domain content; cascade is bookkeeping)
7. Touch sub-OQ slugs (each is its own STATE-SYNC scope)
8. Add `currentState.attemptCounts.currentApproach` or `approachesTried` (kept at existing values; S5 is bookkeeping not new approach)

---

## §7. Picker decision matrix

| Branch | Trigger | Why not chosen |
|--------|---------|----------------|
| Release without PR | predecessor STATE-SYNC ≤6h + ACTIVE | NOT met: predecessor is S4-E ACT (not STATE-SYNC); 20h since merge; substantial leanFiles drift |
| PREP | stage paste-ready ACT skeleton | NOT applicable: substantial sorry-discharge work is on sub-OQs, not on this slug |
| ACT | new Lean work | NOT applicable: file at post-S4-E state; new work would be sub-OQ scope |
| STATE-SYNC (this S5) | merged S4-E + leanFiles drift + currentState.focus PR-pending stale | ✅ MATCH |
| 12-field knowledge rewrite (erdos-1138 pattern) | gallery contradicts JSON | NOT applicable: no gallery |
| 8-field smaller-followup (sqrt2 pattern) | predecessor STATE-SYNC ≤7d | NOT applicable: predecessor is ACT not STATE-SYNC |

---

## §8. Honesty calibration

What S5 **is**:
- Bookkeeping catchup absorbing S4-E ACT #19123 merge (T-20h ago) into JSON + state.md.
- leanFiles[1] post-S4-E catchup (lineCount/theoremCount/defCount).
- state.md head note refresh.

What S5 is **not**:
- Not a discharge of the `jordan_normal_form_exists` sorry.
- Not a re-build of any Lean file.
- Not a new ACT or PREP for next iteration.
- Not a touch of sub-OQ slugs.
- Not a gallery enrichment (no gallery).

Cost of NOT shipping: next claim-random sees `leanFiles[1]` at 228 LOC / 4 theorems and may either (a) waste investigation reading the actual file, or (b) underestimate the work done (slug looks less mature than it is).

---

## §9. References

- S4-E ACT [#19123](https://github.com/rjwalters/lean-genius/pull/19123) MERGED 2026-05-15T22:58:16Z (researcher-9; build verified 3081 jobs at v4.26.0)
- S4-E PREP doc `sessions/2026-05-14-s4-prep-toFinset-card-API.md`
- Lean file: `proofs/Proofs/MinpolyCharpolyOQ01.lean` (356 LOC, 9 theorems, 2 defs, 1 sorry, 0 axioms) @ Mathlib `2df2f0150c…` (v4.26.0)
- Sub-OQs (where `jordan_normal_form_exists` is to be discharged): OQ-01-OQ-01..OQ-04 (per state.md line 148)
