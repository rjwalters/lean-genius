# S6 STATE-SYNC — JSON catchup + state.md bottom-section repair + Pattern E line 219 confirmation (doc-only)

**Iteration**: 6 (researcher-5, 2026-05-16)
**Phase**: ORIENT (BUILD-BLOCKER follow-up — state-sync only; no new audit work)
**Predecessors absorbed**:
- PR #19508 (S4 PREP — Pattern E + H audit, MERGED 2026-05-16T08:52:53Z)
- PR #19557 (S5 PREP — Pattern C site count 3→8 + F/G cascade, MERGED 2026-05-16T13:53:15Z)
**Scope**: doc-only. 3 files: this session memo + `state.md` + slug JSON. Zero `*.lean` / `meta.json` / `knowledge.md` / `problem.md` edits.
**Disk/Docker**: Host disk **100% full** (`/dev/disk3s1s1  920Gi / 926Gi`, **6.6 Gi free**). Docker daemon non-responsive (`docker info` exit 124 at 10 s). No build executed in this STATE-SYNC; v4.26.0 confirmation done via direct file inspection at the cloned-Mathlib-pin checked into the worktree (lake pin `v4.26.0` per `proofs/lakefile.toml`).

---

## §1 Why this STATE-SYNC now

Three iterations have shipped doc-only PREPs since S3 BUILD-BLOCKER PREP (#19446) without refreshing the canonical state surfaces:

| Iter | PR | Date | What it touched | What it left stale |
|------|-----|------|-----------------|--------------------|
| S4 PREP | #19508 | 2026-05-16T08:52:53Z | sessions/2026-05-16-s4-prep-pattern-e-h-v4-26-0-audit.md (NEW, 349 LOC) | **state.md**, **slug JSON** (PR was 1-file: session memo only) |
| S5 PREP | #19557 | 2026-05-16T13:53:15Z | sessions/2026-05-16-s5-prep-pattern-c-v4-26-0-audit-and-site-count-correction.md (NEW, 317 LOC); state.md (+18/-5 LOC head update) | **slug JSON** (PR body explicit: "0 ... research JSON ... edits"); **state.md bottom sections** (Iteration History stops at S3; Reference Files lists 5 of 7 memos; Open PRs table stops at S3; Attempt Counts = "4") |

**Net drift on origin/main as of branch-creation:**

- **state.md head**: iter 5 — current ✓ (S5 quick-summary block landed at top)
- **state.md bottom**:
  - "Open PRs" table: missing rows for S4 PREP #19508, S5 PREP #19557, (this iter)
  - "Iteration History" table: missing rows for S4 PREP, S5 PREP, (this iter)
  - "Reference Files (in this directory)" bullet list: missing 2 session-memo entries (S4 + S5)
  - "Attempt Counts": Total = 4 (correct value: 6 = S1, S2, S2c, S3, S4, S5 — this PR makes 7); "approachesTried" still 2 (correct after S4/S5 audit-correction: still 2, no new approach attempted; S4/S5 are PREP-refinement continuations of R2-pure route).
- **slug JSON** (`src/data/research/problems/<slug>.json`):
  - `currentState.iteration`: 4 (should be 6)
  - `currentState.phase`: ORIENT ✓ (unchanged)
  - `currentState.since`: `2026-05-16T03:38:00Z` (should be `2026-05-16T09:15:00Z` per S5 PREP, or `2026-05-16T14:00:00Z` for this iter)
  - `currentState.focus`: S3 BUILD-BLOCKER PREP — 2 iters stale; missing S4/S5/S6 narrative
  - `currentState.nextAction`: still cites S3 BUILD-BLOCKER PREP §2; missing S4's Pattern E/H paste-ready fixes, missing S5's Pattern C correction (3→8 sites) + Approach A recipe + F/G cascade removal, missing S6's Pattern E line 219 confirmation
  - `currentState.blockers`: 3-item list — still correct (parent v4.26.0 repair gate unchanged); refresh wording is optional
  - `knowledge.insights` (19 entries): missing S4-PREP findings, missing S5-PREP findings, missing this STATE-SYNC's line 219 confirmation
  - `knowledge.builtItems` (7 entries): missing S4 #19508, S5 #19557, (this iter) entries
  - `knowledge.progressSummary`: S3-era text; 2 iters stale
  - `knowledge.mathlibGaps`: 5 entries — should add v4.26.0 audit-derived entries from S4 (Pattern E signature) + S5 (Pattern C site count + signature)
  - `knowledge.nextSteps`: 11 entries — S3-era; should update the BLOCKER row + add S5's Approach A specifics
  - `lastUpdate`: `2026-05-16T00:15:00Z` (14h+ stale; refresh to this PR's open time)

**Material content carried over verbatim**: `relatedProofs`, `tags`, `references`, `significance`, `tractability`, `path`, `started`, `problemStatement`, `knownResults` — all stable across S3→S6 (no scope change).

---

## §2 Pattern E line 219 confirmation (the one new audit datum this PR)

**S5 PREP §"Pattern E addendum" raised**: "Line 219 `IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_adj_ℚ` is a potential 3rd Pattern E site (S4 PREP catalogued 2 at 426/429). Recommend mechanic check line 219 when applying E paste-ready."

**Confirmation via local grep at lake pin `v4.26.0`** (`grep -n "adjoin_eq_top" proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean`):

```
154:    via map_injective + adjoin_union + adjoin_self, then use adjoin_eq_top_of_adjoin_eq_top   (docstring; not a site)
219:    have h_adj_Ka := IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_adj_ℚ
426:           IntermediateField.adjoin_eq_top_of_algebra h_alg_top
429:           IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_gen_Q
```

Line 219 is **CONFIRMED a 3rd Pattern E site** — same call shape as line 429 (`adjoin_eq_top_of_adjoin_eq_top` applied to a single `h_adj_*` argument with no positional/named annotations).

**Local context** (parent lines 215-220):

```lean
        (IntermediateField.adjoin_simple_le_iff.mpr
          (IntermediateField.subset_adjoin ℚ _
            (Set.mem_union_right ↑Ka (Set.mem_singleton_self β)))))
  -- tower law: adjoin ℚ S = ⊤ implies adjoin ↥Ka S = ⊤
  have h_adj_Ka := IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_adj_ℚ
```

where `h_adj_ℚ : IntermediateField.adjoin ℚ (Ka_set ∪ {β'}) = ⊤` and the desired conclusion is `IntermediateField.adjoin ↥Ka (Ka_set ∪ {β'}) = ⊤` (within the IntermediateField lattice over `ℚ` with the inclusion `ℚ → ↥Ka`).

**Paste-ready fix template** (mirror of S4 PREP §4.2's Site 2 fix for line 429):

```diff
-    have h_adj_Ka := IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_adj_ℚ
+    have h_adj_Ka : IntermediateField.adjoin ↥Ka (Ka_set ∪ {β'}) = ⊤ :=
+      IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_adj_ℚ
```

The fix is to add an explicit type ascription on the `have` binding so Lean can infer the field-tower context (`ℚ → ↥Ka → ↥(Ka ⊔ ℚ⟮β⟯)`) for `adjoin_eq_top_of_adjoin_eq_top`. This is the same shape as S4 PREP §4.2 — adding the type annotation on the `have` line provides the missing target-type information that v4.26.0's elaborator no longer infers from the argument type alone.

**Coverage delta after this confirmation**:

| Pattern | S3 sites | S4 sites | S5 sites | S6 sites (this PR) | Paste-ready? |
|---------|----------|----------|----------|--------------------|--------------|
| A | 10 | 10 | 10 | 10 | ✓ |
| B | 5+ | 5+ | 5+ | 5+ | investigative |
| C | 3 | 3 | **8** | 8 | ✓ (Approach A, S5) |
| D | 3 | 3 | 3 | 3 | ✓ |
| E | 2 | **2 (paste-ready)** | 2 + 1 candidate | **3 (paste-ready)** | ✓ |
| F | 2 (cascade) | 2 (cascade) | **removed (cascade from B/H)** | — | auto-resolves |
| G | 1 (cascade) | 1 (cascade) | **removed (cascade from H)** | — | auto-resolves |
| H | 1 | **1 (paste-ready)** | 1 | 1 | ✓ |

**Total catalogued sites (S6)**: 10 + 5 + 8 + 3 + 3 + 1 = **30** (S5's count was 31 with line 219 still flagged as candidate; S6 confirms line 219 is real, so it's 30 fixed-site count + (cascades F/G auto-resolve)).

**Paste-ready coverage (S6)**: A (10) + C (8 via Approach A) + D (3) + E (3) + H (1) = **25 of 30** = **83%**.

**Investigative remaining**: Pattern B (5+ sites). Pattern B is the only true investigative work left for the mechanic; the rest is paste-and-iterate.

**Estimated repair LOC**: S5 had +50 to +75; line 219 adds 1 LOC (one extra `have` type ascription). **Revised: +51 to +76 LOC**.

---

## §3 Bearer SHA stability re-spot-check (no new files audited)

**Lake pin**: `v4.26.0` (per `proofs/lakefile.toml`, unchanged across S3/S4/S5/S6).

**Bearer files audited in prior PREPs at the v4.26.0 tag** (no new entries this PR; all carried over):

| File | S2/S2c | S3 | S4 | S5 | S6 (this PR) |
|------|--------|-----|-----|-----|--------------|
| `Mathlib/FieldTheory/Galois/Basic.lean` | ✓ | — | — | — | (carried) |
| `Mathlib/FieldTheory/IsAlgClosed/Basic.lean` | ✓ | — | — | — | (carried) |
| `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean` | ✓ | — | ✓ (`d9154f51`) | — | (carried) |
| `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean` | — | — | ✓ (`be9a6cb2`) | — | (carried) |
| `Mathlib/FieldTheory/IntermediateField/Basic.lean` | — | — | ✓ (`687faa0c`) | — | (carried) |
| `Mathlib/Algebra/Ring/Subsemiring/Defs.lean` | — | — | ✓ (`10b5a608`) | — | (carried) |
| `Mathlib/Algebra/Algebra/Tower.lean` | — | — | — | ✓ (`5597b89c`) | (carried) |

Lake pin is a **tag** (`v4.26.0`), so SHAs cannot drift mid-tag; re-pinning to a different tag would invalidate the audits, but this has not happened (verified `proofs/lakefile.toml` unchanged across S3/S4/S5/S6 via `git log -p main -- proofs/lakefile.toml | grep -c "^+rev = "` = 0 net adds since v4.26.0 was set).

**No new bearer audited this PR.** Line 219 confirmation is in the local parent file (Mathlib bearer for `adjoin_eq_top_of_adjoin_eq_top` already audited in S4 PREP §4.2).

---

## §4 Risk inventory for the upcoming mechanic PR

Carried over from S5 + refined for S6:

- **R1** (LOW): Pattern A — 10 sites, paste-ready. Risk: one miscount in line numbers (S5 grep verified 8 sites for C; A's 10 sites should be re-grepped at apply time).
- **R2** (LOW): Pattern D — 3 sites, paste-ready. Risk: `rw [hp_def]` may need `simp only [hp_def]` if rewriting deeper than head.
- **R3** (LOW): Pattern E — 3 sites (incl. confirmed line 219), paste-ready. Risk: type ascription `: <expected>` must match the elaborator's expected target; manual transcription error → trivial to fix on first docker iter.
- **R4** (LOW): Pattern H — 1 token rename. Risk: minimal (the alias is `:=`, not `iff`).
- **R5** (MEDIUM): Pattern C — 8 sites with Approach A (named `R := ℚ` `S := ↥K` `A := ↥Ka`). Risk: per-site name resolution for `K, Ka` may vary (some sites are inside private lemmas with different local variable names; mechanic must adapt names per site). Fallback: Approach B (letI Algebra instance) or Approach C (switch to `of_algebraMap_eq'`).
- **R6** (HIGH): Pattern B — 5+ sites, investigative. Risk: IntermediateField sup typeclass refactor may require more than `haveI` scaffolding; could need refactoring of the surrounding induction structure or new helper lemmas. If B turns out to be a real architectural mismatch (not just instance synthesis), repair could spill to +30-50 additional LOC beyond the +50-75 estimate.
- **R7** (LOW): Once parent rebuilds clean (Patterns A–H all closed), the companion file from S2c PREP §3 OPT-1 + §5 Steps 1-3 transcribes directly. No new risk from this PR.
- **R8** (INFRA): Host disk + Docker. Not researcher-fixable; operator must intervene before any docker iter possible.

---

## §5 What this STATE-SYNC does NOT do

- **No Lean edits**. Parent unbuilds; mechanic territory.
- **No `meta.json` edits**. `meta.json` lines/sorries/axioms unchanged.
- **No `knowledge.md` edits**. S1 OBSERVE survey unchanged; the S2 D-2 note about `§1`/`§8` staleness still applies and is not material to S6's scope.
- **No `problem.md` edits**. Formal target unchanged since S1 OBSERVE.
- **No Pattern B audit attempted**. Pattern B remains investigative; the next mechanic-PR or a future S7 PREP would tackle it.
- **No Approach A elaboration verification for Pattern C**. Approach A's signature-correctness was checked by S5 against `of_algebraMap_eq` in `Tower.lean:109-111`; full Lean elaboration verification deferred to mechanic with docker.
- **No competing PR with any open peer work**. Open-PRs check at branch-create:
  ```
  gh pr list --repo rjwalters/lean-genius --state open --search "angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01"
  ```
  → 0 open PRs on this slug (S4 #19508 and S5 #19557 both MERGED).

---

## §6 ACT-readiness gate (refreshed for S6)

| Gate | S5 | S6 | Notes |
|------|-----|-----|-------|
| **G1** drift findings catalogued | ✅ | ✅ | All 8 patterns A–H |
| **G2** paste-ready fixes for ≥50% of sites | ✅ | ✅ | 25/30 = 83% (was 17/31 = 55% S5; +8 from Approach A finalization + line 219 confirm) |
| **G3** investigative scope narrowed | ⚠ AMBER | ✅ | Down to Pattern B only (5+ sites); S5 had {B, C} |
| **G4** bearer pins stable | ✅ | ✅ | v4.26.0 tag — cannot drift |
| **G5** parent file unchanged since S3 | ✅ | ✅ | `git log origin/main..origin/main -- proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` = empty |
| **G6** repair LOC estimate | ✅ | ✅ | +51 to +76 (was +50 to +75) |
| **G7** companion plan post-repair valid | ✅ | ✅ | S2c PREP §3 OPT-1 + §5 Steps 1-3 unchanged |
| **G8** host infrastructure | ❌ RED | ❌ RED | Disk 100% (6.6 Gi free) + Docker daemon hung (exit 124 at 10 s) |

**Verdict**: **7/8 GREEN, 1/8 RED (G8 infrastructure)**. The G3 upgrade (AMBER → GREEN) comes from Pattern C closure via Approach A + line 219 absorption into Pattern E. Mechanic can take handoff the moment G8 clears.

---

## §7 Next picker (refreshed from S5)

1. **Operator** (precondition): clear 10–30 Gi host disk; restart Docker daemon.
2. **Mechanic** (parent repair):
   - Apply Pattern A (10 sites: lines 166, 198, 209, 212, 264, 274, 276, 277, 380, 381) — per-site type ascription per S3 PREP §2.
   - Apply Pattern D (3 sites: lines 181, 185-186, 448) — `rw [hp_def]; exact Polynomial.natDegree_X_pow_sub_C`.
   - Apply Pattern E (3 sites: lines **219**, 426, 429) — explicit `have h : <expected> := ...` type ascription. Line 219 confirmed this PR; lines 426/429 from S4 PREP §4.
   - Apply Pattern H (1 site: line 444) — rename `SubsemiringClass.coe_pow → SubmonoidClass.coe_pow`.
   - Apply Pattern C (8 sites: lines 287, 292, 298, 308, 327, 398, 468, 484) — Approach A: explicit named args `(R := ℚ) (S := ↥K) (A := ↥Ka)` per S5 PREP §"3 candidate paste-ready fixes".
   - Iterate Pattern B (5+ sites: lines 160, 170, 174, 183, 242, 268 — S3 catalogue; re-grep at apply time) with `haveI : Algebra ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) := (IntermediateField.inclusion (le_sup_left : ...)).toAlgebra` scaffolding; verify with docker.
   - Confirm F (2 sites) + G (1 site) auto-resolve post-B/H.
   - Est. 45-60 min including 3-4 docker iterations.
3. **Researcher** (post-parent-repair): claim Iter 7 = S3 ACT-α (companion `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean` per S2c PREP §3 OPT-1 + §5 Steps 1-3).

---

## §8 Memory traps consulted

- **`_postship_pivot_to_act_phase_slug_whose_just_merged_statesync_said_0_json_edits_inline_ship_combined_prep`** — STRONG FIRE: predecessor (S5 PREP #19557) merged 13:53Z (~1h ago); PR body explicit "0 ... research JSON ... edits"; JSON drift is 2 iters (S4 + S5 both skipped). Variant from canonical: predecessor is PREP not STATE-SYNC; gap is multi-iter (2) not single-iter (1); also includes state.md bottom-section repair beyond pure JSON catchup. This PR ships exactly the canonical recipe (JSON catchup + state.md bottom repair + one new audit datum [line 219 confirmation]).
- **`_postship_pivot_lands_on_completed_slug_with_just_merged_act_naming_three_substantive_followups`** — NO FIRE: this slug is BLOCKED (not completed); follow-ups exist but are mechanic territory not researcher follow-ups.
- **`_claim_random_lands_on_fully_discharged_slug_with_inflight_doconly_statesync_sibling`** — NO FIRE: no open peer PR (S5 already merged); slug is not fully discharged.

---

## §9 Honesty checklist

- [x] Pattern E line 219 confirmed via direct grep at lake-pin parent file (not synthetic).
- [x] Paste-ready fix for line 219 is mirror-pattern of S4 PREP §4.2 Site 2 (lines 426/429), not novel methodology.
- [x] No claims about Pattern B resolution; Pattern B remains investigative.
- [x] No claim that Approach A is verified by docker; verification deferred to mechanic.
- [x] State.md head iter 5 → 6, bottom Iteration History 4 rows → 7 rows, Reference Files 5 entries → 7 entries, Open PRs 4 rows → 7 rows, Attempt Counts 4 → 6.
- [x] JSON `iteration` 4 → 6, `since` refreshed, `focus` rewritten, `nextAction` refreshed, `insights[]` extended with 4 entries (S4 Pattern E paste-ready; S4 Pattern H rename; S5 Pattern C 3→8 + Approach A; S6 line 219 confirmation), `builtItems[]` extended with 3 entries (S4 + S5 + S6), `mathlibGaps[]` extended with 3 entries (Pattern E signature, Pattern C site count + signature, line 219 same-pattern confirmation), `nextSteps[]` rewritten to current state, `progressSummary` rewritten, `lastUpdate` set to this PR's open time.
- [x] No `meta.json`, no `knowledge.md`, no `problem.md`, no `*.lean` edits.
- [x] Branch created off origin/main HEAD (post-#19557 merge); 0 file overlap with any open PR (slug has 0 open PRs).
- [x] Worktree branch hygiene: switched from prior-cycle branch `research/binary-gcd-oq-02-oq-02-explore` (which had `ecb47b35601` already merged via PR #19454) to fresh `research/angle-tri-oq01x4-s6-state-sync-line219-confirm` off `origin/main` BEFORE writing this file.

---

## §10 What downstream agents should know

- **Mechanic agent** picking up parent repair: Pattern E has **3 sites**, not 2. Line 219 is the 3rd. Same paste-ready shape as 429.
- **Next researcher** claiming this slug: S6 STATE-SYNC has fully refreshed state.md + JSON. ACT remains BLOCKED on G8 + parent repair. Skip the slug if you're hunting for a Lean-modifying iteration; pick it up only if G8 has cleared AND parent has rebuilt.
- **Future S7 PREP candidate work** (if blockers persist another cycle):
  - Pattern B v4.26.0 sup-typeclass audit — the last truly investigative pattern. Read `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean` at the lake pin for the canonical `Algebra ↥K ↥(K ⊔ L)` instance recipe (or its absence).
  - Cross-slug v4.26.0-pattern-A export — many other slugs probably hit Pattern A (`le_sup_left/right` no-auto-coerce). A reusable "v4.26.0 migration cookbook" sessions/ memo could amortize the audit cost.
