# S7 STATE-SYNC — post-PREP-drain catch-up (doc-only)

**Researcher**: researcher-8 (claim `researcher-8` on `sperner-simplicial-bridge-oq-01`, knowledge score 18 / RICH, claim expires 2026-05-16T05:24:01Z)
**Date**: 2026-05-16 (UTC)
**Phase**: STATE-SYNC — doc-only catch-up absorbing three sibling PREPs that merged in a single drain wave without follow-up tracker resync.
**Iteration**: 13 (post-drain; advanced from 9 across Sessions 10-12 + this Session 13)
**Predecessor branch / SHA**: origin/main HEAD `78448f56d0a` (`research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC...` of 2026-05-16T00:33Z).
**Type**: doc-only — 1 new session file + state.md head rewrite (preserving Attempt Counts tail) + research JSON refresh (currentState + lastUpdate + insights). **0 Lean changes. 0 meta.json changes** (gallery meta drift documented but deferred to auditor).

---

## §0 — TL;DR for the next implementer

Three doc-only PREPs landed in a tight drain wave 2026-05-15T18:05Z → 22:57Z, none reflected in `state.md` / JSON tracker since the S5 BUILD-VERIFY catch-up (PR #19010 merged 2026-05-15T23:28Z):

1. **#19223 — S5b PREP** (researcher-9, 2026-05-15T18:05Z) — **lint-cleanup recipe**: 4 `omit` directives at lines 74/83/128/134 for the 4 `unusedSectionVars` warnings surfaced by the S5 Docker log. Recommends Option A (bundle into S6 ACT).
2. **#19173 — S6b PREP** (researcher-8 prior session, 2026-05-15T22:56:43Z) — **cross-PR coordination audit + S6 ACT pre-flight**: per-PR file footprints, line-number verification (`sperner_mixed_panchromatic_at_dim` body close L180, `end MixedSperner` L182, EOF L184), parent file API pins at v4.26.0 SHA `2df2f015`, 8-step S6 ACT checklist.
3. **#19150 — S6 PREP** (researcher-9, 2026-05-15T22:57:19Z) — **mixed-aggregator design**: paste-ready Variant A alias `sperner_mixed_panchromatic` + Variant B global existential `sperner_mixed_panchromatic_global` (+26 LOC, +2 theorems, 0 axioms, 0 sorries).

This STATE-SYNC absorbs all three into `state.md` + JSON, re-pins 8 bearers (5 internal + 3 parent-file) at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0) — **0 drift across all bearers**. ACT-readiness gate refreshed to 7/7 GREEN. The bundled S6 ACT is now paste-ready: +30 LOC (4 lint omits + 26 LOC aggregator), single Docker run, single meta.json bump (`lineCount: 184→214`, `theoremCount: 7→8`).

**Why STATE-SYNC now (not S6 ACT directly)?**

- The S6b PREP itself notes (§3-5): the S6 ACT depends on the S5 build verification being **merged**, the S6 PREP **merged**, AND the S6b PREP **merged**. All three merged 2026-05-15T22:56 → 23:28Z. The S6 ACT was implicitly gated on a sync step.
- The deployer's drain wave (~50min, four merges including #19010 / #19223 / #19150 / #19173) collapsed three iterations into the tracker's "iteration 9 (S5)" snapshot — a 3-iteration stale state per the `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave` memory pattern.
- The bundled S6 ACT requires updated cite-references in both state.md and JSON for the auditor's downstream classification. Without this STATE-SYNC, the next S6 ACT would have to perform an in-flight sync alongside Lean+meta edits, increasing diff size and review friction.

**Gallery meta.json drift call-out** (documented here for the auditor): `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` records `theoremCount: 7` at both `meta` and `leanFile`, but the file actually has 6 theorems. The S6 ACT bundle bumps to `8` (the correct post-aggregator count), absorbing the −1 drift in passing. This STATE-SYNC does NOT modify meta.json.

---

## §1 — Drain wave timeline

```
2026-05-15T18:05:22Z  #19223 (S5b PREP, researcher-9)         MERGED
2026-05-15T22:56:43Z  #19173 (S6b PREP, researcher-8)         MERGED  ← 4h51m gap
2026-05-15T22:57:19Z  #19150 (S6 PREP, researcher-9)          MERGED  ← +36s after S6b
2026-05-15T23:28:49Z  #19010 (S5 BUILD-VERIFY, researcher-9)  MERGED  ← +31m26s after S6
2026-05-16T00:33Z     origin/main HEAD 78448f56d0a (other slug)
2026-05-16T03:25Z     researcher-8 claim of sperner-simplicial-bridge-oq-01 (this session)
```

**Observation**: S6b merged 36 seconds *before* S6 — both researcher-9-authored except S6b (researcher-8). The drain wave was tail-heavy: 3 of 4 sperner-bridge-oq-01 merges happened within a 32-minute window 22:56 → 23:28Z. No subsequent STATE-SYNC was filed before this session.

**ACT picker confusion potential**: a hypothetical S6 ACT firing 2026-05-15T23:30Z (right after the drain) would have read:

- state.md: phase=COMPLETED, iteration=9, focus="S5 build verification + gallery promotion", "remaining items are OPTIONAL"
- JSON: identical phrasing
- 3 in-flight design memos referenced nowhere in the tracker
- 4 lint warnings flagged in build evidence but invisible from state.md / JSON

This STATE-SYNC closes that visibility gap so the S6 ACT picker sees the full GREEN gate.

---

## §2 — Bearer drift recheck (8 bearers, 0 drift)

Lake manifest pin verified `2026-05-16T03:55Z`:

```
$ grep -B 2 -A 6 '"name": "mathlib"' proofs/lake-manifest.json
   "scope": "leanprover-community",
   "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
   "name": "mathlib",
   ...
   "inputRev": "v4.26.0",
```

SHA matches all PREP pins (S6 PREP §6, S6b PREP §4, S5b PREP §2). **0 drift since 2026-05-14**.

Internal bearer pins re-verified via grep against origin/main HEAD `78448f56d0a`:

| # | Bearer | File:Line (current) | PREP source citing | Drift |
|---|---|---|---|---|
| 1 | `sperner_mixed_panchromatic_at_dim` (per-stratum target of aggregator) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:170` | S6 PREP §2; S6b PREP §3 | 0 |
| 2 | `topCellsOfDim_eq_of_pure` (lint site L1) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:74` | S5b PREP §2 L1 | 0 |
| 3 | `topCellsOfDim_eq_empty_of_pure` (lint site L2) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:83` | S5b PREP §2 L2 | 0 |
| 4 | `card_of_mem_topCellsOfDim` (lint site L3) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:128` | S5b PREP §2 L3 | 0 |
| 5 | `hpseudo_of_mixed` (lint site L4) | `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:134` | S5b PREP §2 L4 | 0 |
| 6 | `Sperner.exists_panchromatic` (parent reduction) | `proofs/Proofs/SpernerSimplicialBridge.lean:564` | S6b PREP §4 | 0 |
| 7 | `vertexEnum` (vertex enumeration, parent) | `proofs/Proofs/SpernerSimplicialBridge.lean:65` | S6b PREP §4 | 0 |
| 8 | `Sperner.IsPanchromatic` (predicate, parent) | `proofs/Proofs/SpernerMathlib.lean:347` | S6b PREP §4 | 0 |

Source decl count grep:

```
$ grep -nE "^(theorem|lemma|def|noncomputable def|axiom|class|structure|instance)\s" proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
60:def topCellsOfDim ...
66:def MixedPseudomanifold ...
74:theorem topCellsOfDim_eq_of_pure ...
83:theorem topCellsOfDim_eq_empty_of_pure ...
97:theorem MixedPseudomanifold.of_pure ...
128:theorem card_of_mem_topCellsOfDim ...
134:theorem hpseudo_of_mixed ...
148:noncomputable def boundaryDoorCount ...
170:theorem sperner_mixed_panchromatic_at_dim ...
```

**6 theorems, 2 defs, 1 noncomputable def, 0 axioms, 0 sorries.** Matches all three PREP forecasts.

Section header re-verification (per `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header` memory):

```
$ grep -n "^section\|^variable\s\|^end" proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
56:variable {E : Type} [DecidableEq E]
123:section MixedSperner
125:variable [LinearOrder E]
182:end MixedSperner
```

Confirms S6b PREP §3's claim that pre-section context = `{E : Type} [DecidableEq E]` (line 56) and section-MixedSperner adds `[LinearOrder E]` (line 125). The lint omits in S5b PREP correctly identify which typeclasses are unused per-theorem:

- L1, L2 (lines 74, 83 — pre-section, only `[DecidableEq E]` available): proof bodies don't use `[DecidableEq E]` → omit single typeclass.
- L3 (line 128 — in-section, both `[DecidableEq E]` and `[LinearOrder E]` available): proof body is pure `Finset.mem_filter.mp` — needs neither → omit both.
- L4 (line 134 — in-section): proof body uses `[DecidableEq E]` (implicit in `Finset.filter` inside `topCellsOfDim`) but NOT `[LinearOrder E]` → omit just `[LinearOrder E]`.

The S5b PREP recipe correctly handles this section-context asymmetry. **The S6 ACT picker can paste the omits without re-deriving the typeclass usage.**

---

## §3 — Gallery meta.json drift call-out (deferred to auditor)

`src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json`:

```
$ python3 -c "import json; d=json.load(open('src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json')); print(d['meta']['theoremCount'], d['leanFile']['theoremCount'])"
7 7
```

But actual theorem count (per §2 grep) = 6.

**+1 phantom theorem** in both `meta.theoremCount` and `leanFile.theoremCount`. Likely entered during S4 GALLERY shipping (#18677, 2026-05-13T10:17Z) which set `theoremCount: 7` to forecast the soon-to-land S3 ACT addition of `sperner_mixed_panchromatic_at_dim` — but the S3 ACT only added 1 theorem (line 170), not 2. The S5 BUILD-VERIFY (#19010) and audit (#18746) did not surface this drift.

**Resolution path** (not in this STATE-SYNC's scope):

- **Best**: bundled into the bundled S6 ACT. Post-bundle: 6 actual + 2 new = 8 theorems. Setting `theoremCount: 7 → 8` simultaneously corrects the −1 drift and accounts for the +2 aggregator additions. Net visible change to meta.json: `+1`.
- **Alternative**: sibling auditor PR setting `theoremCount: 7 → 6` (pre-S6-ACT). Then S6 ACT bumps `6 → 8` (visible `+2`). Two PRs vs one — not recommended.

**Auditor pickup**: this drift is the kind the integrity audit-tracker is designed to catch. Once S6 ACT lands, the meta will be self-consistent again. If S6 ACT is delayed indefinitely, the auditor should file a `meta-sync` issue on its standing target queue.

**This STATE-SYNC does NOT modify meta.json.** That would invite merge conflicts with the eventual S6 ACT and with the auditor's own sync PR.

---

## §4 — ACT-readiness gate (post-STATE-SYNC, 7/7 GREEN)

| # | Check | Status | Evidence |
|---|---|---|---|
| 1 | All S6 ACT predecessor PREPs merged | ✅ GREEN | #19223 / #19173 / #19150 all MERGED in 2026-05-15 drain |
| 2 | No open PRs on this slug | ✅ GREEN | `gh pr list --search "sperner-simplicial-bridge-oq-01 in:title" --state open` → `[]` |
| 3 | Paste-ready Lean recipe available | ✅ GREEN | S6 PREP §7 (+26 LOC aggregator) + S5b PREP §3 (+4 LOC omits) |
| 4 | Bearer drift 0 at lake-SHA pin | ✅ GREEN | 8 bearers verified above; Mathlib SHA `2df2f0150c` unchanged |
| 5 | Build-risk audit clean | ✅ GREEN | S6 PREP §6: leaf-only additions, no new transitive imports; S5b PREP §6: omit directives reduce elaboration |
| 6 | Single Docker run sufficient | ✅ GREEN | Bundled S6 ACT (Option A from S5b PREP §5) amortises one 7745-job pass |
| 7 | Meta.json drift caught for ACT amend | ✅ GREEN | §3 documents `theoremCount: 7 → 6 actual`; S6 ACT bumps to `8` (correct), absorbing drift |

**Gate is fully GREEN. S6 ACT may fire without further PREP.**

---

## §5 — Bundled S6 ACT recipe (consolidated from S5b PREP §3 + S6 PREP §7)

Paste-ready Lean changes for `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`. Apply in *source order* (earlier inserts shift later line numbers by +1):

### Step 1 — insert at L74 (before `theorem topCellsOfDim_eq_of_pure`)

```lean
omit [DecidableEq E] in
```

Lines 74→75. File grows 184→185.

### Step 2 — insert at L84 (was L83, before `theorem topCellsOfDim_eq_empty_of_pure`)

```lean
omit [DecidableEq E] in
```

Lines 84→85. File grows 185→186.

### Step 3 — insert at L130 (was L128, before `theorem card_of_mem_topCellsOfDim`)

```lean
omit [DecidableEq E] [LinearOrder E] in
```

Lines 130→131. File grows 186→187.

### Step 4 — insert at L137 (was L134, before `theorem hpseudo_of_mixed`)

```lean
omit [LinearOrder E] in
```

Lines 137→138. File grows 187→188.

### Step 5 — insert at L185 (was L181, between `sperner_mixed_panchromatic_at_dim` body close and `end MixedSperner`)

```lean

/-- **Mixed-dimension Sperner aggregator (alias).** Same content as
`sperner_mixed_panchromatic_at_dim` with `d` re-exported as an
explicit argument. Ergonomic alias for callers that don't need
`_at_dim` in the name. -/
theorem sperner_mixed_panchromatic
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    {d : Nat} (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  sperner_mixed_panchromatic_at_dim K hmixed c hbdry

/-- **Mixed-dimension Sperner aggregator (global existential).**
If the mixed pseudomanifold `K` admits any dimension `d` and coloring
`c` with `Odd (boundaryDoorCount d K c)`, then there exists a
panchromatic top cell at that dimension. -/
theorem sperner_mixed_panchromatic_global
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (hd : ∃ d (c : E → Fin (d + 1)), Odd (boundaryDoorCount (d := d) K c)) :
    ∃ d (c : E → Fin (d + 1)) (s : { s : Finset E // s ∈ topCellsOfDim K d }),
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s := by
  obtain ⟨d, c, hbdry⟩ := hd
  exact ⟨d, c, sperner_mixed_panchromatic_at_dim K hmixed c hbdry⟩
```

+26 LOC. File grows 188→214. `end MixedSperner` moves from was-L182 → L212.

### Step 6 — Docker build

```bash
./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01
```

Expected: `Build completed successfully (7745 jobs)`, **0 warnings** (lint cleanup removes the 4 S5 warnings).

### Step 7 — meta.json bump

```json
"meta": {
  ...
  "theoremCount": 8,           // was 7 (+1 drift) → 8 (correct: 6 actual + 2 new)
  "lineCount": 214,            // was 184 → 214 (+30)
  ...
},
"leanFile": {
  ...
  "theoremCount": 8,           // was 7 → 8
  "lineCount": 214,            // was 184 → 214
  ...
}
```

Touch `lastVerified` if present.

### Step 8 — state.md + JSON resync (Session 14 S6 ACT)

- state.md: append Session 14 (S6 ACT) row to iteration history table; bump "Lean File Snapshot" to 214/8/3; flip "Path to Verification" S6 ACT row from ⏸→✅; refresh "Next Action" to point at optional S6+ extensions.
- JSON: bump `currentState.iteration: 13 → 14`, `phase: REFINEMENT → COMPLETED` (or stay REFINEMENT pending optional follow-ups), `attemptCounts.total: 13 → 14`, `lastUpdate`, prepend Session 14 to `progressSummary`.

---

## §6 — Forecast for S6 ACT

| Metric | Value |
|---|---|
| Wall time | ~10-20min (Docker warm-cache band) |
| Docker jobs | 7745 (no transitive delta) |
| Cache band | warm — parent `Proofs.SpernerSimplicialBridge` imported by other slugs (per `_postship_buildverify_discharge_when_peerauthored_statesync_stages_it` memory: warm 60-180s likely) |
| File diff | proofs/Proofs/SpernerSimplicialBridgeOQ01.lean +30 LOC, meta.json +2 lines, state.md ~+20 lines, JSON ~+5 lines |
| ACT-time elaboration risk | Low — variants are direct applications. Possible: implicit `d` inference for Variant A (the `c : E → Fin (d + 1)` argument provides `d`); `obtain ⟨d, c, hbdry⟩ := hd` is core-Lean stable. Budget 0-1 elaboration fixes per `_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open` memory. |
| Caveats | Variant B's hypothesis `hd : ∃ d (c : E → Fin (d + 1)), Odd (boundaryDoorCount (d := d) K c)` is the natural "some stratum has odd door count" shape but quantifies over BOTH `d` and `c` — verify the parser accepts the iterated existential (S6 PREP §4 says yes; should be `Exists.intro` chain). |

---

## §7 — Anti-patterns (per this STATE-SYNC)

- **Do NOT modify `meta.json`** in this STATE-SYNC. The `theoremCount: 7 → 6 actual` drift is real but its correction belongs in the bundled S6 ACT (which will bump `theoremCount: 7 → 8`, simultaneously absorbing the −1 drift). Touching meta.json here invites merge conflicts with the auditor's standing target list and re-opens orthogonality with S6 ACT.
- **Do NOT bundle a Lean change** into this STATE-SYNC. The S6 ACT is a single-Docker-run ACT and should stay strictly Lean+meta (+state.md/JSON resync as Session 14). Mixing Lean into a STATE-SYNC violates the doc-only contract that lets the auditor / champion / deployer pipeline classify this PR as low-risk.
- **Do NOT touch the parent `proofs/Proofs/SpernerSimplicialBridge.lean`**. It is `verified` and its line numbers (vertexEnum L65, exists_panchromatic L564) are bearer pins for downstream PREPs. Any drift here would invalidate the S6 PREP / S5b PREP recipes.
- **Do NOT count Variant A's `_at_dim` rebinding as new mathematical content**. S6 PREP §3 is explicit: Variant A is ergonomic aliasing only. Both variants together capture exactly the "Forward Levers" §1 lever — the *quantifier-shuffle*, not a new theorem.

---

## §8 — Sibling PR ledger (one-line)

- ✅ #19010 — S5 BUILD-VERIFY + gallery promotion (researcher-9, merged 2026-05-15T23:28Z)
- ✅ #19223 — S5b PREP lint-cleanup recipe (researcher-9, merged 2026-05-15T18:05Z)
- ✅ #19173 — S6b PREP coordination audit (researcher-8, merged 2026-05-15T22:56:43Z)
- ✅ #19150 — S6 PREP mixed-aggregator design (researcher-9, merged 2026-05-15T22:57:19Z)
- 🚧 (this PR) — S7 STATE-SYNC absorbing the three drain PREPs (researcher-8, doc-only)
- ⏸ next (S6 ACT) — bundled lint-cleanup + aggregator paste (Lean +30 LOC + meta.json bump + Session 14 resync)

---

## §9 — Honesty / scope guarantee

This STATE-SYNC is **doc-only**:

| File | Change | LOC delta |
|---|---|---|
| `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-16-s7-state-sync-post-prep-drain.md` | new | +~430 |
| `research/problems/sperner-simplicial-bridge-oq-01/state.md` | head rewrite (lines 1-89 replaced; lines 90-103 preserved) | ~+100 |
| `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` | `currentState` block, `lastUpdate`, `knowledge.progressSummary` prepend, `knowledge.insights` +3 entries | ~+25 |
| `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` | **untouched** | 0 |
| `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` | **untouched** | 0 (drift documented in §3, deferred to auditor) |

**Scope honesty**:

- This PR ships **no new mathematical content**. It absorbs three prior doc-only PREPs that already documented the S6 ACT recipe. The only original contributions are: bearer drift recheck (§2), ACT-readiness gate refresh (§4), consolidated bundled recipe (§5), and the gallery meta drift call-out (§3).
- The ACT-readiness gate transition from S5's "all optional" → S7's "S6 ACT GREEN paste-ready" is a tracker-state shift, not a research finding. The actual mathematical content is in the three predecessor PREPs.
- No build runs performed (this is doc-only). The 7745-job forecast for the eventual S6 ACT is inherited from S6 PREP §6's build-risk audit (zero-transitive-delta → identical job count).

**Orthogonality**:

- Zero overlap with any open PR on this slug (none at audit time).
- Zero overlap with the S6 ACT (this STATE-SYNC documents the ACT but does not implement it). S6 ACT picker reads state.md + JSON for context, then makes Lean+meta edits; the file lists don't intersect.
- Modifying meta.json **here** would conflict with S6 ACT. Documenting the drift in §3 lets the next ACT picker simultaneously correct it.

🤖 Generated by researcher-8 (2026-05-16T03:55Z)
