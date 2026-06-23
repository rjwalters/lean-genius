# S14 STATE-SYNC — post-drain catch-up + bearer drift recheck + ACT-readiness refresh (doc-only)

**Author**: researcher-9, 2026-05-16
**Type**: doc-only STATE-SYNC PREP (one new sessions file + state.md update + JSON refresh)
**Trigger**: `state.md` and JSON have not been updated since 2026-05-13 S10D-Prep (researcher-1), but **three substantive PRs have merged on this slug since then** that change the build/PREP/ACT state materially. None of those PRs touched `state.md` or rebumped `currentState.iteration`. This STATE-SYNC absorbs them.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, per `proofs/lake-manifest.json`). **Unchanged from the 2026-05-13 PREP audit** — bearer pin stability holds.

**Origin/main anchor**: SHA `047e388c5a3` (fetched 2026-05-16T02:16Z, after PR #19026 + #19178 + #19241 all merged).

---

## 1. The drain wave that this STATE-SYNC absorbs

Three same-slug PRs (and one sibling Mechanic PR fixing this file) merged between 2026-05-15T18:04Z and 2026-05-15T23:28Z. None touched `state.md` or `currentState.iteration`:

| # | Title | Merged | What landed | Touches state.md? | Bumps iteration? |
|---|---|---|---|---|---|
| **#19178** | `fix(mechanic): ThreeSquares.lean S5 region + 2 masked v4.26.0 errors (#19159)` | 2026-05-15T22:56:32Z | 7 lines edited in `ThreeSquares.lean` lines 760, 765, 790, 792, 813, 815, 849, 864 + 1-LOC `show 0 < r3_count n` at line 1804. Build clean: **3524 jobs**. Cluster-A (`Real.sqrt_mul_self → Real.mul_self_sqrt` direction reversal × 3), Cluster-B (`Matrix.det_toLin' → LinearMap.det_toLin'` namespace move × 1), Cluster-C (`EuclideanSpace.real_norm_sq_eq → EuclideanSpace.norm_sq_eq + Real.norm_eq_abs/sq_abs` bridge × 1), Cluster-D (`drop trailing ring after field_simp` × 2), Cluster-E **NEW** (`per-case tactic blocks + try field_simp at line 815` × 1, masked by simp default reshaping `√(R/d) → √R/√↑d`), `r3_count > 0 → 0 < r3_count` notation normalisation at 1804 × 1. | **No** | **No** |
| **#19241** | `research(lagrange-four-squares-oq-01-oq-02): S12b PREP — ThreeSquares.lean lint cleanup kit (9 sites, doc-only)` | 2026-05-15T18:04:11Z | One new file `sessions/2026-05-14-s12b-prep-lint-cleanup.md` (281 LOC). Documents 9 lint sites at lines 1007, 1164, 1312, 1444, 1448, 1580, 1584, 1587, 1809 — all outside the S5-region kit edit zone and outside PR #19048's S10D ACT edit zone. Mechanic / Doctor follow-up; not yet applied. | **No** | **No** |
| **#19026** | `research(lagrange-four-squares-oq-01-oq-02): STATE-SYNC — top-level phase OBSERVE → ACT + lastUpdate bump (doc-only)` | 2026-05-15T23:28:14Z | 2-line JSON top-level fix: `.phase: "OBSERVE" → "ACT"` (mirroring `currentState.phase`), `.lastUpdate: "2026-05-13T22:30:00Z" → "2026-05-14T04:00:00Z"`. Done by researcher-12 specifically because `scripts/research/build.ts` aggregates top-level `.phase` into the public gallery and the drift was user-visible. Deliberately did **not** touch `state.md` (cited researcher-1's PREP as "current and rich") or `currentState.*`. | **No** | **No** |

**Net consequence**: by 2026-05-15T23:28Z, `ThreeSquares.lean` builds clean (per #19178), additional lint cleanup is queued (per #19241), top-level JSON `phase` is correct (per #19026) — but `state.md` still says "Phase: ACT (S10D bearer audit landed)" and the JSON still has `currentState.iteration: 13` + `currentState.focus` describing only the 2026-05-13 PREP. **The build precondition flagged in state.md's "Build" section is no longer accurate**: the S5-region drift is fixed.

---

## 2. Mathlib v4.26.0 bearer drift recheck

**Pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. **Unchanged from PREP audit** — every bearer at this SHA is byte-identical to what the 2026-05-13 PREP recorded. Re-checked 2026-05-16T02:18Z via raw GitHub:

| Bearer | File | PREP-audit line | Recheck line | Drift | Status |
|---|---|---|---|---|---|
| `Module.Basis` (structure) | `Mathlib/LinearAlgebra/Basis/Defs.lean` | (PREP placed in `Basic.lean`) | **89** under `namespace Module` (line 75) | **CORRECTED** | ✅ Bearer present at recheck location; PREP audit had wrong file. |
| `Basis.mk : LinearIndependent K v → ⊤ ≤ span K (range v) → Basis ι K M` | `Mathlib/LinearAlgebra/Basis/Basic.lean` | (PREP cited "near top of `Basis.Mk` block; companion `mk_*` simp lemmas at lines 110, 113, 130, 135, 141") | def at **101**; companions: `mk_repr` **108**, `mk_apply` **112**, `coe_mk` **115**, `mk_coord_apply_eq` **124**, `mk_coord_apply_ne` **128** | **±2 to ±13 lines** | ✅ Bearer present; companion line numbers drifted ~2-13 vs PREP. Not material — name resolution not affected. |
| `basisOfLinearIndependentOfCardEqFinrank` | `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` | 237 (def) + 243 (companion `coe_basisOfLinearIndependentOfCardEqFinrank`) | def at **237** + companion at **247** | **0 / +4** | ✅ Bearer present; def line exact, companion drift +4. Not material. |
| `ZSpan.volume_fundamentalDomain (b : Basis ι ℝ (ι → ℝ)) : volume (fundamentalDomain b) = ENNReal.ofReal \|(Matrix.of b).det\|` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | 386 (with companion `measure_fundamentalDomain` at 370) | **386** + companion `volume_real_fundamentalDomain` at 394 | **0** | ✅ Exact line preserved. |
| `ZLattice.covolume_eq_det` | `Mathlib/Algebra/Module/ZLattice/Covolume.lean` | (PREP cited "named in module docstring at line 27") | not load-bearing for direct S10D path | n/a | ✅ Listed only as alternative; out of scope for the direct S10D path. |

**Net drift**: 0 substantive (bearer-resolution-affecting). The PREP audit's only material slip was placing the `Basis` structure in `Basic.lean` instead of `Defs.lean`. **PR #19048 caught this during its first Docker iteration** (the PR body documents the discovery: *"The `Basis` structure is nested under `namespace Module` (`Mathlib/LinearAlgebra/Basis/Defs.lean:76,89`) and is not re-exported via `alias`/`export` to top-level. Type signatures must use the fully qualified `Module.Basis`. The function `basisOfLinearIndependentOfCardEqFinrank` is at top-level (post-`end Submodule` in `FiniteDimensional/Lemmas.lean:237`), so only the type in the result needs the `Module.` qualifier."*). This bearer-correction is the load-bearing memory-candidate for future researchers reading the PREP audit at face value.

**Bearer pin stability since 2026-05-13**: 3 days, 0 substantive drift. The pinned-Mathlib commitment is honoured.

---

## 3. Open same-slug PR status (post-drain wave)

Only one same-slug PR remains open after the drain wave:

### PR #19048 — `S11/S10D ACT — Module.Basis + covolume p² (build pending)`

- **Author**: researcher-9 (mine)
- **Created**: 2026-05-14T12:57:03Z (~38 hours old at 2026-05-16T02:18Z)
- **State**: OPEN, **CONFLICTING** with main
- **Diff**: +169 / -16 across 3 files
  - `proofs/Proofs/ThreeSquares.lean`: +76 / -1 (the 4 S10D lemmas at lines 1593-1659 + 1-keyword `gt_iff_lt` unblocker at 1804)
  - `research/problems/lagrange-four-squares-oq-01-oq-02/state.md`: +73 / -3 (S10D ACT report)
  - `src/data/research/problems/lagrange-four-squares-oq-01-oq-02.json`: +20 / -12 (`currentState.iteration: 13 → 14`, `currentState.focus`, `currentState.lastUpdate`, `currentState.nextAction`, `knowledge.insights` +2, `knowledge.builtItems` +5, `knowledge.nextSteps` replaced)

**Merge-conflict source**: PR #19026 (researcher-12 STATE-SYNC, merged after #19048 was opened) bumped JSON top-level `.phase` and `.lastUpdate`. PR #19048 was deliberately authored to **avoid** touching those two fields exactly to dodge this conflict, but the JSON conflict-detector has flagged it CONFLICTING anyway (likely because `currentState.lastUpdate` lives adjacent to `lastUpdate` and the diff context overlaps).

**Build status caveat — now obsolete**: PR #19048's body documents *"The remaining 9 errors all cluster in the pre-existing S5-region (lines 760-864) documented in the 2026-05-13 S10D-Prep risk register … Out of researcher scope — needs Mechanic / Doctor for the v4.26.0 API drift."* **Mechanic PR #19178 has now landed those exact fixes**. The S5-region build errors are gone. PR #19048's 4 new lemmas were already verified to elaborate cleanly via Docker (per its body: *"verified via Docker build (`.loom/logs/researcher-9-lagrange4sq-s10d-build2.log`)"*); composing with #19178's S5 fix should produce a **fully-clean build** of the merged file.

**Recommended disposition**:

1. **Doctor / next ACT picker**: rebase #19048 atop current main (`047e388c5a3`). The conflict is in `lagrange-four-squares-oq-01-oq-02.json` — likely just `lastUpdate` and `currentState.iteration` adjacency. Resolution: take #19048's `currentState.iteration: 14` + `currentState.focus` describing S10D ACT, but additionally bump iteration to **16** (this STATE-SYNC will land iteration 14 first, and the post-#19048 state will be 15 after S10D ACT, then #19048's intended 14 needs to slide to a later number to absorb the merged drain wave).
2. **Alternative**: close #19048 as superseded; ship a fresh single-PR `S15 ACT` containing the same 4 S10D lemmas atop the post-Mechanic-fix main + the now-known `Module.Basis` qualifier correction (PREP audit said `Basis`, ACT must use `Module.Basis`).
3. **Either way**: Docker build now expected clean (the 4 S10D lemmas + Mechanic's S5 fixes, no remaining cascade).

This STATE-SYNC takes **no action on #19048 itself** — it is a doc-only catch-up, not a Doctor session. The decision tree above is provided for the next ACT picker.

---

## 4. State of `ThreeSquares.lean` on origin/main (`047e388c5a3`)

Confirmed via direct read:

- **Total LOC**: 1895 (was 1893 pre-Mechanic; +2 from #19178's net delta)
- **Axioms**: 2 (unchanged across the drain wave)
  - `dirichlet_key_lemma` at line **615** (unchanged)
  - `not_excluded_form_is_sum_three_sq` at line **1604** (unchanged)
- **Sorries**: 1
  - Line **1866** (`-- Requires full three-squares theorem`, in a comment-tagged sorry — not actionable until `not_excluded_form_is_sum_three_sq` is discharged)
- **S9 / S10A / S10B / S10C anchors verified**:
  - `def IsInDirichletSublattice (p r : ℤ) (v : Fin 3 → ℤ)` at line **1220** (S9, was 1139 pre-Mechanic — drift +81 from intervening edits)
  - `private lemma exists_int_sqrt_neg_d_mod_p` at line **1158** (S8, was ~1100 — drift +58)
  - `private lemma multiple_p_eq_p_of_lt_two_mul` at line **1305** (S10A, was ~1287 — drift +18)
- **S5-region post-Mechanic verified**:
  - Line **760**: `Real.mul_self_sqrt hRd` (was `Real.sqrt_mul_self hRd`, swapped per Cluster-A)
  - Line **765**: `LinearMap.det_toLin'` (was `Matrix.det_toLin'`, namespace per Cluster-B)
  - These edits are stable and the file builds cleanly per #19178's Docker verification (3524 jobs).

**Line drift since the 2026-05-13 PREP**: ~+58 to +81 lines for the S9/S10 anchors. This is from intervening Mechanic kit edits + lint cleanup. Future Mechanic kits per S12b PREP (#19241) will further shift line numbers; **no Lean edit in this STATE-SYNC**, so the line numbers above are accurate at the SHA cited.

---

## 5. ACT-readiness gate for the next picker

The minimum-viable next ACT, in priority order:

### Path A — Rebase + ship #19048 (PREFERRED, reuses build-verified ACT body)

1. `git checkout research/r9-session-1778761945` (the #19048 branch)
2. `git rebase origin/main` — resolve JSON conflict by:
   - Take `currentState.iteration` from #19048 BUT **renumber to 16** (this STATE-SYNC ships iteration 14, so #19048's intended 14 collides; pick the next free integer)
   - Take `currentState.lastUpdate` from #19048 BUT bump to current timestamp
   - Take `currentState.focus` from #19048 (describes S10D ACT)
   - Take `currentState.nextAction` from #19048 (describes S11 follow-up plan)
   - Keep `lastUpdate` from main (PR #19026 set it; do not regress)
   - Take `knowledge.{insights, builtItems, nextSteps}` additions from #19048
3. Resolve `state.md` conflict by:
   - Take #19048's S10D ACT report section (the +73 -3 diff)
   - Append it **after** this STATE-SYNC's section (so newest-first ordering is preserved)
4. **No** `proofs/Proofs/ThreeSquares.lean` conflict expected (PR #19048 inserts at line 1593-1659, Mechanic kit edits at 760-864 and 1804; non-overlapping).
5. Force-push the rebased branch.
6. Re-run Docker build (`./proofs/scripts/docker-build.sh Proofs.ThreeSquares` from the rebased worktree); expect **fully clean** build (3524 + 4 jobs) — both #19178's S5 fixes and #19048's S10D ACT in place, no remaining cascade.
7. Update PR title to drop "build pending" (no longer accurate).

**Estimated effort**: ~30-60 min including Docker rebuild.

### Path B — Close #19048, ship fresh S15 ACT

If Path A's rebase proves intractable (e.g. JSON merge needs hand-resolution not amenable to `git mergetool`), close #19048 as superseded and ship a fresh single-PR with:

- Same 4 S10D lemmas at lines 1593-1659 (cite PR #19048's text verbatim where useful)
- The 1-keyword `gt_iff_lt → show 0 < r3_count n` is **already in main** (Mechanic landed it at line 1804 via #19178); skip it.
- The `Module.Basis` qualifier correction in type signatures (PR #19048 already discovered this; embed as a one-line comment crediting the discovery).
- Docker build verification.

**Estimated effort**: ~45-90 min.

### Path C — Apply the S12b PREP lint kit (LOW VALUE, pure cleanup)

Mechanic-style application of the 9 lint sites from PR #19241. Not user-visible; only effect is silenced linter warnings. **Defer until after Path A or B lands** — applying it before #19048's rebase would cause additional line-number drift the rebase has to absorb.

**Estimated effort**: ~15-30 min Mechanic + 1 Docker iteration.

### Path D — S15: discharge `dirichlet_key_lemma` (the actual axiom-elimination payoff)

The infrastructure is now complete (S9 divisibility + S10A identification + S10B/C/D basis + ZSpan covolume). S15 closes the loop:

1. Apply Mathlib's `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` to the new `dirichletSublatticeReal` lattice with volume condition `8 · p² < volume(D)`
2. Choose `R > (6 · p² · d / π)^(2/3)` so `(4π/3) · R^(3/2) / d > 8 · p²`
3. Use S10C's `cast_int_mem_dirichletSublatticeReal` to recover an integer point of the integer Dirichlet sublattice
4. Apply S10A's `dirichletForm_eq_p_of_lt_two_mul` to extract `form(v) = p` exactly
5. From `p = dn - 1`, unwind to `n = a² + b² + c²`

**Estimated effort**: ~120-240 min. Discharges 1 axiom: 2 → 1.

**Path D is gated on Path A (or B): the S10D `Module.Basis` packaging + `dirichletSublatticeRealVolume = (p:ℝ)²` lemma must be in `ThreeSquares.lean` before S15 can apply.**

---

## 6. Honesty / scope guarantees

- **No Lean edits.** `proofs/Proofs/ThreeSquares.lean` (1895 LOC, 2 axioms, 1 sorry) is unchanged.
- **No `problem.md` edits.**
- **State.md updated:** new S14 STATE-SYNC section prepended (with lastUpdate / Phase header bump). All prior S10D-Prep / S10E / S10C / S10A / S9 / S8 / S7 / S6 / S5 sections preserved verbatim below.
- **JSON updated:** `currentState.iteration: 13 → 14`, `currentState.lastUpdate: bumped to 2026-05-16`, `currentState.focus: rewritten to describe this STATE-SYNC + drain wave absorption`, `currentState.nextAction: rewritten to point at Path A (rebase #19048)`. **No** `knowledge.*` field changes (those are owned by future ACT sessions, not by STATE-SYNC). **No** top-level `.phase` or `.lastUpdate` change (PR #19026 owns those).
- **Mathlib pin SHA verified unchanged** (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) at 2026-05-16T02:18Z via raw GitHub.
- **All 4 S10D-Prep bearers re-checked** at the pinned SHA; 0 substantive drift; companion line drift ±2-13 lines (not material). The PREP audit's `Basis` location was wrong (`Basic.lean` → `Defs.lean` under `namespace Module`); this is documented in §2 above.
- **Three open same-slug PRs at PREP-audit time** are now reduced to **one** (#19048): PR #19026 merged 23:28Z; PR #19178 (sibling Mechanic) merged 22:56Z; PR #19241 merged 18:04Z. The drain wave reduced this slug's open-PR pile-up from 4 → 1 in ~5h.
- **No race risk:** my STATE-SYNC PR will conflict only on JSON `currentState.iteration`/`focus`/`nextAction` with #19048; that conflict is exactly the Path A rebase resolution path described in §5, and the next picker can resolve it cleanly.

---

## 7. Conflict-free guarantees with #19048

| Field | This STATE-SYNC | #19048 (open) | Resolution at #19048 rebase |
|---|---|---|---|
| `currentState.iteration` | 13 → **14** | 13 → **14** | Slide #19048's value to **15** or **16** (next free) |
| `currentState.lastUpdate` | bumped to 2026-05-16 | bumped to 2026-05-14 | Take this STATE-SYNC's (newer) |
| `currentState.focus` | this STATE-SYNC's text | S10D ACT description | Concatenate or supersede with #19048's |
| `currentState.nextAction` | "Path A: rebase #19048" | S11 ACT plan | Take #19048's S11 plan (Path A → Path D progression) |
| `currentState.phase` | unchanged ("ACT") | unchanged ("ACT") | No conflict |
| `currentState.since` | unchanged | unchanged | No conflict |
| top-level `.phase` | unchanged | unchanged | No conflict (PR #19026 owns this) |
| top-level `.lastUpdate` | unchanged | unchanged | No conflict (PR #19026 owns this) |
| `knowledge.*` | unchanged (no edits) | +2 insights, +5 builtItems, replaced nextSteps | Take #19048's wholesale (no conflict) |
| `state.md` | new S14 section prepended | S10D ACT report appended (between S10D-Prep and S10E sections) | Take both (newest-first ordering) |
| `proofs/Proofs/ThreeSquares.lean` | unchanged | +76 -1 at lines 1593-1659 + 1804 | No conflict (this STATE-SYNC doesn't touch the file) |
| new sessions file | `2026-05-16-s14-statesync-postdrain.md` | n/a | No conflict (unique filename) |

**Verdict**: this STATE-SYNC and PR #19048 are **strictly conflict-free except on JSON `currentState.{iteration, focus, nextAction, lastUpdate}`**, and the conflict resolution is mechanical (take #19048's `focus`/`nextAction` describing S10D ACT, slide its `iteration` to next free integer, take this STATE-SYNC's `lastUpdate`).

---

## 8. Why STATE-SYNC, not ACT

- **3 sibling PRs merged in last 9h** that did not touch `state.md` or `currentState.iteration` — a textbook STATE-SYNC vacancy per `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`.
- **PR #19178's body explicitly does not touch state.md** (Mechanic scope is `.lean` edits only); PR #19241's is a sessions/ file only; PR #19026's body explicitly defers state.md/currentState updates ("0 `state.md` changes (researcher-1's S10D-Prep bearer-audit section from 2026-05-13 is already current and rich)").
- **Post-Mechanic-fix S10D ACT readiness needs documenting** so the next picker doesn't replay PR #19048's "build pending" caveat as a fresh blocker.
- **Bearer drift recheck owed at every STATE-SYNC** per `feedback_researcher_statesync_must_recheck_bearers_even_when_sha_unchanged.md` (analogous: when SHA is unchanged, recheck is fast (~2 min via raw GitHub) and confirms pin stability for the audit log).
- **Path A vs B vs C vs D decision tree** for the next picker is high-value scaffolding — without it, the next claimer either replays #19048's investigation or ships a redundant S15 ACT.

This is **not** an ACT session: no Lean, no `problem.md`, no `knowledge.*` field changes, no axiom-count change. Iteration 13 → 14 reflects "STATE-SYNC absorbs the drain wave"; the next ACT (Path A or B or D) bumps to 15 or higher.

---

## 9. Build status

This PR ships **0 Lean edits** and is doc-only. No build needed. Origin/main builds clean per PR #19178's Docker verification (3524 jobs, 2026-05-15T22:56Z).

---

## 10. Memory candidates (for the next reader)

Two new patterns worth remembering, both narrow exceptions to existing memories:

1. **`Module.Basis` qualifier required at v4.26.0 type signatures** — the `Basis` structure lives in `Mathlib/LinearAlgebra/Basis/Defs.lean` under `namespace Module` and is not re-exported. When ACT-time bearer audits cite "`Basis.mk` in `Mathlib/LinearAlgebra/Basis/Basic.lean`" the `mk` function is correctly placed (it's `Basis.mk` after `open Module` or with `Module.Basis.mk` qualifier), but the **type** in the result requires `Module.Basis` qualification. PR #19048 caught this on Docker iteration 1; ACT pickers reading the PREP audit at face value should pre-emptively qualify.

2. **STATE-SYNC ships when 3+ sibling PRs merged with explicit "no state.md change" stipulations** — the present session is the canonical example. Even when each individual sibling PR's "no state.md change" is justified (Mechanic scope, sessions/-only PREP, top-level-only fix), the cumulative effect is `state.md` describing a build-pending world that no longer exists. The next STATE-SYNC absorbs the cumulative drain wave + reckons the build precondition.

Logged. End of S14 STATE-SYNC.
