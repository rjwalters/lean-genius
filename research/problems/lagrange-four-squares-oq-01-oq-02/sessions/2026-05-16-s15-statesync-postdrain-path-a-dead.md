# S15 STATE-SYNC — post-drain catch-up + Path A retirement + Path B promotion (doc-only)

**Author**: researcher-11, 2026-05-16
**Type**: doc-only STATE-SYNC (one new sessions file + state.md head update + JSON refresh)
**Trigger**: S14 STATE-SYNC PR #19377 just merged at 2026-05-16T03:53:07Z — and **in the same drain second, PR #19048 (the S10D ACT body it was meant to gate) was CLOSED** at 2026-05-16T03:53:08Z. The S14 narrative on origin/main treats Path A (rebase #19048) as PREFERRED — but #19048 no longer exists as an open PR. Without this S15, the next picker reads `currentState.nextAction` and tries to rebase a closed PR.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, per `proofs/lake-manifest.json` at origin/main HEAD `78448f56d0a`). **Unchanged from S14's recheck** — bearer pin stability holds (3 days, 0 substantive drift).

**Origin/main anchor**: SHA `78448f56d0ad0d99f4a30befc061c90434749cf6` (fetched 2026-05-16T04:03Z, post-S14-merge).

---

## 1. The state change that this STATE-SYNC absorbs

Two same-slug events landed in a synchronised drain wave at 2026-05-16T03:53:07-08Z. Both are user-action triggered (S14 merge + #19048 close), not autonomous-agent triggered, so no `state.md`/`currentState.iteration` bump happened automatically.

| # | Title / Event | Timestamp | What landed / Effect | Touches state.md? | Bumps iteration? |
|---|---|---|---|---|---|
| **#19377** (S14 STATE-SYNC, mine — researcher-9) | "research(lagrange-four-squares-oq-01-oq-02): S14 STATE-SYNC — post-drain catch-up (Mechanic #19178 + S12b PREP #19241 + STATE-SYNC #19026 absorbed)…" | **MERGED 2026-05-16T03:53:07Z** | Prepended S14 narrative to `state.md`; bumped `currentState.iteration` 13→14; rewrote `currentState.{focus, nextAction}` to describe drain absorption + Path A/B/C/D decision tree. **Path A (PREFERRED): rebase #19048**. **No** Lean edits. **No** `problem.md` or `knowledge.*` edits. | ✅ (head section + nextAction) | ✅ (13→14) |
| **#19048** (S11/S10D ACT, mine — researcher-9, 2026-05-14) | "research(lagrange-four-squares-oq-01-oq-02): S11/S10D ACT — Module.Basis + covolume p² (build pending)" | **CLOSED 2026-05-16T03:53:08Z** | The 4 S10D lemmas (~+76 −1 at `ThreeSquares.lean` lines 1593-1659 + 1804) **did NOT land on main**. Closure happened in the same drain second as S14 — likely by a champion/deployer pass that judged the PR superseded by S14's narrative (the PR body's "build pending" caveat was obsolete post-Mechanic #19178, but the JSON CONFLICTING state vs S14 was unresolved). No comment on why closure rather than merge. | ❌ (its state.md / JSON adjacency edits are now gone from main) | ❌ (its `currentState.iteration: 13→14` did not land) |

**Net consequence**:

- **S14's S10D ACT-readiness gate is now stale at item Path A.** The S14 narrative still recommends Path A as PREFERRED; Path A requires rebasing a closed PR, which is not a normal git operation (would require reopening + force-push).
- **Path B (close #19048 + ship fresh S15 ACT)** is now structurally what already happened — except the "close #19048" half is done and the "ship fresh S15 ACT" half is not. The next picker should pick this up.
- **No Lean state change.** `proofs/Proofs/ThreeSquares.lean` on origin/main `78448f56d0a` is byte-identical to its state on `8a3cda556b6` (the S14 baseline): **1895 LOC, 2 axioms** (`dirichlet_key_lemma` line 615, `not_excluded_form_is_sum_three_sq` line 1604), **1 sorry** (line 1866).
- **No bearer pin change.** Same Mathlib v4.26.0 SHA. Recheck below confirms 4/4 bearers exact at the expected resolution points.

---

## 2. Mathlib v4.26.0 bearer drift recheck

**Pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. **Unchanged from S14's recheck** — every bearer at this SHA is byte-identical to what S14 (and the 2026-05-13 PREP) recorded. Re-checked 2026-05-16T04:03Z via raw GitHub:

| Bearer | File | S14 recheck line | This S15 recheck line | Drift | Status |
|---|---|---|---|---|---|
| `Module.Basis` (structure) | `Mathlib/LinearAlgebra/Basis/Defs.lean` | **89** under `namespace Module` (line 75) | **89** under `namespace Module` (line 76) | 0 on bearer; ±1 on `namespace Module` header (counting convention) | ✅ Exact bearer line. |
| `Basis.mk` def | `Mathlib/LinearAlgebra/Basis/Basic.lean` | def **101**; `mk_repr` **108**; `mk_apply` **112**; `coe_mk` **115** | def **102**; `mk_repr` **110**; `mk_apply` **113**; `coe_mk` **117** | def +1; companions +1 to +2 | ✅ Same SHA → same bytes; my recheck stands as authoritative. S14's manual counting was off by 1-2 on the def block (S14's note "±2-13 lines on companions; not material" already flagged the imprecision). |
| `basisOfLinearIndependentOfCardEqFinrank` | `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` | def **237** + companion **247** | def **237** + companion `coe_basisOfLinearIndependentOfCardEqFinrank` at **243** | 0 / −4 on companion | ✅ Bearer present; def exact. S14's "247" was off by 4 vs the byte-level position at this same SHA. |
| `ZSpan.volume_fundamentalDomain` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | **386** | **386** | 0 | ✅ Exact. |

**Net drift**: 0 substantive (bearer-name-resolution-affecting). All four S10D bearers remain present at the pinned Mathlib v4.26.0 SHA. The minor ±1-4 line discrepancies between S14's recheck and this S15 recheck are at the same SHA, so they reflect S14's manual-count imprecision, not Mathlib churn — same bytes, different counters. **Bearer pin stability since 2026-05-13: 3 days, 0 substantive drift.**

The PR #19048 PR body's documented bearer-correction discovery — "*The `Basis` structure is nested under `namespace Module` (Defs.lean:76,89) and is not re-exported via `alias`/`export` to top-level. Type signatures must use the fully qualified `Module.Basis`. The function `basisOfLinearIndependentOfCardEqFinrank` is at top-level (post-`end Submodule` in `FiniteDimensional/Lemmas.lean:237`), so only the type in the result needs the `Module.` qualifier.*" — is still **the load-bearing memory** for any future S15 ACT picker. (#19048 is closed but its PR description remains queryable on GitHub.)

---

## 3. Updated ACT-readiness gate (next picker)

S14's Path A/B/C/D scaffolding requires one structural amendment: **Path A is retired** (PR #19048 is closed, not "open + conflicting" as S14 described). The remaining paths re-rank as follows:

### Path B (NEW PREFERRED, ~45-90 min): fresh S15 ACT shipping the S10D body from scratch

1. New branch off origin/main `78448f56d0a`.
2. Insert 4 S10D lemmas at `ThreeSquares.lean` line **1593** (immediately after S10C's `cast_int_mem_dirichletSublatticeReal`, immediately before S10A's `dirichletForm_eq_p_of_lt_two_mul`):

   - `dirichletSublatticeRealBasisLinearIndependent (p r : ℤ) (hp : 0 < p) : LinearIndependent ℝ (dirichletSublatticeRealBasisVec p r)` — derived from S10C's `dirichletSublatticeRealBasisMatrix_det = (p : ℝ)²` and `Matrix.linearIndependent_rows_iff_isUnit_det` (or v4.26.0 equivalent: `Matrix.det_ne_zero_iff_isUnit` + `Int.cast_pos.mpr hp |>.ne'` + `pow_ne_zero 2`). **Target**: ~10 LOC.

   - `dirichletSublatticeRealBasis (p r : ℤ) (hp : 0 < p) : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ)` — via `basisOfLinearIndependentOfCardEqFinrank` with the line-(1) result and `Module.finrank_fintype_fun_eq_card ℝ` (or `Module.finrank_pi` as backup at v4.26.0). **Note the `Module.` qualifier on the return type** (PR #19048's iter-1 discovery). **Target**: ~5 LOC.

   - `dirichletSublatticeRealBasis_toMatrix_eq (p r : ℤ) (hp : 0 < p) : Matrix.of (dirichletSublatticeRealBasis p r hp) = dirichletSublatticeRealBasisMatrix p r` — entry-wise via `Matrix.of_apply` + `coe_basisOfLinearIndependentOfCardEqFinrank` (`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:243`). **Target**: ~15 LOC, all `simp` / `rfl`.

   - `dirichletSublatticeRealVolume (p r : ℤ) (hp : 0 < p) : volume (ZSpan.fundamentalDomain (dirichletSublatticeRealBasis p r hp)) = ENNReal.ofReal ((p : ℝ)^2)` — `rw [ZSpan.volume_fundamentalDomain, dirichletSublatticeRealBasis_toMatrix_eq, dirichletSublatticeRealBasisMatrix_det]` + `abs_of_nonneg (sq_nonneg _)`. **Target**: ~15 LOC.

3. **No edit needed at line 1804** — Mechanic PR #19178 already normalised `r3_count > 0 → 0 < r3_count` at that site.

4. Docker build: `./proofs/scripts/docker-build.sh Proofs.ThreeSquares` from the worktree. Expect 3524 + 4 jobs clean (3524 from #19178 baseline + ~4 from new lemmas). Acceptable iteration count: 1-2 (the `Module.Basis` qualifier and `Module.finrank_fintype_fun_eq_card` vs `Module.finrank_pi` name choice are the only ACT-time elaboration uncertainties).

5. Update `state.md` head: prepend S15 ACT section, retain S14 + S10D-Prep + S10E + … tail. Update JSON: `currentState.iteration: 14 → 15` (or higher if this S15 STATE-SYNC bumps to 15 first; in that case S15 ACT bumps to 16), `currentState.focus` rewritten to describe S10D ACT, `currentState.nextAction` rewritten to point at Path D.

6. **Add to `knowledge.builtItems`**: 4 new entries naming each new lemma + its file:line. **Add to `knowledge.insights`**: 1 entry crediting PR #19048's `Module.Basis` qualifier discovery (load-bearing for any reader of S10D source). **Update `knowledge.nextSteps`**: replace "rebase #19048" with "Path D: discharge `dirichlet_key_lemma` via S10D + Minkowski lattice theorem composition".

**Estimated effort**: ~45-90 min including Docker.

### Path C (LOW VALUE, defer): apply S12b PREP lint kit

Unchanged from S14's analysis. 9 lint sites at lines 1007, 1164, 1312, 1444, 1448, 1580, 1584, 1587, 1809 — all outside Path B's edit zone (1593-1659). Mechanic-style cleanup. Apply after Path B lands to avoid line-number drift the Mechanic application would otherwise have to absorb.

### Path D (gated on Path B, ~120-240 min): discharge `dirichlet_key_lemma` (1 axiom drop, 2 → 1)

Unchanged from S14's analysis. After Path B's `dirichletSublatticeRealVolume = (p:ℝ)²` lemma is in `ThreeSquares.lean`:

1. Apply Mathlib's `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` (or v4.26.0 equivalent — `Mathlib/MeasureTheory/Group/FundamentalDomain.lean` neighborhood) to the new `dirichletSublatticeReal` lattice with the volume condition `8 · p² < volume(dirichletEllipsoid)`.
2. Choose `R > (6 · p² · d / π)^(2/3)` so `(4π/3) · R^(3/2) / d > 8 · p²`. The pre-existing `dirichletEllipsoid_volume` lemma (S4, no longer axiomatised post-PR #16964) yields the ellipsoid's volume formula.
3. Use S10C's `cast_int_mem_dirichletSublatticeReal` (line 1565 region) to recover an **integer** point of the **integer** Dirichlet sublattice (round-tripping through `Submodule ℤ (Fin 3 → ℝ)`).
4. Apply S10A's `dirichletForm_eq_p_of_lt_two_mul` (line 1305) to extract `form(v) = p` exactly.
5. From `p = d·n − 1` and `form(v) = p = v 0² + d · v 1² + d · v 2²`, unwind to `n = a² + b² + c²` (the three-squares theorem for `n` not of the form `4^a (8b+7)`).

**Effort**: ~120-240 min. Discharges 1 axiom: 2 → 1.

---

## 4. Honesty / scope guarantees

- **No Lean edits.** `proofs/Proofs/ThreeSquares.lean` (1895 LOC, 2 axioms, 1 sorry) is unchanged on origin/main `78448f56d0a` and remains unchanged in this PR.
- **No `problem.md` edits.**
- **State.md updated:** new S15 STATE-SYNC section prepended (with header phase/iteration/lastUpdate bump). All prior S14 STATE-SYNC / S10D-Prep / S10E / S10C / S10A / S9 / S8 / S7 / S6 / S5 sections preserved verbatim below.
- **JSON updated:** `currentState.iteration: 14 → 15`, `currentState.attemptCounts.{total, current}: 14 → 15`, `currentState.focus` rewritten to describe the post-S14-merge + #19048-closure landing, `currentState.nextAction` rewritten to point at **Path B (now PREFERRED)**, `currentState.lastUpdate` bumped. **No** `knowledge.*` field changes (those are owned by the S15 ACT, not by STATE-SYNC). **No** top-level `.phase` or `.lastUpdate` change (PR #19026 owns those; both already at correct values: `phase: "ACT"`, `lastUpdate: "2026-05-14T04:00:00Z"` — the latter is admittedly slightly stale post-S14 merge, but S14 also chose not to bump it; this S15 follows that precedent rather than picking a fight with #19026's ownership claim).
- **Mathlib pin SHA verified unchanged** (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) at 2026-05-16T04:03Z via raw GitHub.
- **All 4 S10D-Prep bearers re-checked** at the pinned SHA; 0 substantive drift. The minor ±1-4 line discrepancies vs S14's recheck are at the same SHA — same bytes, different counters. S14's "±2-13 lines on companions; not material" already flagged this. Future PREP/ACT pickers should use **this S15's** line numbers (def 102, mk_repr 110, mk_apply 113, coe_mk 117, companion 243) as the authoritative byte-level positions.
- **No open same-slug PR at S15 claim time.** `gh pr list --search "lagrange-four-squares-oq-01-oq-02 in:title" --state open -R rjwalters/lean-genius` returned `[]` (verified at 2026-05-16T04:00Z). Previously 1 open (#19048); now 0. Drain wave reduced this slug's open-PR pile-up from 4 → 0 in ~10h.
- **No race risk.** This S15 STATE-SYNC ships into 0 open same-slug PRs, so the conflict-free guarantee is structural: no JSON, no state.md, no Lean concurrent writer.

---

## 5. Why STATE-SYNC, not ACT

- **State.md and JSON drift relative to material truth.** S14's narrative + `currentState.nextAction` describe a Path A that no longer makes sense (PR #19048 is closed). Without S15, the next picker either (a) tries to rebase a closed PR (no-op) or (b) reads further into state.md and discovers Path B/D, having wasted time on the obsolete Path A.
- **Pattern match to `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`** (and its refinement `_postship_two_release_retries_lands_on_dual_merge_with_stale_duplicate_and_json_drift_ships_statesync.md`): a just-merged STATE-SYNC owns a stale narrative that contradicts the immediate post-merge reality. Refresh in a doc-only S15 STATE-SYNC.
- **No Lean state delta needs documenting** that #19048 would have provided — the 4 S10D lemmas it carried did not land. So the S15 STATE-SYNC is purely a meta-state refresh, not a substantive content delta.
- **Bearer drift recheck owed at every STATE-SYNC** per established memory pattern (analogous trap: "when SHA is unchanged, recheck is fast and confirms pin stability for the audit log").
- **Path A/B/C/D re-ranking is high-value scaffolding for the next ACT picker.** Path B is now structurally PREFERRED (the "close #19048" half is done by the drain wave; the next picker only ships the "fresh S15 ACT" half — ~45-90 min vs S14's hopeful "Path A: ~30-60 min for rebase").

This is **not** an ACT session: no Lean, no `problem.md`, no `knowledge.*` field changes, no axiom-count change. Iteration 14 → 15 reflects "S15 STATE-SYNC absorbs the post-S14-merge + #19048-closure drain"; the next ACT (Path B → Path D) bumps to 16 or higher.

---

## 6. Conflict-free guarantees

| Field | This S15 STATE-SYNC | Open same-slug PRs | Resolution |
|---|---|---|---|
| `currentState.iteration` | 14 → **15** | none | No conflict |
| `currentState.lastUpdate` | bumped to 2026-05-16T04:..Z | none | No conflict |
| `currentState.focus` | this S15 narrative | none | No conflict |
| `currentState.nextAction` | "Path B PREFERRED: fresh S15 ACT" | none | No conflict |
| `currentState.phase` | unchanged ("ACT") | none | No conflict |
| `currentState.since` | unchanged | none | No conflict |
| top-level `.phase` | unchanged ("ACT") | none | No conflict |
| top-level `.lastUpdate` | unchanged | none | No conflict |
| `knowledge.*` | unchanged | none | No conflict |
| `state.md` | new S15 section prepended | none | No conflict |
| `proofs/Proofs/ThreeSquares.lean` | unchanged | none | No conflict |
| new sessions file | `2026-05-16-s15-statesync-postdrain-path-a-dead.md` | none | No conflict |

**Verdict**: 0 open same-slug PRs at claim time. Strictly conflict-free.

---

## 7. Build status

**Origin/main `78448f56d0a`**: `ThreeSquares.lean` builds clean per S14's recorded baseline (3524 jobs post-Mechanic #19178). This S15 makes no Lean edits, so the build is unchanged. No Docker run needed for this STATE-SYNC.

The next ACT picker (Path B) **must** run Docker to verify the 4 new S10D lemmas; expect ~3528 jobs.

---

## 8. Memory candidates for future researchers

1. **Drain-wave-induced PR closure**: when a STATE-SYNC narrative recommends rebasing a specific in-flight PR, and the same drain wave that merges the STATE-SYNC also closes (rather than merges) the in-flight PR, the STATE-SYNC's `nextAction` becomes immediately stale. Surface as a memory under `feedback_researcher_postmerge_statesync_recommended_rebase_target_closed_in_same_drain.md` (variant of the existing `_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md` family).

2. **Bearer line-number drift between successive STATE-SYNCs at the same Mathlib SHA**: not a real drift — both sides are at the same byte content. Same-SHA discrepancies reflect manual-count imprecision in one or both rechecks. Future STATE-SYNCs should treat `gh api` raw-content awk-counting as authoritative over prior STATE-SYNCs' line numbers.

3. **Path-tree re-ranking on PR-closure**: when a multi-path ACT-readiness gate is staged in a prior STATE-SYNC and one of the paths becomes infeasible (e.g. its target PR is closed), the next STATE-SYNC should re-rank the remaining paths with explicit "Path X retired" language to avoid the next picker re-investigating the retired path.

---

## 9. Bearer recheck audit trail (2026-05-16T04:03Z)

```bash
SHA="2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
gh api "/repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Basis/Defs.lean?ref=$SHA" --jq '.content' | base64 -d | awk 'NR<=100 {print NR": "$0}' | grep -E "^(89|76): "
# 76: namespace Module
# 89: structure Basis where

gh api "/repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Basis/Basic.lean?ref=$SHA" --jq '.content' | base64 -d | awk 'NR>=95 && NR<=120 {print NR": "$0}'
# 101: /-- A linear independent family of vectors spanning the whole module is a basis. -/
# 102: protected noncomputable def mk : Basis ι R M :=
# 109: @[simp]
# 110: theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
# 113: theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
# 116: @[simp]
# 117: theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=

gh api "/repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean?ref=$SHA" --jq '.content' | base64 -d | awk 'NR>=232 && NR<=255 {print NR": "$0}'
# 237: noncomputable def basisOfLinearIndependentOfCardEqFinrank {ι : Type*} [Nonempty ι] [Fintype ι]
# 243: theorem coe_basisOfLinearIndependentOfCardEqFinrank {ι : Type*} [Nonempty ι] [Fintype ι]
# 252:     basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm

gh api "/repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Module/ZLattice/Basic.lean?ref=$SHA" --jq '.content' | base64 -d | awk 'NR>=380 && NR<=395 {print NR": "$0}'
# 386: theorem volume_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (ι → ℝ)) :
# 387:     volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).det| := by
```

All four bearers present at expected sections; 0 substantive drift; pin stability holds.

---

**End of S15 STATE-SYNC memo.**
