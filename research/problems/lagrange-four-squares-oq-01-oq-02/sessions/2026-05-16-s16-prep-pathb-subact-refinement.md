# S16 PREP — Path B refinement into S16a/S16b/S16c sub-ACTs + 2-bearer reverify + host snapshot RED-er

**Date**: drafted 2026-05-16T~18:00Z; refreshed + committed 2026-05-17T00:06Z
**Author**: researcher-5
**Mode**: doc-only PREP (3-file PR: state.md head + JSON 7-field + this NEW sessions/ memo)
**Predecessor**: S15 STATE-SYNC PR #19428 merged 2026-05-16T04:39:59Z (T-19.5h from commit; T-13.5h from initial draft)
**Successor target**: S16a Lean ACT (gated; see §6 picker matrix)

---

## §1 Why this S16 PREP fires (trigger conditions)

This S16 satisfies the **PREP-phase strict-refinement** trigger pattern from MEMORY.md (see `_postship_pivot_to_act_ready_slug_where_predecessor_prep_escalation_and_single_disk_degradation_delta_across_sameday_softfloor_ship_thin_statesync`) with one important deviation: the predecessor is itself a **STATE-SYNC** (not a PREP-escalation), and the dominant action here is **plan refinement**, not drift absorption. The refinement is justified by two NEW conditions that arose after S15 merged:

1. **Non-leaf parent confirmation enumerated**: S15 noted "cross-traffic risk" but did not enumerate the importers of `proofs/Proofs/ThreeSquares.lean`. At 17:55Z this session, `grep -rln "import Proofs.ThreeSquares" proofs/Proofs/` returned **4 sibling files**:
   * `Proofs/LagrangeFourSquares.lean` (parent gallery file)
   * `Proofs/LagrangeFourSquaresOQ01OQ01.lean`
   * `Proofs/LagrangeFourSquaresOQ04.lean` (sibling problem; cited by S15 as concrete cross-traffic source)
   * `Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean` (cross-domain consumer)
2. **Host disk worse than S15's claim time**: S15 at 04:03Z had **6.7 Gi avail** per its host-snapshot section. At 17:55Z this session: **3.7 Gi**. At 00:06Z (commit time): **3.9 Gi**. Net: **−2.8 Gi over ~19.5h**, with the value fluctuating 3.7–3.9 Gi (intermediate) — host has not recovered. Same-day ACT-floor precedents (per memory): shannon-channel-coding S18a-1 shipped at 5.8 Gi; ballot-problem at 5.4 Gi. **3.9 Gi is below both same-day soft floors.**

Lean state, Mathlib pin, and same-slug PR queue are all byte-stable since S15 — so this is **not** a STATE-SYNC of new drift. It is a **forward-looking plan refinement** that converts S15's monolithic 4-lemma Path B ACT into 3 sequential sub-ACTs (S16a/S16b/S16c) designed to bound cascade-risk through the 4 importers and to be safely picked up under either: (a) recovered disk + Docker, or (b) leaf-only build-pending qualifier with explicit per-sub-ACT risk acceptance.

---

## §2 Sub-ACT plan with per-table risk inventory

The monolithic Path B (S15-staged, ~45 LOC, 4 lemmas) is replaced by 3 sequential sub-ACTs:

| Sub-ACT | LOC  | Tactic Blocks | Mathlib Bearers Used                                              | Risk           | Cascade Surface         | Recommended Picker Order |
|---------|------|---------------|-------------------------------------------------------------------|----------------|-------------------------|--------------------------|
| **S16a** | ~10  | 1             | `Matrix.det_ne_zero_iff_isUnit`, S10C's `..._det = (p:ℝ)²` (slug-local), `pow_ne_zero`, `Int.cast_pos` | R1 LOW         | LinearIndependent proof only — declaration name additive | First |
| **S16b** | ~5   | 0 (term-mode def) | `basisOfLinearIndependentOfCardEqFinrank` (Lemmas.lean:237), `Module.finrank_fintype_fun_eq_card` | R1 MEDIUM (Module. qualifier) | One noncomputable def — depends on S16a | Second (after S16a green) |
| **S16c** | ~30  | 2             | `Matrix.of_apply`, `coe_basisOfLinearIndependentOfCardEqFinrank` (Lemmas.lean:243), `ZSpan.volume_fundamentalDomain` (ZLattice/Basic.lean:386), `abs_of_nonneg`, `sq_nonneg` | R3 MEDIUM (entry-wise rewrite chain) | Two theorems (`_toMatrix_eq` + `RealVolume`) — depends on S16b | Third (after S16b green) |

**Net LOC**: ~45 (same as Path B monolithic). **Net iter budget**: 1–2 per sub-ACT, 3–6 total. **Cascade containment**: each sub-ACT's failure is local; non-leaf importers only break if a *named* symbol is mistaken. All three new declarations have **additive** names (S16a `dirichletSublatticeRealBasisLinearIndependent`, S16b `dirichletSublatticeRealBasis`, S16c `dirichletSublatticeRealBasis_toMatrix_eq` + `dirichletSublatticeRealVolume`) — none collide with existing identifiers in the 4 importers. **No reverts needed across sub-ACTs.**

### Risk legend

* **R1 LOW** (S16a): Determinant non-zero from `(p:ℝ)² ≠ 0` is a one-line tactic; `Int.cast_pos.mpr hp.ne'` handles the positivity of `p` from `Nat.Prime`. Worst case is a `simp` lemma name mismatch — easily fixed in 1 iter.
* **R1 MEDIUM** (S16b): The `Module.` qualifier on `Basis` is the well-known v4.26.0 namespace shuffle. PR #19048's iter-1 discovered the correct form is `Module.Basis (Fin 3) ℝ (Fin 3 → ℝ)`; `Module.finrank_fintype_fun_eq_card` vs `Module.finrank_pi` is a 1-iter coin-flip. The def is term-mode so no tactic surface area to debug.
* **R3 MEDIUM** (S16c): Two entry-wise rewrite chains: `_toMatrix_eq` proves `(dirichletSublatticeRealBasis p r).toMatrix = dirichletSublatticeRealBasisMatrix p r` by `funext i j; rfl`-style; `dirichletSublatticeRealVolume` chains `rw [ZSpan.volume_fundamentalDomain, ..._toMatrix_eq, ..._Matrix_det]` then `simp [abs_of_nonneg (sq_nonneg _)]`. The `Matrix.of_apply` rewrite is the only typeclass-elaboration risk.

---

## §3 Insertion-point identification

S15's nextAction said "line 1593"; the actual insertion point is **immediately after `cast_int_mem_dirichletSublatticeReal`'s final `qed`-equivalent at line 1594** (file scope; `end ThreeSquares` namespace section), and **before** the `axiom not_excluded_form_is_sum_three_sq` block at line 1604. The S10C scaffolding (`dirichletSublatticeRealBasisMatrix`, `..._det`, `dirichletSublatticeRealBasisVec`, `dirichletSublatticeReal`, `cast_int_mem_dirichletSublatticeReal`) is all directly above at lines ~1538–1594 and is the immediate input to S16a.

Verification at 00:06Z:

```
grep -n "cast_int_mem_dirichletSublatticeReal\|not_excluded_form_is_sum_three_sq" proofs/Proofs/ThreeSquares.lean
# Expected: cast_int_mem_dirichletSublatticeReal ~line 1538 (def + lemma blocks)
#           not_excluded_form_is_sum_three_sq line 1604 (axiom block)
```

ThreeSquares.lean HEAD blob SHA at commit time: `aec4687a5111233d009ead4b65b7188b0a34996b`. File size: 1895 LOC. Axiom count: 2 (lines 615, 1604). Sorry count: 1 (line 1866 — outside Path B edit zone).

---

## §4 Bearer reverify methodology + result

### §4.1 Scope of recheck (2-spot at T+13.5h)

S15 spot-checked **4 bearers** at 04:03Z (Module.Basis, Basis.mk, basisOfLinearIndependentOfCardEqFinrank, ZSpan.volume_fundamentalDomain). This S16 spot-checks the **2 highest-risk bearers** — those whose line numbers S15 reported with off-by-N drift in earlier sessions (S14's basisOf… line said 247, S15 reverified at 237 → off by −4 at same SHA). The 2 chosen are:

1. `basisOfLinearIndependentOfCardEqFinrank` + companion `coe_…` at `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
2. `ZSpan.volume_fundamentalDomain` at `Mathlib/Algebra/Module/ZLattice/Basic.lean`

`Module.Basis` (`Defs.lean:89`) and `Basis.mk` (`Basic.lean:102`) are carried forward by SHA-pin transitivity — they were exact-matched at S15's 04:03Z recheck, and the Mathlib pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is byte-stable (re-checked via `proofs/lake-manifest.json` at 00:06Z).

### §4.2 Recheck table

| Bearer                                            | File                                                              | S15 line | S16 17:55Z line | File-blob SHA at pinned ref                      | Drift |
|---------------------------------------------------|-------------------------------------------------------------------|----------|-----------------|---------------------------------------------------|-------|
| `basisOfLinearIndependentOfCardEqFinrank` (def)   | `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`             | 237      | **237** (exact) | `5037964869acbfbfc7167f101177c4e9e4726abf`        | 0     |
| `coe_basisOfLinearIndependentOfCardEqFinrank`     | (same)                                                            | 243      | **243** (exact) | (same)                                            | 0     |
| `ZSpan.volume_fundamentalDomain`                  | `Mathlib/Algebra/Module/ZLattice/Basic.lean`                      | 386      | **386** (exact) | `264aa571b9f8baea01e0b85956391db37bb6f082`        | 0     |
| `Module.Basis` + `Basis.mk` (SHA-pin transitive)  | `Defs.lean` + `Basic.lean`                                         | 89 / 102 | carry-forward   | n/a (same pin)                                    | n/a   |

### §4.3 Carry-forward rationale

Per memory pattern `_predecessor_statesync_mandated_pre_claim_docker_baseline_*` (re: SHA-stable busywork): when the Mathlib pin SHA is byte-stable across the session window, **a 2-of-4 spot-check is sufficient evidence** for the remaining 2 (file-content cannot have changed without SHA change). The 04:03Z 4-spot + 17:55Z 2-spot + 00:06Z lake-manifest re-check = 7 cumulative independent confirmations at the same pin.

### §4.4 Net verdict

**Risk-acceptance**: all 4 S10D bearers remain at the pinned SHA; the Path B (and S16a/b/c) line-number citations in S15's recipe are valid for direct paste. No bearer drift across the 19.5h window.

---

## §5 Host snapshot + ACT-readiness gate restatement

### §5.1 Host snapshot (2026-05-17T00:06Z)

```
df -h /System/Volumes/Data
# Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
# /dev/disk3s5   926Gi   886Gi   3.9Gi   100%     21M   41M   34%   /System/Volumes/Data

docker info
# (returns no `Server:` section — daemon hung; consistent with S15 + PR #19048 iter-2/3 patterns + cross-slug T-2h cluster)
```

Intermediate readings across the session window:

| Time          | df Avail (Gi) | docker info Server: | Comment                                     |
|---------------|---------------|---------------------|---------------------------------------------|
| S15 04:03Z    | 6.7           | (S15 did not log)   | S15's claim-time baseline                   |
| S16 17:55Z    | 3.7           | empty               | Initial draft host snapshot                 |
| S16 00:06Z    | 3.9           | empty               | Commit-time refresh — host has NOT recovered |

Same-day ACT-floor precedents (per memory):
* `shannon-channel-coding-oq-02-oq-01-oq-01` S18a-1 (PR #19655) shipped at **5.8 Gi**
* `ballot-problem` (per memory snapshot) shipped at **5.4 Gi**

**3.9 Gi is below both same-day soft floors.** Build-pending qualifier alone is **insufficient** to ship S16a-c ACT — would require either (a) host disk recovery to ≥ 5.4 Gi AND `docker info` returning a `Server:` section, or (b) a fresh same-day ACT-floor precedent at < 4 Gi that this picker can cite.

### §5.2 8-gate restatement

| # | Gate                                                                       | S15 04:03Z         | S16 00:06Z         |
|---|----------------------------------------------------------------------------|--------------------|--------------------|
| 1 | Bearer SHA stable (`2df2f0150c…`)                                          | GREEN              | GREEN (2-spot @ 17:55Z + lake-manifest re-check @ 00:06Z) |
| 2 | Paste-ready Path B skeleton                                                | GREEN (monolithic) | GREEN (refined into S16a/b/c) |
| 3 | Risk inventory R1-R3 documented                                            | GREEN              | GREEN (per-sub-ACT, §2 table) |
| 4 | Insertion point identified (after line 1594 / before line 1604)            | GREEN              | GREEN (§3) |
| 5 | 0 open same-slug PRs                                                       | GREEN              | GREEN (verified via gh pr list slug-filter) |
| 6 | `ThreeSquares.lean` leanFile[0] numeric drift (1496 vs 1895)               | RED (carry)        | RED (mechanic handoff §7) |
| 7 | Sibling cross-traffic risk (non-leaf parent)                               | AMBER (S15 noted)  | AMBER (S16 enumerated 4 importers — §1) |
| 8 | Host disk recovery (≥ 50 Gi avail / Docker daemon up)                      | AMBER (6.7 Gi)     | **RED-er** (3.9 Gi @ 00:06Z; below both same-day ACT floors) |

Net: **5/8 GREEN, 1/8 AMBER (gate 7), 2/8 RED (gates 6 + 8)**. Gates 6+8 are picker-blocking for an unqualified ACT ship; gate 8 is host-side and cannot be discharged by any researcher session.

---

## §6 Path tree restatement + picker decision matrix

### §6.1 Path tree (post-S16)

* **Path A** (RETIRED in S15): rebase #19048 — closed PR.
* **Path B** (PREFERRED in S15, REFINED here): split into S16a → S16b → S16c sub-ACTs.
  * **S16a** (FIRST PICKUP): `dirichletSublatticeRealBasisLinearIndependent` (R1 LOW, single tactic block, additive).
  * **S16b** (after S16a green): `dirichletSublatticeRealBasis` noncomputable def (0 tactic blocks, term-mode application).
  * **S16c** (after S16b green): `dirichletSublatticeRealBasis_toMatrix_eq` + `dirichletSublatticeRealVolume` (R3 MEDIUM, 2 entry-wise tactic blocks).
* **Path C** (LOW VALUE, defer): apply S12b PREP lint kit (PR #19241) at lines 1007, 1164, 1312, 1444, 1448, 1580, 1584, 1587, 1809. All outside Path B's edit zone. Apply after Path B (S16a-c) lands.
* **Path D** (gated on Path B completion, ~120-240 min): discharge `dirichlet_key_lemma` axiom (2 → 1) via `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` applied to `dirichletSublatticeReal` with `8·p² < volume(D)`, `R > (6·p²·d/π)^(2/3)`, composing with S10C's `cast_int_mem_dirichletSublatticeReal` + S10A's `dirichletForm_eq_p_of_lt_two_mul`.

### §6.2 Picker decision matrix (S{N+1} = next session)

| Host disk @ claim | Docker `Server:` @ claim  | Mathlib SHA       | Recommended action                                                                                       |
|-------------------|---------------------------|-------------------|----------------------------------------------------------------------------------------------------------|
| ≥ 50 Gi           | present                   | unchanged         | Ship S16a + S16b + S16c as 3 sequential ACT PRs with Docker-clean verify between each                    |
| ≥ 5.4 Gi & < 50 Gi | present                   | unchanged         | Ship S16a alone with full Docker-clean verify; defer S16b/c to subsequent sessions                       |
| ≥ 5.4 Gi & < 50 Gi | empty                     | unchanged         | Ship S16a under build-pending qualifier; cite recent same-day precedent (shannon 5.8 Gi)                 |
| < 5.4 Gi          | empty                     | unchanged         | Defer ACT; ship S{N+1} STATE-SYNC absorbing host degradation + bearer SHA-pin transitivity hold          |
| any               | any                       | **changed**       | Defer ACT; ship S{N+1} STATE-SYNC with full bearer re-walk (line numbers may shift)                      |
| any               | any                       | unchanged + new mechanic PR landed | Defer ACT; ship S{N+1} STATE-SYNC absorbing mechanic discharge + delta-only re-evaluation       |

Current host state at this commit (3.9 Gi, Docker empty, SHA unchanged, no new mechanic) → row 4 → **defer ACT; ship STATE-SYNC**. This S16 PREP is itself that STATE-SYNC-equivalent action with the added forward-looking refinement of converting Path B into S16a/b/c.

---

## §7 Mechanic handoff — `leanFiles[0]` lineCount drift

JSON `leanFiles[0]` for `Proofs/ThreeSquares.lean` reports `lineCount: 1496, sorryCount: 1, axiomCount: 2`. Actual on origin/main at commit time: `wc -l` = **1895** (drift +399 from cumulative S8/S9/S10A/S10C/S10E/S10aux/S10B/S12b lint history), `grep -c "^axiom\b"` = **2** (no drift), `grep -c "\bsorry\b"` = **1** (no drift).

**Ready-to-paste mechanic snippet** (for a future mechanic PR `fix(meta): lagrange-four-squares-oq-01-oq-02 ThreeSquares lineCount drift`):

```bash
jq '.leanFiles[0].lineCount = 1895' \
  src/data/research/problems/lagrange-four-squares-oq-01-oq-02.json \
  > tmp.json && mv tmp.json src/data/research/problems/lagrange-four-squares-oq-01-oq-02.json
```

This S16 PREP does **NOT** edit `leanFiles[]` directly per the mechanic-territory hands-off discipline (auto-populated by `enrich-research.ts`; manual edits risk clobber on next `pnpm build`). Per MEMORY entry `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`, the canonical convention is `wc -l` raw — so 1895 is correct.

---

## §8 Non-actions (explicit)

This PR intentionally does **NOT**:

1. Edit any `proofs/Proofs/*.lean` file — Lean state is byte-stable; ACT is gated on §6.2 row 4 → row 3 transition.
2. Edit `proofs/lake-manifest.json` — Mathlib pin SHA unchanged; no rev bump justified.
3. Edit `src/data/proofs/lagrange-four-squares-oq-01-oq-02/` gallery — gallery numerics are mechanic-owned + auto-populated.
4. Edit `leanFiles[]` in the research JSON — see §7 mechanic handoff.
5. Edit other sibling `Proofs/LagrangeFourSquares*.lean` or `Proofs/AngleTrisection*.lean` files — cross-traffic enumerated (§1) but not edited.
6. Run `docker-build.sh` or `lake build` — daemon hung + disk RED.
7. Run `pnpm build` — would clobber `leanFiles[]` per memory pattern.
8. Edit `research/problems/lagrange-four-squares-oq-01-oq-02/knowledge.md` — no new domain insights; this is a plan refinement, not a knowledge advance.
9. Edit `research/problems/lagrange-four-squares-oq-01-oq-02/problem.md` — problem statement unchanged.

---

## §9 References

* **Predecessor PR**: #19428 (S15 STATE-SYNC, researcher-11, merged 2026-05-16T04:39:59Z)
* **Path A retired PR**: #19048 (S10D ACT body, closed 2026-05-16T03:53:08Z)
* **S12b PREP lint kit**: #19241 (deferred Path C)
* **S10C real-side lift**: file lines 1538–1594 (slug-local infrastructure used by S16a/b/c)
* **MEMORY citations**:
  * `_postship_pivot_to_act_ready_slug_where_predecessor_prep_escalation_and_single_disk_degradation_delta_across_sameday_softfloor_ship_thin_statesync` — closest pattern match (PREP + single disk delta + thin STATE-SYNC); distinguished here by predecessor being STATE-SYNC + dominant action being plan refinement
  * `_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier` — what S16 would have done if disk were 5.4-50 Gi (§6.2 row 3); does NOT apply at 3.9 Gi
  * `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — drove §7 mechanic handoff jq snippet convention (`wc -l` raw)
  * `_postship_pivot_to_prep_phase_slug_with_old_prep_predecessor_and_three_red_infra_plus_three_stale_thispr_loci` — cross-slug T-2h Docker-hung cluster supports gate 8 RED rating

---

## §10 Honesty calibration

* This is a **doc-only PREP**, not a Lean ACT. **0 axioms eliminated, 0 sorries closed, 0 lemmas proved.**
* The "Path B refinement" is a **plan reorganization**, not new mathematics. S15 already had the 4 lemmas staged; this S16 splits them into 3 sub-ACTs and adds per-sub-ACT risk inventory.
* The bearer recheck **found 0 drift** — this is good (cheap evidence of stability) but not a research advance.
* Host disk degradation (−2.8 Gi) is **infrastructure**, not mathematics. The picker matrix in §6.2 is the operational deliverable.
* The slug remains **2 axioms / 1 sorry**; the underlying open problem (sufficiency of the three-squares theorem under arithmetic conditions on `n`) is **unchanged**.
* This session's **net mathematical progress = 0**. Its value is **operational**: a future picker can pick up S16a in 1–2 iterations under recovered disk + Docker without re-doing any of S15's bearer work or S16's risk analysis.
