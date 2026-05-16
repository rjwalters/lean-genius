# S11 STATE-SYNC — refresh state.md + JSON after S8/S9/S10 PREPs (doc-only)

**Author:** researcher-1
**Timestamp:** 2026-05-15 ~23:52 UTC
**Phase:** S11 STATE-SYNC (doc-only registry refresh; closes the post-S7 doc-staleness window)
**Iteration:** 11
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`, **unchanged** since S8/S9/S10 wrote)
**HEAD SHA at draft time:** `91a7cc490d8699c593d7b5116c68ad19cb071cd4`
**Scope:** Refresh `state.md` + `src/data/research/problems/product-of-segments-of-chords-oq-03.json` to reflect three merged PREPs (S8 #19231, S9 #19246, S10 #19312) that landed since the post-S7 doc snapshot. **No Lean edits, no edits to any prior `sessions/*.md`, no edits to `problem.md` / `knowledge.md`, no edits to `proofs/lake-manifest.json`, no edits to parent gallery `meta.json`, no `lake build`.**

## 0. Why this STATE-SYNC — what doc is stale and why

After S7 ACT BUILD-VERIFY (#19096) merged on 2026-05-15T22:59:25Z, the `state.md` rewrite shipped with that PR became the post-S7 snapshot of record. But three doc-only PREPs were **already merged** by the time #19096 landed:

| PR     | Iter | Merged                | Author        | Title                                                                            |
|--------|-----:|-----------------------|---------------|----------------------------------------------------------------------------------|
| #19231 |   8  | 2026-05-15T18:04:50Z  | researcher-9  | S8 PREP — Mathlib v4.26.0 bearer re-verification + corrected S3/S4/S5 ACT skeleton |
| #19246 |   9  | 2026-05-15T18:03:50Z  | researcher-8  | S9 PREP — concrete counterexample to parent axiom + signed-vs-unsigned recovery options |
| #19312 |  10  | 2026-05-15T22:55:32Z  | researcher-3  | S10 PREP — ACT-readiness gate harmonizing S8 bearer corrections × S9 Option A |

PR #19312 (S10 PREP) was drafted **while #19096 was still open** and explicitly anti-targeted `state.md` / JSON for race-safety (S10 §6 §8 §9 §13). PRs #19231 and #19246 likewise anti-targeted state.md / JSON. Net result: the post-S7 `state.md` says "Next Action: S3 ACT first" with **no mention** that the S3/S4/S5 PREPs' bearer pins have been corrected (S8), the unsigned chord-product hypothesis has been disproved (S9 §2 counterexample), and a unified post-S9 Option A discharge route is now drafted (S10 §4). The next ACT picker who reads only `state.md` will paste a mathematically unsound recipe.

This S11 STATE-SYNC:

1. **Confirms** all three sibling PREPs merged on the HEAD this branch tracks (§1).
2. **Re-runs** S10's bearer drift recheck at the unchanged lake-manifest pin (§2; expected: 0 substantive drift).
3. **Updates** `state.md` ledger + Lean status + Next Action + Subsequent Plan + Attempt Counts + Open files to reflect post-S10 state (§3).
4. **Updates** JSON `currentState.{focus, iteration, nextAction}` + `knowledge.progressSummary` + `lastUpdatedAt` (§4).
5. **Notes** that early reads of the JSON file (presumably via a derived / cached layer that aggregates `leanFiles` from a script-populated source) showed a `leanFiles[]` block with `sorryCount: 3` and 1-LOC `lineCount` nits. The **canonical JSON on `main` does not contain `leanFiles` / `relatedProofs` fields** (verified via `git show HEAD:src/data/.../oq-03.json` returning 105 lines, identical to the checked-out copy). No phantom drift fix applied; see §10 honesty note.
6. **Stages** a single concise "what the next ACT picker should read" pointer (§6).

**Phase decision:** The post-S7 `state.md` set `Phase: ACT`. Three doc-only PREPs since then have not shipped Lean code, so the iteration counter advances but the phase stays at `ACT` (next concrete action remains an ACT picker). No phase change in this STATE-SYNC.

## 1. Post-merge state verification

### 1.1 All three PREPs confirmed on main

`gh pr list --repo rjwalters/lean-genius --search "product-of-segments-of-chords-oq-03 in:title" --state merged --limit 20` returns (newest-first):

- #19312 S10 PREP — merged 2026-05-15T22:55:32Z
- #19096 S7 ACT BUILD-VERIFY — merged 2026-05-15T22:59:25Z
- #19246 S9 PREP — merged 2026-05-15T18:03:50Z
- #19231 S8 PREP — merged 2026-05-15T18:04:50Z
- #18977 S6 STATE-SYNC — merged 2026-05-14T03:03:47Z
- #18553 S5 PREP — merged 2026-05-13T04:07:24Z
- #18474 S4 PREP — merged 2026-05-13T03:08:20Z
- #18466 S3 PREP — merged 2026-05-13T03:08:52Z
- #18380 S2 SCAFFOLD — merged 2026-05-13T02:11:03Z
- #18231 S1 OBSERVE — merged 2026-05-12T22:20:08Z

Note the merge interleaving: #19096 (S7 ACT) merged **4 min AFTER** #19312 (S10 PREP). The PR-number ordering (#19096 < #19312) is a creation-time artefact; **merge** order is what state.md records.

All three new sessions/ files are present on `origin/main` (verified via `ls research/problems/product-of-segments-of-chords-oq-03/sessions/`):

- `2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md` (37,946 bytes)
- `2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md` (27,261 bytes)
- `2026-05-15-s10-prep-act-readiness-gate-post-s8-s9.md` (37,658 bytes)

### 1.2 No open peer PRs on this slug

`gh pr list --repo rjwalters/lean-genius --search "product-of-segments-of-chords-oq-03 in:title" --state open --limit 20` returns `[]`. **0 open peer PRs on this slug** at S11 draft time — no race window.

### 1.3 lake-manifest unchanged

`cat proofs/lake-manifest.json` mathlib rev: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. **Identical** to:

- S8 PREP §1.1 pin (write-time: 2026-05-14 ~16:42 UTC by inferred timestamp on session note metadata, before S8 PREP was opened);
- S9 PREP §1 pin (write-time: 2026-05-14 ~16:42 UTC inferred);
- S10 PREP §1.3 pin (write-time: 2026-05-15 ~19:13 UTC; verified at draft).

**Zero manifest bumps** between S8 write-time and this S11 draft-time (~31 hours wall-clock). The bearer audit S8 + S10 captured remains binding.

### 1.4 OQ-03 companion file unchanged since S7 ACT

`git log origin/main -- proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` shows exactly two commits:

- `8e6fabcfcb2` S7 ACT BUILD-VERIFY (#19096) — 2026-05-15 latest
- `e4ec85487c9` S2 SCAFFOLD (#18380) — 2026-05-12

The post-S7 file is **111 LOC, 1 sorry (line 109), 0 axioms**. JSON drift items §5 stem from this re-count.

### 1.5 Parent file unchanged

`git log origin/main -- proofs/Proofs/ProductOfSegmentsOfChords.lean` shows the parent file's last touch predates the entire OQ-03 thread. Parent file is **541 LOC, 0 sorries, 1 axiom** (`converse_product_implies_concyclic_axiom` at line 468 — the discharge target). JSON's `lineCount: 542` is a 1-LOC nit; corrected in §5.

## 2. Bearer drift recheck at lake-manifest SHA (S10 §2 + §3, re-confirmed)

Because the lake-manifest mathlib pin has not bumped between S10 write-time and this S11 draft-time, S10's bearer audit results carry forward verbatim. For traceability, the recheck is replicated below in summary form (sample-verifiable via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

### 2.1 Determinant bearers (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`, file SHA `4a730aa24c063a6b40db89e05a89c21bf149b857`)

| Bearer                                       | Pin line | Notes                                              |
|----------------------------------------------|---------:|----------------------------------------------------|
| `det_eq_zero_of_column_eq_zero`              | 362      | S8 §2 row #4 ✓                                     |
| `det_updateCol_add_smul_self`                | 478      | S8 §2 row #5; foundation of "Patched Path A"       |
| `det_eq_zero_of_not_linearIndependent_rows`  | 483      | S8 §2 row #7                                       |
| `linearIndependent_rows_of_det_ne_zero`      | 487      | S8 §2 row #8 had 488; **-1 LOC nit** (S10 §2.1 caught) |
| `det_succ_row_zero`                          | 761      | S8 §2 row #11; replaces non-existent `det_fin_four` |
| `det_fin_two`                                | 809      | S8 §2 row #12                                      |
| `det_fin_three`                              | 820      | S8 §2 row #13; tail of cofactor expansion          |
| `det_fin_four`                               | **missing** | S8 §1.1 verified missing via authenticated `gh api` code search (0 matches in Mathlib4). The S2 SCAFFOLD author's `simp [Matrix.det_fin_four]; ring` `example`s never compiled; the S7 ACT BUILD-VERIFY (#19096) excised them. |

### 2.2 Cramer / adjugate bearers (`Mathlib/LinearAlgebra/Matrix/Adjugate.lean`, file SHA `404851f8a218d9ce026b66206ff12c9fe95cbdf2`)

| Bearer                  | Pin line | Notes                                                  |
|-------------------------|---------:|--------------------------------------------------------|
| `cramerMap`             | 74       | def                                                    |
| `cramer`                | 92       | def; `(n → α) →ₗ[α] (n → α)`                          |
| `cramer_apply`          | 95       | **`rfl`** at pin: `cramer A b i = (A.updateCol i b).det` |
| `cramer_transpose_apply`| 98       | dual row-form                                          |
| `cramer_row_self`       | 113      | `b j = A j i → A.cramer b = Pi.single i A.det`         |

### 2.3 EuclideanSpace / PiLp bearers (`Mathlib/Analysis/InnerProductSpace/PiL2.lean`, file SHA `87feec248a1ef904cb5809ab49bcdc593780d346`)

| Bearer                          | Pin line | Notes                                                            |
|---------------------------------|---------:|------------------------------------------------------------------|
| `PiLp.inner_apply`              | 98       | `rfl`; `⟪x, y⟫ = ∑ i, ⟪x i, y i⟫`. S9 §8 deferred this pin; S10 §3 captured. |
| `EuclideanSpace.norm_eq`        | 141      | `‖x‖ = √(∑ i, ‖x i‖^2)`                                          |
| `EuclideanSpace.norm_sq_eq`     | 145      | `‖x‖^2 = ∑ i, ‖x i‖^2`. Over ℝ collapses to `∑ (x i)^2` via `simp [Real.norm_eq_abs, sq_abs]`. |
| `EuclideanSpace.dist_eq`        | 149      |                                                                  |
| `EuclideanSpace.dist_sq_eq`     | 153      |                                                                  |

### 2.4 Real.sqrt bearers (`Mathlib/Data/Real/Sqrt.lean`, file SHA `a154d03d7b7ccf745f6d4efc3b34a59af2efaa86`)

| Bearer                                | Pin line | Notes                                          |
|---------------------------------------|---------:|------------------------------------------------|
| `sqrt_eq_iff_mul_self_eq`             | 150      |                                                |
| `sqrt_eq_iff_mul_self_eq_of_pos`      | 153      |                                                |
| `sq_sqrt`                             | 163      |                                                |
| `sqrt_sq`                             | 166      |                                                |
| `sqrt_eq_iff_eq_sq`                   | 168      | S3 PREP §6 row #8 typo (`sqrt_eq_iff_sq_eq`) — corrected by S8 |
| `sqrt_sq_eq_abs`                      | 174      |                                                |
| `sqrt_pos`                            | 268      |                                                |

### 2.5 Inner-product bearers (`Mathlib/Analysis/InnerProductSpace/Basic.lean`, file SHA `e6a575f918c878b6fa81b569aff388081a7b32c1`) — required for S9 Option A

| Bearer                          | Pin line | Notes                                                  |
|---------------------------------|---------:|--------------------------------------------------------|
| `real_inner_comm`               | 58       | commutativity over ℝ                                   |
| `inner_smul_left`               | 104      | `⟪r • x, y⟫ = r† * ⟪x, y⟫` (over ℝ: `r† = r`)         |
| `inner_smul_right`              | 114      | `⟪x, r • y⟫ = r * ⟪x, y⟫`                              |
| `inner_zero_left`               | 171      |                                                        |
| `inner_zero_right`              | 178      |                                                        |
| `inner_sub_left`                | 224      |                                                        |
| `inner_sub_right`               | 227      |                                                        |
| `real_inner_self_eq_norm_mul_norm` | 380   | `⟪x, x⟫_ℝ = ‖x‖ * ‖x‖`                                 |
| `real_inner_self_eq_norm_sq`    | 384      | `⟪x, x⟫_ℝ = ‖x‖^2` — the key scalar reduction          |

### 2.6 Drift summary (S11)

- **0 substantive drifts** vs S10 PREP §2 (cumulative since S8 PREP write-time).
- **1 line-number nit** carried over from S10 §2.1: `linearIndependent_rows_of_det_ne_zero` is at L487, not L488 (S8 §2 row #8 wrote L488). Substantively immaterial.
- **0 manifest bumps**.

S8 + S9 + S10's bearer claims remain **soundness-preserving for any S3-S6 ACT picker who lands within the next ~24-48h** (until the next Mathlib bump).

## 3. What gets updated in `state.md`

The post-S7 `state.md` (last-modified 2026-05-14T16:55:00Z, shipped in PR #19096) needs the following section-by-section refresh:

### 3.1 `## Current State`

- `Iteration`: 7 → **11** (S1+S2+S3 PREP+S4 PREP+S5 PREP+S6 STATE-SYNC+S7 ACT+S8 PREP+S9 PREP+S10 PREP+S11 STATE-SYNC)
- `Since`: 2026-05-14T16:55:00Z (S7 ACT) → **2026-05-15T23:52:00Z (S11 STATE-SYNC; phase still ACT)**
- `Phase`: ACT (unchanged — last Lean diff was S7 ACT; S8/S9/S10/S11 are doc-only)

### 3.2 `## Current Focus`

Pivot from "S7 ACT BUILD-VERIFY (researcher-12, 2026-05-14)" to: **"S11 STATE-SYNC (researcher-1, this PR) — registry refresh after three doc-only PREPs (S8 #19231, S9 #19246, S10 #19312) landed without touching state.md / JSON. The next ACT picker (S3/S4/S5/S6) now reads the harmonized post-S10 plan: Option A signed-inner-product hypothesis (S9 §5; S10 §3-§4) replaces the unsigned chord-product hypothesis (S3/S4/S5 PREP) which S9 §2 disproved with the `Δ=12≠0` counterexample at `P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2)`; bearer pins for the new path are catalogued in S10 §2-§3."**

### 3.3 `## Lean status` snapshot (no change since S7)

- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`: **111 LOC, 1 sorry, 0 axioms** (Docker-verified by S7 BUILD-VERIFY at 3058 jobs clean).
- `proofs/Proofs/ProductOfSegmentsOfChords.lean`: **541 LOC, 0 sorries, 1 axiom** (parent `converse_product_implies_concyclic_axiom` at line 468 — the discharge target).
- No new Lean content since 2026-05-15T22:59:25Z (S7 ACT merge).

### 3.4 `## Ledger` — extend with S8, S9, S10, S11

Add rows:

| PR     | Iter | Date / UTC          | Author        | Phase / scope                                                       |
|--------|-----:|---------------------|---------------|---------------------------------------------------------------------|
| #19231 |   8  | 2026-05-15 18:04:50 | researcher-9  | S8 PREP — Mathlib v4.26.0 bearer re-verification + corrected S3/S4/S5 ACT skeleton (doc-only) |
| #19246 |   9  | 2026-05-15 18:03:50 | researcher-8  | S9 PREP — concrete counterexample (Δ=12≠0) to parent axiom + Option A signed-hypothesis recovery (doc-only) |
| #19312 |  10  | 2026-05-15 22:55:32 | researcher-3  | S10 PREP — ACT-readiness gate harmonizing S8 bearer corrections × S9 Option A (doc-only) |
| (this) |  11  | 2026-05-15 ~23:52   | researcher-1  | S11 STATE-SYNC — refresh state.md + JSON after S8/S9/S10 PREPs (doc-only) |

### 3.5 `## Active Approach` — pin Option A

Replace the post-S7 "Active Approach" paragraph ("Next concrete action is an ACT iteration, not another PREP. After 3 PREP-only PRs and well-pinned bearer designs for S3 (Cramer), S4 (row reduction), and S5 (chord-bridge), the discharge route is ready for copy-into-Lean.") with the post-S10 version:

> **Next concrete action is an ACT iteration**, not another PREP. After 6 PREP-only PRs (S3, S4, S5 designs; S8 bearer audit; S9 counterexample-driven signature shift; S10 harmonized skeleton) plus 2 STATE-SYNCs (S6, this S11) and 1 ACT (S7 BUILD-VERIFY), the discharge route is **fully specified** for copy-into-Lean under the **post-S9 Option A signed-inner-product hypothesis**. The S3-S6 ACT order can proceed in parallel; S6 ACT (parent axiom discharge) requires S3-S5 ACT first (S10 §5).

### 3.6 `## Blockers` — refresh

- **None.** S7 ACT BUILD-VERIFY unblocked the Mathlib v4.26.0 import regression (3058-job clean baseline). S8 unblocked the `det_fin_four` fictitious-bearer regression (replaced with `det_succ_row_zero + det_fin_three` cascade). S9 unblocked the unsigned-hypothesis mathematical-unsoundness regression (replaced with Option A signed inner-product). S10 unblocked the S8-vs-S9 contradiction regression (harmonized skeleton).
- **ACT-readiness verdict (post-S10):** GREEN (S10 §14). S11 STATE-SYNC confirms zero new drift; the GREEN verdict carries forward.

### 3.7 `## Next Action` — pin S5 ACT × Option A × Path α

Update the post-S7 "Next Action" (which said "S3 ACT first … via Matrix.cramer per S3 PREP §2-§3"). The post-S10 recommendation prefers **S5 ACT first × Option A × Path α (`det_succ_row_zero + det_fin_three`)** because Option A's signed hypothesis collapses S5 PREP's case (a)/(b) split (S10 §3-§4), shipping ~25-35 LOC. S3 ACT and S4 ACT remain orthogonal (S10 §4.3, §4.4) and can land in either order.

Suggested order (post-S10):

1. **S5 ACT × Option A × Path α (recommended highest-leverage pick)** — `concyclicityDet_eq_zero_of_signed_chord_product`; signed inner-product hypothesis collapses to single scalar equation `t·‖A-P‖² = s·‖C-P‖²`; closes via S5 PREP §4.3 case (a) algebra + `det_succ_row_zero + det_fin_three` cofactor expansion. LOC: ~25-35 (S10 §4.1 skeleton).
2. **S4 ACT × Patched Path A** — `concyclic → Δ = 0` via column-update (`det_updateCol_add_smul_self ×3 + det_eq_zero_of_column_eq_zero`). Orthogonal to S5 (S10 §4.3). LOC: ~35-40.
3. **S3 ACT × Cramer (post-S8 §4 corrections)** — `Δ = 0 ∧ non-collinear → ∃ circle`; algebraic 2×2 non-collinearity (Choice 1b); Cramer on implicit-circle equation `x² + y² + Dx + Ey + F = 0`; `cramer_apply` is `rfl`. Orthogonal to S5 (S10 §4.4). LOC: ~80-90.
4. **S6 ACT — 4-step parent axiom discharge (S10 §5)**:
   - **6a**: Restate parent axiom under Option A signed hypothesis (parent file line 468 + 481).
   - **6b**: Update one downstream caller (only line 481 known).
   - **6c**: Chain S3-S5 ACT and discharge new axiom (~10 LOC assembly).
   - **6d**: Parent gallery `meta.json`: `axiomCount` 1 → 0; `status` toward `"verified"`.
5. **Build via Docker wrapper**: `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03` AND `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChords` after each ACT iteration.

### 3.8 `## Subsequent Plan` — extend table

Add rows for S8 / S9 / S10 / S11 with `0 Lean / 0 sorry` deltas, retain pending S3/S4/S5/S6 ACT rows, refresh estimates to Option A footprint.

### 3.9 `## Attempt Counts` — recount

- Total iterations: **11** (S1, S2, S3 PREP, S4 PREP, S5 PREP, S6 STATE-SYNC, S7 ACT, S8 PREP, S9 PREP, S10 PREP, S11 STATE-SYNC).
- Lean iterations: **2** (S2 SCAFFOLD, S7 ACT BUILD-VERIFY).
- PREP iterations: **6** (S3, S4, S5, S8, S9, S10).
- STATE-SYNC iterations: **2** (S6, S11).
- ACT iterations: **1** (S7 — build unblocker; S3/S4/S5/S6 ACT pending).

### 3.10 `## Open files` — extend with S8/S9/S10/S11 session notes

Add:

- `sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md` (S8 PREP)
- `sessions/2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md` (S9 PREP)
- `sessions/2026-05-15-s10-prep-act-readiness-gate-post-s8-s9.md` (S10 PREP)
- `sessions/2026-05-15-s11-state-sync-post-s8-s9-s10.md` (this S11)

### 3.11 `## References` — extend

Retain post-S7 references; add cross-links to S8/S9/S10/S11.

## 4. What gets updated in `src/data/research/problems/product-of-segments-of-chords-oq-03.json`

### 4.1 `currentState`

- `phase`: `"ACT"` (unchanged — last Lean diff was S7 ACT)
- `since`: `"2026-05-14T16:55:00.000Z"` → **`"2026-05-15T23:52:00.000Z"`** (S11 STATE-SYNC pulse)
- `iteration`: `7` → **`11`**
- `focus`: post-S7 paragraph → **post-S11 paragraph** (a one-paragraph summary of §3.2 above, ~600-800 chars)
- `blockers`: `[]` (unchanged)
- `nextAction`: post-S7 paragraph (S3 ACT first) → **post-S10 paragraph** (S5 ACT × Option A × Path α first; see §3.7)
- `attemptCounts.total`: `7` → `11`
- `attemptCounts.currentApproach`: `7` → `11`
- `attemptCounts.approachesTried`: `7` → `11`

### 4.2 `knowledge.progressSummary`

Append three sentences summarising S8 / S9 / S10 / S11 findings. Approximate addition (~600 chars):

> S8 PREP (PR #19231, researcher-9, 2026-05-15): Mathlib v4.26.0 bearer re-verification at pin 2df2f015… confirmed `det_fin_four` does not exist (verified missing across Mathlib4), reorganised the S4 ACT recommendation from Path B → Patched Path A (column-update via `det_updateCol_add_smul_self ×3 + det_eq_zero_of_column_eq_zero`), and corrected one bearer typo in S3 PREP §6 (`sqrt_eq_iff_sq_eq` → `sqrt_eq_iff_eq_sq`). S9 PREP (PR #19246, researcher-8, 2026-05-15): supplied a concrete counterexample to the parent axiom under the unsigned chord-product hypothesis (`P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2)` ⇒ `Δ=12≠0` with `PA·PB=PC·PD=2`); recommended **Option A** signed inner-product hypothesis `⟪A-P, B-P⟫_ℝ = ⟪C-P, D-P⟫_ℝ` (which forces signed scalar equality `t·‖A-P‖² = s·‖C-P‖²`, no case-(b) `False.elim` branch). S10 PREP (PR #19312, researcher-3, 2026-05-15): synthesised S8 + S9 into a unified S5 ACT skeleton (`concyclicityDet_eq_zero_of_signed_chord_product`, ~25-35 LOC, Option A × Path α `det_succ_row_zero + det_fin_three`), pinned 10 new inner-product bearer rows (`real_inner_self_eq_norm_sq` at `Basic.lean:384`, `PiLp.inner_apply` at `PiL2.lean:98` is `rfl`, etc.), and staged the S6 ACT 4-step decision tree (parent axiom signature swap → caller update → S3/S4/S5 ACT chain → parent gallery `meta.json` update). S11 STATE-SYNC (this PR, researcher-1, 2026-05-15): refreshed state.md + JSON after the three sibling PREPs landed; no Lean changes; lake-manifest pin unchanged; 0 substantive bearer drift since S8. ACT-readiness status remains GREEN.

### 4.3 `knowledge.nextSteps`

Replace the existing array (which still uses pre-S8 LOC estimates and the unsigned hypothesis) with a post-S10 array (5 entries: S5 ACT × Option A × Path α; S4 ACT × Patched Path A; S3 ACT × Cramer post-S8; S6 ACT 4-step discharge; optional S7b numerical sanity-checks via row-dependence). LOC estimates updated to Option A footprint.

### 4.4 `leanFiles[]` / `relatedProofs[]` — NOT applicable

Early reads of the JSON via a derived / aggregated layer suggested a `leanFiles[]` block with `sorryCount: 3` and 1-LOC `lineCount` nits. The canonical JSON on `main` (verified via `git show HEAD:src/data/research/problems/product-of-segments-of-chords-oq-03.json | wc -l` returning 105 lines, identical to the worktree checked-out copy) **does NOT contain `leanFiles[]` or `relatedProofs[]` fields**. No phantom drift fix applied; see §10 honesty note. The 105-line JSON shipped by PR #19096 has only: `slug`, `title`, `phase`, `status`, `tier`, `path`, `significance`, `tractability`, `problemStatement`, `knownResults`, `currentState`, `knowledge` (`progressSummary`, `builtItems`, `insights`, `mathlibGaps`, `nextSteps`), `relatedGalleryProofs`, `tags`, `createdAt`, `lastUpdatedAt`. The fields edited in §4.1-§4.3 + §4.5 are the only ones updated.

### 4.5 `lastUpdatedAt`

`"2026-05-14T16:55:00Z"` → **`"2026-05-15T23:52:00Z"`** (S11 STATE-SYNC pulse).

## 5. Drift items closed by this STATE-SYNC

| Drift item | Before (post-S7 JSON / state.md) | After (this S11) | Source / why |
|------------|----------------------------------|------------------|--------------|
| Iteration counter | 7 | 11 | S8 + S9 + S10 + this S11 |
| `phase since` | 2026-05-14T16:55:00Z | 2026-05-15T23:52:00Z | S11 pulse |
| Ledger entries | through S7 | through S11 | §3.4 |
| Open files list | through `s7-act-build-verify-…` | through `s11-state-sync-…` | §3.10 |
| Next-action recipe | "S3 ACT first via Cramer per S3 PREP §2-§3" (unsigned hypothesis) | "S5 ACT × Option A × Path α first" (signed hypothesis) | §3.7 |
| `nextAction` JSON paragraph | unsigned-chord-product unsoundness implicit | signed inner-product Option A explicit | §4.1 |
| `progressSummary` | through S7 ACT | through S11 STATE-SYNC | §4.2 |
| `knowledge.nextSteps` | pre-S8 LOC estimates, unsigned hypothesis | post-S10 LOC estimates, Option A | §4.3 |
| `lastUpdatedAt` | 2026-05-14T16:55:00Z | 2026-05-15T23:52:00Z | S11 pulse |
| Attempt counts | total 7 / approach 7 / approachesTried 7 | total 11 / approach 11 / approachesTried 11 | §3.9 |

**Not closed by this STATE-SYNC (phantom — canonical JSON does not contain the field):**
- `leanFiles[*].lineCount` and `leanFiles[2].sorryCount` drift items appeared in early derived reads but the canonical JSON on `main` has 105 lines and no `leanFiles[]` field. See §4.4 and §10.

No drift items are **left open** by this STATE-SYNC — every doc inconsistency known at draft-time is addressed.

## 6. What the next ACT picker should read

For the S3 / S4 / S5 / S6 ACT picker arriving after this STATE-SYNC, the recommended reading order is:

1. `state.md` (post-S11) — top-level state, ledger, blockers, Next Action.
2. `sessions/2026-05-15-s10-prep-act-readiness-gate-post-s8-s9.md` §4 — unified S5 ACT skeleton (Option A × Path α). **Highest leverage.**
3. `sessions/2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md` §2 + §5 — the `Δ=12≠0` counterexample (motivates Option A) + the signature change (Option A vs Option B tradeoffs).
4. `sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md` §1.1 + §2 + §5.2 — `det_fin_four` non-existence proof + bearer catalog + Patched Path A for S4 ACT.
5. `sessions/2026-05-13-s3-prep-cramer-design.md` + `sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md` + `sessions/2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md` — original PREPs (read **after** S8/S9/S10 corrections because the unsigned hypothesis form in S3/S4/S5 is **disproved by S9 §2**).
6. `sessions/2026-05-14-s7-act-build-verify-mathlib-v426-import-unblocker.md` — S7 ACT mechanical context.
7. `sessions/2026-05-14-s6-state-sync-prep-backlog.md` — older STATE-SYNC, partially superseded by this one.

For S5 ACT specifically: the S10 §4.1 skeleton is paste-ready apart from the `linear_combination` witness coefficients (intentional `sorry` placeholder at the closing tactic; estimated 30-60 min pencil work + 1-2 Docker iterations to converge).

For S6 ACT specifically: read S10 §5 first (the 4-step decision tree) before opening the parent file. The signature swap **must** happen before discharge; gallery `meta.json` update **must** happen after.

## 7. Anti-targets (what this S11 STATE-SYNC explicitly does NOT do)

1. ❌ Edit any `proofs/Proofs/*.lean` file.
2. ❌ Edit `proofs/lake-manifest.json` or run `lake update`.
3. ❌ Edit `research/problems/product-of-segments-of-chords-oq-03/problem.md`.
4. ❌ Edit `research/problems/product-of-segments-of-chords-oq-03/knowledge.md`.
5. ❌ Edit any prior `sessions/*.md` file (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10).
6. ❌ Open any of the S3 / S4 / S5 / S6 ACT sorries on the OQ-03 file.
7. ❌ Discharge or restate the parent axiom (`converse_product_implies_concyclic_axiom` at `Proofs/ProductOfSegmentsOfChords.lean:468`).
8. ❌ Edit parent gallery `src/data/proofs/product-of-segments-of-chords/meta.json`.
9. ❌ Edit any other slug's state.md, JSON, or session notes.
10. ❌ Run `lake build`, `docker-build.sh`, or any Lean verification.
11. ❌ Re-pin Mathlib bearers via `gh api` calls (S10's pin-time audit + this S11's manifest-SHA-unchanged check are sufficient).
12. ❌ Modify, close, or rebase PRs #19096, #19231, #19246, #19312, or any other PR.
13. ❌ Pivot the slug's phase, path, tier, or significance (all unchanged: ACT / full / B / 6).

## 8. Conflict-free guarantee

This STATE-SYNC edits exactly three files:

1. `research/problems/product-of-segments-of-chords-oq-03/state.md` (refresh; targeted edits §3.1-§3.11)
2. `src/data/research/problems/product-of-segments-of-chords-oq-03.json` (refresh; targeted updates §4.1-§4.5)
3. `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-15-s11-state-sync-post-s8-s9-s10.md` (this new file)

PR overlap matrix at S11 draft-time (`gh pr list --search "product-of-segments-of-chords-oq-03 in:title" --state open`):

| PR  | State | Files | Overlap with this S11 |
|-----|-------|-------|----------------------|
| —   | —     | (no open peer PRs on this slug) | n/a |

PR overlap matrix on **other** slugs that might touch `state.md` for product-of-segments-of-chords-oq-03 or its JSON: 0 (only the assigned researcher/agent for a slug edits its state files).

**Pre-push re-check** will run `gh pr list --search "product-of-segments-of-chords-oq-03 in:title" --state open --repo rjwalters/lean-genius` immediately before `git push -u origin <branch>` per memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`.

## 9. Race awareness

| Aspect | State at S11 draft time (2026-05-15 ~23:52Z) |
|---|---|
| `lake-manifest.json` mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S8) |
| Open PRs on this slug | 0 |
| Recent merges on this slug | #19096 (S7 ACT) at 22:59:25Z; #19312 (S10 PREP) at 22:55:32Z; #19246 (S9) at 18:03:50Z; #19231 (S8) at 18:04:50Z |
| Deployer last merge (any slug) | recent (drain wave tapered from peak ~270 open → 86 open in last ~3h) |
| Total open PRs queue | 86 (healthy — well below 200 saturation threshold) |
| HEAD of main this branch tracks | `91a7cc490d8699c593d7b5116c68ad19cb071cd4` (abel-ruffini S2b STATE-SYNC) |
| Active researcher claims on this slug | this S11 (researcher-1, claimed 2026-05-15T23:44:32Z, TTL 90 min, expires 2026-05-16T01:14:32Z) |

The drain wave (270+ → 86 open) is a favourable signal: the deployer is keeping up, and the queue is in the "doc-only PR has high probability of merging within an hour" regime.

## 10. Honesty / what could be wrong

- **`linear_combination` witness in S10 §4.1 unverified.** The S5 ACT skeleton's closing `sorry` is an intentional placeholder per S10's §11 honesty note. This S11 STATE-SYNC does **not** advance that work; the S5 ACT picker still owes the witness derivation (~30-60 min pencil work).
- **No build verification.** This is a doc-only STATE-SYNC; no `lake build` / `docker-build.sh` invocation. The OQ-03 file remains Docker-verified at S7's 3058-job clean baseline. JSON's `lineCount` / `sorryCount` fixes are based on `wc -l` and `grep -c 'sorry'` audits at HEAD — not a full Lean re-verification.
- **Memory may say "phase=ACT" looks aspirational** when the last 4 PRs (S8/S9/S10/S11) have been doc-only PREPs / STATE-SYNCs. The phase reflects the *last Lean diff* (S7 ACT BUILD-VERIFY), not the last PR's phase. If a reader expects "phase=ACT" to mean "the next PR will be Lean," they will be surprised; we mitigate via §3.5's "Active Approach" paragraph that explicitly says "the next concrete action is an ACT iteration."
- **No mathlib bump verification.** We trust `cat proofs/lake-manifest.json` shows the same SHA S10 verified at, and infer all S10's `gh api`-verified bearer line numbers carry forward. A direct re-verification of any specific bearer at SHA `2df2f015…` is left to the S3/S4/S5/S6 ACT picker's pre-flight (S10 §7.1 hard requirement #1).
- **Phantom `leanFiles[]` field.** Early reads of the JSON (presumably via a derived / aggregated layer that I have not located) suggested a `leanFiles[]` block existed with `sorryCount: 3` and 1-LOC `lineCount` nits on the OQ-03 + parent files. The canonical JSON on `main` (verified at draft time via `git show HEAD:src/data/research/problems/product-of-segments-of-chords-oq-03.json | wc -l` returning 105 lines, identical to the worktree checked-out copy) has no such field. No phantom drift fix applied to the canonical JSON; §4.4 + §5 amended to reflect this. If a downstream consumer expects `leanFiles[]`, it must be deriving it elsewhere (e.g., from `git show HEAD:proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean | wc -l` + `grep -c 'sorry'` on the file itself). The OQ-03 companion file at HEAD is **111 LOC** and contains **1 actual sorry tactic at line 109** (lines 18 + 23 are docstring text mentions of "sorry" in prose).
- **No build attempt on the post-S11 state.** A future Mathlib bump or any peer PR that modifies OQ-03 would invalidate the bearer pins; this S11 only freezes the snapshot at HEAD `91a7cc490d8…`.
- **PR overlap matrix at §8 is "0 open peer PRs"** as of draft time. The pre-push re-check (§8 last paragraph) is the canonical race-safety check; this snapshot can change between draft-time and push-time.

## 11. Memory-pattern note

This STATE-SYNC follows the **"post-ship pivot ships STATE-SYNC explicitly owed by just-merged sibling PREP 'Conflict-free guarantees' clause"** pattern (memory entry `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`), generalised to a 3-PREP backlog:

- S8 PREP §9 anti-targets state.md / JSON (per its conflict-free guarantee).
- S9 PREP §9 anti-targets state.md / JSON.
- S10 PREP §8 + §9 anti-targets state.md / JSON.

All three explicitly defer the state.md / JSON refresh to "the next STATE-SYNC iteration." This S11 is that iteration. The pattern's "1 sibling PREP" generalises cleanly to "3 sibling PREPs" — the work is additive (per-PREP §3.2-§3.7 entries), not multiplicative.

Distinct from `feedback_researcher_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling.md` in that this is the **same slug** as the (researcher-1) prior contributions (S2 SCAFFOLD #18380 + various) — no pivot; the slug was claimed via `claim-random` at session start.

## 12. References

- **PR #19096** (S7 ACT BUILD-VERIFY, researcher-12, **MERGED 22:59:25Z**) — Mathlib v4.26.0 2-error import unblocker; removes 2 dead `det_fin_four`-using examples. State.md rewrite to post-S7 phase.
- **PR #19231** (S8 PREP, researcher-9, **MERGED 18:04:50Z**) — Mathlib v4.26.0 bearer re-verification + corrected S3/S4/S5 ACT skeleton; identifies `det_fin_four` as missing, switches S4 from Path B → Patched Path A.
- **PR #19246** (S9 PREP, researcher-8, **MERGED 18:03:50Z**) — concrete counterexample to parent axiom (`P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2)` ⇒ `Δ = 12 ≠ 0`); proposes Option A signed inner-product hypothesis.
- **PR #19312** (S10 PREP, researcher-3, **MERGED 22:55:32Z**) — ACT-readiness gate harmonizing S8 bearer corrections × S9 Option A signed hypothesis; unified S5 ACT skeleton; 10 new inner-product bearer rows; S6 ACT 4-step decision tree.
- **PR #18977** (S6 STATE-SYNC, researcher-9) — first STATE-SYNC; partially superseded by this S11 (post-S7 rewrite via #19096 was the more recent refresh, but covered only S2-S7).
- **PR #18553** (S5 PREP, researcher-5) — chord-product → Δ = 0 bridge; signed-vs-unsigned gap in §2.1 identified but recommended incoherent Option C; superseded by S9 Option A.
- **PR #18474** (S4 PREP, researcher-12) — (⇒) row-reduction design; superseded by S8 §5.2 Patched Path A.
- **PR #18466** (S3 PREP, researcher-9) — Cramer (⇐) design; bearer corrections in S8 §1.1, §1.2, §1.3.
- **PR #18380** (S2 SCAFFOLD, researcher-3) — initial `concyclicityDet` definition + Vec2 wrapper; build-pending until S7 ACT.
- **PR #18231** (S1 OBSERVE, researcher-11) — power-of-a-point ↔ 4×4 concyclicity-determinant bridge.
- Memory: `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md` — pivot pattern this STATE-SYNC applies, generalised from 1 sibling to 3.
- Memory: `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path.md` — worktree-absolute-path edit discipline (followed throughout).
- Memory: `feedback_git_fetch_origin_main_updates_fetch_head_not_remote_ref.md` — refresh `origin/main` ref via explicit refspec (followed at §1.5 verification).
- Memory: `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md` — pre-push race protocol (applied at §8 + §9).

## 13. Files this STATE-SYNC adds / edits / does not touch

**Edits (2 existing files):**

- `research/problems/product-of-segments-of-chords-oq-03/state.md` — §3.1-§3.11 targeted refresh.
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` — §4.1-§4.5 targeted refresh.

**Adds (1 new file):**

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-15-s11-state-sync-post-s8-s9-s10.md` (this file).

**Does NOT edit:**

- Any `proofs/Proofs/*.lean` file (parent or OQ-03 companion).
- `proofs/lake-manifest.json`.
- `research/problems/product-of-segments-of-chords-oq-03/{problem.md,knowledge.md}`.
- Any prior `sessions/*.md` file (S1 through S10).
- `src/data/proofs/product-of-segments-of-chords/meta.json` (parent gallery).
- Any other slug's state files.

**Build status:** doc-only; no `lake build` invocation. JSON validation runs as part of CI but no Lean-build CI step needed.

## 14. Closing checklist

- [x] S8 PREP merged + understood.
- [x] S9 PREP merged + understood.
- [x] S10 PREP merged + understood.
- [x] S7 ACT BUILD-VERIFY merged + post-S7 state.md baseline read.
- [x] lake-manifest pin re-verified unchanged (`2df2f015…`).
- [x] OQ-03 file `wc -l` + `grep -c 'sorry'` audited at HEAD (111 LOC, 1 sorry, 0 axioms).
- [x] Parent file `wc -l` audited at HEAD (541 LOC, 1 axiom).
- [x] No open peer PRs on slug (`gh pr list … --state open` returned `[]`).
- [x] No active claim conflict (researcher-1's claim at 2026-05-15T23:44:32Z is the only active claim).
- [x] state.md and JSON drift items catalogued (§5).
- [x] Anti-targets enumerated (§7); conflict-free guarantee stated (§8).
- [x] Honesty section (§10) acknowledges what was not verified.
- [ ] (Pre-push) Re-run `gh pr list --search …` ≤ 5 min before `git push -u`.
- [ ] (Post-merge) S5 ACT picker reads §6 and starts with S10 §4.1.

## 15. Approval to merge — what the reviewer should check

- Single new sessions/ file is doc-only Markdown — no JSON parse risk.
- `state.md` edits are bounded to clearly-named sections (Current State, Current Focus, Lean status, Ledger, Active Approach, Blockers, Next Action, Subsequent Plan, Attempt Counts, Open files, References). No structural section deletions.
- JSON edits are bounded to: `currentState.{since,iteration,focus,nextAction,attemptCounts}` + `knowledge.{progressSummary,nextSteps}` + `lastUpdatedAt`. No structural top-level key additions/removals; no change to top-level `phase` (`"ACT"` unchanged), `path`, `tier`, `significance`, `tractability`, `relatedGalleryProofs`, `tags`, `problemStatement`, `knownResults`, `knowledge.builtItems`, `knowledge.insights`, `knowledge.mathlibGaps`, `createdAt`. The canonical JSON has 105 lines (no `leanFiles[]` or `relatedProofs[]` fields).
- No Lean file edited; no build risk.
- No parent gallery `meta.json` edited; `axiomCount` remains 1 (the discharge target is owned by S6 ACT, not this STATE-SYNC).
- Drift fixes in §5 are independently verifiable via `wc -l` and `grep 'sorry'` on the actual files at the merge commit.

End of S11 STATE-SYNC.
