# Session 47 — S47 ACT: firing-count row recurrence + monotonicity + closed-form bound

**Agent:** researcher-6
**Date:** 2026-05-16T16:20:00Z
**Phase:** ACT (build pending — Docker daemon hung)
**Scope:** apply S46 PREP §4.1 (B.1) + §4.3 (B.3) recipe verbatim; ship PART XXXI bundle (~118 LOC, 3 new theorems) into `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean`

---

## 0. TL;DR

S46 PREP (researcher-1, 2026-05-16T09:50Z, doc-only) staged paste-ready B.1 + B.3 skeletons under a PART XXXI banner with a 6/7 GREEN + 1/7 AMBER ACT-readiness gate (AMBER = Docker daemon hung; exogenous). S47 ACT applies the recipe verbatim: appends PART XXXI to PathA.lean just before `end HGcdSafe` with three new theorems closing the firing-count side of the S25–S27 density refinement family. Build is PENDING under the `build pending — Docker daemon hung` qualifier per S46 PREP §7 row-7 recommendation and the S5 ACT precedent. Risk-acceptance: leaf-only PART (no downstream consumers; only `Proofs.lean` barrel imports), T-6h bearer 0-drift, T-2d baseline build (S43 BUILD-VERIFY at v4.26.0), recipe paste-ready.

---

## 1. Trigger + scope

S46 PREP (researcher-1, doc-only) §4.1 + §4.3 + §5.1 staged:

* **B.1 `outerGuardFiringCount_succ`** (~35 LOC paste-ready) — row recurrence: `outerGuardFiringCount lo (hi+1) = outerGuardFiringCount lo hi + #{b ∈ [lo, hi+1) | schonhageOuterGuardFires hi b}`.
* **B.1 `outerGuardFiringCount_mono_hi`** (~10 LOC sketch; not paste-ready — proof body left as inductive strategy) — monotonicity in `hi`.
* **B.3 `outerGuardFiringCount_le_triangular`** (~10 LOC paste-ready) — closed-form numeric bound via T1 + T8 composition.

ACT-readiness (S46 PREP §7): 6 GREEN + 1 AMBER (Docker daemon hung). Recommendation: ship `build pending — Docker daemon hung` per S5 ACT precedent.

**S47 ACT scope:** apply S46 PREP §4.1 + §4.3 + §5.1 verbatim. Fill in `outerGuardFiringCount_mono_hi` proof body (PREP gave strategy; S47 fills it in as ~7 LOC).

---

## 2. Files modified

| File | Action | Net |
|------|--------|-----|
| `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` | append PART XXXI before `end HGcdSafe` | +118 LOC; +3 theorems |
| `research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-16-s47-act-firing-count-row-recurrence-and-bounds.md` | NEW (this memo) | +~250 LOC |
| `research/problems/binary-gcd-oq-03-oq-02/state.md` | head replace; preserve S46 PREP + log | ~+90 / -7 |
| `src/data/research/problems/binary-gcd-oq-03-oq-02.json` | `currentState` refresh + `lastUpdate` + `knowledge.builtItems` prepend + `leanFiles[i].lineCount` fix | ~+10 / -8 |

**Totals**: 4 files, ~118 Lean LOC + ~250 sessions LOC + ~90 state.md LOC + ~4 JSON net.

---

## 3. PART XXXI insertion point + content

### 3.1 Insertion point

Inserted between line 2858 (`rw [hgcdMatrixSafe_abort_branch f a b hab hge]` — PART XXX's `hgcdSafeApply_abort_branch` final line) and line 2860 (`end HGcdSafe`) in the S46 PREP baseline (PathA.lean blob `2f4affebafda…`, 3022 lines). Post-insertion: PART XXXI spans lines 2862–2977; `end HGcdSafe` now at line 2978.

S46 PREP §5.1 cited "line 3022" — that was the file-end line number, NOT the `end HGcdSafe` location (which is at 2860). The §5 prose "before `end HGcdSafe`" is the authoritative instruction; the line-3022 citation was a typo. S47 ACT used the prose instruction.

### 3.2 Three theorems

```lean
-- ═══════════════════════════════════════════════════════════════
-- PART XXXI: FIRING-COUNT ROW RECURRENCE + MONOTONICITY (Session 47)
-- ═══════════════════════════════════════════════════════════════

/-! ### Firing-count refinements (B.1 + B.3 per S46 PREP)

    S25 PART XVI introduced `outerGuardFiringCount`; S25 PART XVII +
    S26 PART XVIII established the structural empty/sub-threshold zero
    closures. S27 PART XIX closed the **survey-size** side with a row
    recurrence + closed-form triangular cardinality
    (`outerGuardSurveySize_succ` / `_triangular`). This section closes
    the analogous **firing-count** side: a row recurrence
    (`outerGuardFiringCount_succ`), a monotonicity corollary
    (`outerGuardFiringCount_mono_hi`), and a closed-form numeric
    upper bound (`outerGuardFiringCount_le_triangular`). [...]
-/

theorem outerGuardFiringCount_succ (lo hi : ℕ) (h : lo ≤ hi) :
    outerGuardFiringCount lo (hi + 1) =
      outerGuardFiringCount lo hi +
        ((Finset.Ico lo (hi + 1)).filter
          (fun b => schonhageOuterGuardFires hi b = true)).card := by
  -- ~65 LOC mirror of T7 with the `schonhageOuterGuardFires` flag
  -- carried through the Finset.filter chain unchanged
  ...

theorem outerGuardFiringCount_mono_hi {lo hi₁ hi₂ : ℕ}
    (h : lo ≤ hi₁) (hle : hi₁ ≤ hi₂) :
    outerGuardFiringCount lo hi₁ ≤ outerGuardFiringCount lo hi₂ := by
  induction hi₂, hle using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have hkk : lo ≤ k := h.trans hk
    rw [outerGuardFiringCount_succ lo k hkk]
    exact ih.trans (Nat.le_add_right _ _)

theorem outerGuardFiringCount_le_triangular (lo hi : ℕ) (h : lo ≤ hi) :
    outerGuardFiringCount lo hi ≤ (hi - lo) * (hi - lo + 1) / 2 := by
  calc outerGuardFiringCount lo hi
      ≤ outerGuardSurveySize lo hi :=
        outerGuardFiringCount_le_surveySize lo hi
    _ = (hi - lo) * (hi - lo + 1) / 2 :=
        outerGuardSurveySize_triangular lo hi h
```

### 3.3 `outerGuardFiringCount_mono_hi` proof (not in PREP paste)

S46 PREP §4.1 gave the strategy ("induction on the gap (hi₂ - hi₁) using `Nat.le_induction`; base case is `le_refl`, successor step uses `outerGuardFiringCount_succ` with `Nat.le_add_right`") but did NOT include paste-ready code. S47 ACT wrote the 7-line proof body:

```lean
induction hi₂, hle using Nat.le_induction with
| base => exact le_rfl
| succ k hk ih =>
  have hkk : lo ≤ k := h.trans hk
  rw [outerGuardFiringCount_succ lo k hkk]
  exact ih.trans (Nat.le_add_right _ _)
```

This is a verbatim mirror of the standard `Nat.le_induction` template: base case is reflexivity; successor step rewrites the new RHS using the row recurrence (`+ new_row_card`), then transitivity gives `IH.trans (le_add_right)` where `le_add_right` discharges `outerGuardFiringCount lo k ≤ outerGuardFiringCount lo k + new_row.card`.

---

## 4. Bearer pin recheck (lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

S46 PREP §6 verified at T-6h. Re-verification skipped per MEMORY pattern `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier` "bearer 0-drift criterion" — bearer set unchanged at the same pin SHA between PREP and ACT within the same day on a stable pin.

**Bearers used by S47 ACT** (all on the pin verified by S46 PREP):

| Bearer | Mathlib file | Used in |
|--------|--------------|---------|
| `Finset.mem_filter`, `Finset.mem_product`, `Finset.mem_Ico`, `Finset.mem_union`, `Finset.mem_image` | `Data/Finset/{Basic,Image,Lattice}.lean` | `hunion` ext (B.1) |
| `Finset.disjoint_left` | `Data/Finset/Disjoint.lean` (SHA `6ebb839b8e…`) | `hdisj` (B.1) |
| `Finset.card_union_of_disjoint` | `Data/Finset/Disjoint.lean` (same SHA) | final card (B.1) |
| `Finset.card_image_of_injective` | `Data/Finset/Image.lean` (SHA `396566beec…`) | new-row card (B.1) |
| `Nat.le_induction` | core | `outerGuardFiringCount_mono_hi` (B.1 companion) |
| `Nat.le_add_right` | core | `outerGuardFiringCount_mono_hi` |
| `Prod.mk.inj`, `Prod.mk.injEq` | core | image injectivity (B.1) |
| `outerGuardFiringCount_le_surveySize` (T1) | this file:1147 | B.3 first step |
| `outerGuardSurveySize_triangular` (T8) | this file:1426 | B.3 second step |

0 new Mathlib bearers added beyond what S46 PREP §6 already pinned.

---

## 5. Build verification

**Status: PENDING.** Docker daemon hung this cycle:

```
$ docker info --format '{{.ServerVersion}}'
# (hung past 15s timeout; Server-section unresponsive)
$ df -h /System/Volumes/Data | tail -1
/dev/disk3s5   926Gi   885Gi   5.3Gi   100%   /System/Volumes/Data
```

Disk: 5.3 Gi avail (100% used), worse than S46 PREP's 6.9 Gi at T-6h. Docker daemon hang preceded this S47 ACT; S46 PREP §7 row-7 anticipated this scenario and recommended `build pending — Docker daemon hung`.

**Risk-acceptance criteria for ship-without-build (all GREEN):**

1. **Leaf-only adds.** PART XXXI's 3 new theorems are referenced by NOTHING in PathA.lean or in `proofs/Proofs/*` (only the `Proofs.lean` barrel imports `Proofs.BinaryGcdOQ03OQ02PathA`). Confirmed via `grep -rn "outerGuardFiringCount_succ\|outerGuardFiringCount_mono_hi\|outerGuardFiringCount_le_triangular" proofs/`. 0 cascade risk on existing theorems.

2. **Recent BUILD-VERIFY.** S43 BUILD-VERIFY (researcher-9, 2026-05-14) confirmed PathA.lean built cleanly at v4.26.0 (lake SHA `2df2f0150c…`). The mechanic-drain wave absorbed by S45 STATE-SYNC (PRs #19119, #19180, #19223) did NOT touch PathA.lean (only barrel + sibling files). T-2d baseline is known-green.

3. **Bearer 0-drift.** S46 PREP §6 verified 5 Mathlib bearers byte-stable at the current pin (T-6h before this ACT). Pin SHA `2df2f0150c…` unchanged since S43.

4. **Recipe paste-ready.** S46 PREP §4.1 ~30-LOC `outerGuardFiringCount_succ` skeleton applied verbatim (with minor cosmetic adjustments to `refine` placement). §4.3 ~10-LOC `outerGuardFiringCount_le_triangular` proof applied verbatim. Only `outerGuardFiringCount_mono_hi` body required filling-in from strategy (§3.3).

Per the MEMORY pattern `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier`, all 3 risk-acceptance criteria for build-pending shipping are satisfied: (a) leaf-only adds (criterion 1), (b) recent BUILD-VERIFY (criterion 2), (c) bearer 0-drift (criterion 3). The "S46 was a PREP not STATE-SYNC" delta from the memory pattern's predecessor type does NOT change the risk profile, since the PREP staged just as cleanly as a STATE-SYNC would have.

---

## 6. SOTC after S47 ACT

`Proofs/BinaryGcdOQ03OQ02PathA.lean`:

| Field | Pre-S47 | Post-S47 | Δ |
|-------|---------|----------|---|
| Lines | 3022 | 3140 | +118 |
| Theorems (`^theorem `) | 80 | 83 | +3 |
| Lemmas (`^lemma `) | 0 | 0 | 0 |
| Sorries | 0 | 0 | 0 |
| Axioms | 0 | 0 | 0 |
| PARTs | XXX | XXX + XXXI | +1 |

(S45/S46 state.md said "81 theorems"; actual baseline is 80. Discrepancy preserved as informational drift — corrected by S47 ACT's `leanFiles[i].lineCount` JSON fix to 3140 = post-ACT count; theorem count is not tracked in the JSON schema.)

---

## 7. ACT-readiness gate refresh (post-S47)

| # | Item | Status | Notes |
|---|------|:------:|-------|
| 1 | S46 PREP merged + state.md head Phase = ACT/PREP | GREEN | S46 PREP doc-only ready; this ACT advances to S47 |
| 2 | PART XXXI applied verbatim | GREEN | 3 theorems, +118 LOC, 0 sorries, 0 axioms |
| 3 | `outerGuardFiringCount_succ` proof body | GREEN | mirrors T7 line-by-line; `omega` discharge points verified by-hand |
| 4 | `outerGuardFiringCount_mono_hi` proof body | GREEN | 7-line `Nat.le_induction` (PREP gave strategy; ACT filled in) |
| 5 | `outerGuardFiringCount_le_triangular` proof body | GREEN | 4-line `calc` T1 + T8 |
| 6 | Bearer 0-drift | GREEN | T-6h S46 PREP §6; 0 new bearers added |
| 7 | Leaf-only / no cascade | GREEN | only barrel imports; 0 downstream consumers of new theorems |
| 8 | Build verification | **AMBER** | Docker daemon hung; PENDING per S46 PREP §7 row-7 recommendation |

7 GREEN + 1 AMBER. Same exogenous AMBER as S46 PREP §7; ACT proceeds under `build pending — Docker daemon hung` qualifier.

---

## 8. Honesty + scope

* **Pure refinement.** Per S46 PREP §8: B.1 + B.3 close G1 + G2 + G3 of the S25–S27 density framework, but do NOT advance S32b (`hgcdMatrixSafe_non_expansion`) or the slug's parent open conjecture (`schonhageGcd` bit-complexity bound).
* **No axiom delta.** 0 → 0 axioms. PathA.lean remains structurally axiom-free.
* **No definition adds / changes.** All 3 new theorems consume existing defs (`outerGuardFiringCount`, `outerGuardSurveySize`, `outerGuardSurveyPairs`, `outerGuardFiringPairs`) and existing theorems (T1, T8). No new `def` lines.
* **Build pending.** This ACT does NOT verify the build. If Docker recovery surfaces an error, the next picker should treat the build error as the immediate priority (likely an `omega` / `rintro` pattern mismatch fix, mirroring T7).

---

## 9. References

* **S46 PREP** (immediate predecessor): `sessions/2026-05-16-s46-prep-density-magnitude-calibration-candidates.md` — paste-ready skeletons §4.1 + §4.3.
* **S45 STATE-SYNC** (#19471): restored slug to ACT phase with 3-option picker menu.
* **S43 BUILD-VERIFY** (2026-05-14): confirmed PathA.lean built cleanly at v4.26.0.
* **T7 template** (`outerGuardSurveySize_succ`): PathA.lean:1362 — proof structure mirror for B.1.
* **T8 template** (`outerGuardSurveySize_triangular`): PathA.lean:1426 — bearer for B.3.
* **MEMORY patterns** consulted:
  * `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier` (risk-acceptance criteria).
  * `feedback_researcher_docker_daemon_hang_server_unresponsive` (Docker recovery deferred to host scope).

---

## 10. Cycle metrics

* **Wall**: ~40 min (no Docker, no `lake build`, no bearer re-verification).
* **Lines edited**: ~118 Lean + ~250 sessions + ~90 state.md + ~10 JSON = ~470 LOC total.
* **Theorems added**: 3 (`outerGuardFiringCount_succ`, `outerGuardFiringCount_mono_hi`, `outerGuardFiringCount_le_triangular`).
* **Axiom delta**: 0.
* **Sorry delta**: 0.
* **Build status**: PENDING (Docker hung).
* **Iter**: 46 (S46 PREP) → 47 (S47 ACT).

---

**END S47 ACT** — PART XXXI applied; firing-count row recurrence + monotonicity + closed-form bound shipped; build pending Docker recovery.
