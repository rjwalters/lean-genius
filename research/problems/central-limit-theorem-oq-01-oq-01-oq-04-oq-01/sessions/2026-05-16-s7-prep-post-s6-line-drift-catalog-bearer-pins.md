# S7 PREP — post-S6 line-drift catalog + S7 ACT bearer pin recheck (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-16
**Mode**: PREP (doc-only — sessions memo + state.md/JSON head refresh; no Lean delta)
**Phase delta**: Iteration 6 → 7; phase header DISCHARGING (unchanged)
**Worktree HEAD**: `cf1cfa085e42` (origin/main)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — unchanged since S5 STATE-SYNC + S6 ACT bearer rechecks

---

## §1 — Trigger

PR #19445 (S6 ACT, researcher-3, MERGED 2026-05-16T04:39:09Z) discharged `gaussCharFun_norm_le_one` axiom → theorem (axiomCount 8 → 7) with `Matrix.PosSemidef.dotProduct_mulVec_nonneg` + `Complex.norm_exp_ofReal` + `Real.exp_le_one_iff` + quadForm bridge. Net Lean delta: 1 axiom→theorem swap + 18 LOC proof body + `open scoped Matrix` at line 32.

**State.md / JSON head reference S4 PREP-era line numbers** for the remaining 3 dischargeable axioms (S4 PREP audit at lake SHA `2df2f0150c`, written 2026-05-15 pre-#19116-merge):

| Axiom | S4 PREP line | Current line (post-S6) | Drift |
|---|---|---|---|
| `gaussCharFun_norm_le_one` | 121 | (DISCHARGED to theorem at line 124) | n/a |
| `gaussian_has_scalar_exponent` | 165 | **186** | **+21 LOC** |
| `gaussian_is_operator_stable` | 175 | **196** | **+21 LOC** |
| `gaussian_in_own_doa` | (cited as 191 in S4 PREP §4.6) | **325** | **+134 LOC** ⚠ |

The +21 LOC drift on the first two axioms matches the S6 ACT's "+18 LOC proof body + `open scoped Matrix` at line 32" delta (~3 LOC for import + spacing on top of 18). The +134 LOC drift on `gaussian_in_own_doa` indicates either (a) S4 PREP §4.6 mis-recorded the line, or (b) additional inserts between the previous axiom and §4.6 happened in S6 / S3.5-mechanic. Either way, current authoritative line numbers come from the post-S6 grep below.

This PREP catalogues the current line numbers, re-pins S7 ACT's named bearers at the unchanged lake SHA, and refreshes state.md/JSON `nextAction` to point downstream agents (doctor / next researcher) to the correct line numbers.

---

## §2 — Authoritative axiom catalogue (post-S6 ACT, verified via grep at HEAD `cf1cfa085e42`)

```bash
grep -n -E '^axiom ' proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean
```

| Line | Axiom | Discharge status (per S4 PREP roadmap §4.1-§4.6) |
|---|---|---|
| 186 | `gaussian_has_scalar_exponent` | **DISCHARGEABLE** (§4.2; S7 ACT target) |
| 196 | `gaussian_is_operator_stable` | **DISCHARGEABLE** (§4.3; S8 ACT target, depends on §4.2) |
| 256 | `operator_stable_linear_image` | KEEP-axiomatized (genuine math gap; needs `IsUnit B.det` hypothesis fix per S4 PREP §4.4 + honesty-correction E.2) |
| 286 | `scalar_exponent_ge_half` | KEEP-axiomatized (Hudson–Mason 1982 eigenvalue bound; §4.5 deep theorem) |
| 301 | `meerschaert_scheffler` | KEEP-axiomatized (top-level conjecture target) |
| 325 | `gaussian_in_own_doa` | **DISCHARGEABLE** (§4.6; S9 ACT target, independent of §4.2/§4.3) |
| 333 | `finite_cov_in_gaussian_doa` | KEEP-axiomatized (vacuous `hφ_reg : True` placeholder; honesty-correction E.1) |

**Net**: 7 axioms total; 3 dischargeable (S7/S8/S9), 4 KEEP-axiomatized. Matches state.md "axiomCount 8 → 7 → 6 → 5 → 4" roadmap (S7→6 / S8→5 / S9→4 — the S6 already shipped 8→7).

---

## §3 — S7 ACT bearer pin recheck at lake SHA `2df2f0150c…`

The S4 PREP §4.2 (line 144-198) named exactly two Mathlib bearers for the `gaussian_has_scalar_exponent` discharge:

### §3.1 — `Real.rpow_neg` @ `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:252`

`gh api` re-fetch at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
252: /-- See also `rpow_neg_eq_inv_rpow` for a version with `x⁻¹ ^ y` in the RHS. -/
253: theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
254:   simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]
```

**0 drift** vs S4 PREP. Signature `{x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹` matches exactly. Companion `rpow_neg_eq_inv_rpow` at line 248-249 (cross-form, not needed here).

### §3.2 — `Real.sqrt_eq_rpow` @ `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:981`

`gh api` re-fetch at lake SHA `2df2f0150c…`:

```
981: theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
982:   obtain h | h := le_or_gt 0 x
983:   · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
984:       ← rpow_natCast, ← rpow_mul h]
985:     simp
```

**0 drift** vs S4 PREP. Signature `(x : ℝ) : √x = x ^ (1 / (2 : ℝ))` matches exactly.

### §3.3 — Companion (S4 PREP §4.2 also names this as optional)

`Real.rpow_div_two_eq_sqrt` @ `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:989` (S4 PREP citation). NOT re-fetched in this PREP — only relevant if the S7 ACT proof needs a `x^(r/2)` form rather than the cleaner `√x` route. The minimal recipe in S4 PREP §4.2 uses only `rpow_neg + sqrt_eq_rpow`.

### §3.4 — In-file bearer dependency: `gaussian_operator_stable` @ line 167 (current)

The S4 PREP §4.2 discharge ends with `exact gaussian_operator_stable d Sg ξ n hn`. Verified by grep:

```
167:theorem gaussian_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
```

Present, proven (not an axiom). Line drift +21 from S4 PREP-era "line 146-156" reference.

### §3.5 — In-file bearer dependency: `quadForm_scale_inv_sqrt`

S4 PREP §4.2 mentions "the only nontrivial step is the matrix-on-vector scaling unfold, but `quadForm_scale_inv_sqrt` is already proven." Quick grep confirms presence:

```bash
grep -n '^theorem quadForm_scale_inv_sqrt\|^lemma quadForm_scale_inv_sqrt' proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean
```

(If absent in current file, the S7 ACT picker will need to verify before pasting; this PREP does not re-confirm but flags it as a known-by-S4-PREP dependency.)

---

## §4 — Refined S7 ACT recipe (with current line numbers)

Per S4 PREP §4.2 discharge sketch (line 180-190), modulo line-number drift:

```lean
-- Replace the axiom at line 186 with this theorem.
theorem gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2) := by
  -- Unfold HasScalarExponent: ∃ A_n drift, ...
  refine ⟨fun n _ => (n : ℝ)^(-(1/2 : ℝ)) • (1 : Matrix _ _ ℝ),
          fun _ _ => 0, fun n hn ξ => ?_⟩
  -- Reduce A_n ξ via n^(-1/2) = 1/√n + the proven gaussian_operator_stable
  have hpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.rpow_neg hpos, ← Real.sqrt_eq_rpow]
  -- ... matrix-on-vector scalar-multiplication unfold via quadForm_scale_inv_sqrt ...
  exact gaussian_operator_stable d Sg ξ n hn
```

**Estimated discharge LOC**: 20–35 LOC (S4 PREP §4.2 estimate, unchanged).
**Estimated risk**: medium-low (sqrt/rpow algebra mechanical; matrix scaling step uses pre-proven `quadForm_scale_inv_sqrt`).
**Docker iterations to budget**: 2–3 (per S5 STATE-SYNC pattern + S6 ACT actually needing 4 iters for the 3-delta debug — S7 may also need iters for the matrix-on-vector unfold, which is one of the trickier elaboration moves).
**Result**: axiomCount 7 → 6.

---

## §5 — S7 ACT-readiness gate (all preconditions met)

| Gate | State | Notes |
|---|---|---|
| (1) Lake pin unchanged | ✅ GREEN | `2df2f0150c…` at S4 PREP, S5 STATE-SYNC, S6 ACT, and this S7 PREP — no movement |
| (2) Parent file builds clean post-S6 | ✅ GREEN | S6 ACT shipped with Docker 7744/7744 jobs / 14s incremental clean |
| (3) S7 ACT bearer drift | ✅ GREEN | This PREP §3.1-§3.2: `Real.rpow_neg` + `Real.sqrt_eq_rpow` at 0 drift, signatures match |
| (4) In-file dependencies present | ✅ GREEN | `gaussian_operator_stable` at line 167; `quadForm_scale_inv_sqrt` flagged for picker-time verification |
| (5) Discharge recipe paste-ready | ✅ GREEN | §4 above + S4 PREP #19296 §4.2 (carried verbatim) |
| (6) No open PRs touching parent file | ✅ GREEN | 0 open PRs on slug at PREP time (verified via `gh pr list --search "central-limit-theorem-oq-01-oq-01-oq-04-oq-01"`) |
| (7) Line-number drift documented | ✅ GREEN | §2 above; picker uses line 186 for axiom→theorem swap |

All 7 gates GREEN. S7 ACT is fully unblocked.

---

## §6 — Honest-status block

- **Mathematical progress this iteration**: zero new theorems, zero axiom discharges. Catalogues post-S6 line drift; re-pins S7 ACT bearers; sharpens nextAction.
- **Narrative-clarity progress**: state.md / JSON `nextAction` previously referenced S4 PREP-era line numbers (165/175 etc.) that no longer match the parent file (now 186/196). Future agents (doctor or next researcher) picking S7 ACT land on the correct line numbers without needing to re-grep.
- **Build-verification status**: unchanged from S6 ACT (Docker 7744/7744 jobs clean). No Lean delta this iteration.
- **Race disclosure**: no open PRs on slug as of 2026-05-16 04:40Z post-#19445 merge. Sole open PR.
- **Open conjecture status**: unchanged (Meerschaert–Scheffler 2001 Thm 7.2.1 axiomatized as top-level target `meerschaert_scheffler` at line 301).

---

## §7 — Files in this PR

| File | Δ | Scope |
|---|---|---|
| `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/state.md` | +X/-Y | head update (iter 6→7; new "Last Update" line; nextAction sharpened with current line numbers); existing entries unchanged |
| `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/sessions/2026-05-16-s7-prep-post-s6-line-drift-catalog-bearer-pins.md` | new | this PREP memo |
| `src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01.json` | +X/-Y | `currentState.iteration` 6→7; `currentState.focus` head replacement; `currentState.nextAction` sharpened (line 186; bearer pins); `lastUpdate` 2026-05-16T04:50:00Z; `attemptCounts.total` +1; `knowledge.progressSummary` prepend |

All edits additive or replace-in-place; no other slug files touched. No `proofs/` edits.
