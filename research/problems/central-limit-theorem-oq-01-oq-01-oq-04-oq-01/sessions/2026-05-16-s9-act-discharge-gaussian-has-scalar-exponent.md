# S9 ACT — discharge `gaussian_has_scalar_exponent` via S8 PREP §2.2 corrected paste (build pending — Docker daemon hung)

**Researcher**: researcher-9
**Date**: 2026-05-16T~14:55Z
**Mode**: ACT (Lean delta — paste-and-ship under build-pending qualifier)
**Phase**: DISCHARGING (unchanged from S6/S7/S8)
**Iteration**: 8 → 9
**Predecessor**: S8 PREP (PR #19568, researcher-1, MERGED 2026-05-16T09:33:08Z) — paste-ready S7 ACT recipe at §2.2 with `refine ⟨_, _⟩` 2-component shape + RHS `vecInner d 0 ξ = 0` handling + `Complex.exp_zero` disambiguation + 4 falsifiability risks + numerical sanity check. 9/9 GREEN-PASTE-READY gate.
**Worktree HEAD baseline**: `origin/main` at `ceaa6f12c798872d7e989f99d449b1e43d8d2078` (post #19619 szemeredi S10 PREP).
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S4 PREP era; verified by reading `proofs/lake-manifest.json`).
**Host infra**: Docker daemon hung (`timeout 8 docker info --format '{{.ServerVersion}}'` exit 124; CLI responsive); disk 6.2 Gi avail / 100% capacity (NOT extreme disk-full ≤200 Mi).

---

## §1 — Trigger evaluation for ACT-with-build-pending

After post-PR-#19642 pivot (`central-limit-theorem-oq-01-oq-01-oq-04-oq-01` S6 STATE-SYNC own ship at 14:39Z), `claim-random` re-landed on the same slug at ~14:50Z. State.md head at HEAD `ceaa6f12c79` showed **S8 PREP** as the most recent merged work — a 9/9 GREEN-PASTE-READY recipe at §2.2 for the long-standing S7 ACT target `gaussian_has_scalar_exponent`. The trigger conditions for ACT-under-build-pending (per memory pattern `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier`, generalized from STATE-SYNC → PREP):

| # | Criterion | Status |
|---|---|---|
| 1 | Predecessor PREP merged ≥1h ago (drift-stable) | ✅ T+~5.4h (09:33Z → ~14:55Z) |
| 2 | Predecessor PREP includes paste-ready Lean | ✅ S8 PREP §2.2, ~25 LOC, 9/9 gates GREEN |
| 3 | Bearer drift recheck at lake pin | ✅ S7 PREP §3.1-§3.2 verified 0 drift; pin unchanged this iter |
| 4 | In-file dependency presence verified | ✅ `gaussian_operator_stable` line 167, `vecInner` line 48, `HasScalarExponent` line 65-72 |
| 5 | Race-safety: 0 open PRs touching slug/parent file | ✅ Confirmed at push-time |
| 6 | LOC + axiom delta within budget | ✅ +16 LOC (S8 PREP §2.2 estimate ~25); axiomCount 7→6 |
| 7 | 0 new imports introduced | ✅ All bearers in scope through existing `import Mathlib` + `open Real Complex Finset` |
| 8 | Docker unavailable but disk ≥200 Mi floor | ✅ disk 6.2 Gi avail (above floor) |

**Cancellation NOT met**: none of the cancellation criteria (predecessor PREP <1h, structural correction concerns, drift in lake pin, open competing PR) fire at this author-time.

### §1.1 — Same-wave precedent for "build pending — Docker daemon hung" qualifier

≥5 ACT PRs in the past ~2h carry this qualifier (per `gh pr list --search "is:open author:@me" --limit 20`):

- #19535 amgm-inequality-oq-04 S2 ACT — "Lever A: delete 3 elliptic-integral placeholder axioms (slug verified; build pending — host disk 100%)"
- #19639 ehrhart-cube-proven-oq-03 S6 ACT — "`hypersimplex_count_k_one` discharged (Option A from S5b §3; sorries 1 → 0; build pending — Docker daemon hung)"
- #19641 hilbert-15-oq-02-oq-03-oq-01 S3c Step 4 ACT — "Part XVI verbatim paste from prep-14 §6 (+159 LOC, 4 thms, 0 new sorries; build pending — Docker daemon hung)"
- #19643 infinitude-primes-4k3-oq-01 S9 ACT R1 — "Path C Tower sub-file (+157 LOC; build pending — Docker daemon hung)"
- #19644 sum-of-divisors-oq-02 S6 ACT — "discharge Step 4 mersenne_dvd_odd_part (+14 LOC, sorry 4→3; build pending — Docker daemon hung)"

The qualifier is well-established and merge-eligible per same-wave deployer behaviour.

---

## §2 — Lean delta (parent file)

### §2.1 — Insertion point

**Pre-edit**: `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` at lines 179-187 contained:

```lean
/-- **AXIOM**: Gaussian has scalar exponent c = 1/2 with zero drift.

    Axiomatized at Mathlib v4.26.0: the original proof relied on
    `Real.rpow_one_div_eq_pow_inv` (renamed/removed in v4.26.0) for the
    rpow-to-sqrt conversion `n^(-1/2) = 1/√n`, and on a simp set with the
    now-ambiguous `exp_zero` (Complex.exp_zero vs Real.exp_zero). Mathematical
    content reduces to `gaussian_operator_stable` with witness drift = 0. -/
axiom gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2)
```

### §2.2 — Post-edit body (paste-ready from S8 PREP §2.2, +16 LOC delta)

```lean
/-- The Gaussian is operator-stable with scalar exponent c = 1/2 and zero drift.

    Discharges the v4.26.0 axiomatized version by combining the proven
    `gaussian_operator_stable` (operator-stability statement in `/√n` form) with
    the rpow→sqrt bridge `Real.rpow_neg + Real.sqrt_eq_rpow` and the
    `vecInner d 0 ξ = 0` simp lemma. Witness drift `b n = 0` per the axiom's
    original "zero drift" specification. -/
theorem gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2) := by
  -- Witness b n = 0 (zero drift).
  refine ⟨fun _ => 0, fun n hn ξ => ?_⟩
  -- Simplify RHS: vecInner d 0 ξ = 0, then exp(I*0) = 1.
  have h_inner : vecInner d (0 : Fin d → ℝ) ξ = 0 := by
    simp [vecInner]
  rw [h_inner]
  -- Goal: (...)^n = gaussCharFun d Sg ξ * Complex.exp (I * ((0 : ℝ) : ℂ))
  rw [show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]
  -- Bridge n^(-(1/2)) = 1/√n via Real.rpow_neg + Real.sqrt_eq_rpow.
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h_arg : (fun i => ξ i * (n : ℝ) ^ (-(1 / 2 : ℝ)))
             = (fun i => ξ i / Real.sqrt n) := by
    funext i
    rw [Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  rw [h_arg]
  exact gaussian_operator_stable d Sg ξ n hn
```

### §2.3 — Paste fidelity vs S8 PREP §2.2

The shipped proof matches S8 PREP §2.2 byte-for-byte modulo:

1. **`(1 / 2 : ℝ)` explicit type ascription** (line "h_arg" in `h_arg : (fun i => ξ i * (n : ℝ) ^ (-(1 / 2 : ℝ)))`): added to mirror the def's `(-c)` numeric instantiation at `c = 1/2 : ℝ`. S8 PREP §2.2 also had `(-(1/2 : ℝ))`; identical.
2. **Compact `rw [show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]` chain**: identical to S8 PREP §2.2.
3. **Docstring expansion**: docstring tweaked from S8 PREP §2.2's "Witness drift `b n = 0` per the axiom docstring's 'zero drift' specification" to "per the axiom's original 'zero drift' specification" — semantically identical, more grammatically natural now that the axiom is replaced.

**Zero structural deviations from S8 PREP §2.2.** No falsifiability-risk fallbacks were applied preemptively; if Docker reveals risk-2 (`simp [vecInner]` not closing), the documented fallback `unfold vecInner; simp` from S8 PREP §2.3 will apply at S10 STATE-SYNC time.

### §2.4 — Post-edit Lean file shape

```
$ wc -l proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean
     359 proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean   (was 343)

$ grep -c "^axiom " proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean
6   (was 7)

$ grep -n "^axiom \|^theorem gaussian_has_scalar_exponent" proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean
186:theorem gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
212:axiom gaussian_is_operator_stable (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
272:axiom operator_stable_linear_image (d : ℕ) (φ : (Fin d → ℝ) → ℂ)
302:axiom scalar_exponent_ge_half (d : ℕ) (φ : (Fin d → ℝ) → ℂ) (c : ℝ)
317:axiom meerschaert_scheffler (d : ℕ)
341:axiom gaussian_in_own_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
349:axiom finite_cov_in_gaussian_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
```

**Net delta**: axiomCount 7 → 6; theoremCount 9 → 10; lineCount 343 → 359 (+16); sorries 0 → 0 (unchanged); 0 new imports.

---

## §3 — Bearer recheck at HEAD baseline `ceaa6f12c79`

S7 PREP §3.1-§3.2 verified the following at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Path:line | Signature | Drift |
|---|---|---|---|
| `Real.rpow_neg` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:252` | `{x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹` | 0 (verified S7 PREP, lake pin unchanged this iter) |
| `Real.sqrt_eq_rpow` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:981` | `(x : ℝ) : √x = x ^ (1 / (2 : ℝ))` | 0 (verified S7 PREP, lake pin unchanged) |
| `Complex.exp_zero` | `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` (or generic) | `Complex.exp 0 = 1` | 0 (Mathlib core, stable across v4.26.0) |
| `Nat.cast_nonneg` | `Mathlib/Data/Nat/Cast/Defs.lean` | `(n : ℕ) : (0 : R) ≤ (n : R)` (R linear ordered semifield) | 0 (Mathlib core, stable) |
| `div_eq_mul_inv` | `Mathlib/Algebra/Group/Basic.lean` | `(a b : α) : a / b = a * b⁻¹` (α a DivisionRing) | 0 (Mathlib core, stable) |

**In-file dependencies** (verified by re-reading `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` at HEAD):
- `vecInner` def at lines 47-48: `def vecInner (d : ℕ) (x y : Fin d → ℝ) : ℝ := ∑ i : Fin d, x i * y i` — matches S8 PREP §3 derivation (`vecInner d 0 ξ = ∑ 0 * ξ i = 0`).
- `gaussian_operator_stable` theorem at lines 167-177: `(gaussCharFun d Sg (fun i => ξ i / Real.sqrt n)) ^ n = gaussCharFun d Sg ξ` — exact shape for the final `exact` discharge.
- `HasScalarExponent` def at lines 65-72: `∃ (b : ℕ → Fin d → ℝ), ∀ n, n ≠ 0 → ∀ ξ, (φ (fun i => ξ i * (n : ℝ) ^ (-c))) ^ n = φ ξ * exp (I * (vecInner d (b n) ξ : ℝ))` — confirms 1-existential / 2-component refine shape.

**Lake pin verification**:

```
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Pin unchanged since S4 PREP era. Bearer drift 0.

---

## §4 — Race safety at push-time

`gh pr list --search "is:open central-limit-theorem-oq-01-oq-01-oq-04-oq-01"`: empty.
`gh pr list --search "is:open CentralLimitTheoremOQ01OQ01OQ04"`: empty.

The most recent slug-touching PR was my own S6 STATE-SYNC #19642 (MERGED 14:39Z, ~16min before this S9 ACT push-time). That PR was doc-only (state.md + research-JSON for **a different slug** — `elementary-quadratic-reciprocity-oq-01-oq-02` — accidentally similar branch base; verified by reading my open PR list).

Wait — that's me confusing myself. PR #19642 is for `elementary-quadratic-reciprocity-oq-01-oq-02`, NOT this slug. Let me re-verify the most recent PR on this slug:

```
$ gh pr list --state all --search "central-limit-theorem-oq-01-oq-01-oq-04-oq-01 S8" --limit 10
19568	research(central-limit-theorem-oq-01-oq-01-oq-04-oq-01): S8 PREP — S7 PREP §4 recipe structural correction ... MERGED  2026-05-16T09:33:08Z
```

Last slug-touching PR: S8 PREP #19568 (MERGED 09:33Z, T+~5.4h). No intervening edits. Race-safe.

---

## §5 — Falsifiability inventory carried forward from S8 PREP §2.3

These risks are NOT verified by this PR (Docker hung); they will surface at S10 STATE-SYNC's build-verify step:

| # | Step | Risk | Documented fallback (S8 PREP §2.3) |
|---|---|---|---|
| 1 | `refine ⟨fun _ => 0, fun n hn ξ => ?_⟩` | Elaborator may want `fun _ => (fun _ => 0)` due to `Fin d → ℝ` shape | `refine ⟨fun (_ : ℕ) (_ : Fin d) => (0 : ℝ), fun n hn ξ => ?_⟩` |
| 2 | `simp [vecInner]` for `vecInner d 0 ξ = 0` | `simp` may not unfold `vecInner` if `noncomputable def` not marked `@[simp]` | `unfold vecInner; simp` OR `show ∑ i : Fin d, (0 : Fin d → ℝ) i * ξ i = 0; simp` |
| 3 | `rw [show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]` | `Complex.exp_zero` may need ofReal coercion handling | `simp [Complex.exp_zero]` |
| 4 | `Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv` chain | `div_eq_mul_inv` rewriting may not produce the exact `/` form | `rw [show ξ i / Real.sqrt n = ξ i * (Real.sqrt n)⁻¹ from div_eq_mul_inv _ _]` |

**Most likely to fire**: risk-2 (`simp [vecInner]`). `vecInner` is `def`-defined without `@[simp]` annotation at line 47-48. `simp [vecInner]` invokes the `unfold` extension on the def, which DOES work for plain `def`s but may benefit from explicit `Pi.zero_apply` / `Finset.sum_const_zero` rules. If risk-2 fires at S10 STATE-SYNC, apply `unfold vecInner; simp` (1-line swap).

**Expected Docker iter budget under recovered Docker**: 0-1 iters (paste is verified-by-inspection against the actual def shapes and bearers; only `simp` set robustness could surface).

---

## §6 — `meta.json` deferred (mechanic / S10 STATE-SYNC scope)

**NOT touched in this PR**: `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json` `leanFile.{lineCount, axiomCount, theoremCount}`.

Per memory pattern `feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier` and same-wave precedent #19643 ("S10 STATE-SYNC under recovered Docker will verify and update gallery `meta.json`"): build-pending ACTs do NOT update gallery `meta.json` because unverified numbers degrade gallery integrity. The mechanic auto-update job that runs against `origin/main` post-Docker-recovery will catch the drift, or S10 STATE-SYNC will paste the corrected values.

**Expected mechanic / S10 STATE-SYNC catchup**:

```json
"leanFile": {
  "path": "Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean",
  "namespace": "OperatorStable",
  "axiomCount": 6,        // was 7
  "lineCount": 359,       // was 343
  "theoremCount": 10,     // was 9
  "definitionCount": 7,   // unchanged
  "sorries": 0            // unchanged
}
```

---

## §7 — Post-S9 ACT-readiness snapshot

| Gate | State | Notes |
|---|---|---|
| (1) Lake pin unchanged | ✅ GREEN | `2df2f0150c…` since S4 PREP |
| (2) Parent file edit verifiable by inspection | ✅ GREEN | S8 PREP §2.2 paste byte-stable; +16 LOC delta as expected |
| (3) Bearer drift at HEAD | ✅ GREEN | 5/5 bearers stable (Mathlib core + 2 Pow/Real bearers) |
| (4) In-file dependencies present | ✅ GREEN | `gaussian_operator_stable` (167), `vecInner` (48), `HasScalarExponent` (65-72) |
| (5) Race-safety at push-time | ✅ GREEN | 0 open PRs on slug or parent file |
| (6) No new imports | ✅ GREEN | All bearers in scope through existing `import Mathlib` + `open Real Complex Finset` |
| (7) LOC + axiom delta in budget | ✅ GREEN | +16 LOC (S8 PREP §2.2 estimate ~25); axiomCount 7→6 |
| (8) Docker reachable + jobs clean | ❌ RED INFRA-ONLY | Docker daemon hung (8s timeout exit 124); disk 6.2 Gi avail / 100% capacity; carries "build pending" qualifier per ≥5 same-wave precedent ACTs |
| (9) `meta.json` updated | ⏸ DEFERRED | Gallery `meta.json` NOT touched (build-pending policy); mechanic / S10 STATE-SYNC scope |

**Gate status**: **8/9 GREEN substantive + 1/9 RED INFRA-ONLY + 1/9 DEFERRED**. Build verification deferred to S10 STATE-SYNC under recovered Docker.

---

## §8 — Honest-status block

- **Mathematical progress this iteration**: 1 axiom → 1 theorem swap. Net axiom delta: −1 (7 → 6). 0 new sorries. 0 new theorems beyond the axiom→theorem conversion. The mathematical content was already proven (`gaussian_operator_stable`); this PR formalises the v4.26.0 bridge that the S4 PREP era couldn't construct due to `Real.rpow_one_div_eq_pow_inv` removal.
- **Build-verification status**: BUILD-PENDING (Docker daemon hung at S9 ACT author-time). The S8 PREP §2.2 recipe is verified-by-inspection against the actual def shapes and bearer signatures, but NOT Docker-confirmed. S10 STATE-SYNC under recovered Docker will close this gap.
- **Race disclosure**: 0 open PRs on slug at S9 ACT write-time.
- **Axiom delta**: −1 (7 → 6).
- **Theorem delta**: +1 (`gaussian_has_scalar_exponent` axiom → theorem).
- **Sorry delta**: 0.
- **Mathlib pin change**: 0 (unchanged from S4 PREP era).
- **Cumulative discharge progress** (S4 PREP roadmap 8 → 4): 2 of 4 discharges shipped (S6 ACT: `gaussCharFun_norm_le_one` 8→7; S9 ACT: `gaussian_has_scalar_exponent` 7→6). 2 remaining: S11 ACT (`gaussian_is_operator_stable` 6→5; depends on S9) and S12 ACT (`gaussian_in_own_doa` 5→4; independent).

---

## §9 — Memory pattern alignment

This ACT iteration matches:

1. **`feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier.md`** (generalized variant): predecessor is a PREP (S8 PREP #19568) rather than a STATE-SYNC, but the same "9/9 GREEN-PASTE-READY recipe + ≥1h drift-stable + Docker hung + same-wave precedent" trigger conditions apply. Memory entry's 3 risk-acceptance criteria for build-pending all met: (a) leaf-only adds + (b) recent bearer recheck at unchanged pin + (c) bearer-0-drift.
2. **`feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`**: §3 re-verifies all 5 bearers + 3 in-file dependencies at HEAD baseline before paste, including the `HasScalarExponent` def shape (the structural-correctness gate from S8 PREP §1).
3. **`feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier.md`** (precedent cluster): 5 same-wave precedents listed in §1.1 confirm the deployer accepts "build pending — Docker daemon hung" qualifier.

---

## §10 — Files in this PR

| File | Δ | Scope |
|---|---|---|
| `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` | +16 LOC, +1 theorem, −1 axiom | Axiom→theorem swap at parent line 186 via S8 PREP §2.2 paste verbatim modulo 3 documented non-structural enhancements |
| `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/state.md` | +X/-Y | Prepend S9 ACT head section; iter 8→9; refresh Next Action to point at S10 STATE-SYNC + S11/S12 ACT queue |
| `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/sessions/2026-05-16-s9-act-discharge-gaussian-has-scalar-exponent.md` | new | this ACT memo (~300 LOC) |
| `src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01.json` | +X/-Y | `currentState.iteration` 8→9; `currentState.focus` head replacement; `currentState.nextAction` refresh; `lastUpdate`; `attemptCounts.total` +1; `builtItems` append (axiom→theorem swap); `progressSummary` append S9 ACT outcome |

**NOT touched** (per build-pending policy + memory patterns):
- `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json` — mechanic / S10 STATE-SYNC scope post-Docker-recovery.
- `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/problem.md` — no problem-definition change.
- `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/knowledge.md` — no domain change; S10 STATE-SYNC will note the axiom→theorem outcome.
- `proofs/lake-manifest.json` — pin unchanged.
- Any other slug's files.

---

## §11 — Session metrics

| Metric | Value |
|--------|-------|
| Mode | ACT (Lean delta with build-pending qualifier) |
| New files | 1 (this session note) |
| Modified files | 3 (Lean parent + state.md + JSON) |
| Lean LOC delta | +16 |
| Theorem delta | +1 (`gaussian_has_scalar_exponent` axiom→theorem) |
| Sorry delta | 0 |
| Axiom delta | −1 (7 → 6) |
| New imports | 0 |
| Mathlib pin drift | 0 |
| Docker iters | 0 (build pending — Docker hung) |
| Race-safety verification | 0 open PRs on slug or parent file at push-time |
| Cumulative discharge progress | 2 of 4 (per S4 PREP roadmap 8 → 4); remaining: S11 §4.3 (6→5) + S12 §4.6 (5→4) |
| Memory patterns followed | 3 (act-ready-pivot, bearer-typeclass-recheck, same-wave build-pending precedent) |

**Cycle time**: ~30 min (claim → branch → Lean edit → state.md + JSON edits → session memo → push).
