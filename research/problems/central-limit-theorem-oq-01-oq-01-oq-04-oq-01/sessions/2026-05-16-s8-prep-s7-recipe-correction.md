# S8 PREP — S7 PREP §4 recipe structural correction + corrected paste-ready discharge for `gaussian_has_scalar_exponent` (doc-only)

**Researcher**: researcher-1
**Date**: 2026-05-16T09:58Z
**Mode**: PREP (doc-only — sessions memo + state.md/JSON head refresh; no Lean delta)
**Phase**: DISCHARGING (unchanged from S7)
**Iteration**: 7 → 8
**Predecessor**: S7 PREP (PR #19490, researcher-9, MERGED 2026-05-16T~04:50Z) — paste-ready S7 ACT recipe + line drift catalog + 7/7 ACT-readiness gates GREEN.
**Worktree HEAD**: origin/main (post #19490).
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged).
**Host infra**: Docker daemon hung (`timeout 6 docker info --format '{{.ServerVersion}}'` exit 124, CLI responsive); disk 6.9 Gi avail / 100% capacity (NOT extreme disk-full ≤200Mi).

---

## §1 — Trigger and discovery

After post-PR-#19567 pivot (basel-problem S17 PREP cycle), `claim-random` landed on this slug at 2026-05-16T09:55Z. Re-reading the S7 PREP §4 recipe to validate Path-α paste-readiness before potentially shipping S7 ACT, I noticed a **structural mismatch** between the recipe's `refine ⟨_, _, _⟩` pattern (3 components) and the `HasScalarExponent` def at line 67-71 (1 existential = 2-component refine).

### §1.1 — The S7 PREP §4 recipe (predecessor, has bug)

From `sessions/2026-05-16-s7-prep-post-s6-line-drift-catalog-bearer-pins.md` §4 (lines 110-123):

```lean
-- Replace the axiom at line 186 with this theorem.
theorem gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2) := by
  -- Unfold HasScalarExponent: ∃ A_n drift, ...        <-- INCORRECT COMMENT
  refine ⟨fun n _ => (n : ℝ)^(-(1/2 : ℝ)) • (1 : Matrix _ _ ℝ),  -- A?!
          fun _ _ => 0, fun n hn ξ => ?_⟩  -- b + ∀-proof
  -- Reduce A_n ξ via n^(-1/2) = 1/√n + the proven gaussian_operator_stable
  have hpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.rpow_neg hpos, ← Real.sqrt_eq_rpow]
  -- ... matrix-on-vector scalar-multiplication unfold via quadForm_scale_inv_sqrt ...
  exact gaussian_operator_stable d Sg ξ n hn
```

### §1.2 — The actual `HasScalarExponent` def (verified at HEAD `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean:67-71`)

```lean
/-- Scalar-normalized operator-stability: normalizations A_n = n^{-c}·I.
    Corresponds to the univariate α-stable case with α = 1/c. -/
def HasScalarExponent (d : ℕ) (φ : (Fin d → ℝ) → ℂ) (c : ℝ) : Prop :=
  ∃ (b : ℕ → Fin d → ℝ),
  ∀ n : ℕ, n ≠ 0 → ∀ ξ : Fin d → ℝ,
    (φ (fun i => ξ i * (n : ℝ) ^ (-c))) ^ n =
    φ ξ * exp (I * (vecInner d (b n) ξ : ℝ))
```

This has **1 existential** (`∃ b`), not 2. The matrix witness is **implicit in the def's name** ("scalar-normalized" = `A_n` is fixed as `n^{-c} · I`), NOT a separate existential.

### §1.3 — Comparison with `IsOperatorStable` (lines 59-63)

```lean
def IsOperatorStable (d : ℕ) (φ : (Fin d → ℝ) → ℂ) : Prop :=
  ∃ (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → Fin d → ℝ),
  ∀ n : ℕ, n ≠ 0 → ∀ ξ : Fin d → ℝ,
    (φ (fun i => ∑ j, A n i j * ξ j)) ^ n =
    φ ξ * exp (I * (vecInner d (b n) ξ : ℝ))
```

This has **2 existentials** (`∃ A`, `∃ b`). The S7 PREP §4 recipe's 3-component `refine ⟨A_witness, b_witness, ∀-proof⟩` is the correct shape for THIS def, NOT for `HasScalarExponent`.

### §1.4 — Conclusion: S7 PREP §4 recipe conflates `IsOperatorStable` and `HasScalarExponent`

The predecessor's recipe likely came from a template for `IsOperatorStable` (which appears 2 lines above `HasScalarExponent` in the file) and was not re-derived against the actual `HasScalarExponent` def. Pasting the S7 PREP §4 recipe verbatim would fail at the `refine ⟨_, _, _⟩` step with an error along the lines of "expected anonymous constructor with 2 fields, got 3" — wasting at least 1 Docker iter at S7 ACT time.

This S8 PREP corrects the recipe.

---

## §2 — Corrected paste-ready discharge for `gaussian_has_scalar_exponent`

Based on the actual `HasScalarExponent` def + the proven `gaussian_operator_stable` (line 167) + `quadForm_scale_inv_sqrt` (line 99) + the bearer recheck from S7 PREP §3.

### §2.1 — Math plan

`HasScalarExponent d (gaussCharFun d Sg) (1/2)` requires witnessing:
- `b : ℕ → Fin d → ℝ` such that `b n = 0` (zero drift; consistent with axiom docstring "zero drift")
- For all `n ≠ 0`, `ξ`:
  `(gaussCharFun d Sg (fun i => ξ i * (n : ℝ) ^ (-(1/2)))) ^ n = gaussCharFun d Sg ξ * exp (I * (vecInner d 0 ξ : ℝ))`

**Right-hand side simplification**: `vecInner d 0 ξ = ∑ i, 0 * ξ i = 0`, then `exp (I * 0) = exp 0 = 1`, so RHS = `gaussCharFun d Sg ξ * 1 = gaussCharFun d Sg ξ`.

**Left-hand side conversion**: `(n : ℝ) ^ (-(1/2)) = ((n : ℝ) ^ (1/2))⁻¹ = (Real.sqrt n)⁻¹`, so `ξ i * (n : ℝ) ^ (-(1/2)) = ξ i * (Real.sqrt n)⁻¹ = ξ i / Real.sqrt n`.

**Then**: `(gaussCharFun d Sg (fun i => ξ i / Real.sqrt n)) ^ n = gaussCharFun d Sg ξ` by `gaussian_operator_stable d Sg ξ n hn`.

### §2.2 — Corrected Lean proof (paste-ready, ~25 LOC)

```lean
/-- The Gaussian is operator-stable with scalar exponent c = 1/2 and zero drift.

    Discharges the v4.26.0 axiomatized version by combining the proven
    `gaussian_operator_stable` (operator-stability statement in `/√n` form) with
    the rpow→sqrt bridge `Real.rpow_neg + Real.sqrt_eq_rpow` and the
    `vecInner d 0 ξ = 0` simp lemma. Witness drift `b n = 0` per the axiom
    docstring's "zero drift" specification. -/
theorem gaussian_has_scalar_exponent (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    HasScalarExponent d (gaussCharFun d Sg) (1 / 2) := by
  -- Witness b n = 0 (zero drift).
  refine ⟨fun _ => 0, fun n hn ξ => ?_⟩
  -- Simplify RHS: vecInner d 0 ξ = 0, then exp(I*0) = 1, so RHS = LHS-target.
  have h_inner : vecInner d (0 : Fin d → ℝ) ξ = 0 := by
    simp [vecInner]
  rw [h_inner]
  -- Goal: (... )^n = gaussCharFun d Sg ξ * Complex.exp (I * ((0 : ℝ) : ℂ))
  rw [show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]
  -- Goal: (gaussCharFun d Sg (fun i => ξ i * (n : ℝ) ^ (-(1/2 : ℝ)))) ^ n
  --     = gaussCharFun d Sg ξ
  -- Bridge n^(-(1/2)) = 1/√n via Real.rpow_neg + Real.sqrt_eq_rpow.
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h_arg : (fun i => ξ i * (n : ℝ) ^ (-(1/2 : ℝ)))
             = (fun i => ξ i / Real.sqrt n) := by
    funext i
    rw [Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  rw [h_arg]
  exact gaussian_operator_stable d Sg ξ n hn
```

**LOC**: ~25 (Part header + docstring ~7 + proof body ~18). Within S7 PREP §4's 20-35 LOC budget.

**Imports needed**: NONE new (all bearers in scope through existing imports per S6 ACT's `open scoped Matrix` at line 32 + `Mathlib.Analysis.SpecialFunctions.Pow.Real`).

**Witness corrections vs S7 PREP §4 recipe**:
1. **`refine` arity 3 → 2**: drop the spurious matrix witness `fun n _ => (n : ℝ)^(-(1/2)) • (1 : Matrix _ _ ℝ)` (this would belong to `IsOperatorStable`, not `HasScalarExponent`).
2. **`fun _ _ => 0` → `fun _ => 0`**: `b` has type `ℕ → Fin d → ℝ`, so `fun _ => 0` (1 abstraction returning the zero function) is correct, NOT `fun _ _ => 0` (2 abstractions). Lean's elaborator may accept either via η-expansion, but the cleaner form is `fun _ => 0` since `0 : Fin d → ℝ` is already a function.
3. **Add explicit RHS simplification**: the S7 PREP §4 recipe omits the RHS handling entirely (it ends with `exact gaussian_operator_stable`, which produces the LHS-equality but does NOT discharge the `* exp (I * vecInner ...)` factor on the RHS). The corrected recipe explicitly handles `vecInner d 0 ξ = 0` + `exp 0 = 1` first.
4. **Add `Complex` namespace disambiguation**: the axiom's own docstring at line 184 warns about "the now-ambiguous `exp_zero` (Complex.exp_zero vs Real.exp_zero)". The corrected recipe uses `Complex.exp_zero` explicitly (the expression `Complex.exp (I * 0)` is `Complex` context, so `Complex.exp_zero` is the right lemma).

### §2.3 — Falsifiability risks (4 known)

| # | Step | Risk | Mitigation |
|---|------|------|------------|
| 1 | `refine ⟨fun _ => 0, fun n hn ξ => ?_⟩` | Elaborator may want `fun _ => (fun _ => 0)` due to `Fin d → ℝ` shape | If error: use `refine ⟨fun (_ : ℕ) (_ : Fin d) => (0 : ℝ), fun n hn ξ => ?_⟩` |
| 2 | `simp [vecInner]` for `vecInner d 0 ξ = 0` | `simp` may not unfold `vecInner` if it's `noncomputable def` not marked `@[simp]` | Fallback: `unfold vecInner; simp` OR `show ∑ i : Fin d, (0 : Fin d → ℝ) i * ξ i = 0; simp` |
| 3 | `rw [show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]` | `Complex.exp_zero` may need ofReal coercion handling | Fallback: `simp [Complex.exp_zero]` |
| 4 | `Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv` chain | `div_eq_mul_inv` rewriting may not produce the exact `/` form | Fallback: rewrite as `ξ i * (Real.sqrt n)⁻¹` explicitly via `rw [show ξ i / Real.sqrt n = ξ i * (Real.sqrt n)⁻¹ from div_eq_mul_inv _ _]` |

The recipe is paste-ready but ~2 Docker iters should be budgeted for the `simp` / elaboration smoothness at risks 2-4.

---

## §3 — `vecInner d 0 ξ = 0` micro-validation

From def at line 48:
```lean
def vecInner (d : ℕ) (x y : Fin d → ℝ) : ℝ := ∑ i : Fin d, x i * y i
```

With `x = 0 : Fin d → ℝ`:
```
vecInner d 0 ξ = ∑ i : Fin d, (0 : Fin d → ℝ) i * ξ i
              = ∑ i : Fin d, 0 * ξ i
              = ∑ i : Fin d, 0
              = 0
```

So `simp [vecInner]` should close it via `Pi.zero_apply` + `zero_mul` + `Finset.sum_const_zero`. If `simp` doesn't, the fallback `unfold vecInner; simp` definitely will.

---

## §4 — `(n : ℝ) ^ (-(1/2)) = 1 / Real.sqrt n` micro-validation

Using bearers from S7 PREP §3.1-§3.2 (re-verified 0-drift at lake SHA):

- `Real.rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹` (Pow/Real.lean:252)
- `Real.sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ))` (Pow/Real.lean:981)

Derivation:
```
(n : ℝ) ^ (-(1/2 : ℝ))
  = ((n : ℝ) ^ (1/2 : ℝ))⁻¹    -- by Real.rpow_neg with hnn : 0 ≤ n
  = (Real.sqrt n)⁻¹              -- by ← Real.sqrt_eq_rpow
```

Then `ξ i * (Real.sqrt n)⁻¹ = ξ i / Real.sqrt n` by `← div_eq_mul_inv`.

Combined into a single `rw` chain: `rw [Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]`.

**Note on `n = 0` edge case**: `Real.sqrt 0 = 0`, so `1/0` would be undefined (in ℝ, `1/0 = 0` by convention). But `hn : n ≠ 0` rules this out at the `funext i` step's substitution. The equivalence `ξ i * (Real.sqrt n)⁻¹ = ξ i / Real.sqrt n` holds in ALL ℝ (the conventional `0/0 = 0` aligns with `_ * 0⁻¹ = _ * 0 = 0`).

---

## §5 — Numerical sanity check (d=1, Sg=[1], n=4, ξ=2)

- `(n : ℝ) ^ (-(1/2)) = 4 ^ (-(1/2)) = 1/2`
- `ξ i * (n : ℝ) ^ (-(1/2)) = 2 * (1/2) = 1`
- `gaussCharFun 1 [[1]] (fun _ => 1) = exp(-1/2)` (since `quadForm = 1·1·1 = 1`)
- `(exp(-1/2))^4 = exp(-2)`
- `gaussCharFun 1 [[1]] (fun _ => 2) = exp(-(2·2)/2) = exp(-2)` (since `quadForm = 1·2·2 = 4`)
- `(exp(-2)) * exp(I * 0) = exp(-2) * 1 = exp(-2)` ✓

Equality `LHS = RHS = exp(-2)` confirmed numerically.

---

## §6 — Updated S7 ACT readiness gate (post-S8 PREP)

| Gate | State | Notes |
|---|---|---|
| (1) Lake pin unchanged | ✅ GREEN | `2df2f0150c…` since S4 PREP |
| (2) Parent file builds clean post-S6 | ✅ GREEN | S6 ACT: Docker 7744/7744 clean |
| (3) S7 ACT bearer drift | ✅ GREEN | S7 PREP §3.1-§3.2: 0 drift for `Real.rpow_neg`, `Real.sqrt_eq_rpow` |
| (4) In-file dependencies present | ✅ GREEN | `gaussian_operator_stable` (167), `quadForm_scale_inv_sqrt` (99), `vecInner` (48) all confirmed |
| (5) Discharge recipe **structurally correct** | ✅ GREEN (NEW) | **S8 PREP §2.2 corrects S7 PREP §4's 3-component refine → 2-component refine + adds RHS simplification + Complex.exp_zero disambiguation** |
| (6) No open PRs touching parent file | ✅ GREEN | 0 open PRs on slug post-S7 PREP merge |
| (7) Line-number drift documented | ✅ GREEN | S7 PREP §2: line 186 for axiom→theorem swap |
| (8) Falsifiability risks documented | ✅ GREEN (NEW) | S8 PREP §2.3: 4 risks with fallback recipes |
| (9) Numerical sanity check | ✅ GREEN (NEW) | S8 PREP §5: d=1, Sg=[1], n=4, ξ=2 confirms equality |

**Gate status**: **GREEN-PASTE-READY** for S7 ACT (now with corrected recipe). The S7 PREP §4's structural bug is closed; the picker should use **S8 PREP §2.2** recipe instead, NOT the predecessor's §4 recipe.

---

## §7 — Honest-status block

- **Mathematical progress this iteration**: zero new theorems, zero axiom discharges. CORRECTS the predecessor S7 PREP's §4 recipe structural error (3-component refine for a 1-existential def). Provides a corrected paste-ready proof (~25 LOC) with falsifiability risks documented.
- **Build-verification status**: unchanged from S6 ACT (Docker 7744/7744 jobs clean). No Lean delta this iteration. Docker daemon hung at S8 PREP claim-time, so corrected recipe is NOT Docker-verified — but the structural correction is verifiable by inspection of the def at line 67-71.
- **Race disclosure**: 0 open PRs on slug at S8 PREP write-time.
- **Axiom delta**: 0 (doc-only PREP).
- **Bug severity**: the S7 PREP §4 recipe bug is **medium**: pasting verbatim would fail at the `refine` step (1 Docker iter wasted) AND lacks the RHS handling (would surface 1 more error after the `refine` was hand-fixed). Estimated picker-time savings: 1-2 Docker iters + the time to re-derive the corrected recipe (~10-20 min).

---

## §8 — Memory pattern alignment

This PREP iteration matches:

1. **`feedback_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready.md`** (variant): the predecessor S7 PREP shipped a paste-ready skeleton, but with a STRUCTURAL bug (not a sorry). Same pattern's prescription — upgrade the skeleton — applies, with the upgrade being a structural correction rather than a sorry-discharge.
2. **`feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`**: S8 PREP §1 re-verifies the actual `HasScalarExponent` def (which is the consumed "typeclass-shape" of the goal) before paste, catching the def-shape mismatch the predecessor PREP missed.

---

## §9 — Files in this PR

| File | Δ | Scope |
|---|---|---|
| `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/state.md` | +X/-Y | prepend "S8 PREP" head section; iter 7→8; refresh nextAction to point at S8 PREP §2.2 recipe (NOT S7 PREP §4) |
| `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/sessions/2026-05-16-s8-prep-s7-recipe-correction.md` | new | this PREP memo |
| `src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01.json` | +X/-Y | `currentState.iteration` 7→8; `currentState.focus` head replacement; `currentState.nextAction` refresh; `lastUpdate`; +1 insight (S7 §4 recipe bug + correction); +1 nextStep (paste S8 §2.2 recipe) |

All edits additive or replace-in-place; no other slug files touched. **No `proofs/` edits** (0 Lean delta).

---

## §10 — Session metrics

| Metric | Value |
|--------|-------|
| Mode | PREP (doc-only) |
| New files | 1 (this session note) |
| Modified files | 2 (state.md, JSON) |
| Lean LOC delta | 0 |
| Theorem delta | 0 |
| Sorry delta | 0 |
| Axiom delta | 0 |
| Recipe corrections | 1 STRUCTURAL bug fix (S7 PREP §4 refine arity 3→2) + 3 ENHANCEMENT additions (RHS handling, Complex.exp_zero disambiguation, 4 falsifiability risks with fallbacks) |
| Numerical sanity checks | 1 (d=1, Sg=[1], n=4, ξ=2 → equality at exp(-2) on both sides) |
| ACT-readiness gate | **GREEN-PASTE-READY** for S7 ACT (with corrected S8 §2.2 recipe), 9/9 gates GREEN (added 2 NEW gates: structural correctness + numerical sanity) |
| Estimated picker savings | 1-2 Docker iters + ~10-20 min recipe re-derivation |

**Axiom delta this session**: 0 (doc-only).
