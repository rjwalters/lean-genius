# S3b ACT — `chartArcLength_comp_mul_left` + `chartArcLength_comp_mul_left_shift` reparam adapters (build-verified 2590 jobs clean)

- **Date**: 2026-06-05
- **Session**: 7 (S1 OBSERVE → S2a → S2b → S3 PREP → S4 STATE-SYNC → S3a → S3b PREP → **S3b ACT**)
- **Phase**: ACT (discharges S3 PREP §8 sub-iter S3b; both reparametrisation adapters)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, ZERO drift vs S3b PREP)

## 1. TL;DR

Both S3 PREP §5 reparametrisation `sorry`s discharged:

```lean
private lemma chartArcLength_comp_mul_left {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2)) 0 (1 / 2) = chartArcLength γ 0 1

private lemma chartArcLength_comp_mul_left_shift {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2 - 1)) (1 / 2) 1 = chartArcLength γ 0 1
```

+86 LOC `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (120 → 206); 0 new
sorries / 0 new axioms; build-verified at Lean v4.26.0 + Mathlib pin
`2df2f0150c…`: 2590 Docker jobs clean (+39 vs S3a's 2551 from 3 new
`Mathlib.Analysis.Calculus.Deriv.*` imports).

The S3b PREP recipe's Option α (`smul_integral_comp_mul_sub` for the right-half
affine shift) was selected for the second adapter; the first adapter uses
`smul_integral_comp_mul_right` (recipe was `_mul_left`, refined to `_mul_right`
in-flight to match the chain rule's `t * 2` form natively, avoiding a
`mul_comm` rewrite — see §3 fix log).

## 2. Final paste (verbatim from Lean source)

### 2.1 First adapter (left half, `[0, 1/2]`)

```lean
private lemma chartArcLength_comp_mul_left {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2)) 0 (1 / 2) = chartArcLength γ 0 1 := by
  simp only [chartArcLength]
  have h_pointwise : Set.EqOn (fun t => ‖deriv (γ ∘ (· * 2)) t‖)
      (fun t => 2 * ‖deriv γ (t * 2)‖) (Set.uIcc (0 : ℝ) (1 / 2)) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    have ht01 : (t * 2) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hγt2 : DifferentiableAt ℝ γ (t * 2) := hγ _ ht01
    have hmul_has : HasDerivAt (fun x : ℝ => x * 2) 2 t := hasDerivAt_mul_const 2
    have hmul : DifferentiableAt ℝ (fun x : ℝ => x * 2) t := hmul_has.differentiableAt
    have h_deriv_mul : deriv (fun x : ℝ => x * 2) t = 2 := hmul_has.deriv
    show ‖deriv (γ ∘ (fun x : ℝ => x * 2)) t‖ = 2 * ‖deriv γ (t * 2)‖
    rw [deriv.scomp t hγt2 hmul, h_deriv_mul, norm_smul, Real.norm_ofNat]
  rw [intervalIntegral.integral_congr h_pointwise,
      intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_right
              (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
              (f := fun s => ‖deriv γ s‖) (c := 2)
  simp only [smul_eq_mul, zero_mul,
    show (1 / 2 : ℝ) * 2 = 1 from by norm_num] at h
  exact h
```

### 2.2 Second adapter (right half, `[1/2, 1]`)

```lean
private lemma chartArcLength_comp_mul_left_shift {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2 - 1)) (1 / 2) 1 = chartArcLength γ 0 1 := by
  simp only [chartArcLength]
  have h_pointwise : Set.EqOn (fun t => ‖deriv (γ ∘ (· * 2 - 1)) t‖)
      (fun t => 2 * ‖deriv γ (t * 2 - 1)‖) (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    have ht01 : (t * 2 - 1) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hγst : DifferentiableAt ℝ γ (t * 2 - 1) := hγ _ ht01
    have hmul_has : HasDerivAt (fun x : ℝ => x * 2 - 1) 2 t :=
      (hasDerivAt_mul_const 2).sub_const 1
    have hmul : DifferentiableAt ℝ (fun x : ℝ => x * 2 - 1) t := hmul_has.differentiableAt
    have h_deriv_mul : deriv (fun x : ℝ => x * 2 - 1) t = 2 := hmul_has.deriv
    show ‖deriv (γ ∘ (fun x : ℝ => x * 2 - 1)) t‖ = 2 * ‖deriv γ (t * 2 - 1)‖
    rw [deriv.scomp t hγst hmul, h_deriv_mul, norm_smul, Real.norm_ofNat]
  rw [intervalIntegral.integral_congr h_pointwise,
      intervalIntegral.integral_const_mul]
  have h_swap : Set.EqOn (fun t : ℝ => ‖deriv γ (t * 2 - 1)‖)
      (fun t => ‖deriv γ (2 * t - 1)‖) (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t _
    show ‖deriv γ (t * 2 - 1)‖ = ‖deriv γ (2 * t - 1)‖
    rw [mul_comm t 2]
  rw [intervalIntegral.integral_congr h_swap]
  have h := intervalIntegral.smul_integral_comp_mul_sub
              (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
              (f := fun s => ‖deriv γ s‖) (c := 2) (d := 1)
  simp only [smul_eq_mul,
    show (2 : ℝ) * (1 / 2) - 1 = 0 from by norm_num,
    show (2 : ℝ) * 1 - 1 = 1 from by norm_num] at h
  exact h
```

## 3. First-build fix log (1 Docker iter)

The S3b PREP §4.1 recipe used `differentiableAt_id.mul_const 2` for the
differentiability of `(· * 2)`. First Docker build (2551 jobs, 1 import set:
S3a baseline) failed with:

```
error: Invalid field `mul_const`: The environment does not contain
       `Exists.mul_const`
  differentiableAt_id
has type
  ∃ f', HasFDerivAt id f' ?m.227
error: `simp` made no progress     -- on `deriv (fun x => x * 2) t = 2`
error: Unknown constant `deriv.scomp`
```

**Root cause**: at v4.26.0, `differentiableAt_id` lives in `FDeriv.Basic`, but
the `DifferentiableAt.mul_const` dot-notation extension lives in `FDeriv.Mul`
(not transitively imported by our pre-S3b imports). Similarly `deriv.scomp`
lives in `Deriv.Comp` (not transitively imported by `Deriv.Basic`).

**Fix** (single edit):

1. Added imports `Mathlib.Analysis.Calculus.Deriv.Mul`, `Mathlib.Analysis.Calculus.Deriv.Add`, `Mathlib.Analysis.Calculus.Deriv.Comp`.
2. Replaced `differentiableAt_id.mul_const 2` with the cleaner direct
   construction `hasDerivAt_mul_const 2 : HasDerivAt (fun x => x * 2) 2 t`,
   then derived `.differentiableAt` and `.deriv` from it. This avoids the
   `Exists.mul_const` dot-notation failure mode regardless of which mul_const
   extension is in scope.
3. For the second adapter's `(· * 2 - 1)`: `(hasDerivAt_mul_const 2).sub_const 1`
   (uses `HasDerivAt.sub_const` from `Deriv.Add`).

Second Docker iter (2590 jobs): clean build, both adapters typecheck, 0
sorries, 0 axioms.

## 4. Refinement vs S3b PREP §4.1 recipe

| Aspect | S3b PREP §4.1 recipe | S3b ACT actual |
|---|---|---|
| Substitution bearer (left half) | `smul_integral_comp_mul_left` (Basic.lean:866; `f (c * x)` form) | `smul_integral_comp_mul_right` (Basic.lean:856; `f (x * c)` form) |
| Why the swap | Recipe wrote `‖deriv γ (2 * t)‖` (PREP's mathematical convention) | Chain rule's `(fun x => x * 2) t = t * 2` natively matches `smul_integral_comp_mul_right`; avoids one `mul_comm` rewrite |
| `differentiableAt_id.mul_const 2` | Recipe used dot-notation chain | Replaced with `hasDerivAt_mul_const 2` (direct, no `FDeriv.Mul` extension needed) |
| Required imports | Recipe listed implicitly via Mathlib SHA pin | Made explicit: `Deriv.Mul`, `Deriv.Add`, `Deriv.Comp` (+39 build jobs) |

These three refinements were discovered at Docker time and shipped in this S3b
ACT PR. No mathematical content change — the proofs are still the 3-lemma
chain (chain rule + norm extraction + integral substitution).

## 5. Bearer drift recheck at pin `2df2f015…`

ZERO drift since S3b PREP (~6 days ago):

| Bearer | File @ pin | Line | Status |
|---|---|---:|---|
| `deriv.scomp` | `Mathlib/Analysis/Calculus/Deriv/Comp.lean` | 146 | ✅ unchanged |
| `hasDerivAt_mul_const` | `Mathlib/Analysis/Calculus/Deriv/Mul.lean` | 326 | ✅ found at expected line |
| `Real.norm_ofNat` | `Mathlib/Analysis/Normed/Group/Basic.lean` | 1097 | ✅ unchanged |
| `intervalIntegral.smul_integral_comp_mul_right` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | 856 | ✅ unchanged |
| `intervalIntegral.smul_integral_comp_mul_sub` | (same file) | 940 | ✅ unchanged |
| `intervalIntegral.integral_const_mul` | (same file) | 775 | ✅ unchanged |
| `intervalIntegral.integral_congr` | (same file) | 1004 | ✅ unchanged |
| `Set.uIcc_of_le` | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` | 76 | ✅ unchanged |
| `HasDerivAt.sub_const` | `Mathlib/Analysis/Calculus/Deriv/Add.lean` | (line 423+) | ✅ found |

## 6. Build verification

```
$ LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01
...
[150s] Building...
✔ [2590/2590] Built Proofs.TriangleInequalityOQ04OQ01 (5.5s)
Build completed successfully (2590 jobs).
=== Build succeeded ===
```

Pin: Lean v4.26.0 + Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Job
count `2551 → 2590` (+39 jobs from the three new `Deriv.{Mul, Add, Comp}`
imports — each adds a small downstream chain).

Sorry count: 0 (unchanged from S3a).
Axiom count: 0 (unchanged from S3a).

## 7. Next ACT (S3c) preview

`chartArcLength_pathTrans` — additivity along `Path.trans`. Bridges this S3b's
adapters with S2b's `chartArcLength_trans`. The path-trans `extend` function
unfolds to:

```
(Path.trans γ₁ γ₂).extend t = if t ≤ 1/2 then γ₁.extend (t * 2)
                                          else γ₂.extend (t * 2 - 1)
```

(Modulo edge cases at exactly `t = 1/2`.) Applying `chartArcLength_trans` at
the midpoint splits the integral into `[0, 1/2]` + `[1/2, 1]`; each adapter
converts the chart-arc-length to the original parameter on the corresponding
γᵢ. Estimated ~20-30 LOC + ~2 IntervalIntegrable side-hypotheses (chain rule
preserves integrability).

After S3c, **S3d** (`chartIntrinsicDist_triangle`, ~10-20 LOC) is the main
calc: nested iInf over `(γ₁ : Path p q)`, `(γ₂ : Path q r)` exchange via
`Real.iInf_add` / `Real.add_iInf` (R2 from S3 PREP §6). If those distributive
laws are not available for `ℝ` (the parent uses `ENNReal.iInf_add`), the
fallback is ad-hoc derivation via the chartArcLength_nonneg bound.

## 8. Anti-targets (no-edit guarantee)

This S3b ACT **strictly does not** modify:

- `problem.md` (immutable since S1 OBSERVE)
- `knowledge.md` (deferred to S6 STATE-SYNC for the prose update)
- Any prior `sessions/*.md` file (S1 through S3b PREP are immutable)
- `proofs/Proofs/TriangleInequalityOQ04.lean` (parent — out of scope)
- `proofs/lakefile.toml`, `proofs/lake-manifest.json` (no manifest bump)
- `src/data/proofs/triangle-inequality-oq-04-oq-01/meta.json` (no per-proof
  metadata changes — that file does not exist for this slug)
- Any `.github/`, `scripts/`, `Makefile`, `.loom/` infrastructure file

**Single new file**:

- `research/problems/triangle-inequality-oq-04-oq-01/sessions/2026-06-05-s3b-act-reparam-adapters.md` (this file)

**Edited files**:

- `proofs/Proofs/TriangleInequalityOQ04OQ01.lean` (+86 LOC; 120 → 206; 3 new
  imports)
- `research/problems/triangle-inequality-oq-04-oq-01/state.md` (S3a head block
  swapped to S3b head block; iteration history table extended)
- `src/data/research/problems/triangle-inequality-oq-04-oq-01.json`
  (`currentState.{phase, iteration, focus, nextAction, attemptCounts, lastUpdate}`
  + `leanFiles[.path == "Proofs/TriangleInequalityOQ04OQ01.lean"].lineCount`
  + `.theoremCount`)

🤖 Generated with [Claude Code](https://claude.com/claude-code)
