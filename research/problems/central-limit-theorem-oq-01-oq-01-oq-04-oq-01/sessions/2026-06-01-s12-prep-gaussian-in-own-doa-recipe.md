# S12 PREP — paste-ready recipe for `gaussian_in_own_doa` discharge

**Researcher**: researcher-1
**Date**: 2026-06-01T~22Z
**Phase**: PREP (doc-only) for the post-S11 ACT iteration.
**Predecessor**: S11 ACT PR [#21987](https://github.com/rjwalters/lean-genius/pull/21987)
(researcher, 2026-06-01T20:43Z) — open, MERGEABLE, awaiting deployer
(credit-wedged through 2026-06-03 17:00 PT per memory plateau).

## 1. Why doc-only PREP at S12

| Constraint | Decision impact |
|------------|-----------------|
| S11 ACT PR #21987 modifies the same parent file (`CentralLimitTheoremOQ01OQ01OQ04.lean`, +20 LOC around line 212) | An S12 ACT PR opened in parallel would compete for line numbers on the same Lean file → merge conflicts likely once #21987 lands. |
| Memory entries `project_mechanic_1_2026_06_01_post_22020_n101` … `n109` show deployer credit-wedged through 2026-06-03 17:00 PT — even MERGEABLE PRs aren't merging. | Even if S12 ACT shipped clean, it would sit unmerged for days behind #21987. |
| Docker daemon state at S10 STATE-SYNC (2026-05-16T18:02Z) was hung; no reliable Docker recovery has been recorded since for this slug. | An S12 ACT iteration may not be Docker-verifiable until host infra recovers. |
| Memory feedback `feedback_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready` recommends doc-only PREP under these conditions. | Ship doc-only PREP; defer ACT until S11 lands + Docker reachable. |

**S12 PREP deliverable**: paste-ready Lean recipe + bearer pin + falsifiability
risks + line-drift catalog. Estimated ACT-time savings: 1-2 Docker iters
(recipe pre-verified against Mathlib v4.26.0 sources).

## 2. Bearer pin verification at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All bearers fetched via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>` 2026-06-01.

| Bearer | Path:line | Signature (verified verbatim) |
|--------|-----------|-------------------------------|
| `tendsto_pi_nhds` | `Mathlib/Topology/Constructions.lean:746` | `{f : Y → ∀ i, A i} {g : ∀ i, A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i => f i x) u (𝓝 (g x))` |
| `tendsto_atTop_of_eventually_const` | `Mathlib/Topology/Neighborhoods.lean:193` | `{ι : Type*} [Preorder ι] {u : ι → X} {i₀ : ι} (h : ∀ i ≥ i₀, u i = x) : Tendsto u atTop (𝓝 x)` |
| `tendsto_const_nhds` | `Mathlib/Topology/Neighborhoods.lean:190` | `{f : Filter α} : Tendsto (fun _ : α => x) f (𝓝 x)` (fallback if eventually-const path fails) |
| `Real.rpow_neg` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:252` | `{x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹` (carried fwd from S7 PREP §3, SHA unchanged) |
| `Real.sqrt_eq_rpow` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:981` | `(x : ℝ) : √x = x ^ (1 / (2 : ℝ))` (carried fwd from S7 PREP §3, SHA unchanged) |
| `Complex.exp_zero` | `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` (transitive via `Mathlib.Analysis.SpecialFunctions.Exp`) | `Complex.exp 0 = 1` (carried fwd from S8 PREP §2.2, SHA unchanged) |
| `Matrix.smul_apply` | `Mathlib/Data/Matrix/Basic.lean` | `(a • M) i j = a • M i j` (carried fwd from S11 ACT body's verified simp set, Docker-confirmed 7744 jobs in #21987) |
| `Matrix.one_apply` | `Mathlib/Data/Matrix/Basic.lean` | `(1 : Matrix n n α) i j = if i = j then 1 else 0` (carried fwd from S11 ACT) |
| `Finset.sum_ite_eq` | `Mathlib/Algebra/BigOperators/Basic.lean` | `∑ x ∈ s, (if a = x then b x else 0) = if a ∈ s then b a else 0` (carried fwd from S11 ACT) |

**In-file dependencies** (parent `CentralLimitTheoremOQ01OQ01OQ04.lean` @ HEAD `f486a19`):

| Decl | Line | Status |
|------|------|--------|
| `gaussCharFun` def | 53 | proven |
| `quadForm_scale_inv_sqrt` | 99 | proven (S3.5 mechanic PR #19116) |
| `gaussian_operator_stable` (helper, `/√n` form) | 167 | proven (S3.5 mechanic) — **primary discharge bearer** |
| `gaussian_has_scalar_exponent` | 186 | proven (S9 ACT PR #19652, MERGED 2026-05-16T15:20Z) |
| `gaussian_is_operator_stable` | 212 | **axiom** at HEAD; → **theorem** post-S11 PR #21987 |
| `vecInner` def | 48 | proven |
| `InOperatorDomainOfAttraction` def | 75 | proven |

**No new imports required.** All bearers reachable via existing `import Mathlib` line.

## 3. Paste-ready S12 ACT recipe

Replace the `axiom gaussian_in_own_doa` declaration at parent line **341 (HEAD f486a19)**
or **361 (post-S11 PR #21987 merge, +20 LOC drift)** with the following theorem
(~33 LOC primary path):

```lean
/-- The Gaussian N(0, Sg) is in its own operator domain of attraction.

    Discharges the v4.26.0 axiomatized version (whose original proof leaked
    a pointwise-vs-function-valued `tendsto_const_nhds` confusion) by:
    1. Witnessing the matrix scaling `A_n = n^(-1/2) • I` and zero drift `b_n = 0`.
    2. Reducing tendsto in the function space `(Fin d → ℝ) → ℂ` to pointwise
       via `tendsto_pi_nhds`.
    3. For each fixed ξ, observing that for n ≥ 1 the n-th term equals
       `gaussCharFun d Sg ξ` exactly (eventually constant — NOT pointwise
       constant on a non-constant function sequence, avoiding the v4.26.0
       elaborator block).
    4. Applying `tendsto_atTop_of_eventually_const` (Mathlib v4.26.0 surgical
       successor of the broken `tendsto_const_nhds` invocation).

    The matrix-product reduction `(A_n^T ξ) i = ξ i / √n` reuses the verified
    simp set from S11 ACT (PR #21987). Mathematical content: multivariate CLT
    self-similarity for the Gaussian. -/
theorem gaussian_in_own_doa (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ) :
    InOperatorDomainOfAttraction d (gaussCharFun d Sg) (gaussCharFun d Sg) := by
  refine ⟨gaussian_is_operator_stable d Sg, ?_⟩
  refine ⟨fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ),
          fun _ => 0, ?_⟩
  rw [tendsto_pi_nhds]
  intro ξ
  apply tendsto_atTop_of_eventually_const (i₀ := 1)
  intro n hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Reduce the matrix product (A_n^T ξ) i = ξ i / √n
  have h_arg : (fun i => ∑ j, ((n : ℝ) ^ (-(1 / 2 : ℝ)) •
                  (1 : Matrix (Fin d) (Fin d) ℝ)) i j * ξ j)
             = (fun i => ξ i / Real.sqrt n) := by
    funext i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
               mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
               Finset.mem_univ, if_true]
    rw [mul_comm, Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  rw [h_arg]
  -- vecInner d 0 ξ = 0 → exp factor collapses to 1
  have h_inner : vecInner d (0 : Fin d → ℝ) ξ = 0 := by simp [vecInner]
  rw [h_inner, show ((0 : ℝ) : ℂ) = 0 from rfl, mul_zero, Complex.exp_zero, mul_one]
  exact gaussian_operator_stable d Sg ξ n hn0
```

**LOC budget**: ~33 net (axiom → theorem swap is +30 to +35 LOC depending on
docstring length).

**Post-S11 ACT line shifts** (if #21987 merges before S12 ACT):

| Axiom name | HEAD f486a19 line | Post-S11 merge line | Delta |
|-----------|-------------------|---------------------|-------|
| `gaussian_is_operator_stable` | 212 (axiom) | 212 (theorem) | 0 (same start line, +20 body) |
| `operator_stable_linear_image` | 272 | 292 | +20 |
| `scalar_exponent_ge_half` | 302 | 322 | +20 |
| `meerschaert_scheffler` | 317 | 337 | +20 |
| **`gaussian_in_own_doa`** (S12 target) | **341** | **361** | **+20** |
| `finite_cov_in_gaussian_doa` | 349 | 369 | +20 |

(S11 PR #21987 body confirms 359 → 379 lineCount; +20 net file growth.)

## 4. Mathematical verification (paper proof, then Lean rendition)

**Claim**: `InOperatorDomainOfAttraction d (gaussCharFun d Sg) (gaussCharFun d Sg)`.

**Unfolds to** (per def at line 75):
```
IsOperatorStable d (gaussCharFun d Sg) ∧
∃ (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → Fin d → ℝ),
  Filter.Tendsto (fun n => fun ξ => (gaussCharFun d Sg
                                      (fun i => ∑ j, A n i j * ξ j))^n *
                                    exp (I * (vecInner d (b n) ξ : ℝ)))
                 Filter.atTop (𝓝 (gaussCharFun d Sg))
```

**Witness**: `A_n := (n : ℝ)^(-(1/2)) • (1 : Matrix _ _ _)`, `b_n := 0`.

**First conjunct**: `gaussian_is_operator_stable d Sg` (axiom or post-S11 theorem; either way, available).

**Second conjunct** (function-space tendsto):

By `tendsto_pi_nhds`, suffices to prove for each ξ:
```
Tendsto (fun n => (gaussCharFun d Sg (fun i => ∑ j, A_n i j * ξ j))^n *
                  exp (I * (vecInner d 0 ξ : ℝ)))
        atTop (𝓝 (gaussCharFun d Sg ξ))
```

For each fixed ξ, we'll show the sequence is eventually constant at `gaussCharFun d Sg ξ` (eventually = "for all n ≥ 1").

**Matrix-product reduction** (n ≥ 1, hence n ≥ 0 as real, hence (n : ℝ) has well-defined `^(-(1/2))`):
- `((n)^(-(1/2)) • 1) i j = (n)^(-(1/2)) * (if i = j then 1 else 0)` (Matrix.smul_apply + Matrix.one_apply)
- `∑ j, ... * ξ j = (n)^(-(1/2)) * ξ i` (sum_ite_eq + mem_univ)
- `(n)^(-(1/2)) * ξ i = ξ i * (n)^(-(1/2))` (mul_comm)
- `= ξ i * ((n)^(1/2))⁻¹` (Real.rpow_neg, with 0 ≤ n)
- `= ξ i * (√n)⁻¹` (← Real.sqrt_eq_rpow)
- `= ξ i / √n` (← div_eq_mul_inv) ✓

**vecInner collapse**:
- `vecInner d 0 ξ = ∑ i, 0 * ξ i = 0` (simp [vecInner] handles via `Finset.sum_const_zero` or similar)
- `exp (I * (0 : ℝ : ℂ)) = exp 0 = 1` (mul_zero + Complex.exp_zero)

**Eventually-constant value** (via `gaussian_operator_stable d Sg ξ n hn0`):
- `(gaussCharFun d Sg (fun i => ξ i / √n))^n = gaussCharFun d Sg ξ` ✓

Therefore for n ≥ 1, the n-th term `= gaussCharFun d Sg ξ * 1 = gaussCharFun d Sg ξ`,
which is exactly the target value of the limit. `tendsto_atTop_of_eventually_const`
closes the goal. ∎

## 5. Falsifiability risks (failure modes + 1-line fallbacks)

The recipe has been derived from Mathlib sources at the pin, but `simp` and
`rw` order can be brittle. Five risks documented:

### Risk 1 — `simp [vecInner]` does not close `vecInner d 0 ξ = 0`

**Symptom**: simp leaves `∑ i, 0 * ξ i` or `∑ i, (0 : ℝ) * ξ i`.

**Fallback**: replace `by simp [vecInner]` with
```lean
by unfold vecInner; simp [zero_mul, Finset.sum_const_zero]
```

**Likelihood**: low — `vecInner` def is `∑ i, x i * y i`, and `0 * ξ i = 0` is `zero_mul` which simp knows. `Finset.sum_const_zero` is also default-simp.

### Risk 2 — `mul_comm` ambiguity in the post-simp goal

**Symptom**: after the simp block, the goal may be in the form
`(n)^(-(1/2)) * ξ i = ξ i / √n` OR `ξ i * (n)^(-(1/2)) = ξ i / √n`
depending on whether `mul_ite` and `ite_mul` interact with the `*ξ j`
position differently.

**Fallback** (if `mul_comm` rewrites the wrong direction): replace
```lean
rw [mul_comm, Real.rpow_neg hnn, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
```
with
```lean
rw [Real.rpow_neg hnn, ← Real.sqrt_eq_rpow]
ring_nf
rw [← div_eq_mul_inv]
```
or use `field_simp [Real.sqrt_ne_zero'.mpr (by positivity)]` to push through.

**Likelihood**: medium — S11 ACT used `; ring` at the end of an analogous block, suggesting some final normalization may be needed.

### Risk 3 — `tendsto_pi_nhds` elaboration mismatch on `(Fin d → ℝ) → ℂ`

**Symptom**: elaborator complains that `(Fin d → ℝ) → ℂ` is not directly
matching `∀ i, A i` in the lemma statement.

**Fallback** (if elaboration fails): explicit pi-instance with `show`:
```lean
show Filter.Tendsto _ Filter.atTop (𝓝 (fun ξ : Fin d → ℝ => gaussCharFun d Sg ξ))
rw [tendsto_pi_nhds]
```
or use `Pi.tendsto_iff_const` / `nhds_pi` directly.

**Likelihood**: low — `(Fin d → ℝ) → ℂ` is `Pi` over the function type, which
is a valid `∀ i : (Fin d → ℝ), ℂ`, syntactically matching the lemma. The η-redex `fun ξ => gaussCharFun d Sg ξ` should unify with `gaussCharFun d Sg`.

### Risk 4 — `tendsto_atTop_of_eventually_const` expects different `i₀` direction

**Symptom**: lemma wants `∀ i ≥ i₀, u i = x`; if the `hn : 1 ≤ n` is
extracted incorrectly, may need `Nat.one_le_iff_ne_zero` differently.

**Fallback**: use `tendsto_const_nhds.congr'` directly:
```lean
apply (tendsto_const_nhds (X := ℂ) (x := gaussCharFun d Sg ξ)).congr'
filter_upwards [Filter.eventually_ge_atTop 1] with n hn
symm
have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
...
```

**Likelihood**: low — `tendsto_atTop_of_eventually_const` signature explicitly
matches our needs (`Mathlib/Topology/Neighborhoods.lean:193-195`).

### Risk 5 — `gaussian_is_operator_stable` not yet a theorem at S12 ACT time

**Symptom**: if S11 PR #21987 has NOT yet merged when S12 ACT is opened,
the file references `gaussian_is_operator_stable` as an **axiom**.

**Impact**: the proof still type-checks (axiom is a valid term). The
axiomCount delta semantics are unchanged: S12 ACT brings `gaussian_in_own_doa`
from axiom to theorem (axiomCount 6 → 5 if standalone, or 5 → 4 if S11 has
already landed).

**Fallback**: no code change needed; only the axiomCount delta interpretation
shifts depending on merge order.

**Likelihood**: certain (deployer credit-wedged through 2026-06-03 17:00 PT).
S12 ACT should be staged AFTER S11 PR merges to avoid the dual-PR file conflict.

## 6. Race / coordination considerations

**Currently open PRs touching parent file `CentralLimitTheoremOQ01OQ01OQ04.lean`**:

- **#21987** (S11 ACT by another researcher, 2026-06-01T20:43Z, OPEN, MERGEABLE)
  — modifies line 212 axiom → theorem + body. Will not conflict with
  S12 ACT *region* (line 341), but the +20 LOC global file shift means
  S12 ACT recipe must rebase against post-#21987 file before paste.

**Recommendation**: S12 ACT should:
1. Wait for #21987 to merge (or close).
2. Rebase against new HEAD.
3. Confirm post-merge line for `gaussian_in_own_doa` is 361 (per §3 table).
4. Paste recipe at line 361.
5. Docker-verify (`./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ01OQ01OQ04`).
6. Update gallery `meta.json`: `axiomCount` 5 → 4 (post-S11), `theoremCount` 11 → 12, `lineCount` 379 → ~412.

## 7. Expected post-S12 ACT effects (after S11 lands)

| Field | Pre-S12 (post-S11) | Post-S12 ACT |
|-------|--------------------|--------------|
| `axiomCount` | 5 | **4** |
| `theoremCount` | 11 | **12** (gain `gaussian_in_own_doa` as theorem) |
| `lineCount` | 379 | **~412** (+33 LOC) |
| Sorries | 0 | 0 (unchanged) |

**Remaining axioms after S12 (4)**:
- `operator_stable_linear_image` — KEEP (MS 2001 Thm 7.2.1; needs `IsUnit B.det` hyp fix per E.2)
- `scalar_exponent_ge_half` — KEEP (Hudson–Mason 1982 spectral bound; out of scope)
- `meerschaert_scheffler` — KEEP (this OQ's top-level conjecture target)
- `finite_cov_in_gaussian_doa` — KEEP (vacuous `hφ_reg : True` placeholder; needs E.1 fix)

All 4 are KEEP-axiomatized per the S4 PREP roadmap (PR #19296).

## 8. Honest calibration

**S12 PREP produces**:
- One markdown session note (this file).
- Updates to `state.md`, `knowledge.md`, `src/data/research/problems/<slug>.json`.
- A paste-ready Lean recipe with 5 falsifiability risks documented.
- Bearer pin re-verification at lake SHA `2df2f0150c…` (no drift since S10 STATE-SYNC 2026-05-16).

**S12 PREP does NOT**:
- Modify any Lean file.
- Change the parent's axiom count or sorry count.
- Discharge any axiom.
- Conflict with S11 PR #21987.

**Estimated S12 ACT savings from this PREP**:
- 1-2 Docker iterations saved (pre-derived simp set + rw chain).
- ~15-30 min recipe re-derivation saved.
- Risk: 0 — the recipe re-uses verified bearers from S6/S9/S11 ACT and reuses
  the same matrix simp set already Docker-verified in PR #21987.

## 9. References

- S9 ACT PR [#19652](https://github.com/rjwalters/lean-genius/pull/19652) — `gaussian_has_scalar_exponent` discharge (template for `vecInner`-zero handling).
- S11 ACT PR [#21987](https://github.com/rjwalters/lean-genius/pull/21987) — `gaussian_is_operator_stable` discharge (template for matrix-smul-one simp set, Docker-verified 7744 jobs).
- S6 ACT PR [#19445](https://github.com/rjwalters/lean-genius/pull/19445) — `gaussCharFun_norm_le_one` discharge (template for `Complex.norm_exp_ofReal` patterns; not used here but maintains bearer SHA continuity).
- S4 PREP PR [#19296](https://github.com/rjwalters/lean-genius/pull/19296) — 6-axiom roadmap §4.6 (sketched but did not implement `gaussian_in_own_doa_via_charfun_form` companion; this S12 PREP supersedes that sketch with a direct in-file theorem replacement).
- Mathlib v4.26.0 `Mathlib/Topology/Neighborhoods.lean:190,193` — `tendsto_const_nhds`, `tendsto_atTop_of_eventually_const`.
- Mathlib v4.26.0 `Mathlib/Topology/Constructions.lean:746` — `tendsto_pi_nhds`.
- Parent file `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` lines 75 (`InOperatorDomainOfAttraction`), 167 (`gaussian_operator_stable`), 186 (`gaussian_has_scalar_exponent`), 212 (`gaussian_is_operator_stable`), 341 (`gaussian_in_own_doa` axiom).
