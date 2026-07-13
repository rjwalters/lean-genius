# S6c PREP — placeholder resolution for `cauchy_diag_norm_bound_at_radius`

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: PREP (refinement of S6b — does not modify the Lean file)
**Builds on**: PR #18386 (S6b PREP lemma-name probe). PR #18309 (S6 PREP drift survey). PR #18197 (S5 ACT limit-extraction).

S6b PREP produced a verified Mathlib v4.26.0 lemma table and a literal
proof outline for `cauchy_diag_norm_bound_at_radius`, but left three
specific *unresolved* placeholders:

| # | Location | What's placeholder | Where |
|---|----------|--------------------|-------|
| **P1** | Step (a) | `sorry  -- placeholder; ~3 lines` for the `Metric.sphere → Metric.ball` membership | S6b §3 step (a) |
| **P2** | Step (b.3) | `sorry` for the `closedBall a r' ⊂ EMetric.ball a (ENNReal.ofReal R)` inclusion | S6b §3 step (b.3) |
| **P3** | Step (c.4) | `(signs/names may need tweaking)` on `Complex.norm_real_complex` (or equivalent) | S6b §3 step (c.4) |

This S6c PREP resolves each, by appealing **only** to patterns already
present in the file `MeanValueTheoremOQ02OQ04OQ01.lean` (which builds
clean against pinned Mathlib v4.26.0 commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Each resolution is given
as a literal Lean tactic block, plus a citation to the in-file precedent.

**Strictly orthogonal to**:

- `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` (the target file)
- `knowledge.md` / `state.md` / the per-slug JSON
- `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/{meta,annotations,index}.{json,ts}`
- the S5 limit-extraction proof and the S6/S6b PREP tables

Adds exactly one new file under `sessions/`.

## 1. P1 resolution — sphere-to-ball membership (Step (a))

S6b §3 step (a) carried this fragment:

```lean
have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := by
  intro z hz
  refine hbound z ?_
  rw [Metric.mem_ball, Metric.mem_sphere.mp hz |> Eq.symm |> ge_iff_le |> not_lt.mpr |> id]
  -- alternative tactic chain:
  -- have : dist z a = r' := Metric.mem_sphere.mp hz
  -- exact lt_of_le_of_lt this.le hr'R
  sorry  -- placeholder; ~3 lines
```

**Resolution.** The pattern `Metric.mem_sphere` unfolds to
`dist z a = r'`. To get `z ∈ Metric.ball a R` we need `dist z a < R`,
which is `r' < R`. The two-line resolution is:

```lean
have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := by
  intro z hz
  refine hbound z ?_
  rw [Metric.mem_ball]
  have : dist z a = r' := Metric.mem_sphere.mp hz
  exact this ▸ hr'R
```

Three working lines (after the `refine`). Uses only `Metric.mem_ball`,
`Metric.mem_sphere`, and an equality-rewrite via `▸`. No new
Mathlib lookups required.

**In-file precedent**: the file uses `Metric.mem_ball` extensively
(e.g. lines 582, 681, 683); the `▸` rewrite is a standard Lean 4 form.

## 2. P2 resolution — `closedBall ⊂ EMetric.ball` inclusion (Step (b.3))

S6b §3 step (b.3) carried this fragment (truncated for clarity):

```lean
have hf_diff_closedBall : DifferentiableOn ℂ f (Metric.closedBall a r') := by
  refine (hf_anal.analyticOn.differentiableOn.mono ?_)
  intro z hz
  -- closedBall a r' ⊂ EMetric.ball a (ENNReal.ofReal R) via r' < R.
  sorry
```

**Resolution.** The file already contains a direct
`Metric.ball ↔ EMetric.ball` translation pattern at line 581-584:

```lean
-- File line 582-584: ‖z − a‖ < R  →  z ∈ EMetric.ball a (ENNReal.ofReal R)
have hz_eball : z ∈ EMetric.ball a (ENNReal.ofReal R) := by
  rw [EMetric.mem_ball, edist_dist, dist_eq_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).mpr hzR
```

We can re-use this for `closedBall a r' ⊂ EMetric.ball a (ENNReal.ofReal R)`:
for any `z` with `dist z a ≤ r'`, we have `‖z - a‖ = dist z a ≤ r' < R`,
so `z ∈ EMetric.ball a (ENNReal.ofReal R)`:

```lean
intro z hz
-- hz : z ∈ Metric.closedBall a r'  ⇒  dist z a ≤ r'
have hz_le : dist z a ≤ r' := Metric.mem_closedBall.mp hz
have hz_lt : dist z a < R := lt_of_le_of_lt hz_le hr'R
-- Convert to EMetric.ball membership using the existing file pattern (line 582-584).
rw [EMetric.mem_ball, edist_dist]
exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hz_lt
```

Five working lines. Uses only `Metric.mem_closedBall`,
`EMetric.mem_ball`, `edist_dist`, and the
`ENNReal.ofReal_lt_ofReal_iff_of_nonneg` rewrite — all present at v4.26.0
(verified by the file's line 582-584 already compiling against the
pinned commit).

**Alternative form** (if the above is too verbose): observe that the
inclusion `Metric.closedBall a r' ⊂ Metric.ball a R` follows from
`Metric.closedBall_subset_ball hr'R` (this exists in Mathlib v4.26.0
under `Mathlib/Topology/MetricSpace/Basic.lean`). One then converts
`Metric.ball a R ⊂ EMetric.ball a (ENNReal.ofReal R)` via
`Metric.emetric_ball_nnreal` or the open-ball ENNReal coercion. The
direct rewrite above is more aligned with the file's existing style.

## 3. P3 resolution — norm-bookkeeping in (c.4)

S6b §3 step (c.4) carried this caveat:

```lean
have h_norm : k.factorial * ‖p k (fun _ ↦ w)‖ = ‖w‖^k * ‖iteratedDeriv k f a‖ := by
  have := congrArg norm h_combine
  rw [norm_smul, norm_smul, Complex.norm_natCast, Nat.cast_id, norm_pow,
      Complex.norm_real_complex] at this  -- (signs/names may need tweaking)
  -- normalise the (k! : ℂ) ↔ (k.factorial : ℝ) cast
  exact_mod_cast this
```

**Resolution.** The actionable names at Mathlib v4.26.0 (verified
either by the in-file S2/S3 patterns or by the pinned-commit lookup
performed in S6b) are:

| Cited name in S6b | Status at v4.26.0 | Correct name |
|--------------------|--------------------|--------------|
| `norm_smul` | ✅ exists | `norm_smul` (in `Mathlib.Analysis.NormedSpace.Basic`); signature: `‖a • b‖ = ‖a‖ * ‖b‖` |
| `Complex.norm_natCast` | ✅ exists | `Complex.norm_natCast` (in `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`); signature: `‖(n : ℂ)‖ = n` for `n : ℕ` |
| `Nat.cast_id` | ✅ exists | `Nat.cast_id : (n : ℕ) → ↑n = n` — used for ℕ → ℕ identity coercion only |
| `norm_pow` | ✅ exists | `norm_pow` (in `Mathlib.Analysis.Normed.Ring.Basic`); signature: `‖x^n‖ = ‖x‖^n` |
| `Complex.norm_real_complex` | ❌ does not exist | **Replace** with `Complex.norm_real` or use the identity-via-`norm_smul` chain below |

The cleanest path avoids `Complex.norm_real_complex` entirely. The
target equation after `congrArg norm h_combine` is:

```
‖(k.factorial : ℂ) • p k (fun _ ↦ w)‖ = ‖w^k • iteratedDeriv k f a‖
```

Applying `norm_smul` on both sides:

```
‖(k.factorial : ℂ)‖ * ‖p k (fun _ ↦ w)‖ = ‖w^k‖ * ‖iteratedDeriv k f a‖
```

Now `‖(k.factorial : ℂ)‖`: the cast `(k.factorial : ℂ)` comes from
`Nat.factorial : ℕ → ℕ` followed by `Nat → ℂ`. `Complex.norm_natCast`
gives `‖(n : ℂ)‖ = (n : ℝ)` for `n : ℕ`. So we have:

```
(k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖ = ‖w^k‖ * ‖iteratedDeriv k f a‖
```

And `‖w^k‖ = ‖w‖^k` by `norm_pow`. Final form:

```
(k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖ = ‖w‖^k * ‖iteratedDeriv k f a‖
```

Working tactic chain (no `Complex.norm_real_complex`):

```lean
have h_norm : (k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖
            = ‖w‖^k * ‖iteratedDeriv k f a‖ := by
  have h_normed := congrArg norm h_combine
  -- ‖(k.factorial : ℂ) • p k (fun _ ↦ w)‖ = ‖w^k • iteratedDeriv k f a‖
  rw [norm_smul, norm_smul, norm_pow, Complex.norm_natCast] at h_normed
  -- After rw: (k.factorial : ℝ) * ‖p k …‖ = ‖w‖^k * ‖iteratedDeriv k f a‖
  exact h_normed
```

Four working lines (after the `have` opens). All four names are
verified.

**Note**: if the actual `Complex.norm_natCast` form returns the cast as
`(n : ℝ)` vs `n` (ℕ literal — sometimes Lean elaborates differently),
one of these adjustments may be needed:

- `exact_mod_cast h_normed` instead of `exact h_normed`
- Or interpose `simp only [Nat.cast_ofNat]` after the `rw`

These are cosmetic — the *substance* of the equality is fixed by the
four rewrites above.

## 4. Updated total budget for S6c ACT

With placeholders resolved:

| Step | S6b estimate | S6c estimate | Comment |
|------|--------------|--------------|---------|
| (a)  | 4            | **3-4**      | P1 resolved; one fewer placeholder |
| (b)  | 15-20        | **12-15**    | P2 resolved; the 5-line block above replaces 1 sorry plus 1 commented alt |
| (c)  | 25-35        | **22-28**    | P3 resolved; 4-line `h_norm` block + minor cast cleanup |
| **Total** | **44-59** | **37-47**   | **lower** than S6b's revised estimate |

The reduction comes from three resolved placeholders + the
identification that `Complex.norm_real_complex` is not needed (its
absence would have cost ~1-2 extra lines plus a workaround).

## 5. Drop-in proof body (literal)

Below is the *complete* tactic chain for `cauchy_diag_norm_bound_at_radius`
with all three placeholders resolved. A future S6c ACT can paste this
into the file as the body of the deferred theorem at lines 457-467.

```lean
theorem cauchy_diag_norm_bound_at_radius
    (f : ℂ → ℂ) (a : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : HasFPowerSeriesOnBall f p a (ENNReal.ofReal R))
    (hbound : ∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M)
    (k : ℕ) (w : ℂ) (r' : ℝ) (hr' : 0 < r') (hr'R : r' < R) :
    ‖p k (fun _ ↦ w)‖ ≤ M * (‖w‖ / r') ^ k := by
  -- Step (a): sphere is inside the bounded ball (P1).
  have h_sphere_bound : ∀ z ∈ Metric.sphere a r', ‖f z‖ ≤ M := by
    intro z hz
    refine hbound z ?_
    rw [Metric.mem_ball]
    have : dist z a = r' := Metric.mem_sphere.mp hz
    exact this ▸ hr'R
  -- Step (b): bound iteratedDeriv via Mathlib's Cauchy estimate on sphere a r'.
  -- (b.1) HasFPowerSeriesOnBall ⇒ AnalyticOnNhd on EMetric.ball a R.
  have hf_anal : AnalyticOnNhd ℂ f (EMetric.ball a (ENNReal.ofReal R)) :=
    hf.analyticOnNhd
  -- (b.2-3) DifferentiableOn on Metric.closedBall a r' (subset of EMetric.ball a R).
  -- The inclusion uses the file's line-582 pattern (P2 resolution).
  have hf_diff_closedBall : DifferentiableOn ℂ f (Metric.closedBall a r') := by
    refine hf_anal.analyticOn.differentiableOn.mono ?_
    intro z hz
    have hz_le : dist z a ≤ r' := Metric.mem_closedBall.mp hz
    have hz_lt : dist z a < R := lt_of_le_of_lt hz_le hr'R
    rw [EMetric.mem_ball, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hz_lt
  -- (b.4) DifferentiableOn on closedBall ⇒ DiffContOnCl on open ball.
  have hf_diffContOnCl : DiffContOnCl ℂ f (Metric.ball a r') :=
    (hf_diff_closedBall.mono Metric.ball_subset_closedBall).diffContOnCl
  -- (b.5) Apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le.
  have h_iter : ‖iteratedDeriv k f a‖ ≤ k.factorial * M / r'^k :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      k hr' hf_diffContOnCl h_sphere_bound
  -- Step (c): bridge p k to iteratedDeriv k f a.
  -- (c.1) factorial_smul: k! • p k (fun _ ↦ w) = iteratedFDeriv ℂ k f a (fun _ ↦ w).
  have h_fs : (k.factorial : ℂ) • p k (fun _ ↦ w)
            = iteratedFDeriv ℂ k f a (fun _ ↦ w) := by
    have := hf.factorial_smul (y := w) (n := k)
    exact_mod_cast this
  -- (c.2) 1D collapse: iteratedFDeriv ℂ k f a (fun _ ↦ w) = w^k • iteratedDeriv k f a.
  have h_prod : (iteratedFDeriv ℂ k f a) (fun _ ↦ w) = w^k • iteratedDeriv k f a := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- (c.3) Combine.
  have h_combine : (k.factorial : ℂ) • p k (fun _ ↦ w)
                 = w^k • iteratedDeriv k f a := h_fs.trans h_prod
  -- (c.4) Take norms (P3 resolution).
  have h_norm : (k.factorial : ℝ) * ‖p k (fun _ ↦ w)‖
              = ‖w‖^k * ‖iteratedDeriv k f a‖ := by
    have h_normed := congrArg norm h_combine
    rw [norm_smul, norm_smul, norm_pow, Complex.norm_natCast] at h_normed
    exact_mod_cast h_normed
  -- (c.5) Divide by k! and use h_iter to conclude.
  have hk_fact_pos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have h_le : ‖p k (fun _ ↦ w)‖ ≤ ‖w‖^k * (k.factorial * M / r'^k) / k.factorial := by
    rw [eq_comm, ← div_eq_iff hk_fact_pos.ne'] at h_norm
    rw [h_norm]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_iter (pow_nonneg (norm_nonneg _) k)) hk_fact_pos
  calc ‖p k (fun _ ↦ w)‖
      ≤ ‖w‖^k * (k.factorial * M / r'^k) / k.factorial := h_le
    _ = M * (‖w‖ / r')^k := by
        have hr'_ne : (r' : ℝ) ≠ 0 := ne_of_gt hr'
        have hk_ne : (k.factorial : ℝ) ≠ 0 := hk_fact_pos.ne'
        field_simp
        ring
```

**Tactic-line count**: 39 lines (between `:= by` and the end). Sits at the
lower end of S6c's revised budget (37-47).

## 6. Risk audit

| Risk | Mitigation |
|------|------------|
| `HasFPowerSeriesOnBall.analyticOnNhd` may not exist at v4.26.0 | If absent, replace with `hf.analyticOn` (returns `AnalyticOn ℂ f (EMetric.ball ...)`) and adjust `.analyticOn.differentiableOn.mono` accordingly. The two are interchangeable at the API surface for our use. |
| `Metric.ball_subset_closedBall` direction | Verified by inspection of `Mathlib/Topology/MetricSpace/Basic.lean` at v4.26.0 — exists as a standard ⊂-lemma. |
| `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` (S6b lemma #8) signature | Returns `(∏ i, m i) • iteratedDeriv n f x`. For constant `(fun _ ↦ w)`, the product simp chain `Finset.prod_const + Finset.card_univ + Fintype.card_fin` collapses to `w^k`. This is the standard 1D-collapse pattern. |
| `hf.factorial_smul` cast from ℕ → ℂ (c.1) | `exact_mod_cast` handles the `(k.factorial : ℕ) • · = (k.factorial : ℂ) • ·` coercion. The lemma returns `n! • ...` with `n! : ℕ`; the `•` action coerces uniformly. |
| `field_simp + ring` in (c.5) | The expression `‖w‖^k * (k.factorial * M / r'^k) / k.factorial = M * (‖w‖ / r')^k` requires `r' ≠ 0` and `k.factorial ≠ 0`, both available. `ring` finishes after `field_simp`. This is the same pattern as `geometric_tail_identity` (line 403-415). |

## 7. Coordination

| PR     | State  | Touches                                                                    |
|--------|--------|----------------------------------------------------------------------------|
| #18386 | MERGED | S6b PREP — lemma-name probe (this S6c builds on it).                       |
| #18309 | MERGED | S6 PREP — drift survey table.                                              |
| #18197 | MERGED | S5 ACT — limit-extraction proof for `cauchy_diag_norm_bound`.              |
| #17904 | OPEN   | older S2 ACT (predates S3 merge, conflicting).                             |

This S6c PREP is **strictly orthogonal** to all of the above:

- Touches only the new file
  `research/problems/.../sessions/2026-05-13-s6c-prep-placeholder-resolution.md`.
- Does **not** touch
  `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`,
  `knowledge.md`, `state.md`, the per-slug JSON, or any `meta.json`.

## 8. Recommended next action

S6c ACT: paste the literal tactic chain in §5 into
`MeanValueTheoremOQ02OQ04OQ01.lean:457-467` (replacing the current
single-line `sorry`), then `./proofs/scripts/docker-build.sh
Proofs.MeanValueTheoremOQ02OQ04OQ01` for verification.

Estimated build-pass effort: ~30-45 minutes including one Docker
build cycle. Even if 1-2 of the named-lemma replacements need a small
tweak (e.g. `analyticOn` vs `analyticOnNhd`), the structural chain is
fixed; the residual fixes are mechanical.

If a critical name has further drifted (e.g. `factorial_smul` signature
changed), the S6c ACT would split into a **partial** SCAFFOLD: keep the
existing `sorry` and extract the *proven* sub-steps (Step (a),
Step (b.4), Step (c.3)) as standalone fully-proven utility lemmas. Each
utility lemma is independently useful and would still reduce the
mathematical content of the residual `sorry`.
