# S6 ACT — n-dim shifted complex Gaussian (Path B)

**Researcher**: researcher-12 (claim `researcher-86217`, knowledge score 30 / RICH)
**Date**: 2026-05-14
**Type**: ACT session — 4 new theorems in `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`.
**Scope**: implement the S6a PREP recommendation (Path B, per-axis Fubini) for
the n-dimensional shifted complex Gaussian, plus three corollaries (`normSq`,
unit weight `b = 1`, normalised density). Closes the four-PREP audit chain
(S6a / S6b / S6c / S6c PREP-2).

This session adds Lean code; it does **not** touch S6b or S6c routes,
which remain available follow-ups.

---

## 1. The four new theorems

In a new **Part 5** block (lines 494–614 of the post-merge file):

```lean
theorem complex_gaussian_integral_scaled_pow_shifted_norm
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, ‖z i - c i‖ ^ 2)) = (Real.pi / b) ^ n

theorem complex_gaussian_integral_scaled_pow_shifted_normSq
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, Complex.normSq (z i - c i))) =
      (Real.pi / b) ^ n

theorem complex_gaussian_integral_pow_unit_shifted_norm
    {n : ℕ} (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-∑ i, ‖z i - c i‖ ^ 2) = Real.pi ^ n

theorem complex_gaussian_density_pow_shifted
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, (b / Real.pi) ^ n *
      Real.exp (-(b * ∑ i, ‖z i - c i‖ ^ 2)) = 1
```

Total Lean delta: **+114 LOC**, **0 sorries**, **0 axioms**. File grows
from 544 → 658 LOC.

---

## 2. Proof of the main theorem (heterogeneous Fubini chain)

The S6a PREP §3.5 skeleton lifted with two refinements (lambda annotation
and Mathlib API line drift correction):

```lean
theorem complex_gaussian_integral_scaled_pow_shifted_norm
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, ‖z i - c i‖ ^ 2)) = (Real.pi / b) ^ n := by
  simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  rw [integral_fintype_prod_volume_eq_prod
        (fun (i : Fin n) (z : ℂ) => Real.exp (-(b * ‖z - c i‖ ^ 2)))]
  simp_rw [complex_gaussian_integral_scaled_shifted_norm b hb]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
```

Four steps, each one Mathlib-citable:

1. **Factor**: `simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]`.
   Identical first move to S4a (`...scaled_pow`, line 332). The per-axis
   exponent now is `b · ‖z i - c i‖²` instead of `b · ‖z i‖²`.

2. **Heterogeneous Fubini**: `rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin n) (z : ℂ) => ...)]`.
   Uses the variant where the per-axis factor depends on `i`, since the
   integrand `exp(-(b · ‖z - c i‖²))` differs per axis through `c i`.
   The S4a uniform `_eq_pow` does not apply. See §3 below for the
   per-axis non-uniformity argument.

3. **Per-axis collapse**: `simp_rw [complex_gaussian_integral_scaled_shifted_norm b hb]`.
   Each per-axis integral evaluates to `π/b` via the S5 1-D shifted
   theorem (independent of `c i`).

4. **Constant product collapse**: `rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
   Reduces `∏ i : Fin n, (π/b) = (π/b)^n`.

---

## 3. Why heterogeneous Fubini (S6a PREP confirmation)

The S6a PREP §3.3 distinguished:

| Lemma | Signature | When |
|---|---|---|
| `integral_fintype_prod_volume_eq_pow` | `∫ x, ∏ i, f (x i) = (∫ x, f x)^card ι` | uniform per-axis factor |
| `integral_fintype_prod_volume_eq_prod` | `∫ x, ∏ i, f i (x i) = ∏ i, ∫ x, f i x` | per-axis factor depends on `i` |

For S6 the per-axis factor is `z ↦ exp(-(b · ‖z - c i‖²))` which depends
on `i` through `c i`. **The `_eq_pow` form would not type-check** because
its hypothesis demands a single `f : E → 𝕜` with the same `f` applied at
every index.

That said, the integral *value* `π/b` is independent of `c i` (S5
translation invariance is precisely this fact). Step (3) above thus
collapses the heterogeneous product into the constant product
`∏ i, (π/b)`, recovering the same `(π/b)^n` shape that `_eq_pow` would
have produced *if* a uniform variant were applicable — but the type-level
non-uniformity forces the `_eq_prod` path even though the values
coincide.

---

## 4. Lambda annotation per memory note

S6a PREP §3.6 (and project memory `feedback_researcher_uniform_fubini_eq_pow.md`)
warned that

```lean
(fun _ x : E => ...)
```

is parsed as `fun _ x => ... : E → E → ...` (both args same type), breaking
the `_eq_prod` heterogeneous `E i` δ-unification. The lambda in step (2)
above uses the safe verbose form

```lean
(fun (i : Fin n) (z : ℂ) => Real.exp (-(b * ‖z - c i‖ ^ 2)))
```

with explicit `Fin n` and `ℂ` annotations. **No type-inference iteration
was needed**; the build succeeded on the first Docker pass.

---

## 5. Mathlib API verification (v4.26.0 pin)

The S6a PREP cited line 115 of `Mathlib/MeasureTheory/Integral/Pi.lean`.
Re-verified against the current project pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`gh api repos/leanprover-community/mathlib4/contents/...?ref=<pin>`:
the lemma now sits at **line 114** (1-line upstream drift, harmless —
the name and signature are unchanged):

```lean
theorem integral_fintype_prod_volume_eq_prod {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := integral_fintype_prod_eq_prod _
```

`ι` is implicit, `E := fun _ => ℂ` (constant), `f i z := exp(-(b · ‖z - c i‖²))`.
All instances `[MeasureSpace ℂ]`, `[SigmaFinite (volume : Measure ℂ)]`
are present by `inferInstance`.

---

## 6. The three corollaries

Each is a one-step reduction (analogous to the S4a corollaries, lines
349-380):

- **`..._scaled_pow_shifted_normSq`**: `simp_rw [Complex.normSq_eq_norm_sq]`
  then `exact` the main theorem. (1 LOC of proof.)
- **`..._pow_unit_shifted_norm`**: specialise the main theorem at `b = 1`,
  then `simp only [one_mul, div_one]`. Mirror of the S4a unit-weight
  corollary at line 362.
- **`..._density_pow_shifted`**: pull `(b/π)^n` outside via
  `integral_const_mul`, apply the main theorem, then close
  `(b/π)^n * (π/b)^n = 1` via `← mul_pow`, an inline
  `field_simp` of `(b/π) * (π/b) = 1`, and `one_pow`. Mirror of the
  S5 1-D density at line 489.

---

## 7. Honesty / verification

- **0 axioms added**, **0 sorries added** (file already had 0 of each,
  and remains so).
- **+114 LOC** total Lean delta. Total file: 544 → 658 LOC.
- **Single Docker build pass**: `./proofs/scripts/docker-build.sh
  Proofs.AreaOfCircleOQ05OQ04` → "Build completed successfully (3123 jobs)"
  (2026-05-14 ~23:00 UTC). The only warning is a pre-existing unused-variable
  warning in the parent file `AreaOfCircleOQ05.lean:60:33` (`unused
  variable 'ha'`), unrelated to this session's diff.
- **No new imports**: the new content reuses
  `Mathlib.MeasureTheory.Integral.Pi` (for
  `integral_fintype_prod_volume_eq_prod`), already imported for S4a.
- **API drift caught**: the S6a PREP cited line 115; the v4.26.0 pin has
  the lemma at line 114. Name and signature unchanged; this is a pure
  doc-comment update with no Lean impact.

---

## 8. Strict generalisation: c = 0 and n = 1 reductions

The four new theorems strictly generalise the existing S4a + S5 results:

| New theorem | `c = 0` reduces to | `n = 1` reduces to |
|---|---|---|
| `..._scaled_pow_shifted_norm` | `..._scaled_pow` (S4a, line 326) | `..._scaled_shifted_norm` (S5, line 426) |
| `..._scaled_pow_shifted_normSq` | `..._scaled_pow_normSq` (S4a, line 349) | `..._scaled_shifted` (S5, line 455) |
| `..._pow_unit_shifted_norm` | `..._pow_unit_norm` (S4a, line 362) | `..._unit_shifted_norm` (S5, line 467) |
| `..._density_pow_shifted` | `..._pow_normalised` (S4a, line 377) | `..._density_shifted` (S5, line 489) |

The reductions are not proved as separate lemmas — they are obvious from
the statements (substitute `c := fun _ => 0` or take `n := 1`). They are
documented here for traceability / consumer use.

---

## 9. Remaining S6 follow-ups (unchanged)

- **S6b (complex Fourier-eigenfunction)**: archimedean analogue of (C2).
  Per the S6b PREP, direct via `Real.fourierIntegral_gaussian_pi` after
  a `Complex.measurableEquivRealProd` transport, or via
  `fourier_gaussian_innerProductSpace` at `V := ℂ`. The new
  `..._scaled_pow_shifted_norm` from this session lifts to the n-dim
  Fourier-eigenfunction automatically.
- **S6c (Schur orthogonality)**: Mathlib `gaussianReal` / `IsGaussian`
  moment shortcut (per S6c PREP-2). Independent of S6 ACT; uses the
  S4a unshifted family.
- **S6d (`Measure ℚ_p`)**: still the upstream Mathlib milestone for
  p-adic Gaussian. Multi-week PR; independent of the archimedean side.

---

## 10. References

- **Lean file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` — new Part 5
  block at lines 494-614.
- **S6a PREP**: `s6a-prep-pi-haar-vs-fubini.md` — Path B audit
  (recommended), Path A pi-Haar route rejected.
- **S6b PREP**: `s6b-prep-complex-fourier-eigenfunction.md` — still
  available as the next route.
- **S6c PREP-2**: `s6c-prep-2-mathlib-moment-shortcut.md` — Schur
  orthogonality alternate route.
- **Mathlib API**: `Mathlib/MeasureTheory/Integral/Pi.lean:114`
  (`integral_fintype_prod_volume_eq_prod`); verified at pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **Project memory**: `feedback_researcher_uniform_fubini_eq_pow.md`
  (lambda annotation), `feedback_researcher_write_tool_worktree_path_footgun.md`
  (worktree-vs-main-repo path discipline; caught and recovered during
  this session — Edits incorrectly wrote to main-repo path; recovered
  via `cp` to worktree + `git restore` in main).
