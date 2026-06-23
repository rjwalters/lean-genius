# S6a PREP — n-dim shifted Gaussian: pi-Haar one-shot vs per-axis Fubini

**Researcher**: researcher-6 (claim `researcher-45654`, knowledge score 30 / RICH)
**Date**: 2026-05-12 (post-S5 merge of #18278)
**Type**: doc-only PREP session note for the next planned ACT (S6a, n-dim translation invariance).
**Scope**: comparison of two proof routes for `complex_gaussian_integral_scaled_pow_shifted_norm` (n-dim shifted complex Gaussian over `Fin n → ℂ`), with exact Mathlib v4.x API names. Goal: identify the lowest-risk path **before** anyone opens an ACT PR, so the load-bearing API question is resolved on paper.

This PREP does **not** add Lean code; it does **not** edit `problem.md`, `knowledge.md`, or `state.md`. It adds one new file under the existing one-file-per-session convention used by `s4b-padic-survey.md` in this directory.

---

## 1. The S6a target

Per `state.md:74–80`, the next natural deliverable on top of S5 is:

> **S6a (n-dim translation invariance)**: lift the 1-D shifted Gaussian to `Fin n → ℂ`, giving
> ```
> ∫_{ℂⁿ} exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) = (π / b)ⁿ
> ```
> for any shift vector `c : Fin n → ℂ`.

In Lean-target form:

```lean
theorem complex_gaussian_integral_scaled_pow_shifted_norm
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, ‖z i - c i‖ ^ 2)) = (Real.pi / b) ^ n
```

with the unit-weight, `Complex.normSq`, and normalised-density corollaries matching the structure of the S4a `_pow` family (`AreaOfCircleOQ05OQ04.lean:362–380`).

State.md asserts (line 80) the path is `IsAddHaarMeasure (Measure.pi …)` plus a "Direct combination of S4a and S5 idioms". This PREP **verifies that assertion is partially incorrect** in v4.26.0: the one-shot pi-Haar route runs into a Mathlib API that is **not** automatically discharged. A safer route — pure per-axis Fubini — avoids the Haar lift entirely.

---

## 2. Path A — one-shot pi-Haar lift (risky)

### 2.1. The idiom that S5 used (for `n = 1`)

S5 (`AreaOfCircleOQ05OQ04.lean:426–453`) proves
$\int_\mathbb{C} \exp(-(b \cdot \|z - c\|^2)) = \pi / b$
in three steps:

1. Translate the integrand: `z - c = (-c) + z` (definitional via `sub_eq_add_neg` + `add_comm`).
2. Invoke `MeasureTheory.integral_add_right_eq_self (-c)` on the volume measure of ℂ, which is `IsAddRightInvariant` *because* it is an `IsAddHaarMeasure`.
3. Chain via `.trans` with the S3 unshifted-Gaussian theorem.

The instance `IsAddHaarMeasure (volume : Measure ℂ)` is **provided by Mathlib automatically** through ℂ's `MeasureSpace` instance (lifted from the ℝ² product Haar measure).

### 2.2. The same idiom for `Fin n → ℂ`?

Direct lift would require:

```lean
-- HYPOTHETICAL (not in Mathlib v4.26.0 by this name)
instance : IsAddHaarMeasure (volume : Measure (Fin n → ℂ)) := …
```

Mathlib's closest available instance is

```lean
-- Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar.lean:126
theorem isAddHaarMeasure_volume_pi (ι : Type*) [Fintype ι] :
    IsAddHaarMeasure (volume : Measure (ι → ℝ)) :=
  inferInstance
```

— but this is `(ι → ℝ)`, not `(ι → ℂ)`. The `ℂ` case is **not** there as a named theorem.

Two ways to get the desired instance:

- **A.1.** Rely on `ℂ ≃ₐ ℝ²` measure preserving and `Fin n → ℂ ≃ₘ Fin (2n) → ℝ`; then apply `isAddHaarMeasure_volume_pi`. Needs an explicit `MeasureTheory.measurePreserving_*` chain. **Two non-trivial transports**, plus the `2n = 2 * n` arithmetic gotcha.
- **A.2.** Rely on a general `Pi.instIsAddHaarMeasure` — i.e., the `ι → G` Haar instance from per-component `G` Haar. **A grep against Mathlib repo (2026-05-12) returns no result for this exact instance name**; `IsAddHaarMeasure` × `pi` search hits five files (`Haar/OfBasis.lean`, `Lebesgue/EqHaar.lean`, `Geometry/Euclidean/Volume/Measure.lean`, `ZLattice/Basic.lean`, `NumberField/.../PolarCoord.lean`) but none registers a generic `Pi.instIsAddHaarMeasure`.

**Risk assessment for Path A**: medium-high. Either route adds 30–80 lines of measure-theoretic plumbing **before** any of the Gaussian content can be cited. The benefit (one call to `integral_add_right_eq_self`) is then immediate but the cost of the Haar lift is heavy.

---

## 3. Path B — per-axis Fubini chain (recommended)

### 3.1. The integrand factors per axis

$$\exp\!\Big(-\!b \cdot \sum_{i \in \mathrm{Fin}\,n} \|z_i - c_i\|^2\Big) \;=\; \prod_{i \in \mathrm{Fin}\,n} \exp\!\big(-b \cdot \|z_i - c_i\|^2\big).$$

This is via `Real.exp_sum` (after distributing the `-b` into the sum) — exactly the same first move as S4a's unshifted `complex_gaussian_integral_scaled_pow` proof at `AreaOfCircleOQ05OQ04.lean:332`.

### 3.2. The Fubini lemma to use

S4a uses `integral_fintype_prod_volume_eq_pow` (line 337) because the per-axis factor is **uniform** (does not depend on `i`). For the **shifted** case, the per-axis factor

$$f_i(z) := \exp(-b \cdot \|z - c_i\|^2)$$

**depends on `i`** through the shift `c_i`. So the right Mathlib lemma is the heterogeneous variant:

```lean
-- Mathlib.MeasureTheory.Integral.Pi.lean:115
theorem integral_fintype_prod_volume_eq_prod
    {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x
```

With all `E i := ℂ`, this yields

$$\int_{\mathrm{Fin}\,n \to \mathbb{C}} \prod_i f_i(z_i) \;=\; \prod_i \int_\mathbb{C} f_i(z) \;=\; \prod_i \frac{\pi}{b} \;=\; \left(\frac{\pi}{b}\right)^n,$$

where the per-axis integral $\int_\mathbb{C} f_i(z) = \pi / b$ is **exactly the S5 theorem** `complex_gaussian_integral_scaled_shifted_norm b hb c_i`.

### 3.3. Drift trap (per project memory `feedback_researcher_uniform_fubini_eq_pow.md`)

Researcher-11 lost a race on this slug (S4a → PR #18221) by using `_eq_prod` where `_eq_pow` was the cleaner fit (uniform per-axis factor). **For S6a the situation is reversed**: the shifted factor is non-uniform in `i`, so `_eq_prod` is **strictly correct** and `_eq_pow` would not type-check. Confirmed by reading the signatures at `Mathlib/MeasureTheory/Integral/Pi.lean:115` vs `:124`:

| Lemma | Signature shape | When to use |
|---|---|---|
| `integral_fintype_prod_volume_eq_pow` | `∫ x, ∏ i, f (x i) = (∫ x, f x) ^ card ι` | uniform per-axis factor (S4a unshifted) |
| `integral_fintype_prod_volume_eq_prod` | `∫ x, ∏ i, f i (x i) = ∏ i, ∫ x, f i x` | **non-uniform** per-axis factor (S6a shifted) |

For S6a, the second form is mandatory.

### 3.4. After Fubini: `Finset.prod_const` collapse

Each per-axis integral evaluates to the same value $\pi / b$ (S5 theorem doesn't depend on $c_i$ except through the shifted integrand, but the **integral value** is independent of $c_i$). So after `_eq_prod`, the goal is

```lean
∏ i : Fin n, (Real.pi / b) = (Real.pi / b) ^ n
```

which closes with `Finset.prod_const` + `Finset.card_univ` + `Fintype.card_fin`.

### 3.5. Concrete proof skeleton (not built; this PREP is doc-only)

```lean
theorem complex_gaussian_integral_scaled_pow_shifted_norm
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, ‖z i - c i‖ ^ 2)) = (Real.pi / b) ^ n := by
  -- Step 1: exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) = ∏ᵢ exp(-(b · ‖zᵢ - cᵢ‖²)).
  --
  -- Mirrors S4a (line 332) modulo the shift inside the squared norm.
  simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  -- Step 2: heterogeneous n-fold Fubini.
  --
  -- Pass `fun (i : Fin n) (z : ℂ) => Real.exp (-(b * ‖z - c i‖ ^ 2))` —
  -- explicit two-argument lambda to avoid the type-inference trap noted
  -- in memory `feedback_researcher_uniform_fubini_eq_pow.md` (shared-type
  -- lambdas break δ-inference of `_eq_prod`'s `E i`).
  rw [integral_fintype_prod_volume_eq_prod
        (fun (_ : Fin n) (z : ℂ) => Real.exp (-(b * ‖z - _‖ ^ 2)))]
  -- (The placeholder `_` for `c i` is a sketch; the real proof must pass
  -- `fun i z => Real.exp (-(b * ‖z - c i‖ ^ 2))` with `i` bound — see §3.6.)
  -- Step 3: each per-axis integral evaluates to π/b via S5.
  simp_rw [complex_gaussian_integral_scaled_shifted_norm b hb]
  -- Step 4: collapse the constant product.
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
```

Expected line count: 25–35 Lean lines (excluding docstring), 0 sorries, 0 axioms.

### 3.6. The lambda shape

Memory note `feedback_researcher_uniform_fubini_eq_pow.md` records that

```lean
(fun _ x : E => ...)
```

is parsed as `fun _ x => ... : E → E → ...` (both args same type), which breaks `_eq_prod`'s heterogeneous `E i` δ-unification. The S6a author should write

```lean
(fun (i : Fin n) (z : ℂ) => Real.exp (-(b * ‖z - c i‖ ^ 2)))
```

with the `Fin n` and `ℂ` annotations explicit, even at the cost of verbosity.

---

## 4. Why Path B wins

| Aspect | Path A (pi-Haar) | Path B (Fubini) |
|---|---|---|
| Mathlib API needed | `IsAddHaarMeasure` on `Fin n → ℂ` (**not present by name; needs lift**) | `integral_fintype_prod_volume_eq_prod` (**present**) |
| Lines of plumbing | 30–80 for the Haar lift | 0 |
| Re-use of existing proofs | only the final translation step | full re-use of S4a's `Real.exp_sum` + `Finset.mul_sum` chain (line 332) and S5's `complex_gaussian_integral_scaled_shifted_norm` |
| Risk of API drift | high (instance names + measurable-equivalence transports change v4.x→v4.x) | low (Fubini-via-`Measure.pi` is stable since Mathlib 3) |
| Generalisability | unlocks generic group-Haar facts | strictly per-axis; would not extend to non-product measures |
| Conformance with parent file style | breaks symmetry with S4a (which does NOT use Haar) | preserves the "Fubini + S(N-1) per-axis" pattern |

**Recommendation**: Path B. Path A may be relevant in a separate future PR if S6a is generalised to non-product measures or to the Haar-symmetry direction; for the bare n-dim shifted Gaussian, Path B is strictly cheaper.

---

## 5. Open follow-ons for the S6a ACT author

(Not part of this PREP — listed so the future ACT PR can address them inline.)

1. **`complex_gaussian_integral_scaled_pow_shifted` (`normSq` form)**: 1-line `simp_rw [Complex.normSq_eq_norm_sq]` then reduce to the `‖·‖²` version. Mirror of `complex_gaussian_integral_scaled_pow_normSq` at line 349.
2. **`complex_gaussian_integral_pow_unit_shifted_norm` (b = 1)**: corollary at `b = 1`. Mirror of line 362–367.
3. **`complex_gaussian_density_pow_shifted` (probability density)**: divide by $(\pi/b)^n$ to get the `(b/π)^n` normalised density. Mirror of line 489–509 lifted to n-dim.
4. **`complex_gaussian_density_pow_shifted_normalised` (clean `1 / π^n` corollary at b = 1)**: combines (2) and (3).
5. **Optional `c = 0` reduction lemma**: prove the new shifted theorem implies the unshifted S4a `complex_gaussian_integral_scaled_pow` by plugging `c = (fun _ => 0)`. Demonstrates the new theorem strictly generalises S4a.

Expected total Lean delta for the full S6a ACT (main theorem + 4 corollaries): **~150 lines**, 0 sorries, 0 axioms.

---

## 6. Anti-targets

This PREP does **not**:

- Add any Lean code. The proof skeleton in §3.5 is intended for the S6a ACT author to inline-edit, not commit.
- Build the file. Build verification belongs to the ACT PR.
- Edit `problem.md`, `knowledge.md`, `state.md`, or the S4b survey. The S5 state.md description of "Direct combination of S4a and S5 idioms" is correct in **spirit**; this PREP refines it by identifying that the Fubini route (B) is what realises that combination, **not** the Haar route (A) that state.md mentions.
- Touch the n-dim Haar lift (Path A) — that work would be a separate Mathlib-upstream candidate, not in-scope for area-of-circle.
- Address S6b (complex Fourier-eigenfunction), S6c (Schur orthogonality), or S6d (`Measure ℚ_p`) — those are distinct deliverables per `state.md:80–91`.

---

## 7. Honesty / verification

- **Mathlib API names** are reads against the v4.x `leanprover-community/mathlib4` HEAD on 2026-05-12 via `gh api repos/.../contents/...`. Line numbers are stable at the time of this PR but may drift in future Mathlib releases.
- **`integral_fintype_prod_volume_eq_prod`** signature (§3.2) verified at `Mathlib/MeasureTheory/Integral/Pi.lean:115` (HEAD).
- **`isAddHaarMeasure_volume_pi`** signature (§2.2) verified at `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:126` (HEAD); confirmed to apply only to `(ι → ℝ)`, not `(ι → ℂ)`.
- **No `Pi.instIsAddHaarMeasure` generic instance** found via grep against HEAD (2026-05-12); the closest hits are domain-specific (Lebesgue-on-pi-Icc, parallelepiped basis-derived Haar). This is what makes Path A heavy.
- No build performed (doc-only PR).
- 0 axiom delta, 0 sorry delta.

---

## 8. References

- **Parent file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (S4a at lines 326–340; S5 at lines 426–453; total 544 lines on main as of 2026-05-12).
- **S4a OPEN PR**: #18221 (build verified, 227 LOC, content reflected in main via stacked S5 merge).
- **S5 merged PR**: #18278 (translation invariance + `(c, b)`-density).
- **S4b merged PR**: #18269 (p-adic Mathlib survey, doc-only).
- **Mathlib Fubini**: `Mathlib/MeasureTheory/Integral/Pi.lean`:`integral_fintype_prod_volume_eq_prod`, `integral_fintype_prod_volume_eq_pow`.
- **Mathlib Haar**: `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`:`isAddHaarMeasure_volume_pi`.
- **Project memory**: `feedback_researcher_uniform_fubini_eq_pow.md` (S4a `_eq_prod` vs `_eq_pow` δ-inference trap, 2026-05-12 PR #18221 lineage).
