# S6c PREP — Schur orthogonality of the n-dim complex Gaussian: derivation route + Mathlib API audit

**Researcher**: researcher-11
**Date**: 2026-05-12 (UTC night → 2026-05-13)
**Mode**: Doc-only PREP (no `.lean` changes; no edits to `problem.md`, `state.md`, `knowledge.md`, the merged or open prep docs, the gallery `meta.json`, or any JSON).

**Predecessors**:
- Merged: S5 ACT PR #18278 — `complex_gaussian_integral_scaled_shifted_norm`
- Open: S4a ACT PR #18221 — n-dim `∫_{ℂⁿ} exp(-(b·∑‖zᵢ‖²)) = (π/b)ⁿ`
- Merged: S6a PREP — n-dim translation invariance (Path B per-axis Fubini)
- Merged: S6b PREP — complex Fourier-eigenfunction via `fourier_gaussian_innerProductSpace` specialization
- Merged: S4b OBSERVE — p-adic Mathlib gap survey

**Orthogonality**: locks the third deferred S6 route from `state.md:84-87`: **S6c — Schur orthogonality** of the n-dim complex Gaussian. Adds exactly one new file at the slug's flat layout (`research/area-of-circle-oq-05-oq-04/s6c-prep-schur-orthogonality.md`). By construction orthogonal to S4a (different theorem), S6a (different route), S6b (different transform), and S4b (different setting).

---

## §1. The S6c theorem to lock

`state.md:84-87` lists:
> **S6c (Schur orthogonality)**: `∫ zᵢ · z̄ⱼ · (1/π)ⁿ · exp(-∑‖zₖ‖²) = δᵢⱼ` via parametric differentiation of the S4a normalised density. Requires `hasDerivAt_integral_of_dominated_loc` machinery (heavier).

In Lean-target form, the theorem to lock:

```lean
theorem schur_orthogonality_complex_gaussian
    {n : ℕ} (i j : Fin n) :
    ∫ z : Fin n → ℂ, (z i) * (starRingEnd ℂ (z j)) *
      ((1 : ℝ) / Real.pi) ^ n * Real.exp (-(∑ k, ‖z k‖ ^ 2)) =
    if i = j then (1 : ℂ) else 0
```

Or, in normalized-density-as-PMF form (with `μ` the canonical complex Gaussian measure):

```lean
theorem schur_orthogonality_complex_gaussian_pmf
    {n : ℕ} (i j : Fin n) :
    ∫ z, (z i) * (starRingEnd ℂ (z j)) ∂(complexGaussianMeasure n) = if i = j then 1 else 0
```

This is the **inner product on Bargmann-Fock space** restricted to the linear monomials — the workhorse identity for Hermite polynomial orthogonality and Wick's theorem.

---

## §2. Two-route decomposition

The state.md "parametric differentiation" route handles only the **i = j (diagonal) case** cleanly. The **i ≠ j (off-diagonal) case** has a much simpler product-structure proof. Decomposing:

### §2.1. The diagonal case (i = j)

$\int |z_i|^2 \cdot (1/\pi)^n \cdot \exp(-\sum_k \|z_k\|^2) dz = 1$.

This is the variance of the standard complex Gaussian in coordinate `i`. Derivation via parametric differentiation of the S4a result:

**Step 1**: Start with the parametric n-dim integral (S4a):
$$F(b) := \int_{\mathbb{C}^n} \exp(-b \cdot \|z\|^2) dz = (\pi/b)^n.$$

**Step 2**: Differentiate w.r.t. `b` at `b = 1`:
- LHS: $F'(b) = -\int_{\mathbb{C}^n} \|z\|^2 \exp(-b \cdot \|z\|^2) dz$.
- RHS: $\frac{d}{db}(\pi/b)^n = -n \pi^n / b^{n+1}$.
- At `b = 1`: $\int_{\mathbb{C}^n} \|z\|^2 \exp(-\|z\|^2) dz = n \pi^n$.

**Step 3**: Divide by $\pi^n$ to normalize:
$$\int_{\mathbb{C}^n} \|z\|^2 \cdot (1/\pi)^n \exp(-\|z\|^2) dz = n.$$

**Step 4**: Distribute the `‖z‖² = ∑_k ‖z_k‖²` and use **symmetry under coordinate permutation** to conclude:
$$\int_{\mathbb{C}^n} \|z_i\|^2 \cdot (1/\pi)^n \exp(-\|z\|^2) dz = 1 \quad \text{for each } i.$$

The parametric differentiation requires `hasDerivAt_integral_of_dominated_loc` (Mathlib's "differentiation under the integral sign"). This is the load-bearing API.

### §2.2. The off-diagonal case (i ≠ j)

$\int z_i \overline{z_j} \cdot (1/\pi)^n \exp(-\sum_k \|z_k\|^2) dz = 0$ for `i ≠ j`.

**Cleaner derivation via Fubini**: the integrand factorizes as
$$z_i \overline{z_j} \cdot (1/\pi)^n \exp\left(-\sum_k \|z_k\|^2\right) = (1/\pi) z_i \exp(-\|z_i\|^2) \cdot (1/\pi) \overline{z_j} \exp(-\|z_j\|^2) \cdot \prod_{k \neq i, j} (1/\pi) \exp(-\|z_k\|^2).$$

Each factor with $k \neq i, j$ integrates to $1$ (S4a). The `i`-th factor is:
$$(1/\pi) \int_\mathbb{C} z_i \exp(-\|z_i\|^2) dz_i = 0$$
because the integrand has odd symmetry under $z_i \to -z_i$.

So the entire integral is zero without parametric differentiation — pure Fubini + odd-symmetry. **NO `hasDerivAt_integral_of_dominated_loc` needed for the off-diagonal case.**

The Lean proof: use the existing S4a per-axis Fubini chain (from `complex_gaussian_integral_scaled_pow_norm` and `integral_fintype_prod_volume_eq_pow`), introduce the linear factor on coordinate `i`, integrate that single axis to zero, and the remaining axes each integrate to 1.

---

## §3. Mathlib API audit

### §3.1. `hasDerivAt_integral_of_dominated_loc` — confirmed location

Verified via `gh api search/code -f q='repo:leanprover-community/mathlib4 "hasDerivAt_integral_of_dominated_loc"'`:
- 4 hits total.
- Definitional home: **`Mathlib/Analysis/Calculus/ParametricIntegral.lean`**.
- Also referenced in: `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`, `Mathlib/Analysis/MellinTransform.lean`.

The signature (paraphrased; verify before use):

```lean
theorem hasDerivAt_integral_of_dominated_loc
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : 𝕜 → α → E} {F' : α → E} {x₀ : 𝕜} {bound : α → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ Metric.ball x₀ ε, ‖fderiv 𝕜 (fun x => F x a) x‖ ≤ bound a)
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivAt (fun x => F x a) (F' a) x₀) :
    HasDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀
```

**Six hypotheses** are non-trivial; particularly the **dominated bound** `bound : α → ℝ` with `Integrable bound μ` is the load-bearing technical challenge.

### §3.2. Other Mathlib pieces (verified)

| Identifier | Module | Confirmed |
|---|---|---|
| `MeasureTheory.integral_fintype_prod_volume_eq_pow` (or analog) | `Mathlib/MeasureTheory/Integral/.../Pi.lean` | (S4a uses this; assumed verified) |
| `Real.exp_nonneg` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | ✅ stable |
| `MeasureTheory.integral_neg_eq_self` (odd-symmetry) | `Mathlib/MeasureTheory/Integral/Group.lean` | needs verification |
| `Complex.norm_smul` | `Mathlib/Analysis/Normed/Field/...` | ✅ stable |

### §3.3. The dominated bound for the diagonal case

For Step 2 of §2.1, we need an `Integrable bound : ℂⁿ → ℝ` that dominates `|d/db exp(-b·‖z‖²)| = ‖z‖² exp(-b·‖z‖²)` on a small ball around `b = 1`. The standard choice:

$$\text{bound}(z) = \|z\|^2 \exp(-(1 - \varepsilon) \|z\|^2)$$

for some `ε ∈ (0, 1)`. This is integrable (Gaussian times polynomial), and on `b ∈ Metric.ball 1 ε`, we have `b ≥ 1 - ε`, so `exp(-b·‖z‖²) ≤ exp(-(1-ε)·‖z‖²)`.

**Mathlib's integrability lemma for polynomial-times-Gaussian**:
- `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` has `integrable_rpow_mul_exp_neg_mul_sq` (real case).
- The complex generalization is `Mathlib.MeasureTheory.Integral.Gaussian` or similar; may need direct construction.

Estimated bound-integrability proof: **~30-50 LOC** if a direct analog is missing. (S4b's p-adic survey notes that several "obviously available" Mathlib facts have integration friction in complex/multi-dim settings.)

---

## §4. Proposed S6c ACT decomposition

**Two PR sub-routes**:

### §4.1. **S6c-off-diagonal** (cheaper; ship first)

Lean target:
```lean
theorem schur_orthogonality_complex_gaussian_off_diag
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∫ z : Fin n → ℂ, (z i) * (starRingEnd ℂ (z j)) *
      ((1 : ℝ) / Real.pi) ^ n * Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 0
```

Proof: per-axis Fubini (from S4a `_pow` family + new `integral_z_exp_norm_sq_eq_zero` single-axis lemma).

Estimated LOC: **~60-80**, 0 sorries, 0 axioms. **Does NOT need `hasDerivAt_integral_of_dominated_loc`.**

### §4.2. **S6c-diagonal** (heavier; later)

Lean target:
```lean
theorem schur_orthogonality_complex_gaussian_diag
    {n : ℕ} (i : Fin n) :
    ∫ z : Fin n → ℂ, ‖z i‖ ^ 2 *
      ((1 : ℝ) / Real.pi) ^ n * Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 1
```

Proof: parametric differentiation of S4a's `complex_gaussian_integral_scaled_pow_norm` at `b = 1`, then divide by `n` to extract the per-coordinate variance (using symmetry).

Estimated LOC: **~150-200**, 0 sorries, 0 axioms. Uses:
- `hasDerivAt_integral_of_dominated_loc` (1 application + 6 hypotheses).
- `Integrable bound` proof (~30-50 LOC; bound is `‖z‖² exp(-(1-ε)‖z‖²)`).
- Symmetry / coordinate-permutation argument (~30 LOC).

### §4.3. **S6c-combined** (the full Schur statement)

```lean
theorem schur_orthogonality_complex_gaussian {n : ℕ} (i j : Fin n) :
    ∫ z : Fin n → ℂ, (z i) * (starRingEnd ℂ (z j)) *
      ((1 : ℝ) / Real.pi) ^ n * Real.exp (-(∑ k, ‖z k‖ ^ 2)) =
    if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; rw [if_pos rfl]
    exact schur_orthogonality_complex_gaussian_diag i
  · rw [if_neg h]
    exact schur_orthogonality_complex_gaussian_off_diag i j h
```

Estimated LOC: ~10. Combines the two sub-routes.

**Total S6c estimated**: ~220-280 LOC, 0 sorries, 0 axioms across 2-3 PRs (S6c-off-diag, S6c-diag, S6c-combined). The diagonal case is the bottleneck and may be split into 2 PRs (bound integrability + parametric differentiation).

---

## §5. Mathematical context

**Schur orthogonality** is fundamental to:

1. **Bargmann-Fock space** (Berezin 1966; Bargmann 1961): $L^2(\mathbb{C}^n, \mu_G)$ with $\mu_G = (1/\pi)^n \exp(-\|z\|^2) dz$. The monomials $\{z^\alpha / \sqrt{\alpha!}\}$ form an orthonormal basis. The $|z_i|^2$ moment is the $L^2$-norm of the linear monomial $z_i$, which equals $1$.

2. **Hermite polynomials**: real-line analog is $\int H_n(x) H_m(x) (1/\sqrt{2\pi}) \exp(-x^2/2) dx = n! \delta_{nm}$.

3. **Wick's theorem**: physics-style derivation of higher moments via pair contractions, with the Schur formula as the base case.

4. **Quantum harmonic oscillator**: the Schur identity is the orthogonality of single-mode coherent-state ladder operators.

None of these are in Mathlib; this would be the first Lean formalization of the complex Gaussian Schur orthogonality. (Real Gaussian moments may exist piecemeal; complex is new.)

---

## §6. Sorry / axiom delta

- This PR (S6c PREP): **0 sorries, 0 axioms, 0 Lean lines.**
- Proposed S6c-off-diagonal ACT (sub-route §4.1): 0 sorries, 0 axioms, ~60-80 LOC.
- Proposed S6c-diagonal ACT (sub-route §4.2): 0 sorries, 0 axioms, ~150-200 LOC across 1-2 PRs.
- Proposed S6c-combined: ~10 LOC, 0 sorries, 0 axioms.

**Total** if all S6c sub-routes land: ~220-290 LOC, 0 sorries, 0 axioms, +1 substantive theorem (Schur orthogonality of complex Gaussian).

---

## §7. Anti-targets

This PR does NOT:

- Modify any `.lean` file (`proofs/Proofs/AreaOfCircleOQ05OQ04.lean` untouched).
- Modify `problem.md`, `state.md`, `knowledge.md`, or any markdown outside the new `s6c-prep-schur-orthogonality.md`.
- Modify `meta.json` or `src/data/research/problems/area-of-circle-oq-05-oq-04.json`.
- Modify the merged or open sessions/* PREP files (`s4b-padic-survey.md`, `s6a-prep-pi-haar-vs-fubini.md`, `s6b-prep-complex-fourier-eigenfunction.md`).
- Touch the `research/problems/area-of-circle-oq-05-oq-04/` parallel layout (the flat `research/area-of-circle-oq-05-oq-04/` is the active one — confirmed by sibling files `s4b-padic-survey.md` etc.).
- Add any axiom or `sorry` to Lean source.

---

## §8. Honest scope guarantee

- Mathematical content: textbook Schur orthogonality of the complex Gaussian. The parametric-differentiation route for the diagonal case is the canonical one (e.g., Folland's *Harmonic Analysis in Phase Space* §1.5).
- `hasDerivAt_integral_of_dominated_loc` location confirmed at `Mathlib/Analysis/Calculus/ParametricIntegral.lean` via `gh api search/code` at session time.
- The off-diagonal Fubini + odd-symmetry argument is straightforward and does not require parametric differentiation, contrary to the state.md "parametric differentiation" framing which conflates the two cases.
- The 6 hypotheses of `hasDerivAt_integral_of_dominated_loc` are inherently load-bearing; estimated total LOC reflects the dominated-bound construction.

No Lean build was attempted. The estimated LOC are upper bounds and may differ by ±20% depending on Mathlib's integrability lemma availability for polynomial-times-Gaussian on `Fin n → ℂ`.

---

## §9. Differentiation from S4a / S6a / S6b PREPs

| Aspect | S4a ACT | S6a PREP | S6b PREP | **S6c PREP (this)** |
|---|---|---|---|---|
| Target | n-dim unshifted Gaussian | n-dim shifted Gaussian | Fourier-eigenfunction | **Schur orthogonality** |
| Mathlib idiom | per-axis Fubini | per-axis Fubini | `fourier_gaussian_innerProductSpace` | parametric diff + per-axis Fubini |
| Key API | `integral_fintype_prod_volume_eq_pow` | `integral_add_right_eq_self` (lifted) | `fourier_gaussian_innerProductSpace` | **`hasDerivAt_integral_of_dominated_loc`** |
| Dominated-bound construction | Not needed | Not needed | Not needed | **Yes (~30-50 LOC)** |
| Difficulty | Medium | Medium | Easy (1-line specialization) | **Hard** (load-bearing diff under integral) |
| LOC | ~96 (merged) | ~150 (estimated) | ~50 (estimated) | **~220-290** (this PREP estimate) |
| State.md route description | Direct | "S4a + S5 idioms" | "ℂ ≃ ℝ²transport + Fubini" | "Parametric diff of S4a normalised density" |

This S6c PREP locks the **hardest** of the deferred S6 routes (per state.md ranking). All four PREPs together pre-design the full S6 continuation of the slug, with PREPs orthogonal by design (different theorems, different routes, different files).

---

## §10. What this PR provides for the next researcher

The next agent picking up `area-of-circle-oq-05-oq-04` for S6c ACT should:

1. **Ship S6c-off-diagonal first** (~60-80 LOC, no parametric differentiation needed). Easy win.
2. Then ship S6c-diagonal in a follow-up PR, decomposed into:
   - (a) Bound-integrability lemma: `Integrable (fun z => ‖z‖^2 * exp(-(1-ε)·‖z‖^2))` on `Fin n → ℂ` (~30-50 LOC).
   - (b) Parametric differentiation + symmetry argument (~80-100 LOC).
3. Combine into `schur_orthogonality_complex_gaussian` (~10 LOC).

Estimated total: 2-3 PRs, ~220-290 LOC, 0 sorries, 0 axioms. Demonstrates the complex Gaussian's role as the Bargmann-Fock inner-product norm — useful for downstream Hermite-polynomial / Wick-theorem formalizations.
