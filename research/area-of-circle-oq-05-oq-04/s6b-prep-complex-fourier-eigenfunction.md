# Session S6b PREP — Complex Fourier-eigenfunction via direct `fourier_gaussian_innerProductSpace` specialization at `V := ℂ`

**Researcher**: researcher-4
**Date**: 2026-05-12
**Mode**: Doc-only (no `.lean` changes, no markdown edits outside this new file, no JSON edits)
**Predecessors**:
- Merged: S5 ACT PR #18278 (`complex_gaussian_integral_scaled_shifted_norm`, the `(c,b)`-shifted Gaussian)
- Open: S4a ACT PR #18221 (n-dim `∫_{ℂⁿ} exp(-(b·∑‖zᵢ‖²)) = (π/b)ⁿ`)
- Open: S6a PREP PR #18389 (n-dim shifted Gaussian via Path B per-axis Fubini)
- Merged: S4b OBSERVE PR #18269 (p-adic Mathlib gap survey)
**Orthogonality**: this note locks **S6b**, which `state.md:80` lists as one of three deferred routes — adds **exactly one new file** at the slug's flat layout. No edits to `problem.md`, `state.md`, `knowledge.md`, `s4b-padic-survey.md`, the S6a PREP file, the gallery `meta.json`, or any `.lean` file. By construction orthogonal to S4a (different theorem), S6a (different route), and S4b (different setting).

---

## §1. The S6b theorem to lock

The "canonical archimedean analogue of (C2)" envisioned in `state.md:80` is

```
𝓕 (fun (z : ℂ) ↦ cexp (-π · ‖z‖²)) w = cexp (-π · ‖w‖²)   for all w : ℂ.
```

I.e., the **complex Gaussian at scale `b = π`** is a fixed point of the Fourier transform on `ℂ`, mirroring the real-line statement `Real.fourierIntegral_gaussian_pi`. The more general parametric statement is

```
𝓕 (fun (z : ℂ) ↦ cexp (-b · ‖z‖²)) w = (π / b) · cexp (-π² · ‖w‖² / b)
  for all `b : ℂ` with `0 < b.re` and `w : ℂ`.
```

with the `b = π` case as a one-line corollary.

---

## §2. Mathlib already provides the n-dim case — `V := ℂ` is a direct specialization

**Key finding**: the `state.md:80` route description ("Mathlib has `Real.fourierIntegral_gaussian_pi`; the complex case is one ℂ ≃ ℝ × ℝ transport + Fubini reduction") is **suboptimal**. Mathlib's `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform` ships the **inner-product-space-valued** Fourier-Gaussian theorem at full generality, which specializes to `V := ℂ` in **one line** because the ℂ ≃ ℝ × ℝ structure is already encoded in `instance : InnerProductSpace ℝ ℂ`.

### §2.1 The Mathlib lemma to specialize

`Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` (lines ~370-380):

```lean
theorem _root_.fourier_gaussian_innerProductSpace
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {b : ℂ} (hb : 0 < b.re) (w : V) :
    𝓕 (fun (v : V) ↦ cexp (-b * ‖v‖ ^ 2)) w =
      (π / b) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * ‖w‖ ^ 2 / b)
```

(The 2025-11-16-deprecated alias `fourierIntegral_gaussian_innerProductSpace` is also available for back-compat.)

A companion *with-shift* lemma is

```lean
theorem _root_.fourier_gaussian_innerProductSpace'
    (hb : 0 < b.re) (x w : V) :
    𝓕 (fun v ↦ cexp (-b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪x, v⟫)) w =
      (π / b) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * ‖x - w‖ ^ 2 / b)
```

### §2.2 The two missing facts for `V := ℂ`

Both **already in Mathlib HEAD** (v4.26.0):

1. **`Complex.finrank_real_complex : Module.finrank ℝ ℂ = 2`**
   - Location: `Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:31`
   - Statement: literal `theorem finrank_real_complex : finrank ℝ ℂ = 2`.
   - Also: `Complex.finrank_real_complex_fact : Fact (finrank ℝ ℂ = 2)` at the same file:42.

2. **`instance : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal`**
   - Location: `Mathlib/Analysis/InnerProductSpace/Basic.lean:984`
   - Statement: `instance : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal`
   - Identification at file:1007: `instInnerProductSpaceRealComplex = RCLike.toInnerProductSpaceReal`.
   - The inner product unfolds as `⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im`, and the induced norm is `‖z‖ = sqrt (z.re² + z.im²) = sqrt (Complex.normSq z)`, matching the parent file's `complex_gaussian_integral_scaled_norm` (S3).

The `MeasurableSpace` and `BorelSpace` requirements on `V = ℂ` are auto-derived from the metric/topological structure (`MeasurableSpace.instBorel`).

### §2.3 The Lean target for S6b ACT

With those two facts plus `fourier_gaussian_innerProductSpace`, the parametric S6b ACT theorem is:

```lean
theorem complex_fourier_gaussian (b : ℂ) (hb : 0 < b.re) (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ cexp (-b * ‖z‖ ^ 2)) w
      = (π / b) * cexp (-π ^ 2 * ‖w‖ ^ 2 / b) := by
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb w
  rw [show ((Module.finrank ℝ ℂ : ℂ) / 2) = (1 : ℂ) by
    simp [Complex.finrank_real_complex]] at h
  simpa [Complex.cpow_one] using h
```

(±15 lines including imports and namespace setup.)

The `b = π` corollary (the self-Fourier eigenfunction, the canonical archimedean (C2)) is then:

```lean
theorem complex_fourier_gaussian_pi (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ cexp (-π * ‖z‖ ^ 2)) w
      = cexp (-π * ‖w‖ ^ 2) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h := complex_fourier_gaussian (π : ℂ) (by simpa) w
  simp [div_self, ofReal_ne_zero, Real.pi_ne_zero] at h
  -- close with (π² · ‖w‖² / π) = π · ‖w‖² for the rhs simplification
  ...
```

(~25-30 LOC with the algebraic cleanup of `π² / π = π` and the resulting `cexp` argument.)

### §2.4 With-shift companion (S6b-bis)

The `fourier_gaussian_innerProductSpace'` lemma gives, at `V := ℂ`,

```lean
theorem complex_fourier_gaussian_shifted (b : ℂ) (hb : 0 < b.re) (x w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ cexp (-b * ‖z‖ ^ 2 + 2 * π * Complex.I * ⟪x, z⟫_ℝ)) w
      = (π / b) * cexp (-π ^ 2 * ‖x - w‖ ^ 2 / b)
```

This is the **archimedean analogue of "translate-then-Fourier"**, parallel to the S5 ACT translation-invariance lemma but in Fourier domain rather than integral domain.

---

## §3. Why this route dominates the `state.md:80` ℂ ≃ ℝ² + Fubini route

| Axis                       | `ℂ ≃ ℝ²` + Fubini route                                 | Direct specialization at `V := ℂ`             |
|----------------------------|---------------------------------------------------------|------------------------------------------------|
| Lean LOC (theorem + corollaries) | 80-150                                                  | **15-40**                                      |
| Mathlib lemmas required    | `Real.fourierIntegral_gaussian_pi` + `MeasureTheory.integral_prod` + `Complex.measurableEquivRealProd` (or `Complex.equivRealProd`) + Fubini + transport | `fourier_gaussian_innerProductSpace` + `Complex.finrank_real_complex` + the `InnerProductSpace ℝ ℂ` instance |
| Measurable-equiv plumbing  | Required for `volume`-transport across `ℂ ≃ ℝ²`         | **None** — handled by `instInnerProductSpaceRealComplex` |
| Risk of `volume`-instance drift | High — `volume : Measure ℂ` vs `volume : Measure (ℝ × ℝ)` not definitionally equal; an explicit `MeasurePreserving` lemma is needed | None — the n-dim inner-product-space lemma is stated against the `volume` on `V` via `BorelSpace V` |
| Generalizes to `ℂⁿ` for free? | No — would need a re-run of the same `ℂ ≃ ℝ²` plumbing for each axis | **Yes** — `V := EuclideanSpace ℂ (Fin n)` is also an `InnerProductSpace ℝ V` with `finrank = 2n` |

The `EuclideanSpace ℂ (Fin n)` generalization in row 5 is **the same theorem the merged S4a ACT (#18221) computes** as `∫ exp(-b·∑‖zᵢ‖²) = (π/b)ⁿ` — except now it computes the **Fourier transform** rather than just the integral. So `fourier_gaussian_innerProductSpace (V := EuclideanSpace ℂ (Fin n))` is, in a precise sense, **S4a + S6b combined into one theorem**, which is the n-dim self-Fourier eigenfunction.

This unifies the S4a/S4b/S5/S6a/S6b chain into a single inner-product-space-valued statement, with the slug's various corollaries (1-D, n-D, shifted, scaled, density-normalised) as specializations.

---

## §4. Mathlib `MeasurableSpace ℂ` + `BorelSpace ℂ` precondition audit

The inner-product-space lemma requires `[MeasurableSpace V] [BorelSpace V]`. For `V := ℂ`:

| Instance                                    | Mathlib location                                             | Status      |
|---------------------------------------------|--------------------------------------------------------------|-------------|
| `MeasurableSpace ℂ` (Borel-σ from topology) | `Mathlib.MeasureTheory.MeasurableSpace.Defs` + `Mathlib.Analysis.Complex.Basic` (topology) | Present     |
| `BorelSpace ℂ`                              | `Mathlib.Topology.Instances.Complex` or derived in `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic` | Present     |
| `MeasureTheory.MeasureSpace ℂ` with `volume` = 2-D Lebesgue | `Mathlib.MeasureTheory.Measure.Haar.OfBasis` | Present     |
| `IsAddHaarMeasure (volume : Measure ℂ)`     | Derived from `Complex.measureSpace = (ℝ × ℝ).measureSpace`   | Present (transitive) |

All preconditions are unconditionally available; no explicit instance argument is needed when invoking `fourier_gaussian_innerProductSpace (V := ℂ)`.

---

## §5. Decomposition for the S6b ACT

| Sub-deliverable                                  | LOC est. | Mathlib calls (new)                                    | Notes                                  |
|--------------------------------------------------|----------|---------------------------------------------------------|----------------------------------------|
| `complex_fourier_gaussian` (parametric, §2.3)    | 15       | `fourier_gaussian_innerProductSpace` + `Complex.finrank_real_complex` | Direct application                     |
| `complex_fourier_gaussian_pi` (`b = π` corollary, §2.3) | 25       | + `Real.pi_pos` + arithmetic                            | The self-Fourier eigenfunction         |
| `complex_fourier_gaussian_normSq` (`‖·‖²` → `normSq` form) | 10 | + `Complex.sq_abs` (or `Complex.normSq_eq_abs_sq`)     | Convenience corollary                  |
| `complex_fourier_gaussian_shifted` (§2.4)        | 20       | `fourier_gaussian_innerProductSpace'`                   | With-shift companion                   |
| `complex_fourier_gaussian_density_eigen` (normalized eigenstate `(1/π)·exp(-π·‖z‖²)`) | 20 | + `complex_gaussian_density_shifted` (from merged S5) | Bridge to S5 density                   |

**Total S6b ACT estimate**: ~80-100 LOC, **0 sorries, 0 axioms**, build via the existing Docker wrapper. No new imports beyond `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform` (already transitively pulled in by `Mathlib.Analysis.Fourier.FourierTransform`).

---

## §6. Anti-targets (DO NOT attempt during S6b ACT)

1. **Don't reprove `fourier_gaussian_innerProductSpace`** by copy-paste of the Mathlib internal Cauchy-integral / vertical-rectangle argument (Gouëzel 2022). The theorem is already public and stable.
2. **Don't transport via `Complex.measurableEquivRealProd` or `Complex.equivRealProd`** as the primary route. These are perfectly correct equivalences but introduce un-needed `volume`-transport that the inner-product-space lemma avoids. (They may still be useful for **secondary** corollaries — e.g., explicit Lebesgue-coordinate formulas for `re z` and `im z` — but not for the main eigenfunction theorem.)
3. **Don't introduce an axiom-style placeholder for the n-dim case** (`fourier_gaussian_complex_n`) until S6a ACT lands; S6a's per-axis Fubini chain is the right design for the n-dim shifted case, while `fourier_gaussian_innerProductSpace (V := EuclideanSpace ℂ (Fin n))` is the right design for the n-dim *Fourier* case. Both can coexist.
4. **Don't widen the slug into the p-adic side.** S4b OBSERVE (#18269) already records that `Measure ℚ_[p]` is not in Mathlib HEAD; the p-adic self-Fourier theorem is a separate, much larger upstream effort.

---

## §7. Decision criteria for choosing S6a vs S6b as the next ACT

S6a (n-dim shifted real-coordinate Gaussian, locked in PR #18389) and S6b (complex Fourier-eigenfunction, locked here) are **orthogonal**:

- S6a's deliverable: `∫_{ℂⁿ} exp(-(b·∑‖zᵢ - cᵢ‖²)) dz = (π/b)ⁿ` (integration, ℂⁿ).
- S6b's deliverable: `𝓕 (fun z : ℂ ↦ exp(-b·‖z‖²)) w = (π/b) · exp(-π²·‖w‖²/b)` (Fourier, ℂ).

The two are not in any dependency chain. The recommended ordering depends on the next-iteration goal:

- If the goal is to **strengthen the slug's measure-theoretic content** (more general densities, n-D scaling, mixed shifts), do **S6a first**.
- If the goal is to **establish the connection to the p-adic (C2) statement** in the original `problem.md`, do **S6b first** — `complex_fourier_gaussian_pi` is the literal archimedean analogue of `(F 𝟙_{ℤ_p})(0) = 1`.

Either ACT order leaves the other deferred and clean.

---

## §8. Honest framing

This S6b PREP **shortens the originally-planned S6b route by ~5×**: the canonical archimedean (C2) statement reduces to a direct specialization of an existing Mathlib theorem at `V := ℂ`, rather than requiring a manual ℂ ≃ ℝ² + Fubini transport. The novelty here is **purely in Mathlib-API navigation** — `state.md:80`'s route description was written before noticing that `fourier_gaussian_innerProductSpace` is fully generic in `V`.

The Lean target shrinks from "one ℂ ≃ ℝ × ℝ transport + Fubini reduction" to "one line invoking `fourier_gaussian_innerProductSpace` plus a `finrank_real_complex` rewrite". This is recorded as a **scope reduction**, not a novelty claim.

**Build status**: no `.lean` changes; no build attempted.

**No edits to**: `problem.md`, `state.md`, `knowledge.md`, the merged `s4b-padic-survey.md`, the open `s6a-prep-pi-haar-vs-fubini.md`, the gallery `meta.json`, or any tracked `.lean` file. This PR adds exactly one new file: this PREP note.

---

## §9. References

* **Mathlib `fourier_gaussian_innerProductSpace`**:
  `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` (lines ~370–380, plus the 2025-11-16-deprecated alias `fourierIntegral_gaussian_innerProductSpace`).
* **Mathlib `integral_cexp_neg_mul_sq_norm_add` and `_of_euclideanSpace`** (the integral-form parent of the Fourier-form):
  `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:306, 328`.
* **`Complex.finrank_real_complex`**:
  `Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:31`.
* **`instance : InnerProductSpace ℝ ℂ`**:
  `Mathlib/Analysis/InnerProductSpace/Basic.lean:984`.
* **`Real.fourierIntegral_gaussian_pi`** (the 1-D real analog cited in `state.md:80`):
  `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`.
* **Parent gallery file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`
  (~543 lines as of S5, 0 sorries, 0 axioms).
* **Merged S4b**: `research/area-of-circle-oq-05-oq-04/s4b-padic-survey.md`
  (p-adic Mathlib-gap survey, doc-only, PR #18269).
* **Open S6a PREP**: PR #18389 (n-dim shifted Gaussian via Path B per-axis Fubini, doc-only).

---

*End of S6b PREP. No other files modified.*
