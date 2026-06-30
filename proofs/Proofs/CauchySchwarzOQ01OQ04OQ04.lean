import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

/-!
# The Converse of Parseval: Completeness from the Equality Case (Cauchy–Schwarz, OQ-01-OQ-04-OQ-04)

## What This Proves

The Bessel/Parseval entry `CauchySchwarzOQ01OQ04` establishes **Bessel's inequality**
`∑' i, |⟨vᵢ, x⟩|² ≤ ‖x‖²` for every orthonormal family `v : ι → E`, and shows that when `v` is
(the underlying family of) a `HilbertBasis`, Bessel becomes the **Parseval identity**
`∑' i, |⟨vᵢ, x⟩|² = ‖x‖²`. That entry's docstring left as its fourth open question the
*converse*:

  *"Prove the converse: if `∑' i, ‖⟪vᵢ, x⟫‖² = ‖x‖²` for some orthonormal family, is it
  necessarily a Hilbert basis? (This characterizes complete orthonormal systems.)"*

This file answers exactly that, with a full **iff** characterization of completeness:

  **An orthonormal family `v` in a Hilbert space satisfies Parseval for every vector `x`
  if and only if `v` is the underlying family of a Hilbert basis.**

The forward (converse-of-Parseval) direction is the substance: Parseval forces the orthogonal
complement of `span v` to be trivial, so by `HilbertBasis.mkOfOrthogonalEqBot` the family
completes to a Hilbert basis *without enlargement* — its underlying family is `v` itself. The
backward direction reproduces the parent's `parseval_identity` (`parseval_of_hilbertBasis`).

This entry is deliberately **self-contained** (it imports only Mathlib), so it stands
independently of the parent file.

## A small sharpening

Triviality of the orthogonal complement — and hence density of the span — follows from the
Parseval identity **alone**: orthonormality of `v` plays no role in `orthogonal_eq_bot_of_parseval`
or `span_topologicalClosure_eq_top_of_parseval`. Indeed, if every Fourier coefficient
`⟪vᵢ, y⟫` of `y` vanishes (i.e. `y ⟂ span v`), then `‖y‖² = ∑' i, 0 = 0`, so `y = 0`. The
orthonormality hypothesis re-enters only when we *package* the total family as a genuine
Hilbert basis via `mkOfOrthogonalEqBot`.

## Original Contributions
- `orthogonal_eq_bot_of_parseval` — the analytic core: Parseval-for-all-`x` ⟹
  `(span 𝕜 (range v))ᗮ = ⊥`. Needs neither completeness nor orthonormality.
- `hilbertBasisOfParseval` / `coe_hilbertBasisOfParseval` — the construction: a Hilbert basis
  built from `v` and the Parseval hypothesis, whose underlying family is `v` itself.
- `span_topologicalClosure_eq_top_of_parseval` — totality: Parseval ⟹ `span v` is dense.
- `parseval_of_hilbertBasis` — the parent's forward Parseval identity, via the `ℓ²` isometry
  `b.repr` (reproduced so the file is standalone).
- `parseval_iff_isHilbertBasis` — the headline equivalence characterizing complete orthonormal
  systems: Parseval-for-all-`x` ⟺ `v` is (the coe of) a Hilbert basis.

## Proof Techniques
The core is a one-line energy argument: membership in `(span v)ᗮ` (via `Submodule.mem_orthogonal`
applied to each `vᵢ ∈ span v`) kills every Fourier coefficient `⟪vᵢ, y⟫`, so the Parseval sum
collapses to `0`, forcing `‖y‖ = 0` (`pow_eq_zero_iff`, `norm_eq_zero`). The construction is
`HilbertBasis.mkOfOrthogonalEqBot`; totality is `Submodule.orthogonal_orthogonal_eq_closure`
together with `bot_orthogonal_eq_top`. The Parseval identity uses the `ℓ²`-norm formula
`lp.norm_rpow_eq_tsum` and the isometry `b.repr.norm_map`. Everything is over an `RCLike`
field and is `0`-axiom (`propext`, `Classical.choice`, `Quot.sound` only) / `0`-sorry.
-/

open scoped InnerProductSpace ENNReal

namespace CauchySchwarzOQ01OQ04OQ04

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-! ## Part I: The analytic core — Parseval forces a trivial orthogonal complement

If the Parseval identity holds for *every* vector, then no nonzero vector can be orthogonal
to the whole family: such a vector would have all Fourier coefficients zero, hence Parseval
energy `0`, hence norm `0`. This needs neither completeness nor orthonormality. -/

/-- **Parseval ⟹ trivial orthogonal complement.** If `∑' i, ‖⟪vᵢ, x⟫‖² = ‖x‖²` for every `x`,
then `(span 𝕜 (range v))ᗮ = ⊥`: the family is *total*. Orthonormality is not used. -/
theorem orthogonal_eq_bot_of_parseval {v : ι → E}
    (hpar : ∀ x : E, ∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2) :
    (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  -- Every basis vector lies in the span, so `y ⟂ vᵢ` for all `i`.
  have hzero : ∀ i, ⟪v i, y⟫_𝕜 = 0 := fun i =>
    (Submodule.mem_orthogonal _ y).mp hy (v i) (Submodule.subset_span (Set.mem_range_self i))
  -- Hence the Parseval sum is the sum of zeros.
  have hsum : ∑' i, ‖⟪v i, y⟫_𝕜‖ ^ 2 = 0 := by
    have hfun : (fun i => ‖⟪v i, y⟫_𝕜‖ ^ 2) = fun _ : ι => (0 : ℝ) := by
      funext i; rw [hzero i, norm_zero]; ring
    rw [hfun, tsum_zero]
  -- Parseval then forces `‖y‖² = 0`, so `y = 0`.
  have hy2 : ‖y‖ ^ 2 = 0 := by rw [← hpar y, hsum]
  have hy0 : ‖y‖ = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hy2
  exact norm_eq_zero.mp hy0

/-! ## Part II: The construction — completing to a Hilbert basis

With the orthogonal complement trivial, `HilbertBasis.mkOfOrthogonalEqBot` turns the
orthonormal family into a genuine Hilbert basis, *without* adding any vectors: the underlying
family of the resulting basis is `v` itself. This requires `E` to be complete. -/

/-- **Construction of the completing Hilbert basis.** An orthonormal family satisfying Parseval
for every vector *is* a Hilbert basis (no enlargement needed). -/
noncomputable def hilbertBasisOfParseval [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hpar : ∀ x : E, ∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.mkOfOrthogonalEqBot hv (orthogonal_eq_bot_of_parseval hpar)

/-- The constructed Hilbert basis has `v` as its underlying family. -/
@[simp]
theorem coe_hilbertBasisOfParseval [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hpar : ∀ x : E, ∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2) :
    ⇑(hilbertBasisOfParseval hv hpar) = v :=
  HilbertBasis.coe_mkOfOrthogonalEqBot hv _

/-! ## Part III: Totality (density of the span)

Triviality of the orthogonal complement is, in a Hilbert space, exactly density of the span.
This is the classical "complete orthonormal system" picture, and again uses only Parseval. -/

/-- **Totality.** Parseval-for-all-`x` makes the span of the family dense. -/
theorem span_topologicalClosure_eq_top_of_parseval [CompleteSpace E] {v : ι → E}
    (hpar : ∀ x : E, ∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2) :
    (Submodule.span 𝕜 (Set.range v)).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    orthogonal_eq_bot_of_parseval hpar, Submodule.bot_orthogonal_eq_top]

/-! ## Part IV: The forward Parseval identity and the headline equivalence

`parseval_of_hilbertBasis` reproduces the parent's Parseval identity through the `ℓ²` isometry
`b.repr`; combined with Parts I–II it yields a clean characterization of completeness. -/

/-- **Parseval's identity for a Hilbert basis.** Via the `ℓ²` isometry `b.repr`, the squared
Fourier coefficients of `x` sum to `‖x‖²`. -/
theorem parseval_of_hilbertBasis [CompleteSpace E] (b : HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i, ‖⟪b i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have key := lp.norm_rpow_eq_tsum hp (b.repr x)
  rw [b.repr.norm_map] at key
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2, Real.rpow_natCast] at key
  rw [key]
  refine tsum_congr (fun i => ?_)
  rw [Real.rpow_natCast, b.repr_apply_apply]

/-- **Completeness characterization.** For an orthonormal family `v` in a Hilbert space, the
Parseval identity holds for *every* vector if and only if `v` is the underlying family of a
Hilbert basis. This is the exact converse of `parseval_of_hilbertBasis`. -/
theorem parseval_iff_isHilbertBasis [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    (∀ x : E, ∑' i, ‖⟪v i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2) ↔ ∃ b : HilbertBasis ι 𝕜 E, ⇑b = v := by
  constructor
  · intro hpar
    exact ⟨hilbertBasisOfParseval hv hpar, coe_hilbertBasisOfParseval hv hpar⟩
  · rintro ⟨b, hb⟩ x
    have h := parseval_of_hilbertBasis b x
    simpa only [hb] using h

end CauchySchwarzOQ01OQ04OQ04
