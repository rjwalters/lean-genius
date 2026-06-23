/-
  Parseval Completeness over RCLike Fields: an Orthonormal System is a
  Hilbert Basis iff Parseval's Identity Holds
  (cauchy-schwarz-oq-02-oq-02-oq-01-oq-01)

  The parent `CauchySchwarzOQ02OQ02OQ01` (Parseval Completeness) proves, for a
  *real* orthonormal family {vᵢ} in a Hilbert space F, the characterization

    (∃ b : HilbertBasis ι ℝ F, ⇑b = v)  ↔  ∀ x, ∑' i, ⟨vᵢ, x⟩² = ‖x‖².

  This file lifts that equivalence to an arbitrary `RCLike` field `𝕜`
  (i.e. ℝ or ℂ).  Over ℂ the inner product is complex-valued, so the natural
  Parseval statement replaces the square `⟨vᵢ, x⟩²` by the squared norm of the
  complex Fourier coefficient:

    (∃ b : HilbertBasis ι 𝕜 E, ⇑b = v)  ↔  ∀ x, ∑' i, ‖⟨vᵢ, x⟩‖² = ‖x‖².

  Proof strategy:
  * (⟹) Forward: a Hilbert basis satisfies Parseval.  Mathlib's
    `HilbertBasis.hasSum_inner_mul_inner b x x` gives
    `∑' i, ⟪x, b i⟫ * ⟪b i, x⟫ = ⟪x, x⟫` in `𝕜`.  Projecting onto the real part
    (via the continuous ℝ-linear map `RCLike.reCLM`) and using
    `conj z * z = ‖z‖²` together with `re ⟪x, x⟫ = ‖x‖²` turns this into the
    real-valued Parseval identity `∑' i, ‖⟪b i, x⟫‖² = ‖x‖²`.
  * (⟸) Reverse (field-agnostic): from Parseval the span of {vᵢ} has trivial
    orthogonal complement — a vector orthogonal to every `vᵢ` has all Fourier
    coefficients zero, so Parseval forces its norm to vanish.  Trivial
    orthogonal complement is exactly the hypothesis of Mathlib's
    `HilbertBasis.mkOfOrthogonalEqBot`, which manufactures the basis.

  This is the "totality ⟺ Parseval" half of the standard equivalence
  (orthonormal basis ⟺ complete ⟺ Parseval ⟺ total), now over any `RCLike`
  scalar field.  Mathlib supplies the basis-construction machinery and the
  bilinear Parseval identity; the bridge proved here packages them into the
  norm-squared completeness criterion and supplies the reverse implication.

  Status: 0 sorries, 0 axioms (no `native_decide`/`Lean.ofReduceBool`).
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

set_option linter.unusedSectionVars false

open RCLike

namespace ParsevalCompletenessRCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

-- ============================================================
-- Section 1: Forward direction — a Hilbert basis satisfies Parseval
-- ============================================================

/-- **Parseval's identity over `RCLike`.** For a Hilbert basis `b` of `E` and
any `x`, the squared norms of the Fourier coefficients sum to `‖x‖²`.

The proof takes the real part of Mathlib's bilinear identity
`∑' i, ⟪x, b i⟫ * ⟪b i, x⟫ = ⟪x, x⟫`, using `conj z * z = ‖z‖²` on each summand
and `re ⟪x, x⟫ = ‖x‖²` on the total. -/
theorem parseval_rclike {ι : Type*} (b : HilbertBasis ι 𝕜 E) (x : E) :
    (∑' i, ‖⟪b i, x⟫‖ ^ 2) = ‖x‖ ^ 2 := by
  -- Real part of the bilinear Parseval identity.
  have h := (b.hasSum_inner_mul_inner x x).mapL (reCLM (K := 𝕜))
  simp only [reCLM_apply] at h
  -- Rewrite each summand `re (⟪x, b i⟫ * ⟪b i, x⟫)` to `‖⟪b i, x⟫‖²`.
  have hsummand : (fun i => re (⟪x, b i⟫ * ⟪b i, x⟫)) = fun i => ‖⟪b i, x⟫‖ ^ 2 := by
    funext i
    rw [← inner_conj_symm x (b i), RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [hsummand, inner_self_eq_norm_sq] at h
  exact h.tsum_eq

/-- **Forward direction.** If the orthonormal family `v` underlies a Hilbert
basis `b` (i.e. `⇑b = v`), then Parseval's identity holds for every `x`. -/
theorem parseval_of_hilbertBasis {ι : Type*} {v : ι → E}
    (b : HilbertBasis ι 𝕜 E) (hb : ⇑b = v) (x : E) :
    (∑' i, ‖⟪v i, x⟫‖ ^ 2) = ‖x‖ ^ 2 := by
  subst hb
  exact parseval_rclike b x

-- ============================================================
-- Section 2: Reverse direction — Parseval forces completeness
-- ============================================================

/-- **Completeness from Parseval.** If Parseval's identity holds for every `x`,
then the span of the orthonormal family has trivial orthogonal complement.
A vector orthogonal to every `vᵢ` has all Fourier coefficients zero, so
Parseval makes its norm vanish. -/
theorem orthogonalComplement_eq_bot_of_parseval {ι : Type*} {v : ι → E}
    (hp : ∀ x, (∑' i, ‖⟪v i, x⟫‖ ^ 2) = ‖x‖ ^ 2) :
    (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  -- Every coefficient ⟨vᵢ, x⟩ vanishes since x ⟂ span{vᵢ} ∋ vᵢ.
  have hzero : ∀ i, ⟪v i, x⟫ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self i)) hx
  -- Hence the Parseval sum is zero.
  have hsum : (∑' i, ‖⟪v i, x⟫‖ ^ 2) = 0 := by
    have h0 : ∀ i, ‖⟪v i, x⟫‖ ^ 2 = 0 := fun i => by rw [hzero i, norm_zero]; ring
    simp only [h0, tsum_zero]
  -- Parseval then forces ‖x‖² = 0, so x = 0.
  have hnorm : ‖x‖ ^ 2 = 0 := by rw [← hp x]; exact hsum
  have hx0 : ‖x‖ = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnorm
  exact norm_eq_zero.mp hx0

-- ============================================================
-- Section 3: Main characterization
-- ============================================================

/-- **Parseval Completeness Criterion over `RCLike`.** An orthonormal family `v`
in a Hilbert space `E` over `𝕜` (ℝ or ℂ) underlies a Hilbert basis **iff**
Parseval's identity `∑' i, ‖⟨vᵢ, x⟩‖² = ‖x‖²` holds for every `x`. -/
theorem hilbertBasis_iff_parseval {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) :
    (∃ b : HilbertBasis ι 𝕜 E, ⇑b = v) ↔ ∀ x, (∑' i, ‖⟪v i, x⟫‖ ^ 2) = ‖x‖ ^ 2 := by
  constructor
  · rintro ⟨b, hb⟩ x
    exact parseval_of_hilbertBasis b hb x
  · intro hp
    exact ⟨HilbertBasis.mkOfOrthogonalEqBot hv
      (orthogonalComplement_eq_bot_of_parseval hp),
      HilbertBasis.coe_mkOfOrthogonalEqBot hv _⟩

/-- **Completeness ⟺ Parseval (no construction).** For an orthonormal family,
trivial orthogonal complement of its span is equivalent to Parseval holding
everywhere. -/
theorem orthogonalComplement_eq_bot_iff_parseval {ι : Type*} {v : ι → E}
    (hv : Orthonormal 𝕜 v) :
    (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ ↔
      ∀ x, (∑' i, ‖⟪v i, x⟫‖ ^ 2) = ‖x‖ ^ 2 := by
  constructor
  · intro hsp x
    exact parseval_of_hilbertBasis (HilbertBasis.mkOfOrthogonalEqBot hv hsp)
      (HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp) x
  · exact orthogonalComplement_eq_bot_of_parseval

end ParsevalCompletenessRCLike

-- ============================================================
-- Examples
-- ============================================================

section Examples

open ParsevalCompletenessRCLike

/-- A genuine Hilbert basis (e.g. the standard basis of a complex `ℓ²` space)
satisfies Parseval — an immediate consequence of the forward direction. -/
example {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (b : HilbertBasis ι 𝕜 E) (x : E) :
    (∑' i, ‖inner 𝕜 (b i) x‖ ^ 2) = ‖x‖ ^ 2 :=
  parseval_rclike b x

end Examples

-- Axiom audit: confirms dependence only on standard foundational axioms
-- (propext, Classical.choice, Quot.sound) — no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms ParsevalCompletenessRCLike.hilbertBasis_iff_parseval
