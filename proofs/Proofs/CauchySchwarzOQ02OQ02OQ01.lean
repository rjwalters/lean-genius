/-
  Parseval Completeness: an Orthonormal System is a Hilbert Basis
  iff Bessel's Inequality is an Equality
  (cauchy-schwarz-oq-02-oq-02-oq-01)

  The parent `CauchySchwarzOQ02OQ02` (Bessel's inequality in infinite
  dimensions) proves, for a real orthonormal family {vᵢ} in a Hilbert space F:

    • Bessel:   ∑' i, ⟨vᵢ, x⟩² ≤ ‖x‖²        (always)
    • Parseval: ∑' i, ⟨vᵢ, x⟩² = ‖x‖²        (when {vᵢ} is a Hilbert basis)

  This file proves the **converse / completeness criterion**: equality in
  Bessel is not just a consequence of completeness — it *characterizes* it.
  An orthonormal family is a Hilbert basis **iff** Parseval's identity holds
  for every vector:

    (∃ b : HilbertBasis ι ℝ F, ⇑b = v)  ↔  ∀ x, ∑' i, ⟨vᵢ, x⟩² = ‖x‖².

  Proof strategy:
  * (⟹) Forward: a Hilbert basis satisfies Parseval — this is the parent's
    `BesselInequality.parseval_real`, transported along `⇑b = v`.
  * (⟸) Reverse: from Parseval we show the span of {vᵢ} has trivial orthogonal
    complement. Indeed, if `x ⟂ span{vᵢ}` then every coefficient ⟨vᵢ, x⟩ = 0,
    so Parseval forces ‖x‖² = ∑' i, 0 = 0, i.e. x = 0. Trivial orthogonal
    complement is exactly the hypothesis of Mathlib's
    `HilbertBasis.mkOfOrthogonalEqBot`, which manufactures the Hilbert basis.

  This is the "totality ⟺ Parseval" half of the standard equivalence
  (orthonormal basis ⟺ complete ⟺ Parseval ⟺ total). Mathlib supplies the
  basis-construction machinery and the forward Parseval identity; the bridge
  proved here is the reverse implication that turns Parseval into completeness.

  Status: 0 sorries, 0 axioms (no `native_decide`/`Lean.ofReduceBool`).
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic
import Proofs.CauchySchwarzOQ02OQ02

open scoped RealInnerProductSpace
open BesselInequality

namespace ParsevalCompleteness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

-- ============================================================
-- Section 1: Forward direction — a Hilbert basis satisfies Parseval
-- ============================================================

/-- **Forward direction.** If the orthonormal family `v` underlies a Hilbert
basis `b` (i.e. `⇑b = v`), then Parseval's identity holds for every `x`.
This transports the parent's `parseval_real` along the equality `⇑b = v`. -/
theorem parseval_of_hilbertBasis {ι : Type*} {v : ι → F}
    (b : HilbertBasis ι ℝ F) (hb : ⇑b = v) (x : F) :
    (∑' i, ⟪v i, x⟫ ^ 2) = ‖x‖ ^ 2 := by
  -- `v` is a local variable, so substituting `⇑b = v` reduces this exactly to
  -- the parent's verified Parseval identity for the Hilbert basis `b`.
  subst hb
  exact parseval_real b x

-- ============================================================
-- Section 2: Reverse direction — Parseval forces completeness
-- ============================================================

/-- **Completeness from Parseval.** If Parseval's identity holds for every `x`,
then the span of the orthonormal family has trivial orthogonal complement.
A vector orthogonal to every `vᵢ` has all Fourier coefficients zero, so
Parseval makes its norm vanish. -/
theorem orthogonalComplement_eq_bot_of_parseval {ι : Type*} {v : ι → F}
    (hp : ∀ x, (∑' i, ⟪v i, x⟫ ^ 2) = ‖x‖ ^ 2) :
    (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  -- Every coefficient ⟨vᵢ, x⟩ vanishes since x ⟂ span{vᵢ} ∋ vᵢ.
  have hzero : ∀ i, ⟪v i, x⟫ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self i)) hx
  -- Hence the Bessel/Parseval sum is zero.
  have hsum : (∑' i, ⟪v i, x⟫ ^ 2) = 0 := by
    have h0 : ∀ i, ⟪v i, x⟫ ^ 2 = 0 := fun i => by rw [hzero i]; ring
    simp only [h0, tsum_zero]
  -- Parseval then forces ‖x‖² = 0, so x = 0.
  have hnorm : ‖x‖ ^ 2 = 0 := by rw [← hp x]; exact hsum
  have hx0 : ‖x‖ = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnorm
  exact norm_eq_zero.mp hx0

-- ============================================================
-- Section 3: Main characterization
-- ============================================================

/-- **Parseval Completeness Criterion.** A real orthonormal family `v` in a
Hilbert space `F` underlies a Hilbert basis **iff** Parseval's identity
`∑' i, ⟨vᵢ, x⟩² = ‖x‖²` holds for every `x` — equivalently, iff Bessel's
inequality is everywhere an equality. -/
theorem hilbertBasis_iff_parseval {ι : Type*} {v : ι → F} (hv : Orthonormal ℝ v) :
    (∃ b : HilbertBasis ι ℝ F, ⇑b = v) ↔ ∀ x, (∑' i, ⟪v i, x⟫ ^ 2) = ‖x‖ ^ 2 := by
  constructor
  · rintro ⟨b, hb⟩ x
    exact parseval_of_hilbertBasis b hb x
  · intro hp
    refine ⟨HilbertBasis.mkOfOrthogonalEqBot hv
      (orthogonalComplement_eq_bot_of_parseval hp), ?_⟩
    exact HilbertBasis.coe_mkOfOrthogonalEqBot hv _

/-- **Completeness ⟺ Parseval (no construction).** For an orthonormal family,
trivial orthogonal complement of its span is equivalent to Parseval holding
everywhere. This is the "totality ⟺ Bessel-is-equality" form of the criterion. -/
theorem orthogonalComplement_eq_bot_iff_parseval {ι : Type*} {v : ι → F}
    (hv : Orthonormal ℝ v) :
    (Submodule.span ℝ (Set.range v))ᗮ = ⊥ ↔
      ∀ x, (∑' i, ⟪v i, x⟫ ^ 2) = ‖x‖ ^ 2 := by
  constructor
  · intro hsp x
    exact parseval_of_hilbertBasis (HilbertBasis.mkOfOrthogonalEqBot hv hsp)
      (HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp) x
  · exact orthogonalComplement_eq_bot_of_parseval

end ParsevalCompleteness

-- ============================================================
-- Examples
-- ============================================================

section Examples

open ParsevalCompleteness

/-- A genuine Hilbert basis (e.g. the standard basis of an `ℓ²` space) satisfies
Parseval — an immediate consequence of the forward direction. -/
example {ι : Type*} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (b : HilbertBasis ι ℝ F) (x : F) :
    (∑' i, ⟪b i, x⟫ ^ 2) = ‖x‖ ^ 2 :=
  parseval_of_hilbertBasis b rfl x

end Examples

-- Axiom audit: confirms dependence only on standard foundational axioms
-- (propext, Classical.choice, Quot.sound) — no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms ParsevalCompleteness.hilbertBasis_iff_parseval
