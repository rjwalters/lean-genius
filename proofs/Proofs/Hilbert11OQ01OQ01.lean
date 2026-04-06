/-
# Meyer's Theorem from Hasse-Minkowski: dim ≥ 5 Indefinite Forms are Isotropic

## Open Question: hilbert-11-oq-01-oq-01

Meyer's theorem (1884): Every non-degenerate indefinite quadratic form over ℚ
in at least 5 variables is isotropic (i.e., represents zero nontrivially).

"Indefinite" means the form is not positive definite or negative definite,
equivalently, it is isotropic over ℝ.

## Proof Strategy

By the Hasse-Minkowski theorem (`hasse_minkowski_refined`):
  Q is isotropic over ℚ ⟺ Q is isotropic over ℝ AND over ℚₚ for all p.

So Meyer's theorem follows from:
1. **Real condition** (hypothesis): Q is indefinite, i.e., `IsIsotropicOverReals Q`.
2. **p-adic condition** (Chevalley-Warning + Hensel): For dim ≥ 5, every quadratic
   form over ℚₚ is isotropic. This follows from:
   - Over the residue field 𝔽ₚ: Chevalley-Warning gives solutions for dim ≥ 3 forms.
   - By Hensel's lemma: these lift to ℚₚ solutions (for nonsingular reduction).

## Status: AXIOMATIZED (2 axioms: hasse_minkowski_refined + padic_five_var_isotropic)

The Chevalley-Warning consequence over ℚₚ is axiomized (`padic_five_var_isotropic`).
Meyer's theorem itself is a PROVED theorem from these two axioms.

## References

- Meyer (1884): Original proof
- Serre, "A Course in Arithmetic", Ch. IV §3: Local-global for forms in ≥ 5 vars
- Lam, "Introduction to Quadratic Forms over Fields", §VI.2
-/

import Proofs.Hilbert11OQ01
import Mathlib.Tactic

namespace Hilbert11OQ01OQ01

open Hilbert11OQ01
open scoped TensorProduct

variable {n : ℕ}

/-! ## Chevalley-Warning Consequence for ℚₚ -/

/-- **p-Adic Isotropy for Quadratic Forms in ≥ 5 Variables**.

Every quadratic form over ℚₚ in ≥ 5 variables is isotropic (has a nontrivial zero).

**Proof sketch** (not yet formalized in Mathlib):
1. Reduce mod p: the form gives a quadratic form over 𝔽ₚ in ≥ 5 variables.
2. Chevalley-Warning theorem: any polynomial system of degree d in > d variables
   over a finite field has a nontrivial solution. For quadratic forms (d=2),
   any form in ≥ 3 variables over 𝔽ₚ is isotropic.
3. Hensel's lemma: a nonsingular solution over 𝔽ₚ lifts to ℚₚ.
   (For dim ≥ 5, any isotropic vector for the mod-p reduction can be made nonsingular
   by a standard lifting argument.)

**Formalization status**: Axiom. Chevalley-Warning is present in Mathlib4
(`MvPolynomial.card_roots_le_degree`), but the lift from 𝔽ₚ to ℚₚ via Hensel
requires additional infrastructure connecting `QuadraticForm.baseChange` to
the residue field reduction. -/
axiom padic_five_var_isotropic (Q : QuadraticForm ℚ (Fin n → ℚ)) (hn : 5 ≤ n)
    (p : ℕ) [Fact (Nat.Prime p)] : IsIsotropicOverPadic Q p

/-! ## Meyer's Theorem -/

/-- **Meyer's Theorem**: Every non-degenerate indefinite quadratic form over ℚ
in at least 5 variables is isotropic.

**Proof**: By Hasse-Minkowski (`hasse_minkowski_refined`), Q is isotropic over ℚ
iff Q is isotropic everywhere locally. The hypotheses give:
- Over ℝ: `hreal : IsIsotropicOverReals Q` (the indefiniteness condition)
- Over ℚₚ for all p: `padic_five_var_isotropic Q hn p` (Chevalley-Warning + Hensel)

Combining these via Hasse-Minkowski gives rational isotropy. -/
theorem meyer_theorem (Q : QuadraticForm ℚ (Fin n → ℚ)) (hn : 5 ≤ n)
    (hreal : IsIsotropicOverReals Q) :
    ∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0 := by
  rw [hasse_minkowski_refined]
  exact ⟨hreal, fun p _ => padic_five_var_isotropic Q hn p⟩

/-- **Corollary**: Meyer's theorem for exactly 5 variables. -/
theorem meyer_five_vars (Q : QuadraticForm ℚ (Fin 5 → ℚ))
    (hreal : IsIsotropicOverReals Q) :
    ∃ v : Fin 5 → ℚ, v ≠ 0 ∧ Q v = 0 :=
  meyer_theorem Q (le_refl 5) hreal

/-! ## Real Isotropy Criterion -/

/-- A quadratic form that represents both positive and negative values over ℝ
is isotropic over ℝ (by the intermediate value theorem).

This provides a computable criterion for `IsIsotropicOverReals` when the form
can be evaluated at specific real vectors. -/
theorem real_isotropic_of_sign_change (Q : QuadraticForm ℚ (Fin n → ℚ))
    (v w : Fin n → ℚ)
    (hv : Q.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] v) < 0)
    (hw : 0 < Q.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] w)) :
    IsIsotropicOverReals Q := by
  -- By IVT, there exists t ∈ [0,1] such that Q(t·v + (1-t)·w) = 0
  -- Formalized via the intermediate value theorem for continuous functions
  -- The form Q ∘ baseChange ℝ is continuous (being a polynomial)
  -- Strategy: t·(1⊗v) + (1-t)·(1⊗w) is a path from (1⊗w) to (1⊗v)
  -- f(t) = Q.baseChange ℝ (t·(1⊗v) + (1-t)·(1⊗w)) is continuous
  -- f(0) = hw > 0, f(1) = hv < 0 → ∃ t, f(t) = 0 → ∃ nonzero zero
  -- Proof via IVT on the path t ↦ Q.baseChange ℝ (t•(1⊗v) + (1-t)•(1⊗w)):
  -- f(0) = Q(w) > 0, f(1) = Q(v) < 0, f continuous → ∃ t₀, f(t₀) = 0
  -- Nonzero: v,w are ℚ-linearly independent (since Q(v)<0, Q(w)>0, so Q(cv)=c²Q(v)<0≠Q(w)
  -- for all c), hence 1⊗v, 1⊗w are ℝ-linearly independent, so the path is nonzero.
  -- Technical challenge: SMul instances on ℝ ⊗[ℚ] (Fin n → ℚ) tensor products
  sorry

/-! ## Special Case: Diagonal Forms -/

/-- Indefinite real forms have both positive and negative values:
if Q(v) > 0 and Q(w) < 0 for some rational v, w, then Q is isotropic over ℝ. -/
theorem real_isotropic_of_rational_sign_change (Q : QuadraticForm ℚ (Fin n → ℚ))
    (v w : Fin n → ℚ) (hv : Q v < 0) (hw : 0 < Q w) :
    IsIsotropicOverReals Q := by
  -- Q v and Q w have opposite signs over ℚ, hence over ℝ
  -- The baseChange evaluation at 1 ⊗ₜ v gives Q v (as a real number)
  -- So Q.baseChange ℝ (1 ⊗ₜ v) = Q v < 0 and Q.baseChange ℝ (1 ⊗ₜ w) = Q w > 0
  -- By IVT, there exists a real zero on the path from 1⊗v to 1⊗w
  sorry -- Requires: IVT for continuous quadratic forms, plus casting Q v to ℝ

end Hilbert11OQ01OQ01
