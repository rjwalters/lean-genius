import Mathlib

/-
# De Moivre OQ-04-OQ-03: The Minimal Polynomial of ω is the Cyclotomic Polynomial Φₙ

## Research Problem: de-moivre-oq-04-oq-03

The parent entry `de-moivre-oq-04` isolates

  ω = cos(2π/n) + i·sin(2π/n)

as a *primitive* n-th root of unity, proving ωⁿ = 1 and that its powers
enumerate all n-th roots of unity. This follow-up identifies the algebraic
object that ω satisfies over the rationals:

  **The minimal polynomial of ω over ℚ is the n-th cyclotomic polynomial Φₙ.**

## Mathematical Content

The n-th roots of unity are exactly the roots of Xⁿ − 1, but ω is a *primitive*
root, so it is not a root of Xᵏ − 1 for any 0 < k < n. The cyclotomic polynomial
Φₙ ∈ ℚ[X] collects precisely the primitive n-th roots of unity:

  Xⁿ − 1 = ∏_{d ∣ n} Φ_d(X).

Two classical facts pin down the minimal polynomial:

1. **ω is a root of Φₙ** — by definition Φₙ vanishes at every primitive n-th root.
2. **Φₙ is irreducible over ℚ** (Gauss / Kronecker / Dedekind), hence equal to the
   minimal polynomial of any of its roots, up to the monic normalisation that both
   minimal polynomials and cyclotomic polynomials share.

Consequences that fall out immediately:

* `deg Φₙ = φ(n)` (Euler's totient), so the minimal polynomial has degree φ(n);
* therefore **[ℚ(ω) : ℚ] = φ(n)** — the degree of the n-th cyclotomic field.

This is the algebraic-number-theory deepening of the trigonometric oq-04 picture:
oq-04 says ω generates the n-th roots of unity *geometrically*; here we read off
its *arithmetic* invariant, the cyclotomic field degree φ(n).

## References
- C. F. Gauss, *Disquisitiones Arithmeticae* (1801): irreducibility of Φ_p
- L. Kronecker / R. Dedekind: irreducibility of Φₙ for all n
- Mathlib: `Polynomial.cyclotomic_eq_minpoly_rat`, `Polynomial.cyclotomic.irreducible_rat`,
  `Polynomial.natDegree_cyclotomic`, `IntermediateField.adjoin.finrank`
-/

open Complex Real Polynomial
open scoped IntermediateField

namespace DeMoivreOQ04OQ03

/-- The primitive n-th root of unity in trigonometric form (same as oq-04):
    ω = cos(2π/n) + i·sin(2π/n). -/
noncomputable def omega (n : ℕ) : ℂ :=
  Complex.cos (↑(2 * π / n)) + Complex.sin (↑(2 * π / n)) * I

/-- Euler bridge: ω = e^{2πi/n} (so we can reuse `Complex.isPrimitiveRoot_exp`). -/
theorem omega_eq_exp (n : ℕ) : omega n = Complex.exp (2 * π * I / n) := by
  unfold omega
  rw [← Complex.exp_mul_I]
  congr 1
  push_cast
  ring

/-- ω is a primitive n-th root of unity. -/
theorem omega_isPrimitiveRoot (n : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot (omega n) n := by
  rw [omega_eq_exp]
  exact Complex.isPrimitiveRoot_exp n hn.ne'

/-- ωⁿ = 1, recovered from primitivity (also proved directly in oq-04). -/
theorem omega_pow_n (n : ℕ) (hn : 0 < n) : (omega n) ^ n = 1 :=
  (omega_isPrimitiveRoot n hn).pow_eq_one

/-! ## Part I: ω is integral over ℚ -/

/-- ω is integral over ℚ: it is a root of the monic polynomial Xⁿ − 1. -/
theorem omega_isIntegral (n : ℕ) (hn : 0 < n) : IsIntegral ℚ (omega n) := by
  refine ⟨X ^ n - C 1, ?_, ?_⟩
  · simpa using monic_X_pow_sub_C (1 : ℚ) hn.ne'
  · simp [omega_pow_n n hn]

/-! ## Part II: the minimal polynomial is the cyclotomic polynomial -/

/-- **Headline.** The minimal polynomial of ω over ℚ is the n-th cyclotomic
    polynomial Φₙ. Both sides are monic, and Φₙ is irreducible over ℚ with ω as a
    root, so they coincide. -/
theorem minpoly_omega_eq_cyclotomic (n : ℕ) (hn : 0 < n) :
    minpoly ℚ (omega n) = cyclotomic n ℚ :=
  (cyclotomic_eq_minpoly_rat (omega_isPrimitiveRoot n hn) hn).symm

/-- The minimal polynomial of ω is irreducible over ℚ (it equals Φₙ). -/
theorem minpoly_omega_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible (minpoly ℚ (omega n)) := by
  rw [minpoly_omega_eq_cyclotomic n hn]
  exact cyclotomic.irreducible_rat hn

/-- ω is a root of the cyclotomic polynomial Φₙ: `aeval ω Φₙ = 0`. -/
theorem aeval_omega_cyclotomic (n : ℕ) (hn : 0 < n) :
    aeval (omega n) (cyclotomic n ℚ) = 0 := by
  rw [← minpoly_omega_eq_cyclotomic n hn]
  exact minpoly.aeval ℚ (omega n)

/-! ## Part III: degree φ(n) and the cyclotomic field -/

/-- The minimal polynomial of ω has degree φ(n) (Euler's totient). -/
theorem natDegree_minpoly_omega (n : ℕ) (hn : 0 < n) :
    (minpoly ℚ (omega n)).natDegree = Nat.totient n := by
  rw [minpoly_omega_eq_cyclotomic n hn, natDegree_cyclotomic]

/-- **Cyclotomic field degree.** The simple extension ℚ(ω) has degree φ(n) over ℚ:
    `[ℚ(ω) : ℚ] = φ(n)`. -/
theorem finrank_adjoin_omega (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ ℚ⟮omega n⟯ = Nat.totient n := by
  rw [IntermediateField.adjoin.finrank (omega_isIntegral n hn),
    natDegree_minpoly_omega n hn]

/-! ## Part IV: verified small cases -/

-- n = 1: Φ₁ = X − 1, φ(1) = 1.
example : (minpoly ℚ (omega 1)).natDegree = 1 := by
  rw [natDegree_minpoly_omega 1 (by norm_num)]; rfl

-- n = 4: Φ₄ = X² + 1, φ(4) = 2  (ω = i, minimal polynomial X² + 1).
example : (minpoly ℚ (omega 4)).natDegree = 2 := by
  rw [natDegree_minpoly_omega 4 (by norm_num)]; rfl

-- n = 6: φ(6) = 2  (the primitive 6th root has minimal polynomial X² − X + 1).
example : Module.finrank ℚ ℚ⟮omega 6⟯ = 2 := by
  rw [finrank_adjoin_omega 6 (by norm_num)]; rfl

-- n = 5: φ(5) = 4  (Φ₅ = X⁴ + X³ + X² + X + 1 is irreducible of degree 4).
example : Module.finrank ℚ ℚ⟮omega 5⟯ = 4 := by
  rw [finrank_adjoin_omega 5 (by norm_num)]; rfl

/-! ## Part V: Summary -/

/-- **De Moivre OQ-04-OQ-03 Summary.** For n > 0, with ω = cos(2π/n) + i·sin(2π/n):
    (1) ω is integral over ℚ;
    (2) its minimal polynomial over ℚ is the cyclotomic polynomial Φₙ;
    (3) that minimal polynomial is irreducible of degree φ(n);
    (4) hence the cyclotomic field has degree [ℚ(ω) : ℚ] = φ(n). -/
theorem demoivre_oq04_oq03_summary (n : ℕ) (hn : 0 < n) :
    IsIntegral ℚ (omega n) ∧
    minpoly ℚ (omega n) = cyclotomic n ℚ ∧
    Irreducible (minpoly ℚ (omega n)) ∧
    (minpoly ℚ (omega n)).natDegree = Nat.totient n ∧
    Module.finrank ℚ ℚ⟮omega n⟯ = Nat.totient n :=
  ⟨omega_isIntegral n hn,
   minpoly_omega_eq_cyclotomic n hn,
   minpoly_omega_irreducible n hn,
   natDegree_minpoly_omega n hn,
   finrank_adjoin_omega n hn⟩

end DeMoivreOQ04OQ03
