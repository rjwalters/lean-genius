/-
  Vieta's Formulas for Degree-n Polynomials (General Case)

  This entry answers the first open question of `solution-of-cubic-oq-03-oq-05`
  ("Vieta's Formulas for the General Cubic"):

    "Can Vieta's formulas for degree-n polynomials be proved in generality in Lean
     using Mathlib's `Polynomial.roots` and `Multiset` infrastructure?"
    "Do Mathlib's `Polynomial.Vieta` lemmas cover the general case?"

  Answer: yes, in full generality. The cornerstone is Mathlib's
  `Polynomial.coeff_eq_esymm_roots_of_card`, which expresses every coefficient of a
  polynomial that *splits* (its root multiset has cardinality equal to its degree)
  as an elementary symmetric function of its roots:

      coeff k = leadingCoeff · (-1)^(n-k) · e_{n-k}(roots).

  From this single formula we assemble the classical named relations for an arbitrary
  degree `n`, generalizing the cubic case of the parent entry:

    * sum of the roots          (the X^{n-1} coefficient),
    * second symmetric function (the X^{n-2} coefficient),
    * product of the roots      (the constant coefficient),

  together with the field (non-monic) versions, the symmetric-function form for an
  explicit product of linear factors `∏ (X - rᵢ)`, and a concrete recovery of the
  cubic Vieta relations as the cardinality-3 special case.

  Everything is `0`-sorry, `0`-axiom, building only on Mathlib.
-/
import Mathlib

open Polynomial Multiset

set_option linter.unusedSectionVars false

namespace VietaGeneral

/-! ## Section I: Elementary symmetric helper -/

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The first elementary symmetric function of a multiset is its sum:
`e₁(s) = ∑ s`. -/
theorem esymm_one_eq_sum (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

/-! ## Section II: The general Vieta coefficient formula

The whole theory follows from one Mathlib lemma. -/

/-- **Vieta's formula, general degree-n form.** For a polynomial `p` over an integral
domain whose root multiset has cardinality equal to its degree (i.e. `p` splits), the
`k`-th coefficient equals `leadingCoeff · (-1)^(n-k) · e_{n-k}(roots)`. -/
theorem vieta_coeff (p : R[X]) (hcard : Multiset.card p.roots = p.natDegree)
    {k : ℕ} (hk : k ≤ p.natDegree) :
    p.coeff k =
      p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card hcard hk

/-! ## Section III: The classical named relations (monic case)

For a monic polynomial these collapse to the textbook Vieta formulas. -/

/-- **Sum of the roots.** For a monic, split polynomial of degree `≥ 1`, the
next-to-leading coefficient is minus the sum of the roots:
`coeff (n-1) = -∑ roots`. -/
theorem sum_of_roots (p : R[X]) (hm : p.Monic)
    (hcard : Multiset.card p.roots = p.natDegree) (hdeg : 1 ≤ p.natDegree) :
    p.coeff (p.natDegree - 1) = - p.roots.sum := by
  have hk : p.natDegree - 1 ≤ p.natDegree := Nat.sub_le _ _
  have h := vieta_coeff p hcard hk
  have hsub : p.natDegree - (p.natDegree - 1) = 1 := by omega
  rw [hsub, esymm_one_eq_sum, hm.leadingCoeff] at h
  rw [h]; ring

/-- **Second elementary symmetric function.** For a monic, split polynomial of degree
`≥ 2`, the `X^{n-2}` coefficient is the second elementary symmetric function of the
roots (the sum of products of pairs): `coeff (n-2) = e₂(roots)`. -/
theorem coeff_sub_two_eq_esymm_two (p : R[X]) (hm : p.Monic)
    (hcard : Multiset.card p.roots = p.natDegree) (hdeg : 2 ≤ p.natDegree) :
    p.coeff (p.natDegree - 2) = p.roots.esymm 2 := by
  have hk : p.natDegree - 2 ≤ p.natDegree := Nat.sub_le _ _
  have h := vieta_coeff p hcard hk
  have hsub : p.natDegree - (p.natDegree - 2) = 2 := by omega
  rw [hsub, hm.leadingCoeff] at h
  rw [h]; ring

/-- **Product of the roots.** For a monic, split polynomial, the constant coefficient
is `(-1)^n` times the product of the roots: `coeff 0 = (-1)^n · ∏ roots`. -/
theorem prod_of_roots (p : R[X]) (hm : p.Monic)
    (hcard : Multiset.card p.roots = p.natDegree) :
    p.coeff 0 = (-1) ^ p.natDegree * p.roots.prod :=
  (splits_iff_card_roots.mpr hcard).coeff_zero_eq_prod_roots_of_monic hm

/-! ## Section IV: Field (non-monic) versions

Over a field we may divide by the leading coefficient and recover the familiar
"`-a_{n-1}/a_n`" and "`(-1)^n a_0/a_n`" statements. -/

section Field

variable {F : Type*} [Field F]

/-- Over a field, a split polynomial of degree `≥ 1` has leading coefficient nonzero. -/
private theorem leadingCoeff_ne_zero_of_deg (p : F[X]) (hdeg : 1 ≤ p.natDegree) :
    p.leadingCoeff ≠ 0 := by
  intro h
  rw [Polynomial.leadingCoeff_eq_zero] at h
  rw [h] at hdeg
  simp at hdeg

/-- **Sum of the roots, field form.** `a_{n-1} / a_n = -∑ roots`. -/
theorem sum_of_roots_field (p : F[X]) (hcard : Multiset.card p.roots = p.natDegree)
    (hdeg : 1 ≤ p.natDegree) :
    p.coeff (p.natDegree - 1) / p.leadingCoeff = - p.roots.sum := by
  have hlc := leadingCoeff_ne_zero_of_deg p hdeg
  have hk : p.natDegree - 1 ≤ p.natDegree := Nat.sub_le _ _
  have h := vieta_coeff p hcard hk
  have hsub : p.natDegree - (p.natDegree - 1) = 1 := by omega
  rw [hsub, esymm_one_eq_sum] at h
  rw [div_eq_iff hlc, h]
  ring

/-- **Product of the roots, field form.** `a_0 / a_n = (-1)^n · ∏ roots`. -/
theorem prod_of_roots_field (p : F[X]) (hcard : Multiset.card p.roots = p.natDegree)
    (hdeg : 1 ≤ p.natDegree) :
    p.coeff 0 / p.leadingCoeff = (-1) ^ p.natDegree * p.roots.prod := by
  have hlc := leadingCoeff_ne_zero_of_deg p hdeg
  have h := (splits_iff_card_roots.mpr hcard).coeff_zero_eq_leadingCoeff_mul_prod_roots
  -- h : p.coeff 0 = (-1)^n * p.leadingCoeff * p.roots.prod
  rw [div_eq_iff hlc, h]
  ring

end Field

/-! ## Section V: Symmetric-function form for `∏ (X - rᵢ)`

The same content, phrased for a polynomial *presented* as a product of linear factors,
using the `Multiset` infrastructure directly (no `roots`/splits hypotheses needed). -/

/-- **Vieta in product form.** The `k`-th coefficient of `∏ (X - rᵢ)` is
`(-1)^(m-k) · e_{m-k}(rᵢ)` where `m` is the number of factors. -/
theorem prod_linear_coeff (s : Multiset R) {k : ℕ} (hk : k ≤ Multiset.card s) :
    (s.map fun r => X - C r).prod.coeff k =
      (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) :=
  Multiset.prod_X_sub_C_coeff s hk

/-- The next-to-leading coefficient of `∏ (X - rᵢ)` is `-(∑ rᵢ)`. -/
theorem prod_linear_sub_one (s : Multiset R) (hs : 1 ≤ Multiset.card s) :
    (s.map fun r => X - C r).prod.coeff (Multiset.card s - 1) = - s.sum := by
  have hk : Multiset.card s - 1 ≤ Multiset.card s := Nat.sub_le _ _
  have h := prod_linear_coeff s hk
  have hsub : Multiset.card s - (Multiset.card s - 1) = 1 := by omega
  rw [hsub, esymm_one_eq_sum] at h
  rw [h]; ring

/-! ## Section VI: Recovering the cubic (parent OQ-03-OQ-05)

The general degree-`n` machinery specializes, at cardinality 3, to the classical Vieta
relations for `(X - r₁)(X - r₂)(X - r₃)` proved in the parent entry. -/

/-- The `X²` coefficient of `(X - r₁)(X - r₂)(X - r₃)` is `-(r₁ + r₂ + r₃)`,
as the cardinality-3 instance of `prod_linear_sub_one`. -/
theorem cubic_coeff_two (r₁ r₂ r₃ : R) :
    (({r₁, r₂, r₃} : Multiset R).map fun r => X - C r).prod.coeff 2
      = -(r₁ + r₂ + r₃) := by
  have hcard : Multiset.card ({r₁, r₂, r₃} : Multiset R) = 3 := by simp
  have h := prod_linear_sub_one ({r₁, r₂, r₃} : Multiset R) (by rw [hcard]; norm_num)
  rw [hcard] at h
  rw [show (3 - 1 : ℕ) = 2 from rfl] at h
  rw [h]
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  ring

/-- The constant coefficient of `(X - r₁)(X - r₂)(X - r₃)` is `-(r₁ r₂ r₃)`.
Here we read it off directly via `coeff 0 = eval 0`, complementing `cubic_coeff_two`. -/
theorem cubic_coeff_zero (r₁ r₂ r₃ : R) :
    (({r₁, r₂, r₃} : Multiset R).map fun r => X - C r).prod.coeff 0
      = -(r₁ * r₂ * r₃) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

end VietaGeneral
