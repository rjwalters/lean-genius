/-
# Vieta's Formulas in General Degree: Sum and Product of Roots of a Monic Split Polynomial

For a *monic* polynomial `p` of degree `n` over an integral domain that *splits*
(factors into linear factors, equivalently has `n` roots counted with
multiplicity), Vieta's formulas express every coefficient of `p` as an
elementary symmetric function of the roots:

  `p.coeff (n - j) = (-1)^j * (elementary symmetric function of degree j in the roots)`.

The two most famous instances are the boundary cases:

* `j = 1` -- the **sum of the roots** equals `-p.coeff (n-1)`;
* `j = n` -- the **product of the roots** equals `(-1)^n * p.coeff 0`.

The sibling files `VietasFormulasOQ02`/`OQ03`/`OQ03OQ01` develop Newton's
identities (power sums vs. elementary symmetric functions), and `OQ04`/`OQ03OQ05`
treat the discriminant and quartic resolvent. This file is the complementary
*general-degree* statement: the full elementary-symmetric coefficient
dictionary for an arbitrary monic split polynomial, with the sum and product of
roots unified as its two boundary cases and cross-checked against Mathlib's
`Splits.coeff_zero_eq_prod_roots_of_monic` and
`Splits.nextCoeff_eq_neg_sum_roots_of_monic`.

## Main results

* `Multiset.esymm_one` / `Multiset.esymm_self` -- boundary values of the
  elementary symmetric functions of a multiset (`esymm 1 = sum`,
  `esymm (card s) = prod`).
* `Vieta.coeff_eq_esymm_of_monic` -- the general coefficient dictionary:
  `p.coeff (n - j) = (-1)^j * p.roots.esymm j` for `j ≤ n`.
* `Vieta.coeff_natDegree_sub_one` -- sum of roots: `p.coeff (n-1) = -p.roots.sum`.
* `Vieta.coeff_zero_eq_prod` -- product of roots: `p.coeff 0 = (-1)^n * p.roots.prod`.
* `Vieta.eq_prod_roots` -- the reconstruction `p = ∏ (X - rᵢ)`.
* `Vieta.build_coeff` -- the forward (constructive) coefficient dictionary for a
  monic polynomial built from a prescribed multiset of roots.

## References

- Mathlib.RingTheory.Polynomial.Vieta (`Polynomial.coeff_eq_esymm_roots_of_card`)
- Mathlib.Algebra.Polynomial.Factors (`Polynomial.Splits`, split root formulas)
-/

import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Factors

open Polynomial Multiset

namespace Multiset

variable {R : Type*} [CommRing R]

/-- The degree-`1` elementary symmetric function of a multiset is its sum. -/
theorem esymm_one (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [esymm, powersetCard_one, Multiset.map_map, Function.comp]

/-- The top elementary symmetric function of a multiset (degree equal to its
cardinality) is its product. -/
theorem esymm_self (s : Multiset R) : s.esymm (Multiset.card s) = s.prod := by
  have hmem : s ∈ Multiset.powersetCard (Multiset.card s) s :=
    Multiset.mem_powersetCard.mpr ⟨le_refl s, rfl⟩
  have hcard : Multiset.card (Multiset.powersetCard (Multiset.card s) s) = 1 := by
    rw [Multiset.card_powersetCard, Nat.choose_self]
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  rw [ha, Multiset.mem_singleton] at hmem
  rw [esymm, ha, Multiset.map_singleton, Multiset.sum_singleton, ← hmem]

end Multiset

namespace Vieta

variable {R : Type*} [CommRing R] [IsDomain R] {p : R[X]}

/-- **Vieta's formula, general degree.** For a monic polynomial that splits over
an integral domain, the coefficient in position `n - j` (where `n = natDegree p`)
is `(-1)^j` times the degree-`j` elementary symmetric function of the roots. -/
theorem coeff_eq_esymm_of_monic (hp : p.Monic) (hsplit : p.Splits) {j : ℕ}
    (hj : j ≤ p.natDegree) :
    p.coeff (p.natDegree - j) = (-1) ^ j * p.roots.esymm j := by
  have hcard : Multiset.card p.roots = p.natDegree := splits_iff_card_roots.mp hsplit
  have hk : p.natDegree - j ≤ p.natDegree := Nat.sub_le _ _
  have h := Polynomial.coeff_eq_esymm_roots_of_card hcard (k := p.natDegree - j) hk
  rwa [hp.leadingCoeff, one_mul, Nat.sub_sub_self hj] at h

/-- **Sum of the roots.** For a monic split polynomial of positive degree, the
sub-leading coefficient equals the negative of the sum of the roots. -/
theorem coeff_natDegree_sub_one (hp : p.Monic) (hsplit : p.Splits)
    (hn : 1 ≤ p.natDegree) :
    p.coeff (p.natDegree - 1) = - p.roots.sum := by
  have h := coeff_eq_esymm_of_monic hp hsplit hn
  rwa [pow_one, Multiset.esymm_one, neg_one_mul] at h

/-- **Product of the roots.** For a monic split polynomial the constant
coefficient equals `(-1)^n` times the product of the roots (`n = natDegree p`).
Derived here from the general dictionary at the top elementary symmetric
function; it agrees with `Splits.coeff_zero_eq_prod_roots_of_monic`. -/
theorem coeff_zero_eq_prod (hp : p.Monic) (hsplit : p.Splits) :
    p.coeff 0 = (-1) ^ p.natDegree * p.roots.prod := by
  have hcard : Multiset.card p.roots = p.natDegree := splits_iff_card_roots.mp hsplit
  have h := coeff_eq_esymm_of_monic hp hsplit (le_refl p.natDegree)
  rw [Nat.sub_self] at h
  have hesymm : p.roots.esymm p.natDegree = p.roots.prod := by
    rw [← hcard, Multiset.esymm_self]
  rwa [hesymm] at h

/-- **Root factorization.** A monic split polynomial is the product of the
linear factors `X - rᵢ` over its roots. This is the geometric content behind
Vieta's formulas: expanding this product recovers the coefficient dictionary. -/
theorem eq_prod_roots (hp : p.Monic) (hsplit : p.Splits) :
    p = (p.roots.map fun r => X - C r).prod :=
  hsplit.eq_prod_roots_of_monic hp

/-- The number of roots (with multiplicity) of a monic split polynomial equals
its degree. -/
theorem card_roots_eq_natDegree (hsplit : p.Splits) :
    Multiset.card p.roots = p.natDegree :=
  splits_iff_card_roots.mp hsplit

/-- **Forward (constructive) Vieta.** For any multiset `s` of prescribed roots,
the monic polynomial `∏ (X - rᵢ)` has coefficients given by the elementary
symmetric functions of `s`: the coefficient in position `k` is
`(-1)^(m - k)` times `esymm (m - k)`, where `m = card s`. This is the converse
direction to `coeff_eq_esymm_of_monic`. -/
theorem build_coeff (s : Multiset R) {k : ℕ} (hk : k ≤ Multiset.card s) :
    (s.map fun r => X - C r).prod.coeff k =
      (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k) :=
  Multiset.prod_X_sub_C_coeff s hk

end Vieta
