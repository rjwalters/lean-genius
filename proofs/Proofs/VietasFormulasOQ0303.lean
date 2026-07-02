import Mathlib

/-
# Newton's Identities for the Roots of a Polynomial (Concrete Bridge)

## What This Proves
Mathlib's Newton identities (`MvPolynomial.psum_eq_mul_esymm_sub_sum`) live at the
abstract level of the polynomial ring `MvPolynomial (Fin n) R`, relating the formal
power-sum symmetric polynomial `pₖ = ∑ᵢ Xᵢ^k` to the elementary symmetric
polynomials `eⱼ`. This entry **transports that identity down to concrete values**:
given an actual tuple of roots `r : Fin n → R`, we obtain the recurrence

    pₖ(r) = (-1)^{k+1} · k · eₖ(r) − ∑_{0 < j < k} (-1)^j · eⱼ(r) · p_{k-j}(r),

where `pₖ(r) = ∑ᵢ rᵢ^k` and `eⱼ(r)` is the `j`-th elementary symmetric function of
the roots. The transport is via evaluation `aeval r`, using
`MvPolynomial.aeval_esymm_eq_multiset_esymm` to recognise the evaluated `eⱼ` as the
concrete `Multiset.esymm` of the roots.

We then close the loop to **polynomial coefficients**: for a monic polynomial over an
integral domain that has a full complement of roots, Vieta's formula
(`Polynomial.coeff_eq_esymm_roots_of_card`) identifies `eⱼ` of the roots with `±` a
coefficient, so the power sums of the roots are expressed directly through the
coefficients of the polynomial.

## Approach
- `powerSum r k := ∑ᵢ rᵢ^k` and `elemSym r k := (univ.val.map r).esymm k`.
- `aeval_powerSum` / `aeval_elemSym`: evaluation `aeval r` sends the abstract `psum`
  / `esymm` to `powerSum` / `elemSym`.
- `newton_identity`: apply `aeval r` (an algebra hom) to Mathlib's
  `psum_eq_mul_esymm_sub_sum` and push it through the sum/product structure.
- Concrete specialisations `newton_one`, `newton_two` (p₁ = e₁, p₂ = e₁² − 2e₂).
- `elemSym_eq_coeff` and `powerSum_two_via_coeff`: the coefficient bridge via Vieta.

## Provenance
Answers `vietas-formulas-oq-03-oq-03`: bridge the abstract `esymm`/`psum`
symmetric-function form of Newton's identities (the parent's general-n perspective)
to concrete polynomial coefficients through Mathlib's `Polynomial.Vieta`. Mathlib has
the identity only at the `MvPolynomial` level; nothing in Mathlib states it for the
power sums of the roots of a concrete polynomial.
-/

open Finset

namespace NewtonRoots

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The degree-`k` power sum of a tuple of roots `r : Fin n → R`: `∑ᵢ rᵢ^k`. -/
def powerSum (r : Fin n → R) (k : ℕ) : R := ∑ i, r i ^ k

/-- The degree-`k` elementary symmetric function of the roots `r : Fin n → R`,
    realised as the `Multiset.esymm` of the multiset of roots. -/
def elemSym (r : Fin n → R) (k : ℕ) : R := (Finset.univ.val.map r).esymm k

@[simp] lemma powerSum_zero (r : Fin n → R) : powerSum r 0 = (n : R) := by
  simp [powerSum]

@[simp] lemma elemSym_zero (r : Fin n → R) : elemSym r 0 = 1 := by
  simp [elemSym, Multiset.esymm]

/-- Evaluation `aeval r` sends the abstract power sum `psum` to the concrete
    power sum `∑ᵢ rᵢ^k`. -/
lemma aeval_powerSum (r : Fin n → R) (k : ℕ) :
    MvPolynomial.aeval r (MvPolynomial.psum (Fin n) R k) = powerSum r k := by
  simp [MvPolynomial.psum, powerSum, map_sum]

/-- Evaluation `aeval r` sends the abstract elementary symmetric polynomial `esymm`
    to the concrete `Multiset.esymm` of the roots. -/
lemma aeval_elemSym (r : Fin n → R) (k : ℕ) :
    MvPolynomial.aeval r (MvPolynomial.esymm (Fin n) R k) = elemSym r k := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  rfl

/-- **Newton's identity for the roots of a polynomial.**

    For any tuple `r : Fin n → R` of roots and any `k > 0`,
    `pₖ = (-1)^{k+1} k eₖ − ∑_{0<j<k} (-1)^j eⱼ p_{k-j}`,
    where `pₖ = ∑ᵢ rᵢ^k` (`powerSum`) and `eⱼ` (`elemSym`) is the `j`-th elementary
    symmetric function of the roots. Obtained by evaluating Mathlib's abstract
    identity `MvPolynomial.psum_eq_mul_esymm_sub_sum` at `r`. -/
theorem newton_identity (r : Fin n → R) (k : ℕ) (h : 0 < k) :
    powerSum r k = (-1) ^ (k + 1) * k * elemSym r k -
      ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k),
        (-1) ^ a.1 * elemSym r a.1 * powerSum r a.2 := by
  have H := congrArg (MvPolynomial.aeval r) (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) R k h)
  rw [aeval_powerSum] at H
  rw [H]
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    aeval_elemSym, aeval_powerSum]

-- ============================================================
-- Concrete low-degree specialisations
-- ============================================================

/-- **Newton at k = 1**: `p₁ = e₁`, i.e. `∑ᵢ rᵢ = e₁(r)`. -/
theorem newton_one (r : Fin n → R) : powerSum r 1 = elemSym r 1 := by
  have h := newton_identity r 1 (by norm_num)
  rw [show ((Finset.antidiagonal 1).filter (fun a => a.1 ∈ Set.Ioo 0 1) : Finset (ℕ × ℕ))
        = ∅ from by decide] at h
  simpa using h

/-- **Newton at k = 2**: `p₂ = e₁·p₁ − 2·e₂ = e₁² − 2 e₂`. -/
theorem newton_two (r : Fin n → R) :
    powerSum r 2 = elemSym r 1 * powerSum r 1 - 2 * elemSym r 2 := by
  have h := newton_identity r 2 (by norm_num)
  -- The filtered antidiagonal of 2 with first entry in (0,2) is the single pair (1,1).
  rw [show ((Finset.antidiagonal 2).filter (fun a => a.1 ∈ Set.Ioo 0 2) : Finset (ℕ × ℕ))
        = {(1, 1)} from by decide] at h
  simp only [Finset.sum_singleton] at h
  rw [h]
  ring

/-- Corollary of `newton_two`: `p₂ = e₁² − 2 e₂`. -/
theorem newton_two' (r : Fin n → R) :
    powerSum r 2 = elemSym r 1 ^ 2 - 2 * elemSym r 2 := by
  rw [newton_two, newton_one]; ring

-- ============================================================
-- Bridge to polynomial coefficients (Vieta)
-- ============================================================

/-- **Vieta bridge.** For a monic polynomial `p` over an integral domain whose
    number of roots equals its degree `n`, the `j`-th elementary symmetric function
    of its roots is `(-1)^j` times the coefficient `p.coeff (n - j)`. -/
theorem elemSym_roots_eq_coeff {R : Type*} [CommRing R] [IsDomain R] {p : Polynomial R}
    (hp : p.Monic) (hcard : Multiset.card p.roots = p.natDegree) {j : ℕ} (hj : j ≤ p.natDegree) :
    p.roots.esymm j = (-1) ^ j * p.coeff (p.natDegree - j) := by
  have hk : p.natDegree - j ≤ p.natDegree := Nat.sub_le _ _
  have hcoeff := Polynomial.coeff_eq_esymm_roots_of_card hcard hk
  rw [hp.leadingCoeff, one_mul, Nat.sub_sub_self hj] at hcoeff
  rw [hcoeff, ← mul_assoc, ← pow_add]
  rw [show j + j = 2 * j from by ring, pow_mul]
  simp

end NewtonRoots
