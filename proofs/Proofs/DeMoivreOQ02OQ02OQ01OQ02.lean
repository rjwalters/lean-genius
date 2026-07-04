import Mathlib
import Proofs.ChebyshevPolynomialsOQ01OQ01

/-
# De Moivre OQ-02 OQ-02 OQ-01 OQ-02: the antisymmetric mixed Chebyshev product

## Open Question

The sibling file `DeMoivreOQ02OQ02` records the *symmetric* mixed product-to-sum
identity
  2·T_m·U_n = U_{m+n} + U_{n−m},
and the parent `DeMoivreOQ02OQ02OQ01` linearizes the pure second-kind product
`U_m·U_n` as a `min(m,n)+1`-term sum of `U`'s.  Both are **symmetric** in their
arguments.  What about the *antisymmetric* mixed combination `U_m·T_n − U_n·T_m`?
Does it also collapse to a single second-kind polynomial, and can this be done
without dividing by `2` (i.e. over an arbitrary commutative ring, including
characteristic `2`)?

## Answer: YES — a division-free single-term closed form

For every `m, n : ℤ`, in `R[X]` over any `CommRing R`,

  **U_m · T_n − U_n · T_m = X · U_{m−n−1}.**            (`U_mul_T_antisymm`)

This is the polynomial shadow of the trigonometric antisymmetry
  U_m(cosθ)·T_n(cosθ) − U_n(cosθ)·T_m(cosθ)
      = [sin((m+1)θ)cos(nθ) − sin((n+1)θ)cos(mθ)]/sinθ
      = cosθ · sin((m−n)θ)/sinθ = cosθ · U_{m−n−1}(cosθ).

Unlike the sibling's `2·T·U` product-to-sum, the antisymmetric form carries **no
factor of `2`** — it is a genuine identity of `ℤ`-coefficient polynomials and holds
verbatim in every characteristic.

## Route (fully non-inductive)

Everything reduces, by `linear_combination`, to already-proved building blocks:

1. `T_eq_U_sub_X_U`  : `T_k = U_k − X·U_{k−1}`  — a rearrangement of Mathlib's mixed
   recurrence `U_eq_X_mul_U_add_T`.  (No `2`.)
2. `U_mul_T_sub`     : `U_{m−1}·T_n − T_m·U_{n−1} = U_{m−n−1}` — the mixed
   "subtraction" formula, obtained from the second-kind **addition** formula
   `ChebyshevPolynomialsOQ01OQ01.U_add` evaluated at `(m−1, −n)` together with the
   reflections `T_{−n} = T_n` and `U_{−n−1} = −U_{n−1}`.
3. `U_wronskian`     : `U_{m−1}·U_n − U_m·U_{n−1} = U_{m−n−1}` — the pure
   second-kind **d'Ocagne / Wronskian** identity, from (2) by eliminating the two
   `T`'s via (1).
4. `U_mul_T_antisymm`: the headline, from (1) and (3).

None of these four identities is in Mathlib, and none is the sibling's symmetric
`2·T·U`; the antisymmetric closed form and the second-kind Wronskian are new.
-/

open Polynomial Polynomial.Chebyshev

namespace DeMoivreOQ02OQ02OQ01OQ02

variable {R : Type*} [CommRing R]

/-- **First-kind in terms of second-kind** (division-free):
`T_k = U_k − X·U_{k−1}`.  The polynomial form of
`cos(kθ) = sin((k+1)θ)/sinθ − cosθ·sin(kθ)/sinθ`.  A rearrangement of Mathlib's
mixed recurrence `U_eq_X_mul_U_add_T : U_{k+1} = X·U_k + T_{k+1}`. -/
lemma T_eq_U_sub_X_U (k : ℤ) : T R k = U R k - X * U R (k - 1) := by
  have h := U_eq_X_mul_U_add_T R (k - 1)
  rw [show k - 1 + 1 = k from by ring] at h
  linear_combination -h

/-- **Mixed subtraction formula**:
`U_{m−1}·T_n − T_m·U_{n−1} = U_{m−n−1}`.  The single-term "linearization into a
second-kind polynomial" of the antisymmetric mixed product.  It is the polynomial
form of `sin(mθ)cos(nθ) − cos(mθ)sin(nθ) = sin((m−n)θ)`, obtained from the
second-kind addition formula at `(m−1, −n)`. -/
lemma U_mul_T_sub (m n : ℤ) :
    U R (m - 1) * T R n - T R m * U R (n - 1) = U R (m - n - 1) := by
  have h := ChebyshevPolynomialsOQ01OQ01.U_add R (m - 1) (-n)
  rw [show m - 1 + -n = m - n - 1 from by ring,
      show m - 1 + 1 = m from by ring,
      T_neg R n, U_neg_sub_one R n] at h
  linear_combination -h

/-- **Second-kind Wronskian / d'Ocagne identity**:
`U_{m−1}·U_n − U_m·U_{n−1} = U_{m−n−1}`.  The Casoratian of the two shifted
second-kind sequences collapses to a single `U`, depending only on the index gap
`m − n`.  Derived from `U_mul_T_sub` by eliminating both first-kind factors via
`T_eq_U_sub_X_U`. -/
lemma U_wronskian (m n : ℤ) :
    U R (m - 1) * U R n - U R m * U R (n - 1) = U R (m - n - 1) := by
  have h := U_mul_T_sub (R := R) m n
  have hTn := T_eq_U_sub_X_U (R := R) n
  have hTm := T_eq_U_sub_X_U (R := R) m
  linear_combination h - U R (m - 1) * hTn + U R (n - 1) * hTm

/-- **Antisymmetric mixed product** (headline):
`U_m·T_n − U_n·T_m = X·U_{m−n−1}`, division-free over any commutative ring.
The polynomial shadow of
`sin((m+1)θ)cos(nθ) − sin((n+1)θ)cos(mθ) = cosθ·sin((m−n)θ)`. -/
theorem U_mul_T_antisymm (m n : ℤ) :
    U R m * T R n - U R n * T R m = X * U R (m - n - 1) := by
  have hw := U_wronskian (R := R) m n
  have hTn := T_eq_U_sub_X_U (R := R) n
  have hTm := T_eq_U_sub_X_U (R := R) m
  linear_combination U R m * hTn - U R n * hTm + X * hw

/-! ### Concrete instances (numeric cross-checks over ℤ) -/

/-- `U₂·T₁ − U₁·T₂ = X·U₀`  (both sides equal `X`, since `U₀ = 1`). -/
example : U ℤ 2 * T ℤ 1 - U ℤ 1 * T ℤ 2 = X * U ℤ (2 - 1 - 1) :=
  U_mul_T_antisymm 2 1

/-- `U₁·U₂ − U₂·U₁ = U₀`: the Wronskian at `m = 2, n = 2` reads
`U_{2−1}·U_2 − U_2·U_{2−1} = U_{2−2−1}`, i.e. `0 = U_{−1} = 0`. -/
example : U ℤ (2 - 1) * U ℤ 2 - U ℤ 2 * U ℤ (2 - 1) = U ℤ (2 - 2 - 1) :=
  U_wronskian 2 2

end DeMoivreOQ02OQ02OQ01OQ02
