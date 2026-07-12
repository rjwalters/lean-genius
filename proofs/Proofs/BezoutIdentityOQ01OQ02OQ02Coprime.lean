/-
# Bézout / primitive vectors: the classical coprimality bridges

`BezoutIdentityOQ01OQ02OQ02` develops the `SLₙ(ℤ)`-transitivity theory of
*primitive* integer vectors through the dot-product definition

  `IsPrimitive v := ∃ w, w ⬝ᵥ v = 1`

and already records two structural reformulations: the ideal form
`isPrimitive_iff_span_eq_top` (`Ideal.span (range v) = ⊤`) and the
common-divisor form `isPrimitive_iff_forall_isUnit_of_dvd` (every common divisor
of the entries is a unit).

What is still missing is the bridge to the *literal* classical notions used by
the `n = 2` parent entry `BezoutIdentityOQ01OQ02`, which is phrased throughout in
terms of `Int.gcd` and `Int.gcdA/gcdB`.  This file supplies exactly that
translation, in two forms:

* `isPrimitive_iff_finset_gcd_eq_one` — for arbitrary `n`, primitivity is
  equivalent to the honest computed value `Finset.univ.gcd v = 1` of the entries'
  gcd (not merely "every common divisor is a unit").
* `isPrimitive_iff_isCoprime_fin_two` — in dimension `2`, primitivity of
  `v : Fin 2 → ℤ` is exactly Mathlib's ring-theoretic `IsCoprime (v 0) (v 1)`,
  and hence (`isPrimitive_iff_int_gcd_eq_one_fin_two`) exactly
  `Int.gcd (v 0) (v 1) = 1` — the precise hypothesis under which the parent's
  `bezoutMatrix` produces a genuine `SL₂(ℤ)` element.

All results are `0`-axiom / `0`-sorry, and reuse the existing
characterisations of the parent file rather than re-deriving the descent.

Research file — intentionally NOT registered in `Proofs.lean`.
-/
import Proofs.BezoutIdentityOQ01OQ02OQ02
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic

namespace BezoutPrimitive

open Matrix

variable {n : ℕ}

/-! ### The `Finset.gcd` bridge (all dimensions) -/

/-- **The literal gcd characterisation of primitivity.**  A vector `v : Fin n → ℤ`
is primitive iff the honest computed gcd of its entries equals `1`:

  `IsPrimitive v ↔ Finset.univ.gcd v = 1`.

This upgrades `isPrimitive_iff_forall_isUnit_of_dvd` (every common divisor is a
unit) to the concrete value of the gcd itself, using that `Finset.gcd` over `ℤ`
is normalised (non-negative).

Forward: primitivity makes every common divisor a unit; the gcd `Finset.univ.gcd v`
divides each entry (`Finset.gcd_dvd`), so it is a unit, and a *normalised* unit of
`ℤ` is `1`.  Reverse: any common divisor `d` of the entries divides the gcd
(`Finset.dvd_gcd`), hence divides `1`, so is a unit — primitivity then follows
from `isPrimitive_iff_forall_isUnit_of_dvd`. -/
theorem isPrimitive_iff_finset_gcd_eq_one (v : Fin n → ℤ) :
    IsPrimitive v ↔ (Finset.univ.gcd v) = 1 := by
  rw [isPrimitive_iff_forall_isUnit_of_dvd]
  constructor
  · intro h
    have hunit : IsUnit (Finset.univ.gcd v) :=
      h _ (fun i => Finset.gcd_dvd (Finset.mem_univ i))
    have hnorm : normalize (Finset.univ.gcd v) = Finset.univ.gcd v :=
      Finset.normalize_gcd
    rw [← hnorm, normalize_eq_one.mpr hunit]
  · intro h d hd
    have hdvd : d ∣ Finset.univ.gcd v :=
      Finset.dvd_gcd (fun i _ => hd i)
    rw [h] at hdvd
    exact isUnit_of_dvd_one hdvd

/-! ### The `IsCoprime` / `Int.gcd` bridge (dimension two) -/

/-- **Primitivity is coprimality in dimension two.**  For `v : Fin 2 → ℤ`,

  `IsPrimitive v ↔ IsCoprime (v 0) (v 1)`.

Both sides unfold to a Bézout identity `a·(v 0) + b·(v 1) = 1`: `IsPrimitive v`
provides a dual `w` with `w 0 · v 0 + w 1 · v 1 = 1` (`Fin.sum_univ_two` on the
dot product), which is exactly a coprimality witness `⟨w 0, w 1⟩`, and
conversely a coprimality witness `⟨a, b⟩` assembles into the dual `![a, b]`.
This identifies the file's `SLₙ(ℤ)`-invariant `IsPrimitive` with the classical
`IsCoprime` phrasing the parent `n = 2` entry is built on. -/
theorem isPrimitive_iff_isCoprime_fin_two (v : Fin 2 → ℤ) :
    IsPrimitive v ↔ IsCoprime (v 0) (v 1) := by
  constructor
  · rintro ⟨w, hw⟩
    have hwv : w 0 * v 0 + w 1 * v 1 = 1 := by
      simpa [dotProduct, Fin.sum_univ_two] using hw
    exact ⟨w 0, w 1, hwv⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨![a, b], ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [hab]

/-- **Primitivity is `Int.gcd = 1` in dimension two.**  Composing
`isPrimitive_iff_isCoprime_fin_two` with `Int.isCoprime_iff_gcd_eq_one` gives the
concrete arithmetic form matching the parent `BezoutIdentityOQ01OQ02`:

  `IsPrimitive v ↔ Int.gcd (v 0) (v 1) = 1`.

This is precisely the condition under which the parent's `bezoutMatrix (v 0) (v 1)`
is a genuine `SL₂(ℤ)` element carrying `v` to `e₁`. -/
theorem isPrimitive_iff_int_gcd_eq_one_fin_two (v : Fin 2 → ℤ) :
    IsPrimitive v ↔ Int.gcd (v 0) (v 1) = 1 := by
  rw [isPrimitive_iff_isCoprime_fin_two, Int.isCoprime_iff_gcd_eq_one]

/-- **Consistency of the two bridges.**  For `v : Fin 2 → ℤ` the general
`Finset.univ.gcd` value and the classical `Int.gcd (v 0) (v 1)` agree on the
primitive locus: both equal `1` exactly when `v` is primitive.  Recorded as the
`Finset.gcd = 1 ↔ Int.gcd = 1` corollary tying the two characterisations
together in the base dimension. -/
theorem finset_gcd_eq_one_iff_int_gcd_eq_one_fin_two (v : Fin 2 → ℤ) :
    (Finset.univ.gcd v) = 1 ↔ Int.gcd (v 0) (v 1) = 1 := by
  rw [← isPrimitive_iff_finset_gcd_eq_one, isPrimitive_iff_int_gcd_eq_one_fin_two]

end BezoutPrimitive
