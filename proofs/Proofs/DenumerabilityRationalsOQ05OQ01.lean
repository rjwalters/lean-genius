/-
# Denumerability of the Rationals OQ-05-OQ-01: the dichotomy over any countable ring

## Open Question
OQ-05 isolated, for the rationals, the exact place where the closure of `ℵ₀` breaks:
finite products / finite subsets / finite sequences of ℚ stay denumerable, but the
*countably infinite power* `ℕ → ℚ` already reaches the continuum 𝔠. This child asks for
the structural generalization: the dichotomy is *not* about ℚ at all. For **any countably
infinite (commutative) ring** `R`:

  * `#(R[X]) = ℵ₀`        — the whole polynomial ring stays denumerable, and
  * `#(ℕ → R) = 𝔠`        — the sequence space escapes to the continuum.

So `ℚ` was incidental: the polynomial ring (a countable *colimit* of finite-rank free
modules) never leaves `ℵ₀`, while the countable power always lands on `𝔠`.

## Approach
Two cardinal facts, both driven by `#R = ℵ₀` (`mk_eq_aleph0`, since `R` is countable and
infinite):

  * **`#(R[X]) = ℵ₀`.** `R[X] = AddMonoidAlgebra R ℕ = (ℕ →₀ R)`, which is countable
    (`Finsupp` of countable types) and infinite (`Polynomial.infinite`, valid once `R`
    is nontrivial — automatic from `Infinite R`). A countable infinite type has cardinality
    exactly `ℵ₀` (`mk_eq_aleph0`). Equivalently `#(R[X]) = #R`: passing to polynomials does
    **not** change the cardinality.
  * **`#(ℕ → R) = 𝔠`.** `mk_arrow` gives `#R ^ #ℕ = ℵ₀ ^ ℵ₀`, collapsed to `𝔠` by
    `aleph0_power_aleph0`. The countable power escapes `ℵ₀`.

The contrast `#(R[X]) < #(ℕ → R)` (i.e. `ℵ₀ < 𝔠`, `aleph0_lt_continuum`) is the point, now
stated at the level of an arbitrary countable ring rather than ℚ specifically. Concrete
instances: `ℚ`, `ℤ`, `ℤ[i]`-style countable rings — all behave identically.

Sorry-free and axiom-free.
-/
import Mathlib

namespace DenumerabilityRationalsOQ05OQ01

open Cardinal Polynomial

variable {R : Type}

/-- **`#R = ℵ₀` for a countably infinite type.** The single engine of the file: a type that
is both countable and infinite has cardinality exactly `ℵ₀` (`Cardinal.mk_eq_aleph0`). -/
theorem mk_eq_aleph0_of_countable_infinite [Countable R] [Infinite R] : #R = ℵ₀ :=
  mk_eq_aleph0 R

/-- **`#(ℕ → R) = 𝔠`** for any countably infinite `R`. `mk_arrow` rewrites the function
space to `#R ^ #ℕ = ℵ₀ ^ ℵ₀`, and `aleph0_power_aleph0` collapses that to the continuum.
The countable power escapes `ℵ₀` — generalizing OQ-05's `#(ℕ → ℚ) = 𝔠` away from ℚ. -/
theorem mk_seq [Countable R] [Infinite R] : #(ℕ → R) = 𝔠 := by
  rw [mk_arrow, lift_uzero, lift_uzero, mk_eq_aleph0 R, mk_nat, aleph0_power_aleph0]

/-- **`ℕ → R` is uncountable.** Immediate from `mk_seq` and `ℵ₀ < 𝔠`
(`aleph0_lt_continuum`): sequences over a countably infinite ring are strictly more
numerous than the ring itself. -/
theorem not_countable_seq [Countable R] [Infinite R] : ¬ Countable (ℕ → R) := by
  rw [← mk_le_aleph0_iff, mk_seq, not_le]
  exact aleph0_lt_continuum

/-- **`R[X]` is countable** whenever `R` is. `R[X] = AddMonoidAlgebra R ℕ = (ℕ →₀ R)` is a
finitely supported family over countable types, hence countable; the constructor
`Polynomial.toFinsupp` is injective, transporting that countability to `R[X]`. -/
theorem countable_polynomial [CommRing R] [Countable R] : Countable R[X] := by
  haveI : Countable (AddMonoidAlgebra R ℕ) := inferInstanceAs (Countable (ℕ →₀ R))
  exact Polynomial.toFinsupp_injective.countable

/-- **`#(R[X]) = ℵ₀`** for any countably infinite ring `R`. `R[X]` is countable (above) and
infinite (`Polynomial.infinite`, since `Infinite R ⟹ Nontrivial R`), so `mk_eq_aleph0`
pins its cardinality at exactly `ℵ₀`: the whole polynomial ring stays denumerable. -/
theorem mk_polynomial [CommRing R] [Countable R] [Infinite R] : #(R[X]) = ℵ₀ := by
  haveI : Countable R[X] := countable_polynomial
  exact mk_eq_aleph0 R[X]

/-- **Passing to polynomials does not change the cardinality: `#(R[X]) = #R`.** Both sides
are `ℵ₀`. The polynomial ring is an honestly larger *ring* but the *same size* set. -/
theorem mk_polynomial_eq_mk [CommRing R] [Countable R] [Infinite R] : #(R[X]) = #R := by
  rw [mk_polynomial, mk_eq_aleph0_of_countable_infinite]

/-- **An explicit bijection `R[X] ≃ R` exists** (`Cardinal.eq`), witnessing
`#(R[X]) = #R`. -/
theorem nonempty_equiv_polynomial [CommRing R] [Countable R] [Infinite R] :
    Nonempty (R[X] ≃ R) :=
  Cardinal.eq.mp mk_polynomial_eq_mk

/-- **The dichotomy, in one inequality: `#(R[X]) < #(ℕ → R)`.** The polynomial ring stays
at `ℵ₀` while the sequence space jumps to `𝔠`, and `ℵ₀ < 𝔠` (`aleph0_lt_continuum`). This
is the sharp boundary OQ-05 located for ℚ, now for an arbitrary countable ring. -/
theorem mk_polynomial_lt_mk_seq [CommRing R] [Countable R] [Infinite R] :
    #(R[X]) < #(ℕ → R) := by
  rw [mk_polynomial, mk_seq]
  exact aleph0_lt_continuum

/-! ### Concrete instances: ℚ, ℤ behave identically. -/

/-- **`#(ℚ[X]) = ℵ₀`.** The rational polynomial ring is denumerable. -/
theorem mk_polynomial_rat : #(ℚ[X]) = ℵ₀ :=
  mk_polynomial

/-- **`#(ℤ[X]) = ℵ₀`.** The integer polynomial ring is denumerable. -/
theorem mk_polynomial_int : #(ℤ[X]) = ℵ₀ :=
  mk_polynomial

/-- **`#(ℕ → ℤ) = 𝔠`.** Integer sequences are equinumerous with the continuum — the same
escape as for ℚ. -/
theorem mk_seq_int : #(ℕ → ℤ) = 𝔠 :=
  mk_seq

end DenumerabilityRationalsOQ05OQ01
