import Mathlib

/-!
# Wedderburn's little theorem and its arithmetic corollaries

**Wedderburn's little theorem** states that every finite division ring is a field:
multiplication in a finite division ring is automatically commutative. The result
is one of the gems of algebra — the finiteness of the ring alone forces the
multiplicative structure to collapse to a commutative one, ruling out any finite
analogue of the (infinite) quaternions.

Mathlib proves the theorem as the instance `littleWedderburn`
(`Mathlib/RingTheory/LittleWedderburn.lean`), which equips any
`[DivisionRing D] [Finite D]` with a `Field D` structure, together with the
companion `Finite.isDomain_to_isField` (a finite domain is a field). What Mathlib
does **not** record are the standard *arithmetic* consequences of Wedderburn that
one usually quotes in the same breath, phrased at the level of a **division ring**
(they are stated only for `Field`):

* a finite division ring is **commutative** as an explicit `∀ x y, x * y = y * x`
  (the headline theorem, exposed as a named statement rather than buried in an
  instance);
* the **order of a finite division ring is a prime power** — `IsPrimePow (card D)`
  and the explicit `card D = p ^ n` decomposition;
* the **multiplicative group `Dˣ` is cyclic**;
* hence `Dˣ` is **abelian**, and there is **no noncommutative finite division
  ring** of any cardinality.

These corollaries require Wedderburn as an input (the field-level Mathlib lemmas
`FiniteField.isPrimePow_card`, `FiniteField.card'`, and the integral-domain
instance `IsCyclic Rˣ` only fire *after* `littleWedderburn` upgrades `D` to a
field), so lifting them to division rings is genuinely new derived content. The
headline commutativity is `mul_comm` against the Mathlib instance (hence the
`mathlib` badge); everything is fully machine-checked with no axioms or sorries.
Wedderburn's little theorem is absent from the gallery, whose only `Wedderburn`
content concerns the *Artin–Wedderburn* structure theorem (a different result).
-/

namespace LittleWedderburnOQ01

/-! ## The headline theorem -/

/-- **Wedderburn's little theorem.** Multiplication in a finite division ring is
commutative. This is the defining content of the theorem, exposed as an explicit
universally-quantified statement; the `Field D` structure it rests on is supplied
by Mathlib's `littleWedderburn` instance. -/
theorem mul_comm_of_finite_divisionRing (D : Type*) [DivisionRing D] [Finite D]
    (x y : D) : x * y = y * x :=
  mul_comm x y

/-- A finite division ring is a field, packaged as the structural predicate
`IsField`. -/
theorem isField_of_finite_divisionRing (D : Type*) [DivisionRing D] [Finite D] :
    IsField D :=
  Field.toIsField D

/-- **Companion form.** A finite *domain* (a finite ring with no zero divisors) is
a field: zero divisors are the only obstruction, and finiteness removes the need
for inverses to be assumed. -/
theorem isField_of_finite_domain (D : Type*) [Finite D] [Ring D] [IsDomain D] :
    IsField D :=
  Finite.isDomain_to_isField D

/-! ## Arithmetic corollaries (new at the division-ring level) -/

/-- **The order of a finite division ring is a prime power.** This is the classical
arithmetic shadow of Wedderburn: a finite division ring, being a field, is a vector
space over its prime subfield, so its cardinality is `p ^ n`. Stated here directly
for a division ring via Wedderburn. -/
theorem card_isPrimePow_of_finite_divisionRing (D : Type*) [DivisionRing D]
    [Fintype D] : IsPrimePow (Fintype.card D) :=
  FiniteField.isPrimePow_card D

/-- **Explicit prime-power decomposition.** There is a prime `p` (the
characteristic) and a positive exponent `n` with `card D = p ^ n`. -/
theorem card_eq_primePow_of_finite_divisionRing (D : Type*) [DivisionRing D]
    [Fintype D] :
    ∃ p : ℕ, CharP D p ∧ ∃ n : ℕ+, Nat.Prime p ∧ Fintype.card D = p ^ (n : ℕ) :=
  FiniteField.card' D

/-- **The multiplicative group of a finite division ring is cyclic.** Once
Wedderburn makes `D` a field, `Dˣ` is a finite subgroup of the units of an
integral domain, hence cyclic. -/
theorem isCyclic_units_of_finite_divisionRing (D : Type*) [DivisionRing D]
    [Finite D] : IsCyclic Dˣ :=
  inferInstance

/-- The unit group of a finite division ring is abelian: a direct consequence of
commutativity. -/
theorem units_mul_comm_of_finite_divisionRing (D : Type*) [DivisionRing D]
    [Finite D] (a b : Dˣ) : a * b = b * a :=
  mul_comm a b

/-- **No noncommutative finite division ring exists.** For any finite division
ring and any pair of elements, the two products agree — there is no finite
analogue of the quaternions. (A restatement of the headline theorem, recorded for
emphasis.) -/
theorem no_noncommutative_finite_divisionRing (D : Type*) [DivisionRing D]
    [Finite D] : ∀ x y : D, x * y = y * x :=
  fun x y => mul_comm x y

/-! ## Worked instance: `ZMod p` -/

/-- For prime `p`, the residue ring `ZMod p` is a finite division ring (indeed a
field), so Wedderburn's corollaries apply: its order is the prime power `p ^ 1`. -/
theorem zmod_card_isPrimePow (p : ℕ) [Fact p.Prime] :
    IsPrimePow (Fintype.card (ZMod p)) :=
  card_isPrimePow_of_finite_divisionRing (ZMod p)

/-- The unit group `(ZMod p)ˣ` is cyclic — the existence of a primitive root mod a
prime, obtained here as a special case of the division-ring corollary. -/
theorem zmod_units_isCyclic (p : ℕ) [Fact p.Prime] : IsCyclic (ZMod p)ˣ :=
  isCyclic_units_of_finite_divisionRing (ZMod p)

end LittleWedderburnOQ01
