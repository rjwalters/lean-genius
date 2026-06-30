import Mathlib

/-
# The class-equation core of Wedderburn: the center and the dimension identity

The parent entry (`LittleWedderburnOQ01`) records the arithmetic shadow of
Wedderburn's little theorem — the order of a finite division ring is a prime
power — by upgrading the ring to a field and then quoting the field-level
`FiniteField.isPrimePow_card`. The sibling entry (`LittleWedderburnOQ01OQ01`)
develops the *uniqueness* companion (exactly one finite field of each prime-power
order).

This entry develops the **other** structural companion the parent left open: the
center-and-dimension refinement that sits at the heart of Wedderburn's *own*
proof. For a finite division ring `D` one writes the multiplicative class
equation against the **center** `Z = Z(D)`; the structural inputs that make that
class equation arithmetic are exactly:

* `Z(D)` is a **field** (a commutative division ring), and `D` is a vector space
  over it;
* therefore `|D| = |Z(D)| ^ k` where `k = dim_{Z(D)} D` (the **dimension
  identity**, `Module.card_eq_pow_finrank`);
* `Z(D)` is itself a finite field, so `|Z(D)| = p ^ m` is a prime power;
* combining the two, `|D| = p ^ (m·k)` is a prime power — the prime-power-order
  corollary recovered through the *center route* rather than by collapsing to a
  field first.

The arithmetic content lies in `Module.card_eq_pow_finrank` (which realises the
class-equation bookkeeping), the Mathlib `Field` instance on the center of a
division ring (`Subring.instField`), and `FiniteField.isPrimePow_card`; the
contribution here is to assemble them into the named class-equation refinement
and to record its **collapse**: Wedderburn's theorem (Mathlib's
`littleWedderburn` instance) forces `Z(D) = D` and `k = 1`, i.e. the central
degree that the class equation a priori allows is in fact always `1`. The badge
is therefore `mathlib`: every step rests on a Mathlib lemma, with the value being
the explicit packaging of the center refinement. Everything is fully
machine-checked, with no axioms or sorries.
-/

namespace LittleWedderburnOQ01OQ02

open scoped Classical

variable (D : Type*) [DivisionRing D] [Finite D]

/-! ## The center is a field -/

omit [Finite D] in
/-- **The center of a finite division ring is a field.** Mathlib equips the
center of *any* division ring with a `Field` structure (`Subring.instField`); we
expose it as the structural predicate `IsField`, which is the input the class
equation needs. -/
theorem center_isField : IsField (Subring.center D) :=
  Field.toIsField _

/-- The center is finite (a subset of the finite ring `D`). -/
instance : Finite (Subring.center D) := Subtype.finite

/-! ## The dimension identity: the class-equation core -/

/-- **The dimension identity `|D| = |Z(D)| ^ k`.** Writing `Z = Z(D)`, the
division ring `D` is a `Z`-vector space, so its cardinality is `|Z|` raised to the
`Z`-dimension `k = dim_{Z} D`. This is the bookkeeping identity at the heart of the
class-equation proof of Wedderburn's theorem (it is also the very first step of
Mathlib's own proof). -/
theorem card_eq_center_pow_finrank :
    Nat.card D = Nat.card (Subring.center D) ^ Module.finrank (Subring.center D) D := by
  have hD : Fintype D := Fintype.ofFinite D
  have hZ : Fintype (Subring.center D) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

/-- The dimension identity in existence form: `|D|` is a power of `|Z(D)|`. -/
theorem exists_card_eq_center_pow :
    ∃ k : ℕ, Nat.card D = Nat.card (Subring.center D) ^ k :=
  ⟨_, card_eq_center_pow_finrank D⟩

/-- The central degree `k = dim_{Z(D)} D` is positive (`D` is nontrivial). -/
theorem finrank_center_pos : 0 < Module.finrank (Subring.center D) D := by
  haveI : Module.Finite (Subring.center D) D := Module.Finite.of_finite
  exact Module.finrank_pos

/-! ## Prime-power orders -/

/-- **The center is a finite field, so its order is a prime power** `p ^ m`. -/
theorem center_card_isPrimePow : IsPrimePow (Nat.card (Subring.center D)) := by
  have : Fintype (Subring.center D) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card (Subring.center D)

/-- **Prime-power order recovered via the center route.** Since `|D| = |Z(D)| ^ k`
with `k ≥ 1` and `|Z(D)|` a prime power, `|D|` is a prime power. This is the
parent's prime-power-order corollary obtained through the class-equation
decomposition rather than by upgrading `D` to a field first. -/
theorem card_isPrimePow : IsPrimePow (Nat.card D) := by
  rw [card_eq_center_pow_finrank D]
  exact (center_card_isPrimePow D).pow (finrank_center_pos D).ne'

/-! ## The collapse: Wedderburn forces the central degree to be `1` -/

/-- **Wedderburn collapse, center form.** By Wedderburn's little theorem `D` is
commutative (Mathlib's `littleWedderburn` instance), so its center is the whole
ring. -/
theorem center_eq_top : Subring.center D = ⊤ :=
  Subring.center_eq_top D

/-- With the center equal to the whole ring, `|Z(D)| = |D|`. -/
theorem center_card_eq : Nat.card (Subring.center D) = Nat.card D := by
  have e : Subring.center D ≃+* D :=
    (RingEquiv.subringCongr (center_eq_top D)).trans Subring.topEquiv
  exact Nat.card_congr e.toEquiv

/-- **The central degree collapses to `1`.** Combining the dimension identity
`|D| = |Z(D)| ^ k` with `|Z(D)| = |D|` (Wedderburn) and `|D| ≥ 2`, the exponent
`k = dim_{Z(D)} D` must equal `1`: the class equation that a priori permits an
arbitrary central degree in fact always has degree one. -/
theorem finrank_center_eq_one : Module.finrank (Subring.center D) D = 1 := by
  have hbase := card_eq_center_pow_finrank D
  rw [center_card_eq D] at hbase
  -- hbase : Nat.card D = Nat.card D ^ finrank
  have h2 : 2 ≤ Nat.card D := by
    have : Fintype D := Fintype.ofFinite D
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hpow : Nat.card D ^ 1 = Nat.card D ^ Module.finrank (Subring.center D) D := by
    rw [pow_one]; exact hbase
  exact (Nat.pow_right_injective h2 hpow).symm

end LittleWedderburnOQ01OQ02
