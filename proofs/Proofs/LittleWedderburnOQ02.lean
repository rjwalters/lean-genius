import Mathlib

/-!
# Classification of finite fields: existence and uniqueness of order `q`

The parent proof (`LittleWedderburnOQ01`) records Wedderburn's little theorem —
every finite division ring is a field — together with its arithmetic corollaries,
in particular that the **order of a finite division ring is a prime power**
`p ^ n`. The natural question one asks immediately afterwards is the **converse and
classification**:

> For which `q` does a finite field of order `q` exist, and how many are there?

The answer is the classification of finite fields, originally due to Galois and
Moore:

* **Existence.** For every prime power `q = p ^ n` (`p` prime, `n ≥ 1`) there is a
  field with exactly `q` elements — Mathlib's `GaloisField p n` is the canonical
  model, with `Nat.card (GaloisField p n) = p ^ n`.
* **Uniqueness.** Any two finite fields of the same cardinality are isomorphic as
  rings (`FiniteField.ringEquivOfCardEq`). Together with existence this says the
  finite fields of a given prime-power order form a single isomorphism class —
  the field `GF(q)`.
* **Sharpness.** A finite field's order is *necessarily* a prime power
  (`FiniteField.isPrimePow_card`); equivalently a `Fintype` admits a field
  structure iff its cardinality is a prime power.

Mathlib supplies these ingredients individually (the canonical model `GaloisField`,
its cardinality, the noncanonical isomorphism `ringEquivOfCardEq`, and the
prime-power constraint), but it does **not** package them as the combined
existence-and-uniqueness statement, nor does it record the **division-ring** form:
combining Wedderburn with uniqueness shows that *any two finite division rings of
the same order are isomorphic*, and that every finite division ring of order
`p ^ n` is isomorphic to `GF(p ^ n)`. That bridge — the genuinely new derived
content here — closes the loop opened by the parent: a finite division ring is not
merely *a* field of prime-power order, it is *the* field `GF(q)`.

Everything is fully machine-checked with no axioms or sorries.
-/

namespace LittleWedderburnOQ02

/-! ## Existence: `GaloisField` realizes every prime-power order -/

/-- **Existence (canonical model).** The Galois field `GF(p ^ n)` has exactly
`p ^ n` elements. -/
theorem card_galoisField (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (GaloisField p n) = p ^ n :=
  GaloisField.card p n hn

/-- **Existence (existential form).** For every prime `p` and exponent `n ≥ 1`
there is a finite field with exactly `p ^ n` elements. -/
theorem exists_field_of_primePow (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Nat.card F = p ^ n := by
  haveI := Fact.mk hp
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  exact ⟨GaloisField p n, inferInstance, inferInstance, GaloisField.card p n hn⟩

/-! ## Uniqueness: equal order forces isomorphism -/

/-- **Uniqueness.** Any two finite fields of the same cardinality are isomorphic
as rings. -/
theorem nonempty_ringEquiv_of_card_eq {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] (h : Fintype.card K = Fintype.card L) :
    Nonempty (K ≃+* L) :=
  ⟨FiniteField.ringEquivOfCardEq h⟩

/-- **Uniqueness (`Nat.card` form).** The same statement phrased with `Nat.card`,
for finite fields supplied only with a `Finite` instance. -/
theorem nonempty_ringEquiv_of_natCard_eq {K L : Type*} [Field K] [Field L]
    [Finite K] [Finite L] (h : Nat.card K = Nat.card L) :
    Nonempty (K ≃+* L) := by
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite L
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]

/-! ## Existence + uniqueness combined: every field of order `p ^ n` is `GF(p ^ n)` -/

/-- **Classification.** Every finite field of order `p ^ n` is isomorphic to the
canonical model `GaloisField p n`. With `card_galoisField` this is the full
existence-and-uniqueness statement: the finite fields of order `p ^ n` form a
single isomorphism class, represented by `GF(p ^ n)`. -/
theorem ringEquiv_galoisField_of_card {K : Type*} [Field K] [Fintype K]
    (p n : ℕ) [Fact p.Prime] (h : Fintype.card K = p ^ n) :
    Nonempty (K ≃+* GaloisField p n) := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    have := Fintype.one_lt_card (α := K)
    omega
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [h, ← Nat.card_eq_fintype_card]
  exact (GaloisField.card p n hn).symm

/-! ## Sharpness: only prime powers occur -/

/-- **Necessity.** The order of a finite field is a prime power. -/
theorem isPrimePow_card (K : Type*) [Field K] [Fintype K] :
    IsPrimePow (Fintype.card K) :=
  FiniteField.isPrimePow_card K

/-- **Full characterization.** A finite type admits a field structure iff its
cardinality is a prime power. -/
theorem nonempty_field_iff (α : Type*) [Fintype α] :
    Nonempty (Field α) ↔ IsPrimePow (Fintype.card α) :=
  Fintype.nonempty_field_iff

/-! ## Wedderburn bridge: from division rings to `GF(q)` -/

/-- **Division-ring classification.** Every finite division ring of order `p ^ n`
is isomorphic, as a ring, to `GF(p ^ n)`. Wedderburn's little theorem makes the
division ring a field (the `littleWedderburn` instance), after which uniqueness
identifies it with the canonical model. This is the division-ring strengthening of
`ringEquiv_galoisField_of_card`, absent from Mathlib. -/
theorem divisionRing_ringEquiv_galoisField (D : Type*) [DivisionRing D] [Fintype D]
    (p n : ℕ) [Fact p.Prime] (h : Fintype.card D = p ^ n) :
    Nonempty (D ≃+* GaloisField p n) :=
  ringEquiv_galoisField_of_card (K := D) p n h

/-- **No two distinct finite division rings of equal order.** Any two finite
division rings with the same number of elements are isomorphic as rings: by
Wedderburn each is a field, and finite fields are classified by their order. -/
theorem divisionRing_nonempty_ringEquiv_of_card_eq (D E : Type*)
    [DivisionRing D] [DivisionRing E] [Fintype D] [Fintype E]
    (h : Fintype.card D = Fintype.card E) : Nonempty (D ≃+* E) :=
  ⟨FiniteField.ringEquivOfCardEq h⟩

/-! ## Worked instances -/

/-- `GF(2 ^ 3) = GF(8)` has exactly `8` elements. -/
theorem card_galoisField_eight : Nat.card (GaloisField 2 3) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h := GaloisField.card 2 3 (by norm_num)
  norm_num at h
  exact h

/-- For prime `p`, the prime field `ZMod p` is the order-`p` Galois field `GF(p)`:
it is isomorphic to `GaloisField p 1`. -/
theorem zmod_ringEquiv_galoisField (p : ℕ) [Fact p.Prime] :
    Nonempty (ZMod p ≃+* GaloisField p 1) :=
  ⟨(GaloisField.equivZmodP p).symm.toRingEquiv⟩

end LittleWedderburnOQ02
