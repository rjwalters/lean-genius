import Mathlib

/-!
# Uniqueness of finite fields: the classification by cardinality

The parent entry (`LittleWedderburnOQ01`) records the *arithmetic shadow* of
Wedderburn's little theorem: the order of a finite division ring is a prime power
`p ^ n`. The natural companion to that existence-of-shape statement is a
**uniqueness** statement: for each prime power `q` there is, up to isomorphism,
**exactly one** finite field of order `q`.

Mathlib supplies one half of this — `FiniteField.ringEquivOfCardEq`, which builds a
(noncanonical) ring isomorphism between any two finite fields of equal cardinality,
routed through the Galois field `GaloisField p n`. What is not recorded is the clean
*classification* packaging usually quoted alongside the prime-power corollary:

* the full **iff** `Nonempty (K ≃+* K') ↔ card K = card K'` (the reverse direction —
  isomorphic fields have equal order — is the easy bijection direction and is *not*
  in Mathlib as a named lemma);
* its contrapositive: finite fields of *different* orders are never isomorphic;
* the **canonical representative**: every finite field of order `p ^ n` is isomorphic
  to `GaloisField p n`, so the Galois field is *the* field of that order;
* the **existence-and-uniqueness** statement combined, and the concrete corollaries
  that a field of prime order `p` is isomorphic to `ZMod p`, while `ZMod 2` and
  `ZMod 3` are not isomorphic.

The heavy lifting (the existence of the isomorphism for equal cardinality) is
Mathlib's `ringEquivOfCardEq`; the new content here is the classification *iff* and
its consequences, which turn that one-directional construction into the standard
"exactly one finite field of each prime-power order" statement. Everything is fully
machine-checked with no axioms or sorries.
-/

namespace LittleWedderburnOQ01OQ01

/-! ## The classification theorem -/

/-- **Classification of finite fields by order.** Two finite fields are
ring-isomorphic **iff** they have the same number of elements.

The forward direction is the elementary observation that a ring isomorphism is in
particular a bijection of the underlying types; the reverse direction is the
substantive uniqueness theorem (Mathlib's `FiniteField.ringEquivOfCardEq`, built by
realizing both fields as splitting fields of `X ^ q - X`). -/
theorem ringEquiv_iff_card_eq (K K' : Type*) [Field K] [Fintype K] [Field K'] [Fintype K'] :
    Nonempty (K ≃+* K') ↔ Fintype.card K = Fintype.card K' := by
  constructor
  · rintro ⟨e⟩
    exact Fintype.card_congr e.toEquiv
  · intro h
    exact ⟨FiniteField.ringEquivOfCardEq h⟩

/-- **Finite fields of different orders are never isomorphic.** The contrapositive of
the classification: cardinality is a complete isomorphism invariant for finite
fields. -/
theorem not_nonempty_ringEquiv_of_card_ne (K K' : Type*) [Field K] [Fintype K]
    [Field K'] [Fintype K'] (h : Fintype.card K ≠ Fintype.card K') :
    ¬ Nonempty (K ≃+* K') := by
  rw [ringEquiv_iff_card_eq]
  exact h

/-! ## Existence: every prime power is realized -/

/-- **Existence.** For a prime `p` and exponent `n ≠ 0`, the Galois field
`GaloisField p n` is a finite field of order exactly `p ^ n`. (A re-export of
`GaloisField.card`, recorded here as the existence half of the classification.) -/
theorem galoisField_card (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (GaloisField p n) = p ^ n :=
  GaloisField.card p n hn

/-- **Canonical representative (uniqueness).** Any finite field `K` of order `p ^ n`
is ring-isomorphic to `GaloisField p n`: among all finite fields, the Galois field is
*the* representative of its order up to isomorphism. -/
theorem nonempty_ringEquiv_galoisField (K : Type*) [Field K] [Fintype K] (p n : ℕ)
    [Fact p.Prime] (hn : n ≠ 0) (h : Fintype.card K = p ^ n) :
    Nonempty (K ≃+* GaloisField p n) := by
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [h, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]

/-- **Existence and uniqueness combined.** For every prime power `q = p ^ n`
(`p` prime, `n ≠ 0`) there is a finite field of order `q` — namely `GaloisField p n` —
and every finite field of order `q` is isomorphic to it. This is the precise sense in
which there is, up to isomorphism, exactly one field of each prime-power order. -/
theorem exists_unique_field_of_primePow (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (GaloisField p n) = p ^ n ∧
      ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = p ^ n →
        Nonempty (K ≃+* GaloisField p n) := by
  refine ⟨GaloisField.card p n hn, ?_⟩
  intro K _ _ h
  exact nonempty_ringEquiv_galoisField K p n hn h

/-! ## Concrete corollaries -/

/-- A finite field of *prime* order `p` is ring-isomorphic to `ZMod p`. (The `n = 1`
case of the canonical-representative theorem, against the standard model `ZMod p`.) -/
theorem nonempty_ringEquiv_zmod (K : Type*) [Field K] [Fintype K] (p : ℕ) [Fact p.Prime]
    (h : Fintype.card K = p) : Nonempty (K ≃+* ZMod p) := by
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [h, ZMod.card]

/-- The prime fields `ZMod 2` and `ZMod 3` are **not** isomorphic: they have
different orders, so the classification rules out any ring isomorphism. -/
theorem zmod_two_not_ringEquiv_zmod_three : ¬ Nonempty (ZMod 2 ≃+* ZMod 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [ringEquiv_iff_card_eq, ZMod.card, ZMod.card]
  decide

end LittleWedderburnOQ01OQ01
