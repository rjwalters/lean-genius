/-
  Lagrange's Theorem OQ-01 — order `p²` groups are abelian (a structural companion
  to the `pq` classification)

  The sibling `LagrangeTheoremOQ01` develops the **Sylow theorems** as the partial
  converse to Lagrange, and `LagrangeTheoremOQ01OQ01` classifies groups of order `pq`
  (distinct primes): coprime `n_p, n_q` forces the group to be **cyclic** (e.g. orders
  `15, 35, 77`).

  This file records the neighbouring structural fact for the *other* two-prime-factor
  shape, a prime **square** `p²`:

      a group of order `p²` is **abelian**.

  This is genuinely weaker than the `pq`-cyclic conclusion, and the contrast is the
  point: order `pq` (coprime data) forces *cyclic*, but order `p²` forces only
  *abelian* — it need **not** be cyclic (the Klein four-group `C₂ × C₂` has order
  `4 = 2²` and is abelian but not cyclic).  So `p²` is exactly the boundary where the
  "few prime factors ⟹ cyclic" heuristic first fails while abelianness survives.

  The proof wraps Mathlib's `IsPGroup.commutative_of_card_eq_prime_sq`, whose mechanism
  is the classical one: a nontrivial `p`-group has nontrivial centre, so for `|G| = p²`
  the quotient `G / Z(G)` has order `1` or `p`, hence is cyclic, and a group whose
  central quotient is cyclic is abelian.

  Main results:
  * `card_prime_sq_commutative` — `Nat.card G = p²` (p prime) ⟹ `G` is abelian.
  * `commGroupOfCardPrimeSq`     — the same, packaged as a `CommGroup` structure.
  * `card_4_commutative`, `card_9_commutative`, `card_25_commutative`,
    `card_49_commutative` — concrete instances (orders `2², 3², 5², 7²`), mirroring the
    `order_15_cyclic` / `order_35_cyclic` concrete instances of the sibling file.

  Structural refinement (the cyclic / elementary-abelian fork):
  * `card_prime_sq_cyclic_or_exponent_p` — order `p²` ⟹ cyclic or `exponent = p`.
  * `card_prime_sq_noncyclic_pow_p_eq_one` — a *non-cyclic* order-`p²` group is
    elementary abelian: `gᵖ = 1` for every `g`.
  * `card_prime_sq_cyclic_or_pow_p_eq_one` — the packaged dichotomy `IsCyclic ∨
    (∀ g, gᵖ = 1)`, i.e. the fork `ℤ/p²` versus `(ℤ/p)²`.
  * `card_4_cyclic_or_sq_eq_one`, `card_9_cyclic_or_cube_eq_one` — concrete forks
    at orders `4` and `9`, sharpening the `commutative` instances.

  All results are `0`-sorry / `0`-axiom on top of Mathlib.
-/

import Mathlib

namespace LagrangeOQ01PSquare

variable {G : Type*} [Group G]

/-- **A group of order `p²` is abelian.**  For a prime `p`, if `Nat.card G = p²` then
    every pair of elements commutes.  (Contrast the sibling `pq`-classification: coprime
    order `pq` forces *cyclic*, whereas order `p²` forces only *abelian* — cf. the Klein
    four-group, order `4`, abelian but not cyclic.)  Wraps
    `IsPGroup.commutative_of_card_eq_prime_sq`. -/
theorem card_prime_sq_commutative {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : ∀ a b : G, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.commutative_of_card_eq_prime_sq hG

/-- The abelian structure of an order-`p²` group, packaged as a `CommGroup`. -/
noncomputable def commGroupOfCardPrimeSq {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : CommGroup G :=
  haveI : Fact p.Prime := ⟨hp⟩
  IsPGroup.commGroupOfCardEqPrimeSq hG

/-- Every group of order `4 = 2²` is abelian. -/
theorem card_4_commutative (hG : Nat.card G = 4) : ∀ a b : G, a * b = b * a :=
  card_prime_sq_commutative (p := 2) (by norm_num) (hG.trans (by norm_num))

/-- Every group of order `9 = 3²` is abelian. -/
theorem card_9_commutative (hG : Nat.card G = 9) : ∀ a b : G, a * b = b * a :=
  card_prime_sq_commutative (p := 3) (by norm_num) (hG.trans (by norm_num))

/-- Every group of order `25 = 5²` is abelian. -/
theorem card_25_commutative (hG : Nat.card G = 25) : ∀ a b : G, a * b = b * a :=
  card_prime_sq_commutative (p := 5) (by norm_num) (hG.trans (by norm_num))

/-- Every group of order `49 = 7²` is abelian. -/
theorem card_49_commutative (hG : Nat.card G = 49) : ∀ a b : G, a * b = b * a :=
  card_prime_sq_commutative (p := 7) (by norm_num) (hG.trans (by norm_num))

/-! ## The finer dichotomy: cyclic or elementary abelian

Order `p²` forces abelian (`card_prime_sq_commutative`), but *not* cyclic — the
Klein four-group `C₂ × C₂` is the smallest counterexample.  The precise structural
split refining abelianness is that a **non-cyclic** order-`p²` group is
*elementary abelian*: its exponent is exactly `p`, so every element satisfies
`gᵖ = 1`.  Together with the cyclic case (exponent `p²`, a single generator) this
is the group-theoretic content behind the two-isomorphism-type classification
`C_{p²} ≅ ℤ/p²` versus `Cₚ × Cₚ ≅ (ℤ/p)²`.  The dichotomy wraps Mathlib's
`not_isCyclic_iff_exponent_eq_prime`. -/

/-- **Cyclic-or-exponent-`p` dichotomy.**  A group of order `p²` is either cyclic
    or has exponent exactly `p`.  (For a `p`-group of order `p²` the exponent is
    `p²` in the cyclic case and `p` otherwise — no other value is possible.) -/
theorem card_prime_sq_cyclic_or_exponent_p {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : IsCyclic G ∨ Monoid.exponent G = p := by
  rcases em (IsCyclic G) with h | h
  · exact Or.inl h
  · exact Or.inr ((not_isCyclic_iff_exponent_eq_prime hp hG).mp h)

/-- A **non-cyclic** group of order `p²` is elementary abelian: every element
    satisfies `gᵖ = 1` (equivalently, has order `1` or `p`).  This is the precise
    sense in which the Klein-four phenomenon generalises — order `p²` without a
    generator forces the *uniform* exponent `p`. -/
theorem card_prime_sq_noncyclic_pow_p_eq_one {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (hcyc : ¬ IsCyclic G) (g : G) : g ^ p = 1 := by
  have hexp : Monoid.exponent G = p := (not_isCyclic_iff_exponent_eq_prime hp hG).mp hcyc
  rw [← hexp]
  exact Monoid.pow_exponent_eq_one g

/-- **Full order-`p²` dichotomy.**  Every group of order `p²` is either cyclic or
    satisfies `gᵖ = 1` for every element (elementary abelian).  A single statement
    combining `card_prime_sq_cyclic_or_exponent_p` with the exponent-to-power
    translation `Monoid.pow_exponent_eq_one`; this is the structural fork behind
    the isomorphism classification `ℤ/p²` versus `(ℤ/p)²`. -/
theorem card_prime_sq_cyclic_or_pow_p_eq_one {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : IsCyclic G ∨ ∀ g : G, g ^ p = 1 := by
  rcases card_prime_sq_cyclic_or_exponent_p hp hG with h | h
  · exact Or.inl h
  · exact Or.inr fun g => h ▸ Monoid.pow_exponent_eq_one g

/-- Concrete order-`4` dichotomy: a group of order `4` is either cyclic (`ℤ/4`)
    or every element squares to the identity — the Klein four-group `(ℤ/2)²`.
    Mirrors `card_4_commutative`, sharpening "abelian" to the exact two-type fork. -/
theorem card_4_cyclic_or_sq_eq_one (hG : Nat.card G = 4) :
    IsCyclic G ∨ ∀ g : G, g ^ 2 = 1 :=
  card_prime_sq_cyclic_or_pow_p_eq_one (p := 2) (by norm_num) (hG.trans (by norm_num))

/-- Concrete order-`9` dichotomy: a group of order `9` is either cyclic (`ℤ/9`)
    or every element cubes to the identity — the elementary abelian `(ℤ/3)²`. -/
theorem card_9_cyclic_or_cube_eq_one (hG : Nat.card G = 9) :
    IsCyclic G ∨ ∀ g : G, g ^ 3 = 1 :=
  card_prime_sq_cyclic_or_pow_p_eq_one (p := 3) (by norm_num) (hG.trans (by norm_num))

end LagrangeOQ01PSquare
