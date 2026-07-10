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

end LagrangeOQ01PSquare
