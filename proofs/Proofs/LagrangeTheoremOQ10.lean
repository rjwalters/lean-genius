/-
  The Gcd Refinement of Lagrange: Subgroup Intersections (lagrange-theorem-oq-10)

  This answers OQ-10 from Lagrange's Theorem: the arithmetic of the order of an
  intersection of two subgroups.

  **Open Question**: How is the order of `H ⊓ K` constrained by the orders of
  `H` and `K`?

  **Answer**: `|H ⊓ K|` divides `gcd(|H|, |K|)`. This is the sharp refinement of
  Lagrange applied on the subgroup lattice: `H ⊓ K ≤ H` and `H ⊓ K ≤ K` give
  `|H ⊓ K| ∣ |H|` and `|H ⊓ K| ∣ |K|` respectively, and the two divisibilities
  combine through the universal property of the gcd.

  **Consequences**:
  * Subgroups of coprime order meet only in the identity (`H ⊓ K = ⊥`).
  * Hence any element lying in two coprime-order subgroups is the identity.
  * When the orders additionally multiply to `|G|`, `H` and `K` are complementary
    (`H.IsComplement' K`): the internal direct-product situation behind
    CRT-style splitting of finite (abelian) groups and Sylow decomposition.
  * A concrete instance: two subgroups of distinct prime orders intersect
    trivially.

  Mathlib states only the coprime special case `Subgroup.inf_eq_bot_of_coprime`
  and its proof passes through `Nat.eq_one_of_dvd_coprimes`; the explicit
  gcd-divisibility statement `|H ⊓ K| ∣ gcd(|H|,|K|)` is the honest new core here,
  from which the coprime corollary is re-derived.

  Verified, 0 axioms (beyond Lean's foundational propext/Classical.choice/Quot.sound).
-/
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Complement
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic

namespace LagrangeTheoremOQ10

open Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G)

/-! ## The gcd-divisibility core -/

/-- **Core refinement of Lagrange.** The order of the intersection of two
subgroups divides the gcd of their orders. Both `H ⊓ K ≤ H` and `H ⊓ K ≤ K`
give a Lagrange divisibility, and `Nat.dvd_gcd` combines them. -/
theorem card_inf_dvd_gcd :
    Nat.card (H ⊓ K : Subgroup G) ∣ Nat.gcd (Nat.card H) (Nat.card K) :=
  Nat.dvd_gcd (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

/-! ## Coprime orders force a trivial intersection -/

/-- Subgroups whose orders are coprime intersect trivially, re-derived from the
gcd core: `|H ⊓ K|` divides `gcd(|H|,|K|) = 1`, so it equals `1`. -/
theorem inf_eq_bot_of_coprime_card
    (h : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ := by
  rw [← Subgroup.card_eq_one]
  have hg : Nat.gcd (Nat.card H) (Nat.card K) = 1 := h
  have hd := card_inf_dvd_gcd H K
  rw [hg] at hd
  exact Nat.dvd_one.mp hd

/-- An element lying in two coprime-order subgroups must be the identity. -/
theorem eq_one_of_mem_both
    (h : Nat.Coprime (Nat.card H) (Nat.card K)) {g : G} (hH : g ∈ H) (hK : g ∈ K) :
    g = 1 := by
  have hmem : g ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hH, hK⟩
  rw [inf_eq_bot_of_coprime_card H K h] at hmem
  exact Subgroup.mem_bot.mp hmem

/-! ## The internal direct product -/

/-- With coprime orders whose product is `|G|`, `H` and `K` complement each other
in `G`: the internal direct-product situation. Wraps
`Subgroup.isComplement'_of_coprime`. -/
theorem isComplement'_of_coprime_card [Finite G]
    (hmul : Nat.card H * Nat.card K = Nat.card G)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) : H.IsComplement' K :=
  Subgroup.isComplement'_of_coprime hmul hcop

/-! ## Concrete instance: distinct prime orders -/

/-- Two subgroups of distinct prime orders intersect trivially: the coprimality
of `p ≠ q` feeds directly into `inf_eq_bot_of_coprime_card`. -/
theorem inf_eq_bot_of_prime_orders {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hH : Nat.card H = p) (hK : Nat.card K = q) : H ⊓ K = ⊥ :=
  inf_eq_bot_of_coprime_card H K (by
    rw [hH, hK]; exact (Nat.coprime_primes hp hq).mpr hpq)

end LagrangeTheoremOQ10
