/-
  Cauchy's Theorem: a Prime Dividing |G| Gives an Element of That Order
  (lagrange-theorem-oq-08)

  This answers OQ-08 from Lagrange's Theorem: the classical *partial converse*
  to Lagrange supplied by Cauchy's theorem.

  **Lagrange's theorem** says the order |H| of any subgroup H of a finite group
  G divides |G|. The naive converse — "for every divisor d of |G| there is a
  subgroup of order d" — is **false** (the alternating group A₄ has order 12 but
  no subgroup of order 6). **Cauchy's theorem** rescues the converse for the
  *prime* divisors: if a prime p divides |G|, then G actually contains an element
  of order exactly p, hence a (cyclic) subgroup of order p.

  **Open Question**: To what extent does Lagrange's divisibility admit a converse?

  **Answer**: For prime divisors, fully. A prime p divides |G| iff G has an
  element of order p iff G has a cyclic subgroup of order p iff p divides the
  exponent of G. Equivalently: |G| and exp(G) have exactly the same prime
  factors.

  This file restates Mathlib's `exists_prime_orderOf_dvd_card'` (Cauchy) and
  assembles the standard corollaries that turn it into a clean converse-to-
  Lagrange package:

  * `cauchy` — Cauchy's theorem in `Nat.card` form.
  * `exists_cyclic_subgroup_card_eq_prime` — a prime divisor yields a cyclic
    subgroup of that prime order (the subgroup form of the converse).
  * `prime_dvd_card_iff_dvd_exponent` — a prime divides |G| iff it divides
    exp(G); the two directions are Cauchy and `exponent ∣ card`.
  * `primeFactors_card_eq_primeFactors_exponent` — |G| and exp(G) share prime
    factors exactly.
  * `even_card_iff_exists_involution` — the p = 2 special case: a finite group
    has even order iff it contains an involution (element of order 2).

  Verified, 0 axioms (beyond Lean's foundational propext/Classical.choice/Quot.sound).
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic

namespace LagrangeTheoremOQ08

open Subgroup

variable {G : Type*} [Group G]

/-! ## Cauchy's theorem

For every prime `p` dividing the order of a finite group `G`, there is an
element of `G` of order exactly `p`. This is Mathlib's
`exists_prime_orderOf_dvd_card'`; we restate it taking the primality hypothesis
as an ordinary argument (rather than a `Fact` instance) for ease of use. -/

/-- **Cauchy's theorem.** If a prime `p` divides `|G|`, then `G` has an element
of order `p`. -/
theorem cauchy [Finite G] {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card G) :
    ∃ x : G, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card' p hdvd

/-! ## The subgroup form: a cyclic subgroup of prime order

An element of order `p` generates a cyclic subgroup of order `p`. This is the
subgroup-level converse to Lagrange for prime divisors. -/

/-- If `x` has order `p`, the cyclic subgroup `⟨x⟩ = zpowers x` has order `p`. -/
theorem card_zpowers_of_orderOf {x : G} {p : ℕ} (hx : orderOf x = p) :
    Nat.card (zpowers x) = p := by
  rw [Nat.card_zpowers, hx]

/-- **Converse to Lagrange for prime divisors (subgroup form).** If a prime `p`
divides `|G|`, then `G` has a subgroup of order `p`, and that subgroup is
cyclic. -/
theorem exists_cyclic_subgroup_card_eq_prime [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p ∧ IsCyclic H := by
  obtain ⟨x, hx⟩ := cauchy hp hdvd
  refine ⟨zpowers x, card_zpowers_of_orderOf hx, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact isCyclic_of_prime_card (card_zpowers_of_orderOf hx)

/-- The plain subgroup form, forgetting cyclicity: a prime divisor of `|G|` is
realized as the order of some subgroup. Contrast with the full converse, which
fails for composite divisors (e.g. A₄ has no subgroup of order 6). -/
theorem exists_subgroup_card_eq_prime [Finite G] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p := by
  obtain ⟨H, hcard, _⟩ := exists_cyclic_subgroup_card_eq_prime hp hdvd
  exact ⟨H, hcard⟩

/-! ## Prime divisors of the order vs. prime divisors of the exponent

Cauchy gives the forward direction of a clean equivalence: a prime divides `|G|`
iff it divides the exponent `exp(G)`. The reverse direction is elementary
(`exp(G) ∣ |G|`). -/

/-- **A prime divides `|G|` iff it divides the exponent.**

  * (→) is Cauchy: a prime dividing `|G|` is the order of some element, and every
    element order divides the exponent.
  * (←) is `Group.exponent_dvd_nat_card`: the exponent divides `|G|`. -/
theorem prime_dvd_card_iff_dvd_exponent [Finite G] {p : ℕ} (hp : p.Prime) :
    p ∣ Nat.card G ↔ p ∣ Monoid.exponent G := by
  constructor
  · intro hdvd
    obtain ⟨x, hx⟩ := cauchy hp hdvd
    have := Monoid.order_dvd_exponent x
    rwa [hx] at this
  · intro hdvd
    exact hdvd.trans Group.exponent_dvd_nat_card

/-- **`|G|` and `exp(G)` have exactly the same prime factors.** A direct
consequence of the prime-divisor equivalence: even though the exponent can be
much smaller than the order, no prime is lost. -/
theorem primeFactors_card_eq_primeFactors_exponent [Finite G] :
    (Nat.card G).primeFactors = (Monoid.exponent G).primeFactors := by
  have hcard : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hexp : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
  ext p
  simp only [Nat.mem_primeFactors, hcard, hexp, ne_eq, not_false_eq_true, and_true]
  constructor
  · rintro ⟨hp, hpd⟩
    exact ⟨hp, (prime_dvd_card_iff_dvd_exponent hp).mp hpd⟩
  · rintro ⟨hp, hpd⟩
    exact ⟨hp, (prime_dvd_card_iff_dvd_exponent hp).mpr hpd⟩

/-! ## The `p = 2` special case: involutions

Specializing Cauchy to `p = 2` recovers the classical fact that a finite group
of even order contains an involution. The converse (an involution forces even
order) is Lagrange. -/

/-- **A finite group has even order iff it contains an involution.** The forward
direction is Cauchy at `p = 2`; the reverse is Lagrange (`orderOf x ∣ |G|`). -/
theorem even_card_iff_exists_involution [Finite G] :
    Even (Nat.card G) ↔ ∃ x : G, orderOf x = 2 := by
  constructor
  · intro he
    exact cauchy Nat.prime_two (even_iff_two_dvd.mp he)
  · rintro ⟨x, hx⟩
    have hdvd : (2 : ℕ) ∣ Nat.card G := by
      have := orderOf_dvd_natCard x
      rwa [hx] at this
    exact even_iff_two_dvd.mpr hdvd

/-- Packaged corollary: any finite group of even order has an element `x ≠ 1`
with `x * x = 1`. -/
theorem exists_involution_of_even_card [Finite G] (he : Even (Nat.card G)) :
    ∃ x : G, x ≠ 1 ∧ x * x = 1 := by
  obtain ⟨x, hx⟩ := even_card_iff_exists_involution.mp he
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    simp [orderOf_one] at hx
  · have : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa [pow_two] using this

/-! ## Concrete instance: the symmetric group `S₃`

`S₃ = Perm (Fin 3)` has order `3! = 6`, so Cauchy guarantees elements of orders
`2` and `3` — the transpositions and the 3-cycles, respectively. -/

/-- `|S₃| = 6`. -/
theorem card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  have h3 : Nat.card (Fin 3) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.card_perm, h3]
  rfl

/-- `S₃` contains an element of order `3` (a 3-cycle), by Cauchy. -/
example : ∃ x : Equiv.Perm (Fin 3), orderOf x = 3 :=
  cauchy (p := 3) (by norm_num) (by rw [card_perm_fin_three]; norm_num)

/-- `S₃` contains an involution (a transposition), by the even-order corollary. -/
example : ∃ x : Equiv.Perm (Fin 3), orderOf x = 2 :=
  even_card_iff_exists_involution.mp (by rw [card_perm_fin_three]; decide)

end LagrangeTheoremOQ08
