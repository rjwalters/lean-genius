/-
  The Exponent of a Group of Order p² — a Sharp Invariant for the Dichotomy

  Follow-up open question OQ-01-OQ-01
  (parent: group-order-prime-squared-abelian-oq-01).

  The parent entry proves that a group `G` of order `p²` (`p` prime) is abelian and
  splits into two isomorphism types via the *exponent-p predicate*: `G` is cyclic
  (`≅ ℤ/p²`) **or** every element satisfies `gᵖ = 1` (elementary abelian, `≅ (ℤ/p)²`).

  This follow-up reframes that dichotomy through the single numerical invariant
  `Monoid.exponent G` — the least `n > 0` with `gⁿ = 1` for all `g`. The exponent is
  the *standard* group-theoretic discriminant separating `ℤ/p²` from `(ℤ/p)²`, and we
  show it takes exactly the two possible values and that each value pins down the type:

      exponent G = p²  ⟺  G is cyclic        (≅ ℤ/p²)
      exponent G = p   ⟺  G is NOT cyclic    (≅ (ℤ/p)², elementary abelian)

  ## Contents

  * `orderOf_eq_prime_of_not_isCyclic` — sharpening of the parent's `gᵖ = 1`: in the
    non-cyclic case *every non-identity* element has order **exactly** `p`.
  * `exponent_eq_sq_of_isCyclic` — a cyclic group of order `p²` has exponent `p²`.
  * `exponent_eq_prime_of_not_isCyclic` — a non-cyclic group of order `p²` has
    exponent `p`.
  * `exponent_eq_prime_or_sq` — the exponent is `p` or `p²` and nothing else.
  * `exponent_eq_sq_iff_isCyclic` / `exponent_eq_prime_iff_not_isCyclic` — each value
    of the exponent characterizes the isomorphism type, so the invariant is sharp.

  Everything is elementary finite group theory; no axioms, no sorries. The structural
  dichotomy is imported from the parent file.
-/
import Mathlib
import Proofs.GroupOrderPrimeSquaredAbelian

namespace GroupOrderPrimeSqExponent

open GroupOrderPrimeSq

variable {G : Type*} [Group G]

/-! ## Finiteness and nontriviality helpers -/

/-- A group of cardinality `p²` (`p` prime) is finite. -/
private theorem finite_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : Finite G :=
  Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 2 hp.pos.ne')

/-- A group of cardinality `p²` (`p` prime) is nontrivial: `p² ≥ 4 > 1`. -/
private theorem nontrivial_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : Nontrivial G := by
  haveI : Finite G := finite_of_card_eq_prime_sq hp hG
  rw [← Finite.one_lt_card_iff_nontrivial, hG]
  nlinarith [hp.two_le]

/-! ## Sharpened element orders in the non-cyclic case -/

/-- **Every non-identity element has order exactly `p`.** The parent shows that a
non-cyclic group of order `p²` has `gᵖ = 1` for all `g`; here we sharpen this to: every
`g ≠ 1` has order *exactly* `p`. Indeed `gᵖ = 1` forces `orderOf g ∣ p`, so the order is
`1` or `p`, and `g ≠ 1` rules out `1`. -/
theorem orderOf_eq_prime_of_not_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hnc : ¬ IsCyclic G) {g : G} (hg : g ≠ 1) : orderOf g = p := by
  have hdvd : orderOf g ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr (pow_prime_eq_one_of_not_isCyclic hp hG hnc g)
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact absurd (orderOf_eq_one_iff.mp h1) hg
  · exact hp'

/-! ## The exponent in each case -/

/-- **A cyclic group of order `p²` has exponent `p²`.** A generator `g` has order
`Nat.card G = p²`, so `p² = orderOf g ∣ exponent G`; conversely every element's order
divides `p²`, so `exponent G ∣ p²`. Antisymmetry of divisibility gives equality. -/
theorem exponent_eq_sq_of_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hc : IsCyclic G) : Monoid.exponent G = p ^ 2 := by
  haveI : Finite G := finite_of_card_eq_prime_sq hp hG
  -- exponent divides p²: every order divides the cardinality p²
  have hle : Monoid.exponent G ∣ p ^ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact hG ▸ orderOf_dvd_natCard g
  -- p² divides exponent: a generator has order p²
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hc
  have hge : p ^ 2 ∣ Monoid.exponent G := by
    rw [← hG, ← hg]; exact Monoid.order_dvd_exponent g
  exact Nat.dvd_antisymm hle hge

/-- **A non-cyclic group of order `p²` has exponent `p`.** Every element satisfies
`gᵖ = 1`, so `exponent G ∣ p`; and the group is nontrivial, so some element has order
`> 1`, forcing `exponent G ≠ 1`. As `p` is prime, `exponent G = p`. -/
theorem exponent_eq_prime_of_not_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hnc : ¬ IsCyclic G) : Monoid.exponent G = p := by
  haveI : Finite G := finite_of_card_eq_prime_sq hp hG
  haveI : Nontrivial G := nontrivial_of_card_eq_prime_sq hp hG
  have hle : Monoid.exponent G ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      pow_prime_eq_one_of_not_isCyclic hp hG hnc g
  rcases (Nat.dvd_prime hp).mp hle with h1 | hp'
  · -- exponent = 1 would make every element trivial, contradicting nontriviality
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    have : orderOf g ∣ 1 := h1 ▸ Monoid.order_dvd_exponent g
    exact absurd (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)) hg
  · exact hp'

/-! ## The exponent is a sharp invariant for the dichotomy -/

/-- **The exponent of a group of order `p²` is `p` or `p²`.** -/
theorem exponent_eq_prime_or_sq {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    Monoid.exponent G = p ∨ Monoid.exponent G = p ^ 2 := by
  by_cases hc : IsCyclic G
  · exact Or.inr (exponent_eq_sq_of_isCyclic hp hG hc)
  · exact Or.inl (exponent_eq_prime_of_not_isCyclic hp hG hc)

/-- **Exponent `p²` characterizes the cyclic type.** For a group of order `p²`,
`exponent G = p²` *iff* `G` is cyclic. The reverse is `exponent_eq_sq_of_isCyclic`; the
forward direction is the contrapositive: a non-cyclic group has exponent `p ≠ p²`. -/
theorem exponent_eq_sq_iff_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    Monoid.exponent G = p ^ 2 ↔ IsCyclic G := by
  refine ⟨fun h => ?_, exponent_eq_sq_of_isCyclic hp hG⟩
  by_contra hnc
  rw [exponent_eq_prime_of_not_isCyclic hp hG hnc] at h
  -- p = p² is impossible for p ≥ 2
  nlinarith [hp.two_le]

/-- **Exponent `p` characterizes the elementary-abelian type.** For a group of order
`p²`, `exponent G = p` *iff* `G` is **not** cyclic (so `G ≅ (ℤ/p)²`). -/
theorem exponent_eq_prime_iff_not_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    Monoid.exponent G = p ↔ ¬ IsCyclic G := by
  refine ⟨fun h hc => ?_, exponent_eq_prime_of_not_isCyclic hp hG⟩
  rw [exponent_eq_sq_of_isCyclic hp hG hc] at h
  -- p² = p is impossible for p ≥ 2
  nlinarith [hp.two_le]

end GroupOrderPrimeSqExponent
