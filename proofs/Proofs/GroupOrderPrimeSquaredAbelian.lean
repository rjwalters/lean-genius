/-
  Groups of Order p² are Abelian — with the Cyclic / Elementary-Abelian Dichotomy

  Open question OQ-01 (parent: group-order-prime-squared-abelian).

  The first nontrivial step in the classification of finite p-groups: every group
  `G` of order `p²` (`p` prime) is abelian. Mathlib proves the bare commutativity
  via `IsPGroup.commutative_of_card_eq_prime_sq` (the center is nontrivial, so the
  central quotient `G/Z(G)` has order `1` or `p`, hence is cyclic, hence `G` is
  abelian). This entry packages that result from the *order hypothesis* alone and
  then goes further, supplying the **structural classification** that Mathlib does
  not state:

      |G| = p²  ⟹  G is cyclic (≅ ℤ/p²)   XOR   every element satisfies gᵖ = 1
                                                  (elementary abelian, ≅ (ℤ/p)²).

  ## Contents

  * `mul_comm_of_card_eq_prime_sq` — the abelian theorem, stated from `Nat.card G = p²`.
  * `orderOf_eq_of_card_eq_prime_sq` — every element has order `1`, `p`, or `p²`
    (Lagrange + the divisors of a prime square).
  * `isCyclic_or_exponent_p` — the structural dichotomy: `G` is cyclic, or `G` has
    exponent `p` (i.e. `∀ g, gᵖ = 1`).
  * `pow_prime_eq_one_of_not_isCyclic` — the non-cyclic case is elementary abelian.
  * `isCyclic_iff_not_forall_pow_prime` — the two cases are mutually exclusive, so the
    dichotomy is sharp: `G` is cyclic *iff* it does not have exponent `p`.

  Everything is elementary group theory over a finite group; no axioms, no sorries.
-/
import Mathlib

namespace GroupOrderPrimeSq

variable {G : Type*} [Group G]

/-! ## The abelian theorem -/

/-- **A group of order `p²` is abelian.** Stated from the order hypothesis
`Nat.card G = p²` with `p` prime. This repackages
`IsPGroup.commutative_of_card_eq_prime_sq` (whose proof routes through the
nontrivial center and the cyclic central quotient) so that the only hypotheses are
the cardinality and primality. -/
theorem mul_comm_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    ∀ a b : G, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.commutative_of_card_eq_prime_sq hG

/-! ## Element orders -/

/-- **Trichotomy of element orders.** In a group of order `p²` (`p` prime) every
element has order `1`, `p`, or `p²`: its order divides `p²` (Lagrange), and the only
divisors of a prime square are `1`, `p`, `p²`. -/
theorem orderOf_eq_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (g : G) : orderOf g = 1 ∨ orderOf g = p ∨ orderOf g = p ^ 2 := by
  have hdvd : orderOf g ∣ p ^ 2 := hG ▸ orderOf_dvd_natCard g
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · exact Or.inl (by simpa using hke)
  · exact Or.inr (Or.inl (by simpa using hke))
  · exact Or.inr (Or.inr hke)

/-! ## The structural dichotomy -/

/-- **Cyclic or elementary abelian.** A group of order `p²` (`p` prime) is either
cyclic — there is an element of order `p²` generating it — or it has exponent `p`,
meaning `gᵖ = 1` for every `g` (so it is elementary abelian, `≅ (ℤ/p)²`). The split
is on whether an element of order `p²` exists; if not, the trichotomy forces every
order to divide `p`. -/
theorem isCyclic_or_exponent_p {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    IsCyclic G ∨ ∀ g : G, g ^ p = 1 := by
  by_cases h : ∃ g : G, orderOf g = p ^ 2
  · obtain ⟨g, hg⟩ := h
    haveI : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 2 hp.pos.ne')
    exact Or.inl (isCyclic_of_orderOf_eq_card g (by rw [hg, hG]))
  · push_neg at h
    refine Or.inr (fun g => ?_)
    rcases orderOf_eq_of_card_eq_prime_sq hp hG g with h1 | hp' | hsq
    · rw [← orderOf_dvd_iff_pow_eq_one, h1]; exact one_dvd p
    · rw [← orderOf_dvd_iff_pow_eq_one, hp']
    · exact absurd hsq (h g)

/-- **The non-cyclic case is elementary abelian.** If a group of order `p²` is not
cyclic, then every element satisfies `gᵖ = 1` (exponent `p`). -/
theorem pow_prime_eq_one_of_not_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hnc : ¬ IsCyclic G) (g : G) : g ^ p = 1 :=
  (isCyclic_or_exponent_p hp hG).resolve_left hnc g

/-- **The dichotomy is sharp (mutually exclusive cases).** A group of order `p²`
(`p` prime) is cyclic *iff* it does not have exponent `p`. The forward direction uses
that a cyclic group of order `p²` has a generator of order `p²`, which cannot satisfy
`gᵖ = 1` since `p² ∤ p`; the reverse is the dichotomy. -/
theorem isCyclic_iff_not_forall_pow_prime {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    IsCyclic G ↔ ¬ ∀ g : G, g ^ p = 1 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 2 hp.pos.ne')
  constructor
  · intro hc hall
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hc
    have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hall g)
    have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos (by rwa [hg, hG] at hdvd)
    nlinarith [hp.two_le]
  · intro h
    exact (isCyclic_or_exponent_p hp hG).resolve_right h

end GroupOrderPrimeSq
