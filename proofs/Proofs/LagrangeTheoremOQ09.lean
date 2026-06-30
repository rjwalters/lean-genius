/-
  Center Dichotomy for Groups of Order pq (lagrange-theorem-oq-09)

  This answers OQ-09 from Lagrange's Theorem: pinning down the possible sizes of
  the center Z(G) of a finite group G of order p·q, where p and q are distinct
  primes.

  **Open Question**: For |G| = pq with p ≠ q primes, what are the possible
  orders of the center Z(G)?

  **Answer**: |Z(G)| ∈ {1, pq}. The center is either trivial or all of G; the
  intermediate divisors p and q are impossible.

  **Why the middle is forbidden**: By Lagrange, |Z(G)| divides pq, so it is one
  of 1, p, q, pq. If |Z(G)| = p then the index [G : Z(G)] = q is prime, so the
  quotient G/Z(G) is cyclic; but a group whose central quotient is cyclic is
  abelian, forcing Z(G) = G and |Z(G)| = pq — contradicting |Z(G)| = p (as
  q > 1). The case |Z(G)| = q is symmetric.

  **Consequences**: A nonabelian group of order pq has trivial center. This is
  the structural starting point for the Sylow-based classification carried out in
  the sibling entry `lagrange-theorem-oq-01-oq-01`, which never touches the
  center directly. Mathlib's `card_center_eq_prime_pow` covers prime-power orders
  only, not this two-distinct-prime case.

  Verified, 0 axioms (beyond Lean's foundational propext/Classical.choice/Quot.sound).
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic

namespace LagrangeTheoremOQ09

open Subgroup

/-! ## A divisor lemma for products of two distinct primes

The only divisors of `p * q`, with `p` and `q` distinct primes, are
`1, p, q, p*q`. We obtain this from `n = gcd n p * gcd n q` (valid because `p`
and `q` are coprime and `n ∣ p*q`), since each gcd factor divides a prime. -/

/-- Every divisor of a product of two distinct primes is `1`, one of the primes,
or the product itself. -/
theorem divisors_of_prime_mul_prime {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hn : n ∣ p * q) :
    n = 1 ∨ n = p ∨ n = q ∨ n = p * q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  -- `n = gcd n (p*q) = gcd n p * gcd n q`.
  have hsplit : n = Nat.gcd n p * Nat.gcd n q := by
    rw [← Nat.Coprime.gcd_mul n hcop, Nat.gcd_eq_left hn]
  -- each gcd factor divides a prime, hence is `1` or that prime
  have hdp : Nat.gcd n p = 1 ∨ Nat.gcd n p = p :=
    hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right n p)
  have hdq : Nat.gcd n q = 1 ∨ Nat.gcd n q = q :=
    hq.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right n q)
  rcases hdp with hp1 | hpp <;> rcases hdq with hq1 | hqq
  · -- gcd n p = 1, gcd n q = 1 ⟹ n = 1
    left; rw [hsplit, hp1, hq1, mul_one]
  · -- gcd n p = 1, gcd n q = q ⟹ n = q
    right; right; left; rw [hsplit, hp1, hqq, one_mul]
  · -- gcd n p = p, gcd n q = 1 ⟹ n = p
    right; left; rw [hsplit, hpp, hq1, mul_one]
  · -- gcd n p = p, gcd n q = q ⟹ n = p*q
    right; right; right; rw [hsplit, hpp, hqq]

/-! ## Central quotient of prime index forces commutativity -/

variable {G : Type*} [Group G]

/-- If the central quotient `G ⧸ Z(G)` has prime order, then `G` is abelian
(every pair of elements commutes). This packages
`isCyclic_of_prime_card` with `commutative_of_cyclic_center_quotient`. -/
theorem mul_comm_of_center_index_prime {r : ℕ} [Fact r.Prime]
    (h : (center G).index = r) (a b : G) : a * b = b * a := by
  haveI : IsCyclic (G ⧸ center G) :=
    isCyclic_of_prime_card (p := r) (by rwa [← Subgroup.index_eq_card])
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (center G))
    (QuotientGroup.ker_mk' (center G)).le a b

/-- A group whose central quotient has prime order is its own center. -/
theorem center_eq_top_of_index_prime {r : ℕ} [Fact r.Prime]
    (h : (center G).index = r) : center G = ⊤ := by
  rw [eq_top_iff']
  intro x
  exact mem_center_iff.mpr fun g => mul_comm_of_center_index_prime h g x

/-! ## The center dichotomy -/

/-- **Center dichotomy for groups of order `pq`.** For a finite group `G` with
`|G| = p·q` where `p ≠ q` are primes, the center `Z(G)` has order either `1`
or `pq`: it can never be `p` or `q`. -/
theorem center_card_dichotomy {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hG : Nat.card G = p * q) :
    Nat.card (center G) = 1 ∨ Nat.card (center G) = p * q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  -- By Lagrange the center order divides `pq`.
  have hdvd : Nat.card (center G) ∣ p * q := hG ▸ Subgroup.card_subgroup_dvd_card _
  -- Relation `|Z| · [G:Z] = |G|`.
  have hmul : Nat.card (center G) * (center G).index = p * q := by
    rw [Subgroup.card_mul_index, hG]
  rcases divisors_of_prime_mul_prime hp hq hpq hdvd with h1 | hpc | hqc | hpqc
  · exact Or.inl h1
  · -- `|Z| = p` ⟹ index `= q`, prime ⟹ `Z = ⊤` ⟹ `|Z| = pq`, contradicting `|Z| = p`.
    exfalso
    have hidx : (center G).index = q := by
      have := hmul
      rw [hpc] at this
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have htop : center G = ⊤ := center_eq_top_of_index_prime (r := q) hidx
    have : Nat.card (center G) = p * q := by rw [htop, Subgroup.card_top, hG]
    rw [hpc] at this
    -- `p = p * q` with `q > 1` is impossible
    exact (Nat.ne_of_lt (lt_mul_of_one_lt_right hp.pos hq.one_lt)) this
  · -- symmetric: `|Z| = q` ⟹ index `= p`, prime ⟹ contradiction
    exfalso
    have hidx : (center G).index = p := by
      have := hmul
      rw [hqc, mul_comm p q] at this
      exact Nat.eq_of_mul_eq_mul_left hq.pos this
    have htop : center G = ⊤ := center_eq_top_of_index_prime (r := p) hidx
    have : Nat.card (center G) = p * q := by rw [htop, Subgroup.card_top, hG]
    rw [hqc] at this
    -- `q = p * q` with `p > 1` is impossible
    exact (Nat.ne_of_lt (lt_mul_of_one_lt_left hq.pos hp.one_lt)) this
  · exact Or.inr hpqc

/-! ## Corollaries -/

/-- A nonabelian group of order `pq` (distinct primes) has trivial center. -/
theorem center_trivial_of_nonabelian {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hG : Nat.card G = p * q)
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Nat.card (center G) = 1 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact (Nat.mul_pos hp.pos hq.pos).ne')
  rcases center_card_dichotomy hp hq hpq hG with h1 | hfull
  · exact h1
  · -- if `|Z| = pq = |G|` then `Z = ⊤`, so `G` is abelian — contradiction
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have htop : center G = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hfull, hG]
    have ha : a ∈ center G := htop ▸ Subgroup.mem_top a
    exact hab (mem_center_iff.mp ha b).symm

/-- Restated as a dichotomy: the center of an order-`pq` group is trivial or
everything. -/
theorem center_eq_bot_or_top {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hG : Nat.card G = p * q) :
    center G = ⊥ ∨ center G = ⊤ := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact (Nat.mul_pos hp.pos hq.pos).ne')
  rcases center_card_dichotomy hp hq hpq hG with h1 | hfull
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · refine Or.inr (Subgroup.eq_top_of_card_eq _ ?_)
    rw [hfull, hG]

end LagrangeTheoremOQ09
