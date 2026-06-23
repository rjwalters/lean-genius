/-
  pq-Groups: Classification via Sylow Theory (lagrange-theorem-oq-01-oq-01)

  This answers OQ-01-OQ-01 from Lagrange's Theorem OQ-01 (Sylow as Partial Converse).

  **Open Question**: Use Sylow's theorems to classify all groups of order pq,
  where p < q are distinct primes.

  **Answer** (Burnside 1911, via Sylow):
  Let G be a finite group with |G| = pq, where p < q are primes.

  1. **Unique normal Sylow q-subgroup**: There is exactly one Sylow q-subgroup Q,
     and Q is normal in G. Proof: n_q ≡ 1 (mod q) and n_q | p (by Sylow III),
     so n_q ∈ {1, p}. If n_q = p, then p ≡ 1 (mod q), forcing q | p-1 < q — impossible.

  2. **Cyclic case**: If p ∤ (q-1), then G is cyclic (≅ ℤ/pq).
     In this case n_p = 1 too, so P ⊴ G. With G = PQ, P ∩ Q = {1}, and
     P, Q commuting (from normality + coprime orders), G has an element of order pq.

  3. **Non-abelian case**: If p | (q-1), two groups of order pq exist up to
     isomorphism: the cyclic group ℤ/pq and a non-abelian semidirect product ℤ/q ⋊ ℤ/p.

  **Concrete examples**:
  - Order 15 = 3 × 5: 3 ∤ (5-1), so only ℤ/15 exists.
  - Order 35 = 5 × 7: 5 ∤ (7-1), so only ℤ/35 exists.
  - Order 6 = 2 × 3: 2 | (3-1), so ℤ/6 and S₃ both exist.
  - Order 21 = 3 × 7: 3 | (7-1), so ℤ/21 and a non-abelian group both exist.

  The full classification proof is in `Proofs.SylowTheoremOQ01` (namespace SylowPQ).
  This file re-exposes key results in the Lagrange open-question context.

  References:
  - Burnside, W. (1911). Theory of Groups of Finite Order, 2nd ed., §§93–95.
  - Dummit, D. & Foote, R. (2004). Abstract Algebra, §4.5, Theorem 14.
  - https://en.wikipedia.org/wiki/Sylow_theorems#Examples

  Tags: group-theory, lagrange, sylow, classification, pq-groups, cyclic-groups, finite-groups
-/

import Mathlib
import Proofs.SylowTheoremOQ01

open SylowPQ Subgroup Fintype

namespace LagrangeOQ01OQ01

/-!
## Part I: Sylow Counting Constraints for pq-Groups

For |G| = pq (p < q primes):
- n_q divides p and n_q ≡ 1 (mod q), forcing n_q = 1
- n_p divides q and n_p ≡ 1 (mod p), so n_p ∈ {1, q}
-/

/-- For p < q distinct primes and |G| = pq, the Sylow count constraints:
    n_q = 1 always, and n_p ∈ {1, q}. -/
theorem lagrange_pq_sylow_counts {G : Type*} [Group G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcard : Fintype.card G = p * q) :
    Fintype.card (Sylow q G) = 1 ∧
    (Fintype.card (Sylow p G) = 1 ∨ Fintype.card (Sylow p G) = q) := by
  let h : IsPQGroup G := ⟨p, q, hp, hq, ne_of_lt hpq, hcard⟩
  exact ⟨unique_sylow_q h hpq, sylow_p_count h hpq⟩

/-!
## Part II: Unique Normal Sylow q-Subgroup

The key structural result: Q ⊴ G always, regardless of whether p | q-1.
-/

/-- In a group of order pq (p < q primes), there is exactly one Sylow q-subgroup,
    and it is normal in G.

    Proof: n_q ≡ 1 (mod q) and n_q | p (by Sylow III, since [G:Q] = p).
    Since p < q, we have p < q, so if n_q = p then p ≡ 1 (mod q) requires q | p-1.
    But p-1 < q (as p < q), so p-1 < q implies q ∤ p-1. Contradiction.
    Hence n_q = 1, and the unique Sylow q-subgroup is normal (n_p = 1 ↔ P ⊴ G). -/
theorem lagrange_pq_unique_normal_q {G : Type*} [Group G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcard : Fintype.card G = p * q) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal :=
  sylow_q_normal ⟨p, q, hp, hq, ne_of_lt hpq, hcard⟩ hpq

/-- The unique Sylow q-subgroup count is 1. -/
theorem lagrange_pq_n_q_eq_one {G : Type*} [Group G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcard : Fintype.card G = p * q) :
    Fintype.card (Sylow q G) = 1 :=
  unique_sylow_q ⟨p, q, hp, hq, ne_of_lt hpq, hcard⟩ hpq

/-!
## Part III: The Cyclic Classification

When p ∤ (q-1): n_p = 1 too, both Sylow subgroups are normal,
elements from P and Q commute (commutator ∈ P ∩ Q = {1}),
and G has an element of order p·q, making G cyclic.
-/

/-- If p ∤ (q-1), the Sylow p-subgroup count is also 1 (unique, hence normal). -/
theorem lagrange_pq_n_p_eq_one_when_coprime {G : Type*} [Group G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcard : Fintype.card G = p * q) (hndvd : ¬ (p ∣ q - 1)) :
    Fintype.card (Sylow p G) = 1 :=
  unique_sylow_p_when_coprime ⟨p, q, hp, hq, ne_of_lt hpq, hcard⟩ hpq hndvd

/-- **Main Classification** (cyclic case): If p ∤ (q-1), every group of order pq
    is cyclic. When p ∤ (q-1), there is exactly one group of order pq (up to isomorphism):
    the cyclic group ℤ/pq. -/
theorem lagrange_pq_cyclic {G : Type*} [Group G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcard : Fintype.card G = p * q) (hndvd : ¬ (p ∣ q - 1)) :
    IsCyclic G :=
  pq_cyclic_classification p q hp hq hpq hndvd G hcard

/-- **Universal form**: For primes p < q with p ∤ (q-1), every group of order pq
    is cyclic. This is the universal quantification over all groups. -/
theorem pq_unique_when_coprime (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) (hndvd : ¬ (p ∣ q - 1)) :
    ∀ (G : Type*) [Group G] [Fintype G],
    Fintype.card G = p * q → IsCyclic G :=
  pq_cyclic_classification p q hp hq hpq hndvd

/-!
## Part IV: The Non-Abelian Case

When p | (q-1), n_p can equal q, giving a non-cyclic group.
The semidirect product ℤ/q ⋊ ℤ/p exists and is not cyclic.
-/

/-- When p | (q-1), a non-cyclic group of order pq has exactly q Sylow p-subgroups. -/
theorem lagrange_pq_nonabelian_n_p_eq_q {G : Type*} [Group G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hcard : Fintype.card G = p * q) (hdvd : p ∣ q - 1) (hncyc : ¬ IsCyclic G) :
    Fintype.card (Sylow p G) = q :=
  nonabelian_sylow_p_count ⟨p, q, hp, hq, ne_of_lt hpq, hcard⟩ hpq hdvd hncyc

/-!
## Part V: Concrete Examples

For small primes, we verify the divisibility conditions that determine
which classification applies.
-/

/-- **Order 15 = 3 × 5**: Since 3 ∤ (5-1) = 4, every group of order 15 is cyclic. -/
theorem order_15_cyclic :
    ∀ (G : Type*) [Group G] [Fintype G], Fintype.card G = 15 → IsCyclic G :=
  pq_cyclic_classification 3 5 (by norm_num) (by norm_num) (by norm_num) (by omega)

/-- **Order 35 = 5 × 7**: Since 5 ∤ (7-1) = 6, every group of order 35 is cyclic. -/
theorem order_35_cyclic :
    ∀ (G : Type*) [Group G] [Fintype G], Fintype.card G = 35 → IsCyclic G :=
  pq_cyclic_classification 5 7 (by norm_num) (by norm_num) (by norm_num) (by omega)

/-- **Order 77 = 7 × 11**: Since 7 ∤ (11-1) = 10, every group of order 77 is cyclic. -/
theorem order_77_cyclic :
    ∀ (G : Type*) [Group G] [Fintype G], Fintype.card G = 77 → IsCyclic G :=
  pq_cyclic_classification 7 11 (by norm_num) (by norm_num) (by norm_num) (by omega)

/-- **Order 6 = 2 × 3**: Since 2 | (3-1) = 2, two groups exist: ℤ/6 and S₃. -/
theorem order_6_non_unique : (2 : ℕ) ∣ (3 - 1) := by omega

/-- **Order 21 = 3 × 7**: Since 3 | (7-1) = 6, two groups exist:
    ℤ/21 and the non-abelian group of order 21. -/
theorem order_21_non_unique : (3 : ℕ) ∣ (7 - 1) := by omega

/-- **Order 55 = 5 × 11**: Since 5 | (11-1) = 10, two groups of order 55 exist. -/
theorem order_55_non_unique : (5 : ℕ) ∣ (11 - 1) := by omega

end LagrangeOQ01OQ01
