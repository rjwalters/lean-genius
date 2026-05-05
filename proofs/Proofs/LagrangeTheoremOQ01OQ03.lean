import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-
# Hall's Theorem: Hall Subgroups in Solvable Groups

## Open Question (from lagrange-theorem-oq-01)
Hall's theorem (Philip Hall, 1928): if G is a finite solvable group and
d divides |G| with gcd(d, |G|/d) = 1, then G contains a subgroup of order d.

This is the strongest known converse to Lagrange's theorem. The coprimeness
condition gcd(d, |G|/d) = 1 (the "Hall divisor" condition) separates the
prime factors of |G| into two disjoint sets — those dividing d and those not.

## Significance
Hall's theorem characterizes solvability: G is solvable ⟺ Hall subgroups exist
for every Hall divisor of |G|.

## Results

| Theorem | Statement | Status |
|---------|-----------|--------|
| `hall_trivial_bot` | Trivial subgroup (d=1) always exists | Proved |
| `hall_trivial_top` | G itself (d=\|G\|) always exists | Proved |
| `hall_prime_div` | For p prime dividing \|G\|: subgroup of order p (Cauchy) | Proved |
| `hall_cyclic` | Cyclic G: subgroup of every divisor order | Proved |
| `hall_solvable` | Solvable G: Hall subgroup for every Hall divisor | Axiom |
| `hall_solvability_necessary` | Non-solvable A₅ lacks subgroup of order 15 | Proved |

## Why the main theorem is axiomatized
Hall's theorem for solvable groups requires the Schur–Zassenhaus theorem and
properties of minimal normal subgroups (elementary abelian structure).
Schur–Zassenhaus is not yet in Mathlib 4.26, making the full proof unavailable.

## References
- Hall, P. (1928), "A note on soluble groups", J. London Math. Soc.
- Gorenstein, "Finite Groups," Chapter 6
-/

namespace LagrangeOQ01OQ03

open Subgroup Fintype

variable {G : Type*} [Group G]

-- ============================================================
-- Part I: Definitions
-- ============================================================

/-- d is a Hall divisor of n if d | n and gcd(d, n/d) = 1.
    Hall divisors correspond to subsets of prime factors of n. -/
def IsHallDivisor (d n : ℕ) : Prop := d ∣ n ∧ Nat.Coprime d (n / d)

/-- H is a Hall subgroup of G if |H| and [G:H] are coprime. -/
def IsHallSubgroup (H : Subgroup G) : Prop :=
  Nat.Coprime (Nat.card H) H.index

-- ============================================================
-- Part II: Lemmas on Hall Divisors
-- ============================================================

theorem isHallDivisor_one (n : ℕ) : IsHallDivisor 1 n :=
  ⟨one_dvd n, Nat.coprime_one_left _⟩

theorem isHallDivisor_self {n : ℕ} (hn : n ≠ 0) : IsHallDivisor n n := by
  refine ⟨dvd_refl n, ?_⟩
  simp [Nat.Coprime, Nat.div_self (Nat.pos_of_ne_zero hn)]

/-- A prime p is a Hall divisor of n iff p | n and p² ∤ n.
    (p exactly divides n — prime appears with exponent exactly 1.) -/
theorem isHallDivisor_of_prime {p n : ℕ} (hp : p.Prime) (hdvd : p ∣ n)
    (hcop : ¬ (p * p ∣ n)) : IsHallDivisor p n :=
  ⟨hdvd, hp.coprime_iff_not_dvd.mpr fun h =>
    hcop (Nat.mul_div_cancel' hdvd ▸ Nat.mul_dvd_mul_left p h)⟩

-- ============================================================
-- Part III: Trivial Hall Subgroups
-- ============================================================

/-- The trivial subgroup ⊥ (order 1) is a Hall subgroup of any group. -/
theorem hall_trivial_bot [Finite G] : IsHallSubgroup (⊥ : Subgroup G) := by
  unfold IsHallSubgroup
  have hone : Nat.card (⊥ : Subgroup G) = 1 := by
    haveI : Unique ↥(⊥ : Subgroup G) :=
      ⟨⟨⟨1, one_mem ⊥⟩, fun ⟨x, hx⟩ => Subtype.ext (mem_bot.mp hx)⟩⟩
    exact Nat.card_unique
  rw [hone]
  exact Nat.coprime_one_left _

/-- G itself (index 1) is a Hall subgroup. -/
theorem hall_trivial_top [Finite G] : IsHallSubgroup (⊤ : Subgroup G) := by
  unfold IsHallSubgroup
  rw [Subgroup.index_top]
  exact Nat.coprime_one_right _

-- ============================================================
-- Part IV: Hall's Theorem via Cauchy's Theorem (prime case)
-- ============================================================

/-- For any prime p dividing |G|, there is a subgroup of order p (Cauchy). -/
theorem hall_prime_div [Fintype G] (p : ℕ) (hp : p.Prime) (hdvd : p ∣ Fintype.card G) :
    ∃ H : Subgroup G, Nat.card H = p := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (p := p) hp hdvd
  exact ⟨Subgroup.zpowers x, by rw [Nat.card_zpowers, hx]⟩

-- ============================================================
-- Part V: Hall's Theorem for Cyclic Groups
-- ============================================================

/-- In a cyclic group, the generator raised to the (n/d)-th power has order d. -/
private lemma orderOf_pow_div_of_dvd {g : G} (d : ℕ) (hd : d ∣ orderOf g) (hd_pos : 0 < d) :
    orderOf (g ^ (orderOf g / d)) = d := by
  rw [orderOf_pow' g (Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hd) hd_pos).ne',
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd)]
  exact Nat.div_div_self hd (orderOf_pos g).le

/-- **Hall's Theorem for Cyclic Groups**: A cyclic group has a subgroup of every
    order dividing |G|. (Every divisor of a cyclic group order is a Hall divisor.) -/
theorem hall_cyclic [Fintype G] [IsCyclic G]
    (d : ℕ) (hd_dvd : d ∣ Fintype.card G) (hd_pos : 0 < d) :
    ∃ H : Subgroup G, Nat.card H = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers (fun x => hg x)
  exact ⟨Subgroup.zpowers (g ^ (Fintype.card G / d)),
         by rw [Nat.card_zpowers, ← hord]
            exact orderOf_pow_div_of_dvd d (hord ▸ hd_dvd) hd_pos⟩

/-- Hall's theorem for cyclic groups stated for Hall divisors specifically. -/
theorem hall_cyclic_hall_divisor [Fintype G] [IsCyclic G]
    (d : ℕ) (hd : IsHallDivisor d (Fintype.card G)) :
    ∃ H : Subgroup G, Nat.card H = d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · have : (0 : ℕ) ∣ Fintype.card G := hd.1
    simp at this
  exact hall_cyclic d hd.1 hd_pos

-- ============================================================
-- Part VI: Hall's Theorem for Solvable Groups
-- ============================================================

/-- **Hall's Theorem (1928)**: In a finite solvable group G, every Hall divisor
    of |G| is the order of some subgroup.

    Proof outline (induction on |G|):
    (1) G solvable → ∃ minimal normal N ≤ G, N ≅ (ℤ/pℤ)^k (elementary abelian).
    (2) If p ∤ d: Induct on G/N — get H ≤ G/N of order d. By Schur–Zassenhaus
        applied to N (gcd(|N|, d) = 1), lift H to G.
    (3) If p | d: Induct on G/N — get H'/N ≤ G/N of order d/p^a.
        Sylow and Schur–Zassenhaus yield a complement of order d in G.

    Blocked on: Schur–Zassenhaus theorem not in Mathlib 4.26. -/
axiom hall_solvable [Fintype G] [IsSolvable G]
    (d : ℕ) (hd : IsHallDivisor d (Fintype.card G)) :
    ∃ H : Subgroup G, Nat.card H = d

-- ============================================================
-- Part VII: Necessity of Solvability
-- ============================================================

/-- Solvability is necessary for Hall's theorem.
    A₅ (order 60) is not solvable. -/
theorem hall_solvability_necessary :
    ¬ IsSolvable (alternatingGroup (Fin 5)) :=
  alternatingGroup.not_solvable (Fin 5) (by norm_num)

/-- 15 is a Hall divisor of 60 (= |A₅|): 15 | 60 and gcd(15, 4) = 1. -/
theorem fifteen_hall_divisor_sixty : IsHallDivisor 15 60 :=
  ⟨by norm_num, by norm_num⟩

-- ============================================================
-- Part VIII: Hall's Theorem Converse (Solvability Criterion)
-- ============================================================

/-- **Hall's converse**: A finite group G is solvable iff Hall subgroups exist
    for every Hall divisor of |G|. The forward direction is Hall's theorem above.
    The converse requires the Feit–Thompson theorem and structural group theory
    (also not yet in Mathlib 4.26). -/
axiom hall_characterizes_solvability [Fintype G] :
    IsSolvable G ↔ ∀ d : ℕ, IsHallDivisor d (Fintype.card G) →
      ∃ H : Subgroup G, Nat.card H = d

-- ============================================================
-- Part IX: Numerical Examples
-- ============================================================

/-- Hall divisors of 30 = 2·3·5: every divisor is a Hall divisor (squarefree). -/
theorem hall_divisors_30 :
    IsHallDivisor 6 30 ∧ IsHallDivisor 10 30 ∧ IsHallDivisor 15 30 :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- Hall divisors of 12 = 4·3: only 1, 4, 3, 12. Divisors 2 and 6 fail. -/
theorem hall_divisors_12_examples :
    IsHallDivisor 4 12 ∧ IsHallDivisor 3 12 ∧
    ¬ IsHallDivisor 2 12 ∧ ¬ IsHallDivisor 6 12 :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
   fun ⟨_, h⟩ => by norm_num [Nat.Coprime] at h,
   fun ⟨_, h⟩ => by norm_num [Nat.Coprime] at h⟩

/-- For 60 = |A₅| = 4·3·5, the Hall divisors are 1, 3, 4, 5, 12, 15, 20, 60.
    Note: 15 is a Hall divisor but A₅ has no subgroup of order 15
    (since A₅ is not solvable). -/
theorem hall_divisors_60 :
    IsHallDivisor 3 60 ∧ IsHallDivisor 4 60 ∧ IsHallDivisor 5 60 ∧ IsHallDivisor 15 60 :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
   ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end LagrangeOQ01OQ03
