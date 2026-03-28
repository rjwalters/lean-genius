/-
  Lagrange's Theorem OQ-01: The Sylow Theorems (Partial Converse)

  Lagrange's theorem states: |H| divides |G| for H ≤ G finite.
  The CONVERSE is false: A₄ has order 12 but no subgroup of order 6.

  However, the Sylow theorems provide a powerful partial converse:
  for every prime power p^k dividing |G|, there EXISTS a subgroup of
  order p^k. These "Sylow p-subgroups" are the maximal p-power subgroups.

  **Sylow Theorem I** (Existence): If p^k | |G|, then G has a subgroup of order p^k.
  **Sylow Theorem II** (Conjugacy): All Sylow p-subgroups are conjugate.
  **Sylow Theorem III** (Counting): n_p ≡ 1 mod p and n_p | |G|/p^k.

  This file connects Mathlib's Sylow theory to the Lagrange theorem context.

  Tags: group-theory, algebra, classic, wiedijk-100
-/

import Mathlib

namespace LagrangeOQ01

open Subgroup Fintype

variable {G : Type*} [Group G] [Fintype G]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: LAGRANGE'S THEOREM (FROM MATHLIB)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Lagrange's theorem: the order of a subgroup divides the order of the group. -/
theorem lagrange (H : Subgroup G) [Fintype H] : card H ∣ card G :=
  H.card_subgroup_dvd_card

/-- The index formula: |G| = |H| · [G : H]. -/
theorem lagrange_index (H : Subgroup G) [Fintype H] :
    card G = card H * H.index :=
  (Subgroup.card_mul_index H).symm

/-- The order of every element divides |G|. -/
theorem order_dvd_card (g : G) : orderOf g ∣ card G :=
  orderOf_dvd_card

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: SYLOW EXISTENCE (FIRST SYLOW THEOREM)

Mathlib proves: for every prime p, if p divides |G|, then G has a
Sylow p-subgroup P with |P| = p^k where p^k is the largest power
of p dividing |G|.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Sylow subgroups exist: for every prime p, there is a Sylow p-subgroup. -/
theorem sylow_exists (p : ℕ) [hp : Fact p.Prime] : Nonempty (Sylow p G) :=
  Sylow.nonempty

/-- A Sylow p-subgroup has order p^k where p^k || |G| (maximal p-power). -/
theorem sylow_card_eq (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    card P = p ^ (card G).factorization p :=
  Sylow.card_eq_multiplicity P

/-- The order of a Sylow p-subgroup divides |G| (special case of Lagrange). -/
theorem sylow_order_dvd (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    card P ∣ card G :=
  P.toSubgroup.card_subgroup_dvd_card

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: SYLOW CONJUGACY (SECOND SYLOW THEOREM)

All Sylow p-subgroups are conjugate: if P and Q are Sylow p-subgroups,
then there exists g ∈ G with Q = gPg⁻¹.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- All Sylow p-subgroups are conjugate (Second Sylow Theorem).
    Mathlib gives this as an action on Sylow subgroups. -/
theorem sylow_conjugate (p : ℕ) [hp : Fact p.Prime] (P Q : Sylow p G) :
    ∃ g : G, P.toSubgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) = Q.toSubgroup := by
  obtain ⟨g, hg⟩ := Sylow.conj_eq P Q
  exact ⟨g, by rw [← hg]; ext; simp [Subgroup.mem_map, MulAut.conj_apply]; aesop⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: SYLOW COUNTING (THIRD SYLOW THEOREM)

The number n_p of Sylow p-subgroups satisfies:
1. n_p ≡ 1 (mod p)
2. n_p divides |G| / p^k
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The number of Sylow p-subgroups divides the index of any Sylow p-subgroup. -/
theorem sylow_count_dvd_index (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    card (Sylow p G) ∣ P.toSubgroup.index :=
  Sylow.card_sylow_dvd_index P

/-- The number of Sylow p-subgroups is congruent to 1 mod p. -/
theorem sylow_count_mod_p (p : ℕ) [hp : Fact p.Prime] :
    card (Sylow p G) % p = 1 := by
  exact Sylow.card_sylow_modEq_one p G |>.out

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: PARTIAL CONVERSE OF LAGRANGE

The Sylow theorems give a partial converse: for prime powers dividing |G|,
subgroups of that order exist. For composite divisors, this can fail.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Sylow theorems provide a partial converse to Lagrange's theorem:
    for every prime p and natural number k with p^k | |G|, there is a
    subgroup of order p^k. -/
theorem partial_converse_lagrange (p : ℕ) [hp : Fact p.Prime] (k : ℕ)
    (hk : p ^ k ∣ card G) :
    ∃ H : Subgroup G, Fintype.card H = p ^ k := by
  -- Mathlib's IsPGroup.exists_le_sylow gives subgroups for all p-power divisors
  exact Sylow.exists_subgroup_card_pow_prime p hk

/-- Cauchy's theorem as a corollary: if p | |G|, then G has an element of order p. -/
theorem cauchy_theorem (p : ℕ) [hp : Fact p.Prime] (h : p ∣ card G) :
    ∃ g : G, orderOf g = p :=
  exists_prime_orderOf_dvd_card p h

end LagrangeOQ01

/-
  ## Summary

  The Sylow Theorems as a partial converse of Lagrange's Theorem.

  **Proved** (0 sorries, 0 axioms — all from Mathlib):
  - Lagrange's theorem and index formula
  - Sylow existence (First Sylow Theorem)
  - Sylow conjugacy (Second Sylow Theorem)
  - Sylow counting (Third Sylow Theorem): n_p ≡ 1 mod p, n_p | [G:P]
  - Partial converse: p^k | |G| implies ∃ subgroup of order p^k
  - Cauchy's theorem: p | |G| implies ∃ element of order p

  **Status**: Verified, 0 sorries, 0 axioms
-/
