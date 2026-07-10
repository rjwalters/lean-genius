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

/-- The number of Sylow p-subgroups divides `|G|`.
    Since `n_p` divides the index `[G : P] = |G| / p^k` (`sylow_count_dvd_index`)
    and that index divides `|G|` (`Subgroup.index_dvd_card`), transitivity gives the
    headline Third-Sylow divisibility `n_p | |G|` — the coarser but self-contained
    form of `n_p | |G|/p^k` that needs no reference to the Sylow order. -/
theorem sylow_count_dvd_card (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    card (Sylow p G) ∣ card G := by
  have h := (Sylow.card_sylow_dvd_index P).trans P.toSubgroup.index_dvd_card
  rwa [Nat.card_eq_fintype_card] at h

/-- The number of Sylow p-subgroups is congruent to 1 mod p. -/
theorem sylow_count_mod_p (p : ℕ) [hp : Fact p.Prime] :
    card (Sylow p G) % p = 1 := by
  exact Sylow.card_sylow_modEq_one p G |>.out

/-- The Sylow count `n_p` is **not** divisible by `p` — equivalently, `n_p` is coprime
    to `p`.  Immediate from `sylow_count_mod_p`: a multiple of `p` would have residue `0`,
    but `n_p ≡ 1 (mod p)`.  This is the residue-form companion to `sylow_count_mod_p`
    used, e.g., to rule out `n_p = p` in the classification of groups of small order. -/
theorem sylow_count_not_dvd_p (p : ℕ) [hp : Fact p.Prime] :
    ¬ p ∣ card (Sylow p G) := by
  rw [Nat.dvd_iff_mod_eq_zero, sylow_count_mod_p]
  exact one_ne_zero

/-- **First step of the classification of groups of order `pq`**: if the Sylow count
    `n_p` divides a prime `q`, then `n_p = 1` or `n_p = q`, because the only divisors of a
    prime are `1` and itself (`Nat.Prime.eq_one_or_self_of_dvd`).  Together with
    `n_p ≡ 1 (mod p)` (`sylow_count_mod_p`), this is exactly the arithmetic engine used to
    force a normal Sylow subgroup — hence non-simplicity — for a group of order `p·q`:
    when `q ≢ 1 (mod p)` the value `n_p = q` is excluded and `n_p = 1`, making `P` normal
    by `sylow_normal_iff_card_eq_one`. -/
theorem sylow_count_eq_one_or_prime (p q : ℕ) [hp : Fact p.Prime] (hq : q.Prime)
    (h : card (Sylow p G) ∣ q) :
    card (Sylow p G) = 1 ∨ card (Sylow p G) = q :=
  hq.eq_one_or_self_of_dvd _ h

/-- **Hall property of Sylow subgroups**: the index `[G : P]` of a Sylow p-subgroup is
    prime to `p`.  Since `|P| = p^(vₚ(|G|))` is the *full* p-power in `|G|`
    (`sylow_card_eq`), the complementary index carries no factor of `p`.  This is exactly
    what makes a Sylow subgroup a *Hall* subgroup (`|P|` and `[G:P]` coprime) and the
    defining maximality property behind the First Sylow Theorem.  From
    `Sylow.not_dvd_index` (the `[P.FiniteIndex]` and `Finite (Sylow p G)` instances are
    supplied automatically by `[Fintype G]`). -/
theorem sylow_index_not_dvd_p (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    ¬ p ∣ P.toSubgroup.index :=
  P.not_dvd_index

/-- **Sylow subgroups are Hall subgroups (coprimality form)**: the order `|P| = p^k` and
    the index `[G : P]` are coprime.  This is the sharp, symmetric statement of the Hall
    property upgrading `sylow_index_not_dvd_p`: rewriting `|P|` to the full p-power
    `p^(vₚ(|G|))` (`sylow_card_eq`) reduces coprimality of `p^k` and the index to the
    single fact `p ∤ [G:P]` (`Sylow.not_dvd_index`), raised to the `k`-th power via
    `Nat.Coprime.pow_left`.  A subgroup whose order is coprime to its index is by
    definition a Hall subgroup, so every Sylow subgroup is a Hall subgroup. -/
theorem sylow_card_coprime_index (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.Coprime (card P) P.toSubgroup.index := by
  rw [sylow_card_eq]
  exact ((hp.out.coprime_iff_not_dvd).mpr P.not_dvd_index).pow_left _

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV-B: THE NORMALITY CRITERION (STRUCTURAL COROLLARY OF SYLOW III)

The counting data `n_p` controls normality: a Sylow p-subgroup is normal exactly
when it is the unique one, `n_p = 1`. Combined with `n_p ≡ 1 mod p` and
`n_p | |G|/p^k` this is the standard engine for proving non-simplicity of groups
of many orders (e.g. `|G| = pq`).
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Normality criterion**: a Sylow p-subgroup is normal in `G` iff it is the
    *unique* Sylow p-subgroup, i.e. the Sylow count `n_p` equals `1`.

    Forward (`P.Normal → n_p = 1`): a normal Sylow p-subgroup is the only one
    (`Sylow.unique_of_normal`), so the count is `1`.  Backward (`n_p = 1 → P.Normal`):
    a count of `1` makes the Sylow p-subgroups a subsingleton, and the unique Sylow
    subgroup is normal (`Sylow.normal_of_subsingleton`).  This is the standard bridge
    from the Third-Sylow counting data to structural normality. -/
theorem sylow_normal_iff_card_eq_one (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    P.Normal ↔ card (Sylow p G) = 1 := by
  constructor
  · intro h
    haveI := P.unique_of_normal h
    exact Fintype.card_unique
  · intro h
    haveI : Subsingleton (Sylow p G) :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h)
    exact P.normal_of_subsingleton

/-- A normal Sylow p-subgroup is even **characteristic** (invariant under every
    automorphism of `G`) — a strengthening special to Sylow subgroups, since
    uniqueness (`n_p = 1`) is automorphism-invariant. Immediate from
    `Sylow.characteristic_of_normal`. -/
theorem sylow_characteristic_of_normal (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G)
    (h : P.Normal) : P.Characteristic :=
  P.characteristic_of_normal h

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

/-- **There is always at least one Sylow p-subgroup**: `n_p > 0`.  The positivity
    underlying every Third-Sylow statement (`n_p ≡ 1 mod p`, `n_p ∣ [G:P]`): the set of
    Sylow p-subgroups is nonempty (`Sylow.nonempty`, the First Sylow Theorem), hence its
    cardinality is positive.  Records the base fact that `sylow_count_mod_p` implicitly
    relies on. -/
theorem sylow_count_pos (p : ℕ) [hp : Fact p.Prime] : 0 < card (Sylow p G) :=
  card_pos_iff.mpr Sylow.nonempty

/-- **Subgroup form of Cauchy's theorem**: if `p ∣ |G|` then `G` has a subgroup of order
    exactly `p`.  This is the `k = 1` case of `partial_converse_lagrange` (`p¹ ∣ |G|`), the
    subgroup companion to `cauchy_theorem` (which produces an *element* of order `p`; the
    cyclic group it generates is precisely such a subgroup). -/
theorem exists_subgroup_card_prime (p : ℕ) [hp : Fact p.Prime] (h : p ∣ card G) :
    ∃ H : Subgroup G, Fintype.card H = p := by
  obtain ⟨H, hH⟩ := partial_converse_lagrange p 1 (by rwa [pow_one])
  exact ⟨H, by rwa [pow_one] at hH⟩

end LagrangeOQ01

/-
  ## Summary

  The Sylow Theorems as a partial converse of Lagrange's Theorem.

  **Proved** (0 sorries, 0 axioms — all from Mathlib):
  - Lagrange's theorem and index formula
  - Sylow existence (First Sylow Theorem)
  - Sylow conjugacy (Second Sylow Theorem)
  - Sylow counting (Third Sylow Theorem): n_p ≡ 1 mod p, n_p | [G:P]
  - Coprimality: p ∤ n_p, and the Hall property p ∤ [G:P] (index prime to p)
  - Normality criterion: P normal ⟺ n_p = 1; a normal Sylow is characteristic
  - Partial converse: p^k | |G| implies ∃ subgroup of order p^k
  - Cauchy's theorem: p | |G| implies ∃ element of order p

  **Status**: Verified, 0 sorries, 0 axioms
-/
