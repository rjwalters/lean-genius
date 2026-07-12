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
  Orders are measured with `Nat.card` and finiteness with `[Finite G]`, matching
  the current Mathlib Sylow API.

  Tags: group-theory, algebra, classic, wiedijk-100
-/

import Mathlib

namespace LagrangeOQ01

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: LAGRANGE'S THEOREM (FROM MATHLIB)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Lagrange's theorem: the order of a subgroup divides the order of the group. -/
theorem lagrange (H : Subgroup G) : Nat.card H ∣ Nat.card G :=
  H.card_subgroup_dvd_card

/-- The index formula: |G| = |H| · [G : H]. -/
theorem lagrange_index (H : Subgroup G) :
    Nat.card G = Nat.card H * H.index :=
  (Subgroup.card_mul_index H).symm

/-- The order of every element divides |G|. -/
theorem order_dvd_card (g : G) : orderOf g ∣ Nat.card G :=
  orderOf_dvd_natCard g

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: SYLOW EXISTENCE (FIRST SYLOW THEOREM)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Every finite group has a Sylow p-subgroup (First Sylow Theorem). -/
theorem sylow_exists (p : ℕ) [hp : Fact p.Prime] : Nonempty (Sylow p G) :=
  Sylow.nonempty

/-- A Sylow p-subgroup has order p^k where p^k || |G| (maximal p-power). -/
theorem sylow_card_eq (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card P = p ^ (Nat.card G).factorization p :=
  Sylow.card_eq_multiplicity P

/-- The order of a Sylow p-subgroup divides |G| (special case of Lagrange). -/
theorem sylow_order_dvd (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card P ∣ Nat.card G :=
  P.toSubgroup.card_subgroup_dvd_card

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: SYLOW CONJUGACY (SECOND SYLOW THEOREM)

All Sylow p-subgroups are conjugate: if P and Q are Sylow p-subgroups,
then there exists g ∈ G with Q = gPg⁻¹.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- All Sylow p-subgroups are conjugate (Second Sylow Theorem).
    Mathlib gives this as a transitive action of `G` on the Sylow subgroups:
    there is a `g : G` with `g • P = Q`. -/
theorem sylow_conjugate (p : ℕ) [hp : Fact p.Prime] (P Q : Sylow p G) :
    ∃ g : G, g • P = Q :=
  MulAction.exists_smul_eq G P Q

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: SYLOW COUNTING (THIRD SYLOW THEOREM)

The number n_p of Sylow p-subgroups satisfies:
1. n_p ≡ 1 (mod p)
2. n_p divides |G| / p^k
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The number of Sylow p-subgroups divides the index of any Sylow p-subgroup. -/
theorem sylow_count_dvd_index (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.toSubgroup.index :=
  P.card_dvd_index

/-- The number of Sylow p-subgroups divides `|G|`.
    Since `n_p` divides the index `[G : P] = |G| / p^k` (`sylow_count_dvd_index`)
    and that index divides `|G|` (`Subgroup.index_dvd_card`), transitivity gives the
    headline Third-Sylow divisibility `n_p | |G|` — the coarser but self-contained
    form of `n_p | |G|/p^k` that needs no reference to the Sylow order. -/
theorem sylow_count_dvd_card (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ Nat.card G :=
  P.card_dvd_index.trans P.toSubgroup.index_dvd_card

/-- The number of Sylow p-subgroups is congruent to 1 mod p. -/
theorem sylow_count_mod_p (p : ℕ) [hp : Fact p.Prime] :
    Nat.card (Sylow p G) % p = 1 := by
  have h := card_sylow_modEq_one (p := p) (G := G)
  have hp1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hp.out.one_lt
  rwa [Nat.ModEq, hp1] at h

/-- The Sylow count `n_p` is **not** divisible by `p` — equivalently, `n_p` is coprime
    to `p`.  Immediate from `sylow_count_mod_p`: a multiple of `p` would have residue `0`,
    but `n_p ≡ 1 (mod p)`.  This is the residue-form companion to `sylow_count_mod_p`
    used, e.g., to rule out `n_p = p` in the classification of groups of small order. -/
theorem sylow_count_not_dvd_p (p : ℕ) [hp : Fact p.Prime] :
    ¬ p ∣ Nat.card (Sylow p G) := by
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
    (h : Nat.card (Sylow p G) ∣ q) :
    Nat.card (Sylow p G) = 1 ∨ Nat.card (Sylow p G) = q :=
  hq.eq_one_or_self_of_dvd _ h

/-- **Hall property of Sylow subgroups**: the index `[G : P]` of a Sylow p-subgroup is
    prime to `p`.  Since `|P| = p^(vₚ(|G|))` is the *full* p-power in `|G|`
    (`sylow_card_eq`), the complementary index carries no factor of `p`.  This is exactly
    what makes a Sylow subgroup a *Hall* subgroup (`|P|` and `[G:P]` coprime) and the
    defining maximality property behind the First Sylow Theorem.  From
    `Sylow.not_dvd_index` (the `[P.FiniteIndex]` and `Finite (Sylow p G)` instances are
    supplied automatically by `[Finite G]`). -/
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
    Nat.Coprime (Nat.card P) P.toSubgroup.index := by
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
    P.Normal ↔ Nat.card (Sylow p G) = 1 := by
  constructor
  · intro h
    haveI := P.unique_of_normal h
    exact Nat.card_unique
  · intro h
    haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp h).1
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
    (hk : p ^ k ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ k :=
  Sylow.exists_subgroup_card_pow_prime p hk

/-- Cauchy's theorem as a corollary: if p | |G|, then G has an element of order p. -/
theorem cauchy_theorem (p : ℕ) [hp : Fact p.Prime] (h : p ∣ Nat.card G) :
    ∃ g : G, orderOf g = p :=
  exists_prime_orderOf_dvd_card' p h

/-- **There is always at least one Sylow p-subgroup**: `n_p > 0`.  The positivity
    underlying every Third-Sylow statement (`n_p ≡ 1 mod p`, `n_p ∣ [G:P]`): the set of
    Sylow p-subgroups is nonempty (`Sylow.nonempty`, the First Sylow Theorem), hence its
    cardinality is positive.  Records the base fact that `sylow_count_mod_p` implicitly
    relies on. -/
theorem sylow_count_pos (p : ℕ) [hp : Fact p.Prime] : 0 < Nat.card (Sylow p G) :=
  Nat.card_pos_iff.mpr ⟨Sylow.nonempty, inferInstance⟩

/-- **Subgroup form of Cauchy's theorem**: if `p ∣ |G|` then `G` has a subgroup of order
    exactly `p`.  This is the `k = 1` case of `partial_converse_lagrange` (`p¹ ∣ |G|`), the
    subgroup companion to `cauchy_theorem` (which produces an *element* of order `p`; the
    cyclic group it generates is precisely such a subgroup). -/
theorem exists_subgroup_card_prime (p : ℕ) [hp : Fact p.Prime] (h : p ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p := by
  obtain ⟨H, hH⟩ := partial_converse_lagrange p 1 (by rwa [pow_one])
  exact ⟨H, by rwa [pow_one] at hH⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: A CAPSTONE APPLICATION — GROUPS OF ORDER p·q ARE NOT SIMPLE

The Third-Sylow counting data (`sylow_count_mod_p`, `sylow_count_dvd_index`,
`sylow_count_eq_one_or_prime`) together with the normality criterion
(`sylow_normal_iff_card_eq_one`) yields the classical structural fact that a
group of order `p·q` with `p < q` prime always has a *normal* — hence unique —
Sylow q-subgroup, so it is never simple.  This is the archetypal use of Sylow
theory as a structure engine, going strictly beyond what any divisibility count
alone provides: it is a genuine consequence about the *lattice of subgroups*,
not merely about orders.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- In a group of order `p·q` with `p < q` prime, the top Sylow prime `q` divides
    `|G|` to the first power only, so the Sylow q-subgroup has order exactly `q`.
    (From `sylow_card_eq`: `|Q| = q^(vq(|G|))` and `v_q(p·q) = 1` since `q ∤ p`.) -/
theorem card_sylow_q_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (Q : Sylow q G) (hG : Nat.card G = p * q) :
    Nat.card Q = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqp : ¬ q ∣ p := fun hdvd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd) (ne_of_gt hpq)
  have hfact : (Nat.card G).factorization q = 1 := by
    rw [hG, Nat.factorization_mul hp.pos.ne' hq.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqp, hq.factorization_self, zero_add]
  rw [sylow_card_eq, hfact, pow_one]

/-- **Groups of order `p·q` are not simple** (structural form): if `|G| = p·q` with
    `p < q` prime, the Sylow q-subgroup is normal.

    Proof: `n_q ∣ [G:Q]` and `[G:Q] = p` (Lagrange, since `|Q| = q`), so `n_q ∣ p`
    and hence `n_q ∈ {1, p}` (`sylow_count_eq_one_or_prime`).  But `n_q ≡ 1 (mod q)`
    (`sylow_count_mod_p`) while `p < q` forces `p % q = p ≠ 1`, ruling out `n_q = p`.
    Therefore `n_q = 1`, and `Q` is normal by the normality criterion
    (`sylow_normal_iff_card_eq_one`). -/
theorem sylow_q_normal_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (Q : Sylow q G) (hG : Nat.card G = p * q) :
    Q.Normal := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- The index [G : Q] equals p (Lagrange with |Q| = q).
  have hcardQ : Nat.card Q.toSubgroup = q := card_sylow_q_of_card_eq_pq p q hp hq hpq Q hG
  have hidx : Q.toSubgroup.index = p := by
    have hlag := lagrange_index Q.toSubgroup
    rw [hcardQ, hG, mul_comm p q] at hlag
    exact (Nat.eq_of_mul_eq_mul_left hq.pos hlag).symm
  -- n_q divides p.
  have hdvd : Nat.card (Sylow q G) ∣ p := by
    have h := sylow_count_dvd_index (G := G) q Q
    rwa [hidx] at h
  -- n_q = 1 or n_q = p; the latter contradicts n_q ≡ 1 (mod q).
  rcases sylow_count_eq_one_or_prime (G := G) q p hp hdvd with h1 | hpeq
  · exact (sylow_normal_iff_card_eq_one (G := G) q Q).mpr h1
  · exfalso
    have hmod := sylow_count_mod_p (G := G) q
    rw [hpeq, Nat.mod_eq_of_lt hpq] at hmod
    exact hp.one_lt.ne' hmod

/-- **Every group of order `p·q` (with `p < q` prime) has a normal subgroup of order
    `q`.** Existence form of `sylow_q_normal_of_card_eq_pq`: rather than assume a Sylow
    q-subgroup is given, invoke `sylow_exists` to produce one, then package its exact
    order `q` (`card_sylow_q_of_card_eq_pq`) with its normality
    (`sylow_q_normal_of_card_eq_pq`).  This is the clean structural statement — a normal
    subgroup of the top prime order always exists — with no Sylow object in the
    signature. -/
theorem exists_normal_subgroup_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hG : Nat.card G = p * q) :
    ∃ H : Subgroup G, H.Normal ∧ Nat.card H = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q⟩ := sylow_exists (G := G) q
  exact ⟨Q.toSubgroup,
    sylow_q_normal_of_card_eq_pq p q hp hq hpq Q hG,
    card_sylow_q_of_card_eq_pq p q hp hq hpq Q hG⟩

/-- **No group of order `p·q` is simple** (`p < q` prime).  The normal subgroup `H` of
    order `q` from `exists_normal_subgroup_card_eq_pq` is neither trivial (`|H| = q > 1`)
    nor the whole group (`|H| = q < p·q = |G|`, as `p ≥ 2`), so it witnesses a proper
    nontrivial normal subgroup — contradicting the definition of a simple group.  This is
    the headline consequence of Sylow III for the `pq` case: the smallest genuinely
    composite orders `6, 10, 14, 15, 21, …` all fail to be simple, the first structural
    obstruction beyond prime order in the classification of finite simple groups. -/
theorem not_isSimpleGroup_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hG : Nat.card G = p * q) : ¬ IsSimpleGroup G := by
  obtain ⟨H, hHnorm, hHcard⟩ := exists_normal_subgroup_card_eq_pq p q hp hq hpq hG
  intro hsimple
  rcases hsimple.eq_bot_or_eq_top_of_normal H hHnorm with hbot | htop
  · -- `H = ⊥` would force `q = |H| = 1`, impossible for a prime `q`.
    rw [hbot, Subgroup.card_bot] at hHcard
    exact hq.one_lt.ne' hHcard.symm
  · -- `H = ⊤` would force `p·q = |G| = |H| = q`, i.e. `p = 1`, impossible for a prime `p`.
    rw [htop, Subgroup.card_top, hG] at hHcard
    exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_right hq.pos (hHcard.trans (one_mul q).symm))

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
  - Capstone: groups of order p·q (p < q) have a normal Sylow q-subgroup, hence a
    normal subgroup of order q, hence are NOT simple (¬ IsSimpleGroup) — a genuine
    structural consequence of Sylow III

  **Status**: Verified, 0 sorries, 0 axioms
-/
