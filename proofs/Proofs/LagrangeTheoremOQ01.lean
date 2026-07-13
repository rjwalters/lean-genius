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

/-- **The index of a Sylow p-subgroup equals `|G| / p^k`** where `p^k ‖ |G|`.
    Since `|P| = p^(vₚ|G|)` is the full p-power dividing `|G|` (`sylow_card_eq`),
    Lagrange `|G| = |P|·[G:P]` (`lagrange_index`) gives `[G:P] = |G| / p^(vₚ|G|)`.
    This identifies the abstract index with the concrete "p-free part" `|G|/p^k`
    appearing in the classical statement of the Third Sylow Theorem. -/
theorem sylow_index_eq_card_div_pow (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    P.toSubgroup.index = Nat.card G / p ^ (Nat.card G).factorization p := by
  have hlag : Nat.card G
      = p ^ (Nat.card G).factorization p * P.toSubgroup.index := by
    rw [← sylow_card_eq p P]; exact lagrange_index P.toSubgroup
  have hb : 0 < p ^ (Nat.card G).factorization p := pow_pos hp.out.pos _
  exact (Nat.div_eq_of_eq_mul_right hb hlag).symm

/-- **Sharp Third Sylow Theorem, `n_p ∣ |G|/p^k`.**  The classical divisibility stated in
    the file header (`n_p ∣ |G|/p^k`): the number of Sylow p-subgroups divides the p-free
    part `|G|/p^k` of the group order.  Combine `sylow_count_dvd_index` (`n_p ∣ [G:P]`) with
    the identification `[G:P] = |G|/p^k` (`sylow_index_eq_card_div_pow`).  Strictly sharper
    than `sylow_count_dvd_card` (`n_p ∣ |G|`), which discards the `p^k` factor. -/
theorem sylow_count_dvd_card_div_pow (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ Nat.card G / p ^ (Nat.card G).factorization p := by
  rw [← sylow_index_eq_card_div_pow p P]
  exact sylow_count_dvd_index p P

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

/-- **The Sylow q-subgroup of a group of order `p·q` is unique** (`n_q = 1`), `p < q`
    prime.  Immediate from its normality (`sylow_q_normal_of_card_eq_pq`) via the normality
    criterion (`sylow_normal_iff_card_eq_one`): a normal Sylow subgroup is the only one.
    This is the counting-level shadow of the structural non-simplicity result, and the exact
    input (`n_q = 1`) used when classifying groups of order `p·q`. -/
theorem card_sylow_q_eq_one_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (Q : Sylow q G) (hG : Nat.card G = p * q) :
    Nat.card (Sylow q G) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact (sylow_normal_iff_card_eq_one q Q).mp
    (sylow_q_normal_of_card_eq_pq p q hp hq hpq Q hG)

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

/-- **Every group of order `p·q` (with `p < q` prime) is solvable.**  From
    `exists_normal_subgroup_card_eq_pq` we obtain a normal subgroup `N` of order `q`; being of
    prime order it is cyclic (`isCyclic_of_prime_card`), hence abelian, hence solvable.  The
    quotient `G ⧸ N` then has order `p` by Lagrange (`card_eq_card_quotient_mul_card_subgroup`),
    so it too is of prime order, cyclic, and solvable.  Solvability lifts along the short exact
    sequence `1 → N → G → G ⧸ N → 1` via `solvable_of_ker_le_range` (with `ker (mk' N) = N =
    range N.subtype`).

    This strictly strengthens `not_isSimpleGroup_of_card_eq_pq`: groups of order `p·q` are not
    merely non-simple but genuinely solvable — with the `p·q` case now fully resolved, the
    smallest composite orders `6, 10, 14, 15, 21, …` are all solvable, a hands-on instance of
    the Feit–Thompson landscape (every group of odd — indeed here arbitrary — order `p·q` is
    solvable). -/
theorem isSolvable_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hG : Nat.card G = p * q) : IsSolvable G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨N, hNnorm, hNcard⟩ := exists_normal_subgroup_card_eq_pq p q hp hq hpq hG
  haveI : N.Normal := hNnorm
  -- `N` has prime order `q`, hence is cyclic, hence abelian, hence solvable.
  haveI : IsCyclic N := isCyclic_of_prime_card (p := q) hNcard
  haveI : IsSolvable N :=
    isSolvable_of_comm (fun a b => by letI := IsCyclic.commGroup (α := N); exact mul_comm a b)
  -- The quotient `G ⧸ N` has order `p` (Lagrange), hence is cyclic, hence solvable.
  have hquot : Nat.card (G ⧸ N) = p := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hG, hNcard] at hcard
    exact Nat.eq_of_mul_eq_mul_right hq.pos hcard.symm
  haveI : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (p := p) hquot
  haveI : IsSolvable (G ⧸ N) :=
    isSolvable_of_comm (fun a b => by letI := IsCyclic.commGroup (α := G ⧸ N); exact mul_comm a b)
  -- Lift solvability along `1 → N → G → G ⧸ N → 1`.
  exact solvable_of_ker_le_range (N.subtype) (QuotientGroup.mk' N)
    (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: THE SYLOW p-SIDE — THE `q ≢ 1 (mod p)` REGIME

Everything above pins down the *top* Sylow prime `q`: its Sylow subgroup is always
normal for `|G| = p·q`.  The *bottom* prime `p` is more delicate — its Sylow count
`n_p ≡ 1 (mod p)` divides `[G:P] = q`, so `n_p ∈ {1, q}`, and `n_p = q` is possible
precisely when `q ≡ 1 (mod p)` (e.g. `S₃` of order `2·3` has three Sylow 2-subgroups
since `3 ≡ 1 mod 2`).  Under the *complementary* arithmetic hypothesis `q ≢ 1 (mod p)`
the value `n_p = q` is excluded and the Sylow p-subgroup becomes normal too.  Together
with the (unconditional) normal Sylow q-subgroup this is exactly the input for the full
classification "`|G| = p·q` with `q ≢ 1 (mod p)` ⟹ `G` cyclic": two coprime normal
subgroups whose orders multiply to `|G|`.  This section formalises the p-side, the
symmetric counterpart of Part VI.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Symmetric to `card_sylow_q_of_card_eq_pq`: in a group of order `p·q` with `p < q`
    prime, the *bottom* prime `p` divides `|G|` to the first power only, so the Sylow
    p-subgroup has order exactly `p`.  (From `sylow_card_eq`: `|P| = p^(vₚ(|G|))` and
    `v_p(p·q) = 1` since `p ∤ q`, as `p < q` are distinct primes.) -/
theorem card_sylow_p_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (P : Sylow p G) (hG : Nat.card G = p * q) :
    Nat.card P = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpnq : ¬ p ∣ q := fun hdvd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd) (ne_of_lt hpq)
  have hfact : (Nat.card G).factorization p = 1 := by
    rw [hG, Nat.factorization_mul hp.pos.ne' hq.pos.ne', Finsupp.add_apply,
      hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hpnq, add_zero]
  rw [sylow_card_eq, hfact, pow_one]

/-- **The Sylow p-subgroup is normal when `q ≢ 1 (mod p)`** (`p < q` prime, `|G| = p·q`).
    Symmetric counterpart of `sylow_q_normal_of_card_eq_pq` for the *bottom* prime.

    Proof: `n_p ∣ [G:P]` and `[G:P] = q` (Lagrange, since `|P| = p`), so `n_p ∣ q`
    and hence `n_p ∈ {1, q}` (`sylow_count_eq_one_or_prime`).  But `n_p ≡ 1 (mod p)`
    (`sylow_count_mod_p`), so `n_p = q` would force `q ≡ 1 (mod p)`, excluded by the
    hypothesis `q % p ≠ 1`.  Therefore `n_p = 1`, and `P` is normal by the normality
    criterion (`sylow_normal_iff_card_eq_one`).  (The hypothesis is essential: `S₃` has
    order `2·3` with `3 % 2 = 1`, and its Sylow 2-subgroups are *not* normal.) -/
theorem sylow_p_normal_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hmod : q % p ≠ 1) (P : Sylow p G) (hG : Nat.card G = p * q) :
    P.Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- The index [G : P] equals q (Lagrange with |P| = p).
  have hcardP : Nat.card P.toSubgroup = p := card_sylow_p_of_card_eq_pq p q hp hq hpq P hG
  have hidx : P.toSubgroup.index = q := by
    have hlag := lagrange_index P.toSubgroup
    rw [hcardP, hG] at hlag
    exact (Nat.eq_of_mul_eq_mul_left hp.pos hlag).symm
  -- n_p divides q.
  have hdvd : Nat.card (Sylow p G) ∣ q := by
    have h := sylow_count_dvd_index (G := G) p P
    rwa [hidx] at h
  -- n_p = 1 or n_p = q; the latter would give q ≡ 1 (mod p), excluded by hypothesis.
  rcases sylow_count_eq_one_or_prime (G := G) p q hq hdvd with h1 | hqeq
  · exact (sylow_normal_iff_card_eq_one (G := G) p P).mpr h1
  · exfalso
    have hm := sylow_count_mod_p (G := G) p
    rw [hqeq] at hm
    exact hmod hm

/-- **The Sylow p-subgroup of a group of order `p·q` is unique** (`n_p = 1`) when
    `q ≢ 1 (mod p)`.  Symmetric counterpart of `card_sylow_q_eq_one_of_card_eq_pq`:
    immediate from p-side normality (`sylow_p_normal_of_card_eq_pq`) via the normality
    criterion.  With both `n_p = 1` and `n_q = 1` the group has a unique subgroup of each
    prime order — the counting input to the internal-direct-product decomposition. -/
theorem card_sylow_p_eq_one_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hmod : q % p ≠ 1) (P : Sylow p G) (hG : Nat.card G = p * q) :
    Nat.card (Sylow p G) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact (sylow_normal_iff_card_eq_one p P).mp
    (sylow_p_normal_of_card_eq_pq p q hp hq hpq hmod P hG)

/-- **A group of order `p·q` with `q ≢ 1 (mod p)` has a normal subgroup of order `p`.**
    Existence form of `sylow_p_normal_of_card_eq_pq`, symmetric to
    `exists_normal_subgroup_card_eq_pq`.  Combined with the unconditional normal subgroup of
    order `q` (Part VI), the group possesses normal subgroups of *both* prime orders — two
    coprime normal subgroups whose orders multiply to `|G|`.  This is exactly the hypothesis
    package from which the internal direct product `G ≅ (ℤ/p) × (ℤ/q) ≅ ℤ/pq` follows, i.e.
    the classification "`|G| = p·q`, `q ≢ 1 (mod p)` ⟹ `G` cyclic". -/
theorem exists_normal_subgroup_card_eq_p_of_card_eq_pq (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hmod : q % p ≠ 1) (hG : Nat.card G = p * q) :
    ∃ H : Subgroup G, H.Normal ∧ Nat.card H = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := sylow_exists (G := G) p
  exact ⟨P.toSubgroup,
    sylow_p_normal_of_card_eq_pq p q hp hq hpq hmod P hG,
    card_sylow_p_of_card_eq_pq p q hp hq hpq P hG⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART VIII: THE CLASSIFICATION CAPSTONE — `q ≢ 1 (mod p)` ⟹ `G` IS CYCLIC

Parts VI–VII produce, under `q ≢ 1 (mod p)`, normal subgroups of *both* prime
orders `p` and `q`.  Their orders are coprime, so the two subgroups intersect
trivially and (being normal) commute elementwise.  A generator `a` of the order-`p`
subgroup and a generator `b` of the order-`q` subgroup therefore commute and have
coprime orders, so `a·b` has order `p·q = |G|` — an element of full order, making
`G` cyclic.  This closes the classification of groups of order `p·q`: away from the
arithmetic obstruction `q ≡ 1 (mod p)` there is a *unique* group, the cyclic one
`ℤ/pq`.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Classification capstone: a group of order `p·q` with `q ≢ 1 (mod p)` is cyclic**
    (`p < q` prime).  This is the positive half of the order-`p·q` dichotomy and the
    payoff of the whole Sylow development in this file.

    Proof.  Parts VI–VII give normal subgroups `P` (order `p`) and `Q` (order `q`); each
    has prime order, hence is cyclic.  Let `a` generate `P` and `b` generate `Q`, so
    `orderOf a = p` and `orderOf b = q` (`Nat.card_zpowers`).  Because `|P ⊓ Q|` divides
    both `p` and `q`, which are coprime, it is `1`, so `P` and `Q` are `Disjoint`; two
    disjoint *normal* subgroups commute elementwise
    (`Subgroup.commute_of_normal_of_disjoint`), giving `Commute a b`.  Coprime orders of
    commuting elements multiply (`orderOf_mul_eq_mul_orderOf_of_coprime`), so
    `orderOf (a * b) = p · q = |G|`.  An element of order `|G|` generates the group
    (`isCyclic_of_orderOf_eq_card`), so `G` is cyclic.

    The hypothesis `q ≢ 1 (mod p)` is essential — it is exactly what forces the Sylow
    p-subgroup to be normal (Part VII).  Without it a nonabelian group exists (the
    metacyclic `ℤ/q ⋊ ℤ/p`, e.g. `S₃` for `p·q = 2·3` with `3 ≡ 1 mod 2`). -/
theorem isCyclic_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hmod : q % p ≠ 1) (hG : Nat.card G = p * q) : IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  -- Normal subgroups of both prime orders (Parts VI and VII).
  obtain ⟨P, hPnorm, hPcard⟩ :=
    exists_normal_subgroup_card_eq_p_of_card_eq_pq p q hp hq hpq hmod hG
  obtain ⟨Q, hQnorm, hQcard⟩ := exists_normal_subgroup_card_eq_pq p q hp hq hpq hG
  -- Each is cyclic (prime order); pick generators `a` and `b`.
  haveI : IsCyclic P := isCyclic_of_prime_card (p := p) hPcard
  haveI : IsCyclic Q := isCyclic_of_prime_card (p := q) hQcard
  obtain ⟨a, ha⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top P).mp inferInstance
  obtain ⟨b, hb⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Q).mp inferInstance
  have hao : orderOf a = p := by rw [← Nat.card_zpowers, ha, hPcard]
  have hbo : orderOf b = q := by rw [← Nat.card_zpowers, hb, hQcard]
  have haP : a ∈ P := ha ▸ Subgroup.mem_zpowers a
  have hbQ : b ∈ Q := hb ▸ Subgroup.mem_zpowers b
  -- Coprimality of the two prime orders.
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)
  -- `P` and `Q` are disjoint: `|P ⊓ Q|` divides both `p` and `q`, hence `1`.
  have hdis : Disjoint P Q := by
    rw [disjoint_iff, eq_bot_iff_card]
    have hdp : Nat.card (P ⊓ Q : Subgroup G) ∣ p := hPcard ▸ card_dvd_of_le inf_le_left
    have hdq : Nat.card (P ⊓ Q : Subgroup G) ∣ q := hQcard ▸ card_dvd_of_le inf_le_right
    have hg : Nat.gcd p q = 1 := hcop
    have := Nat.dvd_gcd hdp hdq
    rw [hg] at this
    exact Nat.dvd_one.mp this
  -- Disjoint normal subgroups commute elementwise, so the generators commute.
  have hcomm : Commute a b :=
    Subgroup.commute_of_normal_of_disjoint P Q hPnorm hQnorm hdis a b haP hbQ
  -- `a·b` has coprime commuting factors, so its order is `p·q = |G|`.
  have hord : orderOf (a * b) = Nat.card G := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hao, hbo]; exact hcop),
      hao, hbo, hG]
  exact isCyclic_of_orderOf_eq_card (a * b) hord

/-- **The full order-`p·q` dichotomy** (`p < q` prime): either `q ≡ 1 (mod p)` — the
    arithmetic regime that permits the nonabelian metacyclic group `ℤ/q ⋊ ℤ/p` — or `G`
    is cyclic.  Combines the two Sylow regimes: Part VII's obstruction `q ≡ 1 (mod p)` is
    the *only* way a group of order `p·q` can fail to be cyclic.  Together with
    `not_isSimpleGroup_of_card_eq_pq` and `isSolvable_of_card_eq_pq` this completes the
    structural picture of order-`p·q` groups. -/
theorem cyclic_or_q_mod_p_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hG : Nat.card G = p * q) : q % p = 1 ∨ IsCyclic G := by
  by_cases h : q % p = 1
  · exact Or.inl h
  · exact Or.inr (isCyclic_of_card_eq_pq p q hp hq hpq h hG)

/-- **Groups of order `p·q` with `q ≢ 1 (mod p)` are abelian** (`p < q` prime): the
    commutativity consequence of `isCyclic_of_card_eq_pq`.  A convenient elementwise form
    of the classification — every such group is (isomorphic to) `ℤ/pq`, in particular
    commutative. -/
theorem mul_comm_of_card_eq_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hmod : q % p ≠ 1) (hG : Nat.card G = p * q) (a b : G) :
    a * b = b * a := by
  haveI := isCyclic_of_card_eq_pq p q hp hq hpq hmod hG
  letI := IsCyclic.commGroup (α := G)
  exact mul_comm a b

/-
═══════════════════════════════════════════════════════════════════════════════
PART IX: GROUPS OF ORDER p² ARE ABELIAN
═══════════════════════════════════════════════════════════════════════════════

Part VIII settled the two-distinct-prime case (order `p·q`).  The remaining
two-prime-factor order is the prime *square* `p²`.  The contrast with order `p·q`
is the whole point: order `p·q` admits a nonabelian group exactly when
`q ≡ 1 (mod p)` (e.g. `S₃` at `2·3`), whereas **every** group of order `p²` is
abelian — no arithmetic side condition is needed.

The mechanism is the class equation for `p`-groups: a nontrivial finite `p`-group
has nontrivial centre, so for `|G| = p²` the centre `Z(G)` has order `p` or `p²`.
Either way the quotient `G ⧸ Z(G)` is cyclic (order `1` or `p`, both cyclic), and
a group whose central quotient is cyclic is abelian.  Mathlib packages the core
step as `IsPGroup.commutative_of_card_eq_prime_sq`; here we connect it to the
Sylow / Lagrange narrative and record the structural corollary at the proper
divisor `p`.
-/

/-- **Groups of order `p²` are abelian** (`p` prime).  In sharp contrast with the
    order-`p·q` case (Part VIII), which needs the arithmetic hypothesis `q ≢ 1 (mod p)`
    to force commutativity, *every* group whose order is the square of a prime is
    commutative — via `IsPGroup.commutative_of_card_eq_prime_sq`, itself powered by the
    class equation for `p`-groups (nontrivial centre ⟹ cyclic central quotient ⟹
    abelian). -/
theorem mul_comm_of_card_eq_prime_sq (p : ℕ) (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (a b : G) : a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.commutative_of_card_eq_prime_sq hG a b

/-- **Every subgroup of a group of order `p²` is normal.**  Immediate from
    `mul_comm_of_card_eq_prime_sq`: in an abelian group conjugation is trivial
    (`g * h * g⁻¹ = h`), so every subgroup is stable under conjugation.  This is the
    normality that Part VII had to *earn* arithmetically in the `p·q` case; here it comes
    for free from commutativity. -/
theorem normal_of_card_eq_prime_sq (p : ℕ) (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (H : Subgroup G) : H.Normal := by
  refine ⟨fun a ha g => ?_⟩
  have hconj : g * a * g⁻¹ = a := by
    rw [mul_comm_of_card_eq_prime_sq p hp hG g a, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]; exact ha

/-- **A group of order `p²` has a normal subgroup of order `p`** (`p` prime): the partial
    converse of Lagrange at the proper divisor `p`, with normality supplied for free by
    commutativity.  Cauchy's subgroup form (`exists_subgroup_card_prime`, the `k = 1` case
    of the Sylow partial converse) yields a subgroup of order `p` since `p ∣ p²`, and
    `normal_of_card_eq_prime_sq` makes it normal.  Consequently `1 ◁ H ◁ G` is a normal
    series with cyclic (prime-order) factors, exhibiting order-`p²` groups as abelian —
    hence solvable — with an explicit invariant subgroup at every divisor of `p²`. -/
theorem exists_normal_subgroup_card_eq_p_of_card_eq_prime_sq (p : ℕ) (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : ∃ H : Subgroup G, H.Normal ∧ Nat.card H = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card G := by rw [hG, sq]; exact dvd_mul_right p p
  obtain ⟨H, hHcard⟩ := exists_subgroup_card_prime p hdvd
  exact ⟨H, normal_of_card_eq_prime_sq p hp hG H, hHcard⟩

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
  - Solvability capstone: groups of order p·q (p < q) are solvable (IsSolvable G) —
    the normal N (order q) and quotient G ⧸ N (order p) are both cyclic hence
    solvable, and solvability lifts along 1 → N → G → G ⧸ N → 1
  - Sylow p-side (q ≢ 1 mod p regime): |P| = p, and when q ≢ 1 (mod p) the Sylow
    p-subgroup is normal (n_p = 1) with a normal subgroup of order p — the symmetric
    counterpart of the q-side and the coprime-normal-subgroup input for the full
    "p·q with q ≢ 1 mod p ⟹ cyclic" classification
  - Classification capstone (isCyclic_of_card_eq_pq): a group of order p·q with
    q ≢ 1 (mod p) is CYCLIC — the two coprime normal Sylow subgroups have commuting
    generators of coprime orders p, q, so their product has order p·q = |G|; hence the
    full dichotomy cyclic_or_q_mod_p_of_card_eq_pq (either q ≡ 1 mod p or G cyclic) and
    the abelian corollary mul_comm_of_card_eq_pq. Closes the order-p·q classification.
  - Order-p² classification (Part IX): EVERY group of order p² is abelian
    (mul_comm_of_card_eq_prime_sq) — no arithmetic side condition, in sharp contrast with
    order p·q. Corollaries: every subgroup is normal (normal_of_card_eq_prime_sq), and
    there is a normal subgroup of order p (exists_normal_subgroup_card_eq_p_of_card_eq_prime_sq),
    giving the normal series 1 ◁ H ◁ G with cyclic factors. Uses Mathlib's
    IsPGroup.commutative_of_card_eq_prime_sq (class equation for p-groups).

  **Status**: Verified, 0 sorries, 0 axioms
-/
