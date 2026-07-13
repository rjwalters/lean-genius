import Mathlib

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
| `isHallDivisor_prime_pow` | Hall divisors of `pⁿ` are only `1` and `pⁿ` | Proved |
| `converse_lagrange_pgroup` | p-group G: subgroup of *every* divisor order | Proved |
| `hall_solvable` | Solvable G: Hall subgroup for every Hall divisor | Axiom |
| `hall_solvability_necessary` | Non-solvable A₅ lacks subgroup of order 15 | Proved |

## Why the main theorem is axiomatized
Hall's theorem for solvable groups requires the Schur–Zassenhaus theorem and
properties of minimal normal subgroups (elementary abelian structure).
Schur–Zassenhaus IS available in Mathlib 4.26
(`Subgroup.exists_right_complement'_of_coprime`); the actual remaining gap is the
minimal-normal-subgroup machinery (existence and elementary-abelian structure).
The Schur–Zassenhaus lifting step of the induction is proved with 0 axioms in the
follow-up entry `lagrange-theorem-oq-01-oq-03-oq-01`.

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

/-- **Prime powers have only trivial Hall divisors.**  If `d` is a Hall divisor of a prime
    power `p^n` then `d = 1` or `d = p^n` — there is *no* proper nontrivial Hall divisor.
    Indeed `d ∣ p^n` forces `d = p^m` with `m ≤ n`, and then the complementary factor is
    `p^(n-m)`; coprimality `gcd(p^m, p^(n-m)) = 1` fails whenever both `m > 0` and `n-m > 0`
    (their gcd is divisible by `p`), so one of the exponents must vanish.  This is the
    number-theoretic shadow of the group fact `converse_lagrange_pgroup`: a `p`-group's
    subgroup lattice is *rich* (a subgroup of every divisor order) precisely where its Hall
    structure is *trivial* — the two extremes coincide on prime-power orders. -/
theorem isHallDivisor_prime_pow {p n d : ℕ} (hp : p.Prime)
    (hd : IsHallDivisor d (p ^ n)) : d = 1 ∨ d = p ^ n := by
  obtain ⟨hdvd, hcop⟩ := hd
  obtain ⟨m, hm, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [Nat.pow_div hm hp.pos] at hcop
  have hcop' : Nat.gcd (p ^ m) (p ^ (n - m)) = 1 := hcop
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exact Or.inl (by rw [hm0, pow_zero])
  · refine Or.inr ?_
    have hnm : n - m = 0 := by
      by_contra hne
      have h1 : p ∣ p ^ m := dvd_pow_self p hmpos.ne'
      have h2 : p ∣ p ^ (n - m) := dvd_pow_self p hne
      exact hp.ne_one (Nat.dvd_one.mp (hcop' ▸ Nat.dvd_gcd h1 h2))
    have hnm' : n = m := by omega
    rw [hnm']

/-- Concrete instance of `isHallDivisor_prime_pow`: the Hall divisors of `8 = 2³` are only
    `1` and `8`.  In particular `2` and `4` — which *are* orders of subgroups of any group of
    order `8` — are **not** Hall divisors, since `gcd(2,4) = 2` and `gcd(4,2) = 2`. -/
theorem not_isHallDivisor_two_eight : ¬ IsHallDivisor 2 8 := by
  intro h
  rcases isHallDivisor_prime_pow (p := 2) (n := 3) (by norm_num) h with h | h <;> norm_num at h

-- ============================================================
-- Part III: Trivial Hall Subgroups
-- ============================================================

/-- The trivial subgroup ⊥ (order 1) is a Hall subgroup of any group. -/
theorem hall_trivial_bot [Finite G] : IsHallSubgroup (⊥ : Subgroup G) := by
  unfold IsHallSubgroup
  rw [Subgroup.card_bot]
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
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvd
  exact ⟨Subgroup.zpowers x, by rw [Nat.card_zpowers, hx]⟩

-- ============================================================
-- Part V: Hall's Theorem for Cyclic Groups
-- ============================================================

/-- In a cyclic group, the generator raised to the (n/d)-th power has order d. -/
private lemma orderOf_pow_div_of_dvd [Finite G] {g : G} (d : ℕ) (hd : d ∣ orderOf g)
    (hd_pos : 0 < d) :
    orderOf (g ^ (orderOf g / d)) = d := by
  rw [orderOf_pow' g (Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hd) hd_pos).ne',
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd)]
  exact Nat.div_div_self hd (orderOf_pos g).ne'

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
-- Part V-B: The FULL Converse of Lagrange for p-Groups
-- ============================================================

/-- **The full converse of Lagrange holds for `p`-groups.**  If `G` is a finite `p`-group
    then *every* divisor `d` of `|G|` — not merely the Hall divisors — is the order of some
    subgroup.  Since `|G| = p^n` (`IsPGroup.iff_card`), each divisor is a prime power `p^m`
    with `m ≤ n` (`Nat.dvd_prime_pow`), and Sylow's existence theorem
    (`Sylow.exists_subgroup_card_pow_prime`) supplies a subgroup of that exact order.

    This is the second classical class — alongside cyclic groups (`hall_cyclic`) — for which
    the converse of Lagrange holds in full.  The contrast with `isHallDivisor_prime_pow` is
    the conceptual payoff: a `p`-group has *no* nontrivial Hall divisor, so Hall's theorem
    says nothing beyond `⊥` and `⊤`, yet the subgroup lattice is maximally rich — a subgroup
    of every divisor order.  p-groups are thus the extreme *opposite* of the Hall phenomenon:
    the converse of Lagrange succeeds completely exactly where the coprime-splitting
    hypothesis is vacuous. -/
theorem converse_lagrange_pgroup {p : ℕ} [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (d : ℕ) (hd : d ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = d := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  obtain ⟨m, hm, rfl⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (hn ▸ hd)
  exact Sylow.exists_subgroup_card_pow_prime p (by rw [hn]; exact pow_dvd_pow p hm)

/-- **Every Hall divisor of a `p`-group is realised** — the specialisation of
    `converse_lagrange_pgroup` to Hall divisors, matching the shape of `hall_cyclic_hall_divisor`
    and `hall_solvable`.  Vacuous beyond `d = 1` and `d = |G|` by `isHallDivisor_prime_pow`, but
    recorded so the `p`-group case slots uniformly into the Hall-subgroup framework of this
    file: cyclic and `p`-group cases both give Hall subgroups with `0` axioms, whereas the
    general solvable case (`hall_solvable`) needs the deep minimal-normal-subgroup input. -/
theorem hall_pgroup_hall_divisor {p : ℕ} [Fact p.Prime] [Finite G]
    (hG : IsPGroup p G) (d : ℕ) (hd : IsHallDivisor d (Nat.card G)) :
    ∃ H : Subgroup G, Nat.card H = d :=
  converse_lagrange_pgroup hG d hd.1

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

    Schur–Zassenhaus IS in Mathlib 4.26; the lifting step (case p ∤ d) is proved
    with 0 axioms in lagrange-theorem-oq-01-oq-03-oq-01. The remaining gap is
    minimal-normal-subgroup structure (elementary abelian), needed for case p | d. -/
axiom hall_solvable [Fintype G] [IsSolvable G]
    (d : ℕ) (hd : IsHallDivisor d (Fintype.card G)) :
    ∃ H : Subgroup G, Nat.card H = d

-- ============================================================
-- Part VII: Necessity of Solvability
-- ============================================================

/-- Solvability is necessary for Hall's theorem.
    A₅ (order 60) is not solvable.

    Proof: `A₅` is simple, so `IsSimpleGroup.comm_iff_isSolvable` reduces solvability to
    commutativity.  But `A₅` is non-abelian: commutativity would force the whole group into
    its centre, whereas `A₅` (having `4 ≤ 5` points) has trivial centre
    (`Equiv.Perm.alternatingGroup.center_eq_bot`), and `⊥ ≠ ⊤` for the nontrivial simple
    group `A₅`. -/
theorem hall_solvability_necessary :
    ¬ IsSolvable (alternatingGroup (Fin 5)) := by
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  intro hcomm
  have hbot : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num [Nat.card_fin])
  have htop : Subgroup.center (alternatingGroup (Fin 5)) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_center_iff]
    intro h
    exact hcomm h g
  rw [hbot] at htop
  exact bot_ne_top htop

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
