import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-
# OQ-03-OQ-02: Counting forces a normal Sylow subgroup, and Schur–Zassenhaus splits it

This entry (`sylow-theorem-oq-03-oq-02`) combines two ingredients the gallery
already records separately:

* the **Sylow counting bounds** `nₚ ≡ 1 [MOD p]` and `nₚ ∣ m` (third Sylow
  theorem), and
* the **Schur–Zassenhaus** complement theorem from the parent entry
  `sylow-theorem-oq-03` (`Subgroup.exists_right_complement'_of_coprime`).

## Mathematical content

For distinct primes `p < q`, in *any* group `G` of order `pq` the counting
congruences force the Sylow `q`-subgroup to be unique, hence normal: writing
`n_q = card (Sylow q G)`, we have `n_q ∣ p` and `n_q ≡ 1 [MOD q]`, so
`n_q ∈ {1, p}`; but `n_q = p` would give `q ∣ p - 1`, impossible since
`0 < p - 1 < q`. Therefore `n_q = 1`.

Because a Sylow subgroup is a Hall subgroup (`|Q|` is coprime to its index,
`Sylow.card_coprime_index`), Schur–Zassenhaus applies to the now-normal `Q`
with **no extra hypothesis**, producing a complement `K` of order `p`. Hence

  **every group of order `pq` is an internal semidirect product `G = Q ⋊ K`,**
  with `Q` cyclic of order `q` and `K` cyclic of order `p`.

This is *unconditional* in `p ∣ q - 1`: it holds for the nonabelian groups
(orders `6 = S₃`, `21`, …) just as for the cyclic ones, which is the new content
relative to the sibling `sylow-theorem-oq-01` (that entry proves `G` is *cyclic*
only when `p ∤ q - 1`, and leaves the nonabelian case as a stub). Here the
*splitting* is always available; cyclicity is the special case where the
complement also happens to be normal.

The file is self-contained: it re-derives the `n_q = 1` counting from Mathlib
(rather than importing the sibling structure), and invokes Schur–Zassenhaus
directly.
-/

namespace SylowTheoremOQ03OQ02

open scoped Classical
open Subgroup

variable {G : Type*} [Group G]

/-! ## Section I: counting forces `n_q = 1` -/

/-- In a group of order `p * q` (`p < q` primes), a Sylow `q`-subgroup has
order exactly `q`: the `q`-part of `p * q` is `q¹`. -/
theorem card_sylow_q {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite G]
    (hpq : p < q) (hcard : Nat.card G = p * q) (Q : Sylow q G) :
    Nat.card (Q : Subgroup G) = q := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hq0 : q ≠ 0 := hq.pos.ne'
  have hne : q ≠ p := (Nat.ne_of_lt hpq).symm
  have hnotdvd : ¬ q ∣ p := by
    intro hd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp q hd) with h1 | hqp
    · exact hq.one_lt.ne' h1
    · exact hne hqp
  have hfact : (Nat.card G).factorization q = 1 := by
    rw [hcard, Nat.factorization_mul hp0 hq0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnotdvd, hq.factorization_self,
      zero_add]
  rw [Q.card_eq_multiplicity, hfact, pow_one]

/-- The index of a Sylow `q`-subgroup in a group of order `p * q` is `p`. -/
theorem index_sylow_q {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite G]
    (hpq : p < q) (hcard : Nat.card G = p * q) (Q : Sylow q G) :
    (Q : Subgroup G).index = p := by
  have hq : q.Prime := Fact.out
  have hmul := (Q : Subgroup G).card_mul_index
  rw [card_sylow_q hpq hcard Q, hcard] at hmul
  -- `q * index = p * q = q * p`
  exact (Nat.eq_of_mul_eq_mul_left hq.pos (by rw [hmul]; ring)).symm

/-- **Counting Sylow's theorem forces uniqueness.**
For distinct primes `p < q`, any group of order `pq` has exactly one Sylow
`q`-subgroup. -/
theorem card_sylow_q_eq_one {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite G]
    (hpq : p < q) (hcard : Nat.card G = p * q) :
    Nat.card (Sylow q G) = 1 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q G))
  -- n_q divides the index p
  have hdvd : Nat.card (Sylow q G) ∣ p := by
    have := Q.card_dvd_index
    rwa [index_sylow_q hpq hcard Q] at this
  -- n_q ≡ 1 mod q
  have hmod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hp'
  · exact h1
  · -- n_q = p would give q ∣ p - 1, impossible
    exfalso
    rw [hp'] at hmod
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hqdvd : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp1).mp hmod.symm
    have hpos : 0 < p - 1 := by have := hp.two_le; omega
    have hle : q ≤ p - 1 := Nat.le_of_dvd hpos hqdvd
    omega

/-- The Sylow `q`-subgroup of a group of order `pq` (`p < q`) is normal. -/
theorem sylow_q_normal {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite G]
    (hpq : p < q) (hcard : Nat.card G = p * q) (Q : Sylow q G) :
    (Q : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow q G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_q_eq_one hpq hcard)).1
  exact Q.normal_of_subsingleton

/-! ## Section II: Schur–Zassenhaus splits the normal Sylow subgroup -/

/-- **Main structural theorem.**
For distinct primes `p < q`, every group of order `pq` is an internal
semidirect product `G = Q ⋊ K`: there is a *normal* Sylow `q`-subgroup `Q`
together with a complement `K` such that
`Q ⊓ K = ⊥`, `Q ⊔ K = ⊤`, `|Q| = q`, and `|K| = p`.

This is unconditional — it holds for the nonabelian groups of order `pq` as
well as the cyclic ones. -/
theorem exists_normal_sylow_complement {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [Finite G] (hpq : p < q) (hcard : Nat.card G = p * q) :
    ∃ (Q : Subgroup G) (K : Subgroup G), Q.Normal ∧ IsComplement' Q K ∧
      Q ⊓ K = ⊥ ∧ Q ⊔ K = ⊤ ∧ Nat.card Q = q ∧ Nat.card K = p := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q G))
  haveI hN : (Q : Subgroup G).Normal := sylow_q_normal hpq hcard Q
  -- Hall property: |Q| coprime to its index ⇒ Schur–Zassenhaus applies
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime Q.card_coprime_index
  have hQcard : Nat.card (Q : Subgroup G) = q := card_sylow_q hpq hcard Q
  refine ⟨(Q : Subgroup G), K, hN, hK, hK.isCompl.inf_eq_bot, hK.isCompl.sup_eq_top,
    hQcard, ?_⟩
  -- |Q| * |K| = |G| = p * q, and |Q| = q ⇒ |K| = p
  have hmul := hK.card_mul
  rw [hQcard, hcard] at hmul
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : q.Prime).pos (by rw [hmul]; ring)

/-- The factors of the semidirect decomposition are cyclic of prime order:
`G = Z/q ⋊ Z/p`. -/
theorem exists_cyclic_semidirect {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [Finite G] (hpq : p < q) (hcard : Nat.card G = p * q) :
    ∃ (Q : Subgroup G) (K : Subgroup G), Q.Normal ∧ IsComplement' Q K ∧
      Nat.card Q = q ∧ Nat.card K = p ∧ IsCyclic Q ∧ IsCyclic K := by
  obtain ⟨Q, K, hN, hK, _, _, hQ, hKc⟩ := exists_normal_sylow_complement hpq hcard
  exact ⟨Q, K, hN, hK, hQ, hKc, isCyclic_of_prime_card hQ, isCyclic_of_prime_card hKc⟩

/-- A group of order `pq` (`p < q` primes) is never simple: the normal Sylow
`q`-subgroup is a proper, nontrivial normal subgroup. -/
theorem not_isSimpleGroup {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite G]
    (hpq : p < q) (hcard : Nat.card G = p * q) : ¬ IsSimpleGroup G := by
  intro hsimple
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q G))
  haveI hN : (Q : Subgroup G).Normal := sylow_q_normal hpq hcard Q
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hQcard : Nat.card (Q : Subgroup G) = q := card_sylow_q hpq hcard Q
  rcases hsimple.eq_bot_or_eq_top_of_normal (Q : Subgroup G) hN with hbot | htop
  · -- |Q| = q > 1, so Q ≠ ⊥
    rw [hbot] at hQcard
    simp only [Subgroup.card_bot] at hQcard
    exact hq.one_lt.ne hQcard
  · -- |Q| = |G| = pq ≠ q since p > 1
    rw [htop, Subgroup.card_top, hcard] at hQcard
    have : p = 1 := by
      have hqpos : 0 < q := hq.pos
      nlinarith [hp.one_lt, hQcard]
    exact hp.one_lt.ne' this

/-! ## Section III: concrete small orders (including the nonabelian cases) -/

/-- Every group of order `6` splits as `Z/3 ⋊ K` with `|K| = 2`. This holds for
both `ℤ/6` and the nonabelian `S₃`. -/
theorem order_six_splits [Finite G] (hcard : Nat.card G = 6) :
    ∃ (Q : Subgroup G) (K : Subgroup G), Q.Normal ∧ IsComplement' Q K ∧
      Nat.card Q = 3 ∧ Nat.card K = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, K, hN, hK, _, _, hQ, hKc⟩ :=
    exists_normal_sylow_complement (p := 2) (q := 3) (by norm_num) (by rw [hcard])
  exact ⟨Q, K, hN, hK, hQ, hKc⟩

/-- Every group of order `21` splits as `Z/7 ⋊ K` with `|K| = 3` (the
nonabelian `Z/7 ⋊ Z/3` as well as `Z/21`). -/
theorem order_twentyone_splits [Finite G] (hcard : Nat.card G = 21) :
    ∃ (Q : Subgroup G) (K : Subgroup G), Q.Normal ∧ IsComplement' Q K ∧
      Nat.card Q = 7 ∧ Nat.card K = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Q, K, hN, hK, _, _, hQ, hKc⟩ :=
    exists_normal_sylow_complement (p := 3) (q := 7) (by norm_num) (by rw [hcard])
  exact ⟨Q, K, hN, hK, hQ, hKc⟩

/-- Every group of order `15` is not simple (it has a normal Sylow
`5`-subgroup), and in fact splits as `Z/5 ⋊ K`, `|K| = 3`. -/
theorem order_fifteen_splits [Finite G] (hcard : Nat.card G = 15) :
    ∃ (Q : Subgroup G) (K : Subgroup G), Q.Normal ∧ IsComplement' Q K ∧
      Nat.card Q = 5 ∧ Nat.card K = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, K, hN, hK, _, _, hQ, hKc⟩ :=
    exists_normal_sylow_complement (p := 3) (q := 5) (by norm_num) (by rw [hcard])
  exact ⟨Q, K, hN, hK, hQ, hKc⟩

end SylowTheoremOQ03OQ02
