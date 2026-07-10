/-
  Angle Trisection - OQ-02 / sub-01 / sub-03:
  The p-group Galois → power-of-p degree criterion (general prime)

  The parent `AngleTrisectionOQ02OQ01` proves, for the prime `2`, that a
  2-group Galois group forces the minimal-polynomial degree to be a power
  of 2 — the algebraic core of the impossibility of angle trisection.

  The argument never used anything special about `2`: it rests only on
  `natDegree ∣ |Gal|` together with `IsPGroup.iff_card`.  This file lifts
  the result to an **arbitrary prime `p`**:

      Gal(minpoly ℚ α) is a p-group  ⟹  natDegree(minpoly ℚ α) = p^k,

  and records the contrapositive non-constructibility criterion plus the
  concrete degree-3 obstruction behind the 60° trisection (cos 20° has
  minimal degree 3, which is not a power of 2).

  A general odd-degree obstruction (`odd_degree_gt_one_not_2group`) records
  that *any* algebraic real whose minimal polynomial has odd degree `> 1` has
  no 2-group Galois group — subsuming the degree-3 (cos 20°) case and covering
  degrees `5, 7, 9, …`.

  Parent: AngleTrisectionOQ02OQ01.lean (natDegree_dvd_card_gal, reused here)
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ01

open Polynomial AngleTrisectionOQ02OQ01

namespace AngleTrisectionOQ02OQ01OQ03

/-- **p-group Galois ⟹ degree divides a power of p.**
    Generalizes `galois_2group_implies_degree_pow2` to any prime `p`:
    `natDegree ∣ |Gal| = p^n`. -/
theorem galois_pgroup_implies_degree_pow_p (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime) (hGal : IsPGroup p (minpoly ℚ α).Gal) :
    ∃ n : ℕ, (minpoly ℚ α).natDegree ∣ p ^ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hirr := minpoly.irreducible hα
  have hdvd := natDegree_dvd_card_gal hirr
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hGal
  exact ⟨n, hn ▸ hdvd⟩

/-- **p-group Galois ⟹ degree IS a power of p.**
    Strengthens the divisibility to an equality via `Nat.dvd_prime_pow`. -/
theorem galois_pgroup_implies_degree_is_pow_p (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime) (hGal : IsPGroup p (minpoly ℚ α).Gal) :
    ∃ k : ℕ, (minpoly ℚ α).natDegree = p ^ k := by
  obtain ⟨n, hdvd⟩ := galois_pgroup_implies_degree_pow_p α hα hp hGal
  obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨m, hm⟩

/-- **Non-constructibility criterion (contrapositive).**
    If the minimal-polynomial degree of `α` is not a power of the prime `p`,
    then `Gal(minpoly ℚ α)` is not a p-group. -/
theorem not_pgroup_of_degree_ne_pow_p (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime)
    (h : ∀ k : ℕ, (minpoly ℚ α).natDegree ≠ p ^ k) :
    ¬ IsPGroup p (minpoly ℚ α).Gal := by
  intro hGal
  obtain ⟨k, hk⟩ := galois_pgroup_implies_degree_is_pow_p α hα hp hGal
  exact h k hk

/-- **The degree-3 obstruction.**
    An algebraic real whose minimal polynomial has degree `3` cannot have a
    2-group Galois group — this is precisely the obstruction making the 60°
    angle impossible to trisect (`cos 20°` has minimal degree `3`, and `3`
    is not a power of `2`). -/
theorem degree_three_not_2group (α : ℝ) (hα : IsIntegral ℚ α)
    (h3 : (minpoly ℚ α).natDegree = 3) :
    ¬ IsPGroup 2 (minpoly ℚ α).Gal := by
  refine not_pgroup_of_degree_ne_pow_p α hα Nat.prime_two (fun k hk => ?_)
  rw [h3] at hk
  -- `3 = 2 ^ k` is impossible: `2^0 = 1`, `2^1 = 2`, and `2^k ≥ 4` for `k ≥ 2`.
  have h2k : 2 ^ k ≠ 3 := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k <;> decide
    · have : 4 ≤ 2 ^ k := by
        calc (4 : ℕ) = 2 ^ 2 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
      omega
  exact h2k hk.symm

/-- **The general odd-degree obstruction.**
    Any algebraic real whose minimal polynomial has *odd* degree `> 1` has no
    2-group Galois group: an odd number `> 1` is never a power of `2`
    (`2^0 = 1`, and `2^k` is even for `k ≥ 1`).

    This generalizes `degree_three_not_2group` from the single degree `3` to
    every odd degree `3, 5, 7, 9, …`, and gives a clean sufficient condition
    for non-constructibility: an algebraic real of odd degree `> 1` cannot be
    constructed by straightedge and compass. -/
theorem odd_degree_gt_one_not_2group (α : ℝ) (hα : IsIntegral ℚ α)
    (hodd : Odd (minpoly ℚ α).natDegree) (hgt : 1 < (minpoly ℚ α).natDegree) :
    ¬ IsPGroup 2 (minpoly ℚ α).Gal := by
  refine not_pgroup_of_degree_ne_pow_p α hα Nat.prime_two (fun k hk => ?_)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: `2^0 = 1`, contradicting `natDegree > 1`.
    rw [hk0, pow_zero] at hk; omega
  · -- `k ≥ 1`: `2^k` is even, contradicting the odd degree.
    have heven : (2 ^ k) % 2 = 0 :=
      Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rw [hk, Nat.odd_iff] at hodd
    omega

/-- **The general prime-factor obstruction (master criterion).**
    If *any* prime `q ≠ p` divides `natDegree(minpoly ℚ α)`, then
    `Gal(minpoly ℚ α)` is not a `p`-group.  A `p`-group forces the degree to be
    a power of `p`, whose only prime factor is `p`; so a prime factor other than
    `p` rules out the `p`-group structure outright.

    This single statement subsumes both `degree_three_not_2group` (take
    `p = 2, q = 3`) and `odd_degree_gt_one_not_2group` (an odd degree `> 1` has
    an odd prime factor `q ≠ 2`), and — being stated for an arbitrary target
    prime `p` — also covers non-`p`-group obstructions for every other prime. -/
theorem not_pgroup_of_prime_dvd_degree_ne (α : ℝ) (hα : IsIntegral ℚ α)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q ≠ p)
    (hdvd : q ∣ (minpoly ℚ α).natDegree) :
    ¬ IsPGroup p (minpoly ℚ α).Gal := by
  refine not_pgroup_of_degree_ne_pow_p α hα hp (fun k hk => ?_)
  rw [hk] at hdvd
  -- `q ∣ p ^ k` with `q` prime forces `q ∣ p`, hence `q = p`, contradicting `q ≠ p`.
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd))

/-- **Re-derivation of the odd-degree obstruction from the master criterion.**
    An odd degree `> 1` has an odd prime divisor `q ≠ 2`; feeding it to
    `not_pgroup_of_prime_dvd_degree_ne` reproduces `odd_degree_gt_one_not_2group`
    and exhibits it as a special case of the general prime-factor obstruction. -/
theorem odd_degree_gt_one_not_2group' (α : ℝ) (hα : IsIntegral ℚ α)
    (hodd : Odd (minpoly ℚ α).natDegree) (hgt : 1 < (minpoly ℚ α).natDegree) :
    ¬ IsPGroup 2 (minpoly ℚ α).Gal := by
  obtain ⟨q, hq, hqdvd⟩ :=
    Nat.exists_prime_and_dvd (show (minpoly ℚ α).natDegree ≠ 1 by omega)
  have hq2 : q ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hodd
    omega
  exact not_pgroup_of_prime_dvd_degree_ne α hα Nat.prime_two hq hq2 hqdvd

/-- **A concrete instance at the prime 3.**
    Because the master criterion targets an arbitrary prime `p`, it produces
    obstructions for primes other than `2` as well: any algebraic real whose
    minimal-polynomial degree is *even* cannot have a `3`-group Galois group
    (`2 ≠ 3` and `2` divides the degree). -/
theorem even_degree_not_3group (α : ℝ) (hα : IsIntegral ℚ α)
    (hdvd : 2 ∣ (minpoly ℚ α).natDegree) :
    ¬ IsPGroup 3 (minpoly ℚ α).Gal :=
  not_pgroup_of_prime_dvd_degree_ne α hα (by norm_num) Nat.prime_two (by norm_num) hdvd

/-- **Prime rigidity: the p-group prime is an invariant of a nontrivial extension.**
    On any extension of degree `> 1`, the group `Gal(minpoly ℚ α)` can be a
    `p`-group for at most one prime `p`.  A `p`-group forces the degree to be a
    power of `p`; if the same group is also a `p'`-group the degree is likewise a
    power of `p'`, and a number `> 1` that is simultaneously a power of two primes
    must have those primes equal (`p ∣ p'^j` with `p` prime forces `p = p'`).

    This upgrades the forward criterion: not only does a `p`-group Galois group
    determine the *shape* of the degree (`p^k`), the prime `p` itself is pinned
    down — it is the unique prime dividing the degree, not a free parameter. -/
theorem pgroup_prime_unique (α : ℝ) (hα : IsIntegral ℚ α)
    {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hgt : 1 < (minpoly ℚ α).natDegree)
    (hP : IsPGroup p (minpoly ℚ α).Gal)
    (hP' : IsPGroup p' (minpoly ℚ α).Gal) :
    p = p' := by
  obtain ⟨k, hk⟩ := galois_pgroup_implies_degree_is_pow_p α hα hp hP
  obtain ⟨j, hj⟩ := galois_pgroup_implies_degree_is_pow_p α hα hp' hP'
  -- `k ≠ 0`, else `natDegree = p^0 = 1`, contradicting `natDegree > 1`.
  have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
  -- `p ∣ natDegree = p'^j`, and a prime dividing a prime power hits the base prime.
  have hpdvd : p ∣ (minpoly ℚ α).natDegree := hk ▸ dvd_pow_self p hk0
  rw [hj] at hpdvd
  exact (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hpdvd)

/-- **Two distinct primes force a trivial degree.**
    Contrapositive companion of `pgroup_prime_unique`: if `Gal(minpoly ℚ α)` is
    simultaneously a `p`-group and a `p'`-group for *distinct* primes `p ≠ p'`,
    then `natDegree(minpoly ℚ α) = 1` — the extension is trivial (`α` is
    rational).  Equivalently, a genuinely higher-degree algebraic real can be a
    `p`-group Galois extension for only one prime. -/
theorem pgroup_distinct_primes_degree_one (α : ℝ) (hα : IsIntegral ℚ α)
    {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p')
    (hP : IsPGroup p (minpoly ℚ α).Gal)
    (hP' : IsPGroup p' (minpoly ℚ α).Gal) :
    (minpoly ℚ α).natDegree = 1 := by
  obtain ⟨k, hk⟩ := galois_pgroup_implies_degree_is_pow_p α hα hp hP
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero] at hk; exact hk
  · exfalso
    have hgt : 1 < (minpoly ℚ α).natDegree := by
      rw [hk]
      calc 1 < p := hp.one_lt
        _ ≤ p ^ k := Nat.le_self_pow (by omega) p
    exact hne (pgroup_prime_unique α hα hp hp' hgt hP hP')

/-- **Intrinsic degree shape: a p-group Galois group forces a prime-power degree.**
    Independently of *which* prime `p` it is, `Gal(minpoly ℚ α)` being a `p`-group
    forces `natDegree(minpoly ℚ α)` to be either `1` (trivial extension) or a
    genuine prime power `p^k` (`k ≥ 1`).  This restates
    `galois_pgroup_implies_degree_is_pow_p` in the `p`-free Mathlib predicate
    `IsPrimePow`, so the conclusion no longer mentions the prime at all — the
    prime is recovered intrinsically as the unique prime factor of the degree
    (cf. `pgroup_prime_unique`). -/
theorem pgroup_degree_isPrimePow_or_one (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime) (hP : IsPGroup p (minpoly ℚ α).Gal) :
    (minpoly ℚ α).natDegree = 1 ∨ IsPrimePow (minpoly ℚ α).natDegree := by
  obtain ⟨k, hk⟩ := galois_pgroup_implies_degree_is_pow_p α hα hp hP
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · left; rw [hk, h0, pow_zero]
  · right; exact ⟨p, k, hp.prime, hpos, hk.symm⟩

/-- **Prime-free obstruction: a non-prime-power degree admits no p-group.**
    Contrapositive of `pgroup_degree_isPrimePow_or_one`: if `natDegree(minpoly ℚ α)`
    is neither `1` nor a prime power (e.g. it has two distinct prime factors like a
    degree of `6`, `10`, `12`, …), then `Gal(minpoly ℚ α)` is **not** a `p`-group for
    *any* prime `p`.  Unlike `not_pgroup_of_degree_ne_pow_p`, this needs no candidate
    prime `p` — a single arithmetic property of the degree rules out every `p`-group
    Galois structure at once, subsuming the two-distinct-prime-factors obstruction. -/
theorem not_pgroup_any_of_not_isPrimePow (α : ℝ) (hα : IsIntegral ℚ α)
    (h1 : (minpoly ℚ α).natDegree ≠ 1)
    (hpp : ¬ IsPrimePow (minpoly ℚ α).natDegree)
    {p : ℕ} (hp : p.Prime) :
    ¬ IsPGroup p (minpoly ℚ α).Gal := by
  intro hP
  rcases pgroup_degree_isPrimePow_or_one α hα hp hP with h | h
  · exact h1 h
  · exact hpp h

/-- **A nontrivial p-group Galois group forces `p` to divide the degree.**
    A `p`-group Galois group makes the degree `p^k`; nontriviality (`degree > 1`) forces
    `k ≥ 1`, so `p ∣ degree`.  This exposes as a named lemma the divisibility that the
    proof of `pgroup_prime_unique` uses internally, pinning the `p`-group prime down as a
    *divisor* of the degree — the cleanest positive form of the "which prime" constraint. -/
theorem prime_dvd_degree_of_pgroup (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime) (hgt : 1 < (minpoly ℚ α).natDegree)
    (hP : IsPGroup p (minpoly ℚ α).Gal) :
    p ∣ (minpoly ℚ α).natDegree := by
  obtain ⟨k, hk⟩ := galois_pgroup_implies_degree_is_pow_p α hα hp hP
  have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; omega
  rw [hk]; exact dvd_pow_self p hk0

/-- **The p-group prime must divide the degree (contrapositive, crispest form).**
    If the prime `p` does *not* divide `natDegree(minpoly ℚ α)` and the extension is
    nontrivial (`degree > 1`), then `Gal(minpoly ℚ α)` is not a `p`-group.  This is the
    tightest hypothesis form of the prime-factor obstruction — no dividing prime `q` need
    be exhibited — and generalises `odd_degree_gt_one_not_2group` (the `p = 2` case, where
    `2 ∤ degree` is exactly `degree` odd) to every prime `p`. -/
theorem not_pgroup_of_not_dvd_degree (α : ℝ) (hα : IsIntegral ℚ α)
    {p : ℕ} (hp : p.Prime) (hgt : 1 < (minpoly ℚ α).natDegree)
    (hndvd : ¬ p ∣ (minpoly ℚ α).natDegree) :
    ¬ IsPGroup p (minpoly ℚ α).Gal :=
  fun hP => hndvd (prime_dvd_degree_of_pgroup α hα hp hgt hP)

end AngleTrisectionOQ02OQ01OQ03
