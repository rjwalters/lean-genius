import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Fermat
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.NormNum.Prime

/-!
# Gauss–Wantzel: the number-theoretic core (general `n`)

The Gauss–Wantzel theorem says a regular `n`-gon is constructible iff Euler's totient
`φ(n)` is a power of two, equivalently iff `n = 2^a · p₁ ⋯ p_r` for **distinct Fermat
primes** `pᵢ`.  The *geometric* half (constructibility ⇔ `φ(n)` a power of two) is
axiomatized in the parent entry `angle-trisection-oq-02-oq-02`, and a sibling
(`…-oq-02-oq-03-ext`) verifies the totient/power-of-two condition by **enumeration for
`n ≤ 50`**.

This entry proves the **general arithmetic characterization for arbitrary `n`** — the
purely number-theoretic skeleton on which the geometric theorem rests, with **0 axioms**:

* **Wantzel necessity** (`totient_pow2_structure`): if `φ(n)` is a power of two then every
  *odd* prime `p ∣ n` occurs to the **first power** (`n.factorization p = 1`, i.e. the odd
  part of `n` is squarefree) and has the **Fermat form** `p = 2^m + 1`.
* **Sharp form** (`odd_prime_factor_is_fermat`): combining with Mathlib's
  `Nat.pow_of_pow_add_prime`, every odd prime factor is a *genuine* Fermat prime
  `p = 2^(2^j) + 1`.
* **Gauss sufficiency** (`totient_pow2_two_pow_mul`): conversely, for any finset `s` of odd
  primes with `p − 1` a power of two, `φ(2^a · ∏_{p∈s} p)` is a power of two.
* A clean single-prime equivalence and worked instances (`15`, `2^4·3·5`) derived from the
  *general* theorems rather than `decide`.

All results are over arbitrary naturals; nothing is by case enumeration.
-/

namespace AngleTrisectionOQ02OQ02OQ02

open Nat

/-- A natural number is a power of two. -/
def IsPow2 (m : ℕ) : Prop := ∃ k : ℕ, m = 2 ^ k

theorem isPow2_one : IsPow2 1 := ⟨0, rfl⟩

/-- Powers of two are closed under multiplication. -/
theorem IsPow2.mul {a b : ℕ} (ha : IsPow2 a) (hb : IsPow2 b) : IsPow2 (a * b) := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨i + j, by rw [hi, hj, pow_add]⟩

/-- Any divisor of a power of two is itself a power of two. -/
theorem isPow2_of_dvd_pow2 {d k : ℕ} (h : d ∣ 2 ^ k) : IsPow2 d := by
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact ⟨j, hj⟩

/-- An odd power of two equals `1`. -/
theorem eq_one_of_odd_isPow2 {m : ℕ} (hodd : Odd m) (h : IsPow2 m) : m = 1 := by
  obtain ⟨k, hk⟩ := h
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero] at hk; exact hk
  · exfalso
    have heven : Even m := by rw [hk]; exact (Nat.even_pow).mpr ⟨even_two, hkpos.ne'⟩
    have h0 : m % 2 = 0 := Nat.even_iff.mp heven
    have h1 : m % 2 = 1 := Nat.odd_iff.mp hodd
    omega

-- ============================================================
-- SECTION I:  Wantzel necessity
-- ============================================================

/-- The totient of the prime-power part `p^(v_p n)` divides `φ(n)`; written out,
    `p^(e-1)·(p-1) ∣ φ(n)` where `e = v_p n ≥ 1`. -/
private theorem totient_primePow_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hdvd : p ∣ n) :
    p ^ (n.factorization p - 1) * (p - 1) ∣ Nat.totient n := by
  have he : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hdvd
  have hpe : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
  have h1 : Nat.totient (p ^ n.factorization p) ∣ Nat.totient n := Nat.totient_dvd_of_dvd hpe
  rwa [Nat.totient_prime_pow hp he] at h1

/-- **Wantzel necessity (arithmetic core).**  If `φ(n)` is a power of two, then every odd
    prime `p` dividing `n` occurs to the first power and has the Fermat form `p = 2^m + 1`.

    Equivalently: the odd part of a "constructible" `n` is squarefree, and each of its prime
    factors is a Fermat-form prime. -/
theorem totient_pow2_structure {n p : ℕ} (hn : n ≠ 0) (htot : IsPow2 (Nat.totient n))
    (hp : p.Prime) (hodd : p ≠ 2) (hdvd : p ∣ n) :
    n.factorization p = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1 := by
  obtain ⟨k, hk⟩ := htot
  have hdvd2 : p ^ (n.factorization p - 1) * (p - 1) ∣ 2 ^ k :=
    hk ▸ totient_primePow_dvd hn hp hdvd
  have hf1 : p ^ (n.factorization p - 1) ∣ 2 ^ k := (dvd_mul_right _ _).trans hdvd2
  have hf2 : (p - 1) ∣ 2 ^ k := (dvd_mul_left _ _).trans hdvd2
  have he : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hdvd
  refine ⟨?_, ?_⟩
  · -- squarefree at `p`: the multiplicity is exactly `1`
    by_contra hne
    have h2 : 2 ≤ n.factorization p := by omega
    have hple : p ∣ p ^ (n.factorization p - 1) := dvd_pow_self p (by omega)
    have hp2k : p ∣ 2 ^ k := hple.trans hf1
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hp2k
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
  · -- Fermat form: `p - 1` is a power of two
    obtain ⟨m, hm⟩ := isPow2_of_dvd_pow2 hf2
    have := hp.two_le
    exact ⟨m, by omega⟩

/-- **Sharp Wantzel necessity.**  Every odd prime factor of an `n` with `φ(n)` a power of two
    is a *genuine* Fermat prime `p = 2^(2^j) + 1`.

    This refines `totient_pow2_structure` using Mathlib's `Nat.pow_of_pow_add_prime`
    (`2^m + 1` prime ⟹ `m` is a power of two). -/
theorem odd_prime_factor_is_fermat {n p : ℕ} (hn : n ≠ 0) (htot : IsPow2 (Nat.totient n))
    (hp : p.Prime) (hodd : p ≠ 2) (hdvd : p ∣ n) :
    ∃ j : ℕ, p = 2 ^ (2 ^ j) + 1 := by
  obtain ⟨-, m, hm⟩ := totient_pow2_structure hn htot hp hodd hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hodd (by omega)
  have hPrime : (2 ^ m + 1).Prime := hm ▸ hp
  obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (a := 2) (n := m) (by norm_num) hm0 hPrime
  exact ⟨j, by rw [hm, hj]⟩

/-- Squarefree-at-odd-primes restatement of necessity. -/
theorem squarefree_odd_part_of_totient_pow2 {n p : ℕ} (hn : n ≠ 0)
    (htot : IsPow2 (Nat.totient n)) (hp : p.Prime) (hodd : p ≠ 2) (hdvd : p ∣ n) :
    ¬ p ^ 2 ∣ n := by
  intro hsq
  have h1 : n.factorization p = 1 := (totient_pow2_structure hn htot hp hodd hdvd).1
  have h2 : 2 ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).mp hsq
  omega

-- ============================================================
-- SECTION II:  Gauss sufficiency
-- ============================================================

/-- `φ(2^a)` is a power of two for every `a`. -/
theorem isPow2_totient_two_pow (a : ℕ) : IsPow2 (Nat.totient (2 ^ a)) := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simpa using isPow2_one
  · rw [Nat.totient_prime_pow Nat.prime_two h]
    exact ⟨a - 1, by rw [show (2 : ℕ) - 1 = 1 from rfl, mul_one]⟩

/-- **Gauss sufficiency (squarefree odd part).**  For a finset `s` of odd primes each having
    `p - 1` a power of two, `φ(∏_{p∈s} p)` is a power of two.  Distinctness of the primes
    (`Finset`) provides the required coprimality. -/
theorem totient_pow2_of_oddFermat_prod {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧ IsPow2 (p - 1)) :
    IsPow2 (Nat.totient (∏ p ∈ s, p)) := by
  classical
  revert hs
  induction s using Finset.induction with
  | empty => intro _; simpa using isPow2_one
  | @insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha]
    have hsa : ∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧ IsPow2 (p - 1) :=
      fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha' := hs a (Finset.mem_insert_self a s)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes ha'.1 (hsa q hq).1).mpr (by rintro rfl; exact ha hq)
    rw [Nat.totient_mul hcop]
    refine IsPow2.mul ?_ (ih hsa)
    rw [Nat.totient_prime ha'.1]
    exact ha'.2.2

/-- **Gauss sufficiency (full form).**  For any `a` and any finset `s` of odd primes with
    `p - 1` a power of two, `φ(2^a · ∏_{p∈s} p)` is a power of two — hence the corresponding
    regular polygon is constructible. -/
theorem totient_pow2_two_pow_mul (a : ℕ) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧ IsPow2 (p - 1)) :
    IsPow2 (Nat.totient (2 ^ a * ∏ p ∈ s, p)) := by
  have hcop2 : Nat.Coprime 2 (∏ p ∈ s, p) := by
    apply Nat.Coprime.prod_right
    intro q hq
    exact (Nat.coprime_primes Nat.prime_two (hs q hq).1).mpr ((hs q hq).2.1).symm
  have hcop : Nat.Coprime (2 ^ a) (∏ p ∈ s, p) := Nat.Coprime.pow_left a hcop2
  rw [Nat.totient_mul hcop]
  exact IsPow2.mul (isPow2_totient_two_pow a) (totient_pow2_of_oddFermat_prod hs)

-- ============================================================
-- SECTION III:  Single-prime equivalence and instances
-- ============================================================

/-- For an odd prime `p`: `φ(p)` is a power of two iff `p` is a Fermat-form prime
    `p = 2^m + 1`. -/
theorem totient_prime_pow2_iff {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    IsPow2 (Nat.totient p) ↔ ∃ m : ℕ, p = 2 ^ m + 1 := by
  constructor
  · intro htot
    exact (totient_pow2_structure hp.pos.ne' htot hp hodd dvd_rfl).2
  · rintro ⟨m, hm⟩
    rw [Nat.totient_prime hp]
    have := hp.two_le
    exact ⟨m, by omega⟩

/-- `3` is a Fermat-form prime: a hypothesis bundle for the sufficiency theorems. -/
theorem fermat_data_three : (3 : ℕ).Prime ∧ (3 : ℕ) ≠ 2 ∧ IsPow2 (3 - 1) :=
  ⟨by norm_num, by norm_num, ⟨1, by norm_num⟩⟩

/-- `5` is a Fermat-form prime. -/
theorem fermat_data_five : (5 : ℕ).Prime ∧ (5 : ℕ) ≠ 2 ∧ IsPow2 (5 - 1) :=
  ⟨by norm_num, by norm_num, ⟨2, by norm_num⟩⟩

/-- The `15`-gon is constructible: `φ(15)` is a power of two, derived from the **general**
    sufficiency theorem with `15 = 3 · 5` (distinct Fermat primes), not by `decide`. -/
theorem totient_15_pow2 : IsPow2 (Nat.totient 15) := by
  have hprod : (∏ p ∈ ({3, 5} : Finset ℕ), p) = 15 := by decide
  have h : IsPow2 (Nat.totient (∏ p ∈ ({3, 5} : Finset ℕ), p)) := by
    apply totient_pow2_of_oddFermat_prod
    intro p hp
    fin_cases hp
    · exact fermat_data_three
    · exact fermat_data_five
  rwa [hprod] at h

/-- The `240`-gon (`240 = 2^4 · 3 · 5`) is constructible, derived from the full sufficiency
    theorem. -/
theorem totient_240_pow2 : IsPow2 (Nat.totient 240) := by
  have hprod : 2 ^ 4 * ∏ p ∈ ({3, 5} : Finset ℕ), p = 240 := by decide
  have h : IsPow2 (Nat.totient (2 ^ 4 * ∏ p ∈ ({3, 5} : Finset ℕ), p)) := by
    apply totient_pow2_two_pow_mul
    intro p hp
    fin_cases hp
    · exact fermat_data_three
    · exact fermat_data_five
  rwa [hprod] at h

/-- The `7`-gon is **not** constructible: `7` is an odd prime factor of `7` that is *not* a
    Fermat-form prime, contradicting necessity. -/
theorem totient_7_not_pow2 : ¬ IsPow2 (Nat.totient 7) := by
  intro htot
  obtain ⟨m, hm⟩ := (totient_pow2_structure (by norm_num) htot (by norm_num) (by norm_num)
    (dvd_refl 7)).2
  -- 7 = 2^m + 1 forces 2^m = 6, impossible
  have h6 : 2 ^ m = 6 := by omega
  have hub : m < 3 := by
    by_contra hcon
    push_neg at hcon
    have : (8 : ℕ) ≤ 2 ^ m := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases m <;> norm_num at h6

end AngleTrisectionOQ02OQ02OQ02
