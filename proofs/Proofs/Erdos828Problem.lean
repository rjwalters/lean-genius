/-
Erdős Problem #828: Totient Divisibility φ(n) | n + a

Source: https://erdosproblems.com/828
Status: OPEN

Statement:
For any integer a ∈ ℤ, are there infinitely many n such that φ(n) | n + a?

Key Cases:
- a = 0: φ(n) | n iff n ∈ {0, 1} or n = 2^a · 3^b (easy exercise)
- a = -1: φ(n) | n - 1 is Lehmer's conjecture (implies n is prime when n > 1)
- a = 1: φ(n) | n + 1 - many examples exist

Known Results:
- The a = 0 case is completely characterized
- Lehmer's conjecture (a = -1) remains open since 1932
- The general conjecture is attributed to Graham

References:
- Guy (2004), Problem B37
- Erdős [Er83]
- Lehmer (1932)
-/

import Mathlib

set_option maxHeartbeats 400000

open Nat Set

namespace Erdos828

/- ## Part I: Basic Definitions -/

/-- The set of n where φ(n) | n + a. -/
def totientDivisors (a : ℤ) : Set ℕ :=
  {n : ℕ | (totient n : ℤ) ∣ (n : ℤ) + a}

/- ## Part II: Special Case a = 0 -/

/-- For a > 0, φ(2^a · 3^b) divides 2^a · 3^b. -/
private lemma totient_dvd_two_pow_mul_three_pow (a : ℕ) (ha : 0 < a) (b : ℕ) :
    totient (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b := by
  cases b with
  | zero =>
    simp only [pow_zero, mul_one]
    rw [Nat.totient_prime_pow Nat.prime_two ha]
    simp only [show (2 : ℕ) - 1 = 1 from rfl, mul_one]
    exact pow_dvd_pow 2 (by omega)
  | succ b =>
    have hcop : Nat.Coprime (2 ^ a) (3 ^ (b + 1)) :=
      (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 3)).pow_right (b + 1)
    rw [Nat.totient_mul hcop,
        Nat.totient_prime_pow Nat.prime_two ha,
        Nat.totient_prime_pow Nat.prime_three (by omega : 0 < b + 1)]
    simp only [show (2 : ℕ) - 1 = 1 from rfl, mul_one, show (3 : ℕ) - 1 = 2 from rfl]
    have h2a : 2 ^ (a - 1) * 2 = 2 ^ a := by
      nth_rewrite 2 [show (2 : ℕ) = 2 ^ 1 from rfl]
      rw [← pow_add, Nat.sub_add_cancel (by omega : 1 ≤ a)]
    calc 2 ^ (a - 1) * (3 ^ b * 2)
        = 2 ^ (a - 1) * 2 * 3 ^ b := by ring
      _ = 2 ^ a * 3 ^ b := by rw [h2a]
      _ ∣ 2 ^ a * 3 ^ (b + 1) :=
          Nat.mul_dvd_mul_left _ (pow_dvd_pow 3 (by omega))

/-- If p is an odd prime with (p-1) | 2p, then p = 3. -/
private lemma odd_prime_of_pred_dvd_two_mul (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (h : (p - 1) ∣ 2 * p) : p = 3 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hcop : Nat.Coprime (p - 1) p :=
    (hp.coprime_iff_not_dvd.mpr (fun hdvd =>
      absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))).symm
  have h2 : (p - 1) ∣ 2 := hcop.dvd_of_dvd_mul_right h
  have hp3 : p ≤ 3 := by have := Nat.le_of_dvd (by omega) h2; omega
  interval_cases p <;> simp_all [Nat.Prime]

/- ## Helper lemmas for forward direction -/

/-- 0 < n.factorization p when p is prime and p | n with n ≠ 0. -/
private lemma factorization_pos_of_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) :
    0 < n.factorization p := by
  rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
  exact Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩

/-- p^(n.factorization p) divides n for prime p and n ≠ 0. -/
private lemma pow_factorization_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ^ (n.factorization p) ∣ n :=
  (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mpr le_rfl

/-- If p is prime and e = n.factorization p, then p^e and n/p^e are coprime. -/
private lemma coprime_pow_factorization_div {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    Nat.Coprime (p ^ (n.factorization p)) (n / p ^ (n.factorization p)) := by
  -- First prove Coprime p (n / p^e), then lift to Coprime (p^e) (n/p^e)
  have hbase : Nat.Coprime p (n / p ^ (n.factorization p)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hp_dvd
    have hpow := pow_factorization_dvd hp hn
    have hdecomp : n = p ^ (n.factorization p) * (n / p ^ (n.factorization p)) :=
      (Nat.mul_div_cancel' hpow).symm
    have h_dvd : p ^ (n.factorization p + 1) ∣ n := by
      obtain ⟨k, hk⟩ := hp_dvd
      refine ⟨k, ?_⟩
      conv_lhs => rw [hdecomp, hk]
      rw [pow_succ]; ring
    have h_le := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp h_dvd
    exact absurd h_le (by omega)
  exact hbase.pow_left _

/-- For prime p dividing n (with n ≠ 0): (p-1) | φ(n). -/
private lemma pred_dvd_totient_of_prime_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hne : n ≠ 0) : (p - 1) ∣ totient n := by
  have he_pos := factorization_pos_of_dvd hp hpn hne
  have hpow_dvd := pow_factorization_dvd hp hne
  have hcop := coprime_pow_factorization_div hp hne
  have hdecomp : n = p ^ (n.factorization p) * (n / p ^ (n.factorization p)) :=
    (Nat.mul_div_cancel' hpow_dvd).symm
  calc (p - 1) ∣ p ^ (n.factorization p - 1) * (p - 1) := dvd_mul_left _ _
    _ ∣ totient (p ^ (n.factorization p)) := by rw [Nat.totient_prime_pow hp he_pos]
    _ ∣ totient (p ^ (n.factorization p)) * totient (n / p ^ (n.factorization p)) := dvd_mul_right _ _
    _ = totient n := by rw [← Nat.totient_mul hcop, ← hdecomp]

/-- 2 divides p-1 for any odd prime p. -/
private lemma two_dvd_pred_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ∣ (p - 1) := by
  have hp_not_even : ¬ Even p := by
    intro ⟨k, hk⟩
    have := hp.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩
    omega
  exact (Nat.even_sub (show 1 ≤ p from by have := hp.two_le; omega) |>.mpr
    (iff_of_false hp_not_even not_even_one)).two_dvd

/-- If m is odd then 4 does not divide 2*m. -/
private lemma four_not_dvd_two_mul_odd {m : ℕ} (hm_odd : ¬ 2 ∣ m) : ¬ (4 ∣ 2 * m) := by
  intro ⟨k, hk⟩; exact hm_odd ⟨k, by omega⟩

/-- If m is odd, m > 1, and φ(m) | 2m, then m is a power of 3. -/
private lemma odd_totient_dvd_two_mul {m : ℕ} (hm_pos : 0 < m) (hm_ne1 : m ≠ 1)
    (hm_odd : ¬ 2 ∣ m) (hdvd : totient m ∣ 2 * m) :
    ∃ e : ℕ, 0 < e ∧ m = 3 ^ e := by
  have hm_ne : m ≠ 0 := by omega
  -- Get a prime factor of m
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm_ne1
  have hp2 : p ≠ 2 := fun h => by subst h; exact hm_odd hpm
  -- Step 1: m has exactly one distinct prime factor (otherwise 4 | φ(m) | 2m, contradiction)
  have hunique : m.primeFactors = {p} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp, hpm, hm_ne⟩, fun r hr => ?_⟩
    rw [Nat.mem_primeFactors] at hr
    obtain ⟨hr_prime, hrm, -⟩ := hr
    by_contra hne
    have hr2 : r ≠ 2 := fun h => by subst h; exact hm_odd hrm
    -- Extract p-part: m = p^ep * mp with coprime parts
    have hpow_dvd := pow_factorization_dvd hp hm_ne
    have hcop := coprime_pow_factorization_div hp hm_ne
    have hdecomp : m = p ^ (m.factorization p) * (m / p ^ (m.factorization p)) :=
      (Nat.mul_div_cancel' hpow_dvd).symm
    -- φ(m) = φ(p^ep) * φ(mp)
    have htot_split : totient m = totient (p ^ (m.factorization p)) *
        totient (m / p ^ (m.factorization p)) := by
      rw [← Nat.totient_mul hcop, ← hdecomp]
    -- 2 | φ(p^ep) since p is odd
    have h2_phi_p : 2 ∣ totient (p ^ (m.factorization p)) := by
      rw [Nat.totient_prime_pow hp (factorization_pos_of_dvd hp hpm hm_ne)]
      exact dvd_mul_of_dvd_right (two_dvd_pred_of_odd_prime hp hp2) _
    -- r divides mp := m / p^ep (r | m and r coprime to p)
    have hr_mp : r ∣ m / p ^ (m.factorization p) := by
      have hrdvd : r ∣ p ^ (m.factorization p) * (m / p ^ (m.factorization p)) :=
        hdecomp ▸ hrm
      have hrcop : Nat.Coprime r (p ^ (m.factorization p)) := by
        apply Nat.Coprime.pow_right
        rw [Nat.Prime.coprime_iff_not_dvd hr_prime]
        intro hrd
        exact hne (hp.eq_one_or_self_of_dvd r hrd |>.resolve_left hr_prime.one_lt.ne')
      exact (Nat.Coprime.dvd_of_dvd_mul_left hrcop) hrdvd
    have hmp_ne : m / p ^ (m.factorization p) ≠ 0 := by
      intro h; rw [h, mul_zero] at hdecomp; omega
    -- 2 | φ(mp) since r is an odd prime dividing mp
    have h2_phi_mp : 2 ∣ totient (m / p ^ (m.factorization p)) :=
      dvd_trans (two_dvd_pred_of_odd_prime hr_prime hr2)
        (pred_dvd_totient_of_prime_dvd hr_prime hr_mp hmp_ne)
    -- 4 | φ(m), contradicting 4 ∤ 2m (since m odd)
    have h4 : 4 ∣ totient m := by
      rw [htot_split, show (4 : ℕ) = 2 * 2 from rfl]
      exact Nat.mul_dvd_mul h2_phi_p h2_phi_mp
    exact absurd (dvd_trans h4 hdvd) (four_not_dvd_two_mul_odd hm_odd)
  -- Step 2: m = p^e since p is the only prime factor
  have he_pos := factorization_pos_of_dvd hp hpm hm_ne
  have hm_eq : m = p ^ (m.factorization p) := by
    have h := Nat.factorization_prod_pow_eq_self hm_ne
    rw [Finsupp.prod, show m.factorization.support = {p} from by
      rwa [Nat.support_factorization], Finset.prod_singleton] at h
    exact h.symm
  -- Step 3: (p-1) | 2p, so p = 3
  have h_pred : (p - 1) ∣ 2 * p := by
    -- φ(p^e) = p^(e-1)*(p-1) | 2*p^e, and 2*p^e = p^(e-1) * (2*p)
    have hdvd' : p ^ (m.factorization p - 1) * (p - 1) ∣ 2 * p ^ (m.factorization p) := by
      rwa [← Nat.totient_prime_pow hp he_pos, ← hm_eq]
    have hp_eq : p ^ (m.factorization p) = p ^ (m.factorization p - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m.factorization p)]
    have hrewrite : 2 * p ^ (m.factorization p) = p ^ (m.factorization p - 1) * (2 * p) := by
      rw [hp_eq]; ring
    rw [hrewrite] at hdvd'
    exact (Nat.mul_dvd_mul_iff_left
      (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero))).mp hdvd'
  have hp3 : p = 3 := odd_prime_of_pred_dvd_two_mul p hp hp2 h_pred
  subst hp3
  exact ⟨m.factorization 3, he_pos, hm_eq⟩

/-- Characterization: φ(n) | n iff n ≤ 1 or n = 2^a · 3^b for some a > 0. -/
theorem totient_dvd_self_iff (n : ℕ) :
    totient n ∣ n ↔ n ≤ 1 ∨ ∃ a > 0, ∃ b : ℕ, n = 2^a * 3^b := by
  constructor
  · intro hdvd
    by_cases hn1 : n ≤ 1
    · left; exact hn1
    right; push_neg at hn1; have hn2 : 2 ≤ n := by omega
    have hne : n ≠ 0 := by omega
    -- n must be even: φ(n) is even for n ≥ 3, and φ(n) | n forces 2 | n
    have heven : 2 ∣ n := by
      by_contra h2
      have : 2 ∣ totient n := by
        obtain ⟨k, hk⟩ := Nat.totient_even (show 3 ≤ n by omega)
        exact ⟨k, by omega⟩
      exact h2 (dvd_trans this hdvd)
    -- Extract the 2-part: n = 2^α * m with m odd, α ≥ 1
    have hα_pos := factorization_pos_of_dvd Nat.prime_two heven hne
    have h2pow_dvd := pow_factorization_dvd Nat.prime_two hne
    have hdecomp : n = 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) :=
      (Nat.mul_div_cancel' h2pow_dvd).symm
    -- m := n / 2^α is odd
    have hm_odd : ¬ 2 ∣ (n / 2 ^ (n.factorization 2)) := by
      intro h2m
      obtain ⟨k, hk⟩ := h2m
      have h_pow_dvd : 2 ^ (n.factorization 2 + 1) ∣ n := by
        refine ⟨k, ?_⟩
        conv_lhs => rw [hdecomp, hk]
        rw [pow_succ]; ring
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp h_pow_dvd
      omega
    -- Coprime(2^α, m) since 2 ∤ m
    have hcop : Nat.Coprime (2 ^ (n.factorization 2)) (n / 2 ^ (n.factorization 2)) := by
      have : Nat.Coprime 2 (n / 2 ^ (n.factorization 2)) := by
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; exact hm_odd
      exact this.pow_left _
    -- φ(n) = 2^(α-1) * φ(m), so φ(m) | 2m
    have htot_n : totient n = 2 ^ (n.factorization 2 - 1) *
        totient (n / 2 ^ (n.factorization 2)) := by
      have h1 := Nat.totient_mul hcop
      -- h1 : φ(2^α * m) = φ(2^α) * φ(m)
      rw [← hdecomp] at h1
      have h2 : totient (2 ^ (n.factorization 2)) = 2 ^ (n.factorization 2 - 1) := by
        rw [Nat.totient_prime_pow Nat.prime_two hα_pos]
        simp only [show (2 : ℕ) - 1 = 1 from rfl, mul_one]
      rw [h2] at h1; exact h1
    have hphi_m : totient (n / 2 ^ (n.factorization 2)) ∣ 2 * (n / 2 ^ (n.factorization 2)) := by
      have h2pow_pos : 0 < 2 ^ (n.factorization 2 - 1) :=
        Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
      -- Build a divisibility chain without rewriting n inside factorization
      have key : 2 ^ (n.factorization 2 - 1) * totient (n / 2 ^ (n.factorization 2)) ∣
          2 ^ (n.factorization 2 - 1) * (2 * (n / 2 ^ (n.factorization 2))) := by
        calc 2 ^ (n.factorization 2 - 1) * totient (n / 2 ^ (n.factorization 2))
            = totient n := htot_n.symm
          _ ∣ n := hdvd
          _ = 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) := hdecomp
          _ = 2 ^ (n.factorization 2 - 1) * (2 * (n / 2 ^ (n.factorization 2))) := by
              have : 2 ^ (n.factorization 2) = 2 ^ (n.factorization 2 - 1) * 2 := by
                rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n.factorization 2)]
              rw [this]; ring
      exact (Nat.mul_dvd_mul_iff_left h2pow_pos).mp key
    have hm_pos : 0 < n / 2 ^ (n.factorization 2) := by
      rcases Nat.eq_zero_or_pos (n / 2 ^ (n.factorization 2)) with h | h
      · rw [h, mul_zero] at hdecomp; omega
      · exact h
    by_cases hm1 : n / 2 ^ (n.factorization 2) = 1
    · refine ⟨n.factorization 2, hα_pos, 0, ?_⟩
      rw [pow_zero, mul_one]
      calc n = 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) := hdecomp
        _ = 2 ^ (n.factorization 2) * 1 := by rw [hm1]
        _ = 2 ^ (n.factorization 2) := by ring
    · obtain ⟨e, he_pos, hm_eq⟩ :=
        odd_totient_dvd_two_mul hm_pos hm1 hm_odd hphi_m
      refine ⟨n.factorization 2, hα_pos, e, ?_⟩
      calc n = 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) := hdecomp
        _ = 2 ^ (n.factorization 2) * 3 ^ e := by rw [hm_eq]
  · intro h
    rcases h with h_le | ⟨a, ha, b, rfl⟩
    · interval_cases n <;> simp [Nat.totient]
    · exact totient_dvd_two_pow_mul_three_pow a ha b

/-- The set {n : φ(n) | n} is infinite. -/
theorem totientDivisors_zero_infinite : (totientDivisors 0).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 2 ^ (k + 1))
  · intro k₁ k₂ h
    have := Nat.pow_right_injective (by norm_num : 1 < 2) h
    omega
  · intro k
    simp only [totientDivisors, Set.mem_setOf_eq, add_zero]
    have htot : totient (2 ^ (k + 1)) = 2 ^ k := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < k + 1)]
      simp only [show (2 : ℕ) - 1 = 1 from rfl, mul_one, Nat.add_sub_cancel]
    rw [htot]; norm_cast; exact pow_dvd_pow 2 (by omega)

/- ## Part III: Special Case a = -1 (Lehmer's Conjecture) -/

def lehmerConjecture : Prop :=
  ∀ n : ℕ, n > 1 → (totient n ∣ n - 1 ↔ n.Prime)

theorem prime_totient_dvd_pred (p : ℕ) (hp : p.Prime) : totient p ∣ p - 1 := by
  rw [totient_prime hp]

theorem totientDivisors_neg_one_infinite : (totientDivisors (-1)).Infinite := by
  apply Set.Infinite.mono (s := setOf Nat.Prime)
  · intro p hp
    simp only [totientDivisors, Set.mem_setOf_eq]
    rw [totient_prime hp]
    refine ⟨1, ?_⟩
    rw [mul_one, Nat.cast_sub hp.one_le]
    ring
  · exact Nat.infinite_setOf_prime

/- ## Part IV: The Main Conjecture -/

def erdos828Conjecture : Prop :=
  ∀ a : ℤ, (totientDivisors a).Infinite

/- ## Part V: Structural Properties -/

theorem totient_even_of_gt_two (n : ℕ) (hn : n > 2) : 2 ∣ totient n := by
  obtain ⟨k, hk⟩ := Nat.totient_even (show 3 ≤ n by omega)
  exact ⟨k, by omega⟩

theorem totient_prime' (p : ℕ) (hp : p.Prime) : totient p = p - 1 :=
  totient_prime hp

theorem totient_prime_pow_formula (p k : ℕ) (hp : p.Prime) (hk : k > 0) :
    totient (p^k) = p^(k-1) * (p - 1) :=
  Nat.totient_prime_pow hp hk

/- ## Part VI: Summary -/

theorem erdos_828_summary :
    (totientDivisors 0).Infinite ∧ (totientDivisors (-1)).Infinite :=
  ⟨totientDivisors_zero_infinite, totientDivisors_neg_one_infinite⟩

end Erdos828
