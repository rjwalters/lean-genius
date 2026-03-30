/-
# Erdős Problem #700: GCD of n with Binomial Coefficients

Erdős and Szekeres study f(n) = min_{1 < k ≤ n/2} gcd(n, C(n,k)).

Three questions:
1. Which composite n satisfy f(n) = n/P(n) where P(n) = largest prime factor?
2. Are there infinitely many composite n with f(n) > √n?
3. Is f(n) ≪_A n/(log n)^A for every A > 0 and all composite n?

Known:
- f(n) ≤ n/P(n) for all composite n
- f(n) = n/P(n) when n = pq (product of two primes) or n = 30
- f(n) ≥ p(n), the smallest prime factor of n
- f(p²) ≥ p = √n

Reference: https://erdosproblems.com/700
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Multiplicity

/- ## Definitions -/

/-- The largest prime factor of n. Returns 0 if n ≤ 1. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if _ : 2 ≤ n then
    Finset.sup ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n)) id
  else 0

/-- The smallest prime factor of n. -/
noncomputable def smallestPrimeFactor (n : ℕ) : ℕ :=
  Nat.minFac n

/-- f(n) = min_{1 < k ≤ n/2} gcd(n, C(n,k)).
    Defined for n ≥ 4 (where the range [2, n/2] is nonempty).
    Returns 0 for n < 4. -/
noncomputable def fBinom (n : ℕ) : ℕ :=
  if h : 4 ≤ n then
    ((Finset.Icc 2 (n / 2)).image (fun k => Nat.gcd n (Nat.choose n k))).min' (by
      apply Finset.Nonempty.image
      exact ⟨2, Finset.mem_Icc.mpr ⟨le_refl 2, by omega⟩⟩)
  else 0

/- ## Helper Lemmas -/

/-- The smallest prime factor of p² is p, for any prime p. -/
theorem minFac_prime_sq (p : ℕ) (hp : p.Prime) : Nat.minFac (p * p) = p := by
  have hpp : p * p ≠ 1 := by have := hp.two_le; nlinarith
  have hpf : (Nat.minFac (p * p)).Prime := Nat.minFac_prime hpp
  have hdvdp : Nat.minFac (p * p) ∣ p := by
    have h := Nat.minFac_dvd (p * p)
    have h2 : Nat.minFac (p * p) ∣ p ^ 2 := by convert h using 1; ring
    exact hpf.dvd_of_dvd_pow h2
  exact (hp.eq_one_or_self_of_dvd _ hdvdp).resolve_left (by have := hpf.one_lt; omega)

/-- minFac(p * q) = p for primes p ≤ q. -/
theorem minFac_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    Nat.minFac (p * q) = p := by
  have hpq_ne1 : p * q ≠ 1 := by have := hp.two_le; nlinarith
  have hpf := Nat.minFac_prime hpq_ne1
  have hdvd := Nat.minFac_dvd (p * q)
  rcases hpf.dvd_mul.mp hdvd with hp_dvd | hq_dvd
  · exact (hp.eq_one_or_self_of_dvd _ hp_dvd).resolve_left hpf.one_lt.ne'
  · have heq := (hq.eq_one_or_self_of_dvd _ hq_dvd).resolve_left hpf.one_lt.ne'
    have hle : Nat.minFac (p * q) ≤ p :=
      Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
    omega

/-- Any prime factor of n is ≤ largestPrimeFactor(n). -/
theorem le_largestPrimeFactor {n r : ℕ} (hr : r.Prime) (hdvd : r ∣ n) (hn : 2 ≤ n) :
    r ≤ largestPrimeFactor n := by
  unfold largestPrimeFactor
  simp only [hn, dite_true]
  have hr_le_n : r ≤ n := Nat.le_of_dvd (by omega) hdvd
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr, hdvd⟩)

/-- From the absorption identity: n divides k * C(n, k) for 1 ≤ k ≤ n.
    Uses Nat.succ_mul_choose_eq: (n+1) * C(n,k) = C(n+1,k+1) * (k+1). -/
private theorem n_dvd_k_mul_choose {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    n ∣ k * n.choose k := by
  have hn' : n - 1 + 1 = n := by omega
  have hk' : k - 1 + 1 = k := by omega
  have h := Nat.succ_mul_choose_eq (n - 1) (k - 1)
  rw [hn', hk'] at h
  -- h : n * (n - 1).choose (k - 1) = n.choose k * k
  exact ⟨(n - 1).choose (k - 1), by rw [mul_comm k]; exact h.symm⟩

/-- For n ≥ 4 and k ∈ [2, n/2], gcd(n, C(n,k)) ≥ minFac(n).
    Key idea: n/gcd(n,k) divides both n and C(n,k) (by coprime cancellation
    from the absorption identity), hence divides their gcd. Since gcd(n,k) ≤ k ≤ n/2 < n,
    the quotient n/gcd(n,k) ≥ minFac(n). -/
private theorem gcd_choose_ge_minFac {n k : ℕ} (hn : 4 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n / 2) :
    n.minFac ≤ Nat.gcd n (n.choose k) := by
  have hk_le_n : k ≤ n := le_trans hkn (Nat.div_le_self n 2)
  -- Step 1: n | k * C(n, k) from absorption identity
  have h_dvd := n_dvd_k_mul_choose (by omega : 1 ≤ n) (by omega : 1 ≤ k) hk_le_n
  -- Step 2: Setup gcd, derive (n/g) | C(n,k) by coprime cancellation
  set g := Nat.gcd n k
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left k (by omega)
  have hg_dvd_n := Nat.gcd_dvd_left n k
  have hg_dvd_k := Nat.gcd_dvd_right n k
  have hcop : Nat.Coprime (n / g) (k / g) := Nat.coprime_div_gcd_div_gcd hg_pos
  have hgk : g * (k / g) = k := by rw [mul_comm]; exact Nat.div_mul_cancel hg_dvd_k
  have hgn : g * (n / g) = n := by rw [mul_comm]; exact Nat.div_mul_cancel hg_dvd_n
  obtain ⟨m, hm⟩ := h_dvd
  have h_eq : k / g * n.choose k = n / g * m := by
    have h1 : g * (k / g * n.choose k) = g * (n / g * m) := by
      calc g * (k / g * n.choose k)
          = g * (k / g) * n.choose k := (mul_assoc g (k / g) (n.choose k)).symm
        _ = k * n.choose k := by rw [hgk]
        _ = n * m := hm
        _ = g * (n / g) * m := by rw [hgn]
        _ = g * (n / g * m) := mul_assoc g (n / g) m
    exact Nat.eq_of_mul_eq_mul_left hg_pos h1
  have h_nd_dvd_C : n / g ∣ n.choose k := hcop.dvd_of_dvd_mul_left ⟨m, h_eq⟩
  -- Step 3: (n/g) divides gcd(n, C(n,k))
  have h_nd_dvd_n : n / g ∣ n := ⟨g, (Nat.div_mul_cancel hg_dvd_n).symm⟩
  have h_nd_dvd_gcd : n / g ∣ Nat.gcd n (n.choose k) := Nat.dvd_gcd h_nd_dvd_n h_nd_dvd_C
  -- Step 4: gcd ≥ n/g ≥ minFac(n)
  have h_gcd_ge : n / g ≤ Nat.gcd n (n.choose k) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) h_nd_dvd_gcd
  have h_minFac_le : n.minFac ≤ n / g := by
    apply Nat.minFac_le_of_dvd
    · -- 2 ≤ n / g: since g ≤ k ≤ n/2 < n, if n/g ≤ 1 then n ≤ g ≤ n/2, contradiction
      by_contra h
      push_neg at h
      have hng1 : n / g ≤ 1 := by omega
      have hng : n ≤ g := by
        calc n = n / g * g := (Nat.div_mul_cancel hg_dvd_n).symm
          _ ≤ 1 * g := Nat.mul_le_mul_right g hng1
          _ = g := one_mul g
      have : g ≤ n / 2 := le_trans (Nat.le_of_dvd (by omega) hg_dvd_k) hkn
      omega
    · exact h_nd_dvd_n
  linarith

/- ## Basic Bounds -/

/- ## Upper Bound: f(n) ≤ n/P(n)

Strategy: For composite n with largest prime factor p and p^a ‖ n:
- Non-prime-power case (n = p^a * m, m ≥ 2): k = p^a gives
  gcd(n, C(n,k)) = n/p^a ≤ n/p via absorption identity + non-divisibility.
- Prime power case (n = p^a, a ≥ 2): k = p^(a-1) similarly gives
  gcd(n, C(n,k)) = p ≤ p^(a-1) = n/p.

The key lemma: p ∤ C(p^a*m - 1, p^a - 1) when p ∤ m.
Proof: By Legendre's formula, (p-1) * v_p(C(N,K)) = S_p(K) + S_p(N-K) - S_p(N).
Digit sum computation shows S_p(p^a-1) + S_p(p^a*(m-1)) = S_p(p^a*m-1),
so the difference is 0, hence v_p = 0, hence p ∤ C(N,K). -/

/-- Non-divisibility: p ∤ C(p^a * m - 1, p^a - 1) for any prime p, a ≥ 1, m ≥ 1.
    Proof via Kummer's theorem: K = p^a - 1 has base-p support at positions 0..a-1,
    while N-K = p^a*(m-1) has support at positions ≥ a. Their digit supports don't
    overlap, so adding them in base p produces zero carries, giving v_p(C(N,K)) = 0. -/
private theorem prime_not_dvd_choose_shift {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a)
    {m : ℕ} (hm_pos : 1 ≤ m) :
    ¬(p ∣ Nat.choose (p ^ a * m - 1) (p ^ a - 1)) := by
  -- Setup: N = p^a*m - 1, K = p^a - 1, N - K = p^a*(m-1)
  set N := p ^ a * m - 1
  set K := p ^ a - 1
  have hp2 : 2 ≤ p := hp.two_le
  have hpa_pos : 0 < p ^ a := Nat.pos_of_ne_zero (by positivity)
  have hKN : K ≤ N := by unfold_let K N; omega
  have hNK_eq : N - K = p ^ a * (m - 1) := by unfold_let N K; omega
  have hC_pos : 0 < Nat.choose N K := Nat.choose_pos hKN
  -- Use Kummer: multiplicity p (C(N,K)) = |{carries}|
  set b := Nat.log p N + 2
  have hNb : Nat.log p N < b := by unfold_let b; omega
  have h_kummer := Nat.Prime.multiplicity_choose hp hKN hNb
  -- Step 1: Show the carry set is empty (no carry at any position)
  have h_no_carry : ∀ i, i ∈ Finset.Ico 1 b →
      K % p ^ i + (N - K) % p ^ i < p ^ i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [hNK_eq]
    by_cases hia : i ≤ a
    · -- Case i ≤ a: (N-K) % p^i = 0 since p^i | p^a*(m-1)
      have : p ^ a * (m - 1) % p ^ i = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (pow_dvd_pow p hia) _)
      rw [this, add_zero]
      exact Nat.mod_lt K (by positivity)
    · -- Case i > a: K < p^i, and mod of (p^a*(m-1)) bounded
      push_neg at hia
      -- K % p^i = K = p^a - 1
      have hK_mod : K % p ^ i = K := Nat.mod_eq_of_lt (by
        calc K = p ^ a - 1 := rfl
          _ < p ^ a := by omega
          _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) (le_of_lt hia))
      -- (p^a*(m-1)) % p^i = p^a * ((m-1) % p^(i-a))
      have hia_sub : a + (i - a) = i := by omega
      set r := (m - 1) % p ^ (i - a)
      have hr_lt : r < p ^ (i - a) := Nat.mod_lt _ (by positivity)
      have h_pa_r_lt : p ^ a * r < p ^ i := by
        calc p ^ a * r < p ^ a * p ^ (i - a) := Nat.mul_lt_mul_left hpa_pos hr_lt
          _ = p ^ i := by rw [← pow_add, hia_sub]
      have h_mod_NK : p ^ a * (m - 1) % p ^ i = p ^ a * r := by
        have h_eq : p ^ a * (m - 1) = (m - 1) / p ^ (i - a) * p ^ i + p ^ a * r := by
          calc p ^ a * (m - 1)
              = p ^ a * (p ^ (i - a) * ((m - 1) / p ^ (i - a)) + r) := by
                rw [Nat.div_add_mod]
            _ = p ^ a * p ^ (i - a) * ((m - 1) / p ^ (i - a)) + p ^ a * r := by ring
            _ = p ^ i * ((m - 1) / p ^ (i - a)) + p ^ a * r := by
                rw [← pow_add, hia_sub]
            _ = (m - 1) / p ^ (i - a) * p ^ i + p ^ a * r := by ring
        rw [h_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_pa_r_lt]
      rw [hK_mod, h_mod_NK]
      -- K + p^a * r = (p^a - 1) + p^a * r ≤ p^i - 1 < p^i
      have : p ^ a * r ≤ p ^ i - p ^ a := by
        calc p ^ a * r ≤ p ^ a * (p ^ (i - a) - 1) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = p ^ a * p ^ (i - a) - p ^ a * 1 := by rw [Nat.mul_sub_one]
          _ = p ^ i - p ^ a := by rw [← pow_add, hia_sub, mul_one]
      unfold_let K; omega
  -- Step 2: Empty carry set → multiplicity 0 → ¬(p | C(N,K))
  have h_filter_empty : ((Finset.Ico 1 b).filter fun i =>
      p ^ i ≤ K % p ^ i + (N - K) % p ^ i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i hi; exact not_le.mpr (h_no_carry i hi)
  -- multiplicity p C(N,K) = 0
  intro h_dvd
  have h_one_le : (1 : PartENat) ≤ multiplicity (p : ℕ) (Nat.choose N K) :=
    multiplicity.le_multiplicity_of_pow_dvd (show p ^ 1 ∣ _ from by rwa [pow_one])
  rw [h_kummer, h_filter_empty, Finset.card_empty, Nat.cast_zero] at h_one_le
  exact absurd h_one_le (by norm_num)

/-- The absorption identity: C(n, k) = (n/k) * C(n-1, k-1) when k | n and k ≥ 1. -/
private theorem choose_eq_mul_choose_pred {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hdvd : k ∣ n) :
    Nat.choose n k = (n / k) * Nat.choose (n - 1) (k - 1) := by
  have hk_pos : 0 < k := by omega
  have h := Nat.succ_mul_choose_eq (n - 1) (k - 1)
  have hn' : n - 1 + 1 = n := by omega
  have hk' : k - 1 + 1 = k := by omega
  rw [hn', hk'] at h
  -- h : n * C(n-1, k-1) = C(n, k) * k
  obtain ⟨q, hq⟩ := hdvd
  have hq_eq : n / k = q := by rw [hq]; exact Nat.mul_div_cancel_left q hk_pos
  rw [hq_eq]
  have : k * (q * Nat.choose (k * q - 1) (k - 1)) = k * Nat.choose (k * q) k := by
    rw [← mul_assoc]; linarith [hq ▸ h]
  exact Nat.eq_of_mul_eq_mul_left hk_pos this.symm

/-- For a prime power p^a, if ¬(p ∣ x) then gcd(p^a, x) = 1. -/
private theorem coprime_prime_pow_of_not_dvd {p a x : ℕ} (hp : p.Prime) (hx : ¬(p ∣ x)) :
    Nat.gcd (p ^ a) x = 1 := by
  rw [Nat.Coprime.comm]
  exact (hp.coprime_iff_not_dvd.mpr hx).pow_right a

/-- For p^a * m with p prime, a ≥ 1, m ≥ 1: gcd(p^a*m, C(p^a*m, p^a)) = m.
    Combines absorption identity, GCD factoring, and non-divisibility. -/
private theorem gcd_choose_prime_pow_eq {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a)
    {m : ℕ} (hm_pos : 1 ≤ m) :
    Nat.gcd (p ^ a * m) (Nat.choose (p ^ a * m) (p ^ a)) = m := by
  have hpa_pos : 0 < p ^ a := Nat.pos_of_ne_zero (by positivity)
  have hk : 1 ≤ p ^ a := by omega
  have hkn : p ^ a ≤ p ^ a * m := Nat.le_mul_of_pos_right _ (by omega)
  have hdvd : p ^ a ∣ p ^ a * m := dvd_mul_right _ _
  have hchoose := choose_eq_mul_choose_pred hk hkn hdvd
  have hdiv : p ^ a * m / p ^ a = m := Nat.mul_div_cancel_left m hpa_pos
  rw [hdiv] at hchoose
  rw [hchoose, mul_comm (p ^ a) m, Nat.gcd_mul_left]
  have h_not_dvd := prime_not_dvd_choose_shift hp ha hm_pos
  rw [coprime_prime_pow_of_not_dvd hp h_not_dvd, mul_one]

/-- f(n) ≤ n/P(n) for all composite n.
    For non-prime-powers: k = P(n)^a with P(n)^a ‖ n gives
    gcd(n, C(n,k)) = n/P(n)^a ≤ n/P(n).
    For prime powers n = p^a: k = p^(a-1) gives gcd = p ≤ n/P(n). -/
theorem f_upper_bound (n : ℕ) (hn : ¬n.Prime) (hn2 : 2 ≤ n) :
    fBinom n ≤ n / largestPrimeFactor n := by
  -- Key insight: just use k = P (the largest prime factor, with exponent 1).
  -- Since n is composite, n/P ≥ 2, so P ∈ [2, n/2].
  -- gcd(n, C(n, P)) = n/P by gcd_choose_prime_pow_eq.
  set P := largestPrimeFactor n
  have h4 : 4 ≤ n := by
    -- n ≥ 2 and not prime → n ≥ 4
    interval_cases n <;> simp_all [Nat.Prime] <;> omega
  have hP_prime : P.Prime := by
    unfold_let P; unfold largestPrimeFactor; rw [dif_pos hn2]
    exact (Nat.mem_primeFactors.mp (Finset.max'_mem _ _)).1
  have hP_dvd : P ∣ n := by
    unfold_let P; unfold largestPrimeFactor; rw [dif_pos hn2]
    exact (Nat.mem_primeFactors.mp (Finset.max'_mem _ _)).2.1
  -- n/P ≥ 2 since n is composite (if n/P = 1 then n = P is prime)
  set q := n / P
  have hPq : n = P * q := (Nat.div_mul_cancel hP_dvd).symm ▸ (mul_comm P q ▸ rfl)
  have hq_ge2 : 2 ≤ q := by
    by_contra h; push_neg at h
    interval_cases q
    · omega  -- q = 0: impossible since P ≥ 2 and n ≥ 4
    · -- q = 1: n = P, but n is not prime
      have : n = P := by omega
      exact hn (this ▸ hP_prime)
  -- P ∈ [2, n/2]
  have hP_ge2 : 2 ≤ P := hP_prime.two_le
  have hP_le_half : P ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc P * 2 ≤ P * q := Nat.mul_le_mul_left P hq_ge2
      _ = n := by omega
  -- fBinom n ≤ gcd(n, C(n, P))
  unfold fBinom; rw [dif_pos h4]
  have hP_mem : P ∈ Finset.Icc 2 (n / 2) := Finset.mem_Icc.mpr ⟨hP_ge2, hP_le_half⟩
  calc ((Finset.Icc 2 (n / 2)).image (fun k => Nat.gcd n (Nat.choose n k))).min' _
      ≤ Nat.gcd n (Nat.choose n P) :=
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨P, hP_mem, rfl⟩)
    _ = q := by
        -- gcd(P * q, C(P * q, P)) = q by gcd_choose_prime_pow_eq
        have h_eq : P * q = P ^ 1 * q := by rw [pow_one]
        conv_lhs => rw [show n = P * q from by omega, h_eq]
        exact gcd_choose_prime_pow_eq hP_prime (le_refl 1) (by omega : 1 ≤ q)
    _ = n / largestPrimeFactor n := by unfold_let q P

/-- f(n) ≥ p(n), the smallest prime factor of n.
    For every 2 ≤ k ≤ n/2, gcd(n, C(n,k)) ≥ minFac(n).
    Proof: from the absorption identity n | k·C(n,k), coprime
    cancellation gives (n/gcd(n,k)) | C(n,k). Since gcd(n,k) ≤ k ≤ n/2 < n,
    we get n/gcd(n,k) ≥ minFac(n), completing the bound. -/
theorem f_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    smallestPrimeFactor n ≤ fBinom n := by
  unfold fBinom smallestPrimeFactor
  rw [dif_pos hn]
  apply Finset.le_min'
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hk2, hkn⟩ := Finset.mem_Icc.mp hk
  exact gcd_choose_ge_minFac hn hk2 hkn

/- ## Known Equalities -/

/-- When n = pq is a product of two primes with p ≤ q, f(n) = p.
    Sandwich: p = minFac(pq) ≤ f(pq) ≤ pq/largestPrimeFactor(pq) ≤ pq/q = p. -/
theorem f_semiprime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    fBinom (p * q) = p := by
  have h2 : 2 ≤ p * q := by have := hp.two_le; nlinarith
  have h4 : 4 ≤ p * q := by have := hp.two_le; have := hq.two_le; nlinarith
  have hcomp : ¬(p * q).Prime := by
    intro hprime
    rcases hprime.eq_one_or_self_of_dvd p (dvd_mul_right p q) with h1 | h2
    · exact hp.one_lt.ne' h1
    · have : q = 1 := by nlinarith [hp.one_lt]
      exact absurd this (by omega)
  -- Lower bound: p ≤ f(pq)
  have hlower : p ≤ fBinom (p * q) := by
    have hmin := f_lower_bound (p * q) h4
    rw [show smallestPrimeFactor (p * q) = Nat.minFac (p * q) from rfl,
        minFac_mul_prime hp hq hpq] at hmin
    exact hmin
  -- Upper bound: f(pq) ≤ p
  have hupper : fBinom (p * q) ≤ p := by
    have hup := f_upper_bound (p * q) hcomp h2
    have hq_le : q ≤ largestPrimeFactor (p * q) :=
      le_largestPrimeFactor hq (dvd_mul_left q p) h2
    have hlpf_pos : 0 < largestPrimeFactor (p * q) := by
      have := hq.two_le; linarith
    have hpq_le : p * q / largestPrimeFactor (p * q) ≤ p :=
      calc p * q / largestPrimeFactor (p * q)
          ≤ p * largestPrimeFactor (p * q) / largestPrimeFactor (p * q) :=
            Nat.div_le_div_right (Nat.mul_le_mul_left p hq_le)
        _ = p := Nat.mul_div_cancel p hlpf_pos
    linarith
  omega

/-- f(30) = 30/5 = 6. Verified by checking gcd(30, C(30,k)) ≥ 6 for all
    2 ≤ k ≤ 15, with equality at k = 5 where C(30,5) = 142506
    and gcd(30, 142506) = 6. -/
theorem f_30 : fBinom 30 = 6 := by
  unfold fBinom
  rw [dif_pos (show (4 : ℕ) ≤ 30 by norm_num)]
  apply le_antisymm
  · -- Upper bound: min' ≤ 6 via k = 5
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨5, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
      by native_decide⟩
  · -- Lower bound: 6 ≤ min' (all gcd values ≥ 6)
    apply Finset.le_min'
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hk2, hk15⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> native_decide

/- ## Question 1: Characterization (OPEN)

  Which composite n satisfy f(n) = n/P(n)?

  Known examples: all semiprimes pq (by f_semiprime) and n = 30 (by f_30).
  The general characterization is an open problem. Note that f(n) = n/P(n)
  does NOT hold for all composite n — it fails when n has many prime factors
  of varying sizes, since then the minimizing k can achieve a smaller gcd. -/

/- ## Question 2: Large Values -/

/-- For n = p², f(n) ≥ p = √n.
    PROVED from f_lower_bound and minFac(p²) = p. -/
theorem f_prime_square (p : ℕ) (hp : p.Prime) :
    p ≤ fBinom (p * p) := by
  have h4 : 4 ≤ p * p := by have := hp.two_le; nlinarith
  have hbound := f_lower_bound (p * p) h4
  have hmin : smallestPrimeFactor (p * p) = p := by
    unfold smallestPrimeFactor
    exact minFac_prime_sq p hp
  rw [hmin] at hbound
  exact hbound

/-- Question 2: Are there infinitely many composite n with f(n) > √n?
    Prime squares achieve f(p²) = p = √(p²), so they give ≥ but not >.
    Whether strict inequality f(n) > √n occurs for infinitely many
    composite n remains open. -/
/- ## Question 3: Upper Bound Conjecture -/

/-- Question 3: Is f(n) ≪_A n/(log n)^A for every A > 0?
    This would show f(n) is much smaller than n/P(n) for typical n,
    since P(n) ~ log n for most n by the Hardy-Ramanujan theorem. -/
