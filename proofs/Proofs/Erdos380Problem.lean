/-
# Erdős Problem 380: Bad Intervals and Greatest Prime Factors

An interval `[u, v]` is "bad" if the greatest prime factor of `∏{u ≤ m ≤ v} m`
occurs with exponent > 1 in the product. Let `B(x)` count integers `n ≤ x`
contained in at least one bad interval.

**Conjecture:** `B(x) ~ #{n ≤ x : P(n)² | n}` where `P(n)` is the
greatest prime factor of `n`.

Erdős and Graham (1980) proved `B(x) > x^{1-o(1)}`.

*Reference:* [erdosproblems.com/380](https://www.erdosproblems.com/380)
-/

import Mathlib

open Nat Finset

/- ## Greatest prime factor

Previously axiomatized (4 axioms: definition + 3 properties).
Now defined concretely via `Nat.primeFactors` and `Finset.max'`,
with all properties proved from the definition. -/

/-- The greatest prime factor of `n`. Returns 0 for `n ≤ 1`.
    Defined as the maximum of the prime factor set.
    Previously an axiom; now concrete via Mathlib. -/
noncomputable def greatestPrimeFactor (n : ℕ) : ℕ :=
  if h : n > 1 then n.primeFactors.max' (Nat.nonempty_primeFactors.mpr h) else 0

/-- `greatestPrimeFactor n` is prime for `n ≥ 2`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_prime (n : ℕ) (hn : 2 ≤ n) :
    (greatestPrimeFactor n).Prime := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  have hmem := Finset.max'_mem n.primeFactors (Nat.nonempty_primeFactors.mpr (by omega : n > 1))
  exact (Nat.mem_primeFactors.mp hmem).1

/-- `greatestPrimeFactor n` divides `n`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_dvd (n : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ∣ n := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  have hmem := Finset.max'_mem n.primeFactors (Nat.nonempty_primeFactors.mpr (by omega : n > 1))
  exact (Nat.mem_primeFactors.mp hmem).2.1

/-- `greatestPrimeFactor n` is the largest prime dividing `n`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_largest (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hd : p ∣ n) :
    p ≤ greatestPrimeFactor n := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  apply Finset.le_max'
  exact Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩

/- ## Bad intervals -/

/-- An interval `[u, v]` is bad if the greatest prime factor of the
product `u * (u+1) * ⋯ * v` occurs with exponent ≥ 2. -/
def IsBadInterval (u v : ℕ) : Prop :=
    u ≤ v ∧
    greatestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ (Finset.Icc u v).prod id

/-- An integer `n` is in a bad interval if there exist `u ≤ n ≤ v`
with `[u, v]` bad. -/
def InBadInterval (n : ℕ) : Prop :=
    ∃ (u v : ℕ), u ≤ n ∧ n ≤ v ∧ IsBadInterval u v

/- ## Counting functions -/

open Classical in
/-- `B(x)`: count of integers `n ≤ x` in some bad interval. -/
noncomputable def badCount (x : ℕ) : ℕ :=
    ((Finset.Icc 1 x).filter InBadInterval).card

/-- Count of `n ≤ x` with `P(n)² | n`. -/
noncomputable def gpfSquareCount (x : ℕ) : ℕ :=
    ((Finset.Icc 2 x).filter
      (fun n => greatestPrimeFactor n ^ 2 ∣ n)).card

/- ## Main conjecture -/

/-- Erdős Problem 380: `B(x) ~ #{n ≤ x : P(n)² | n}`.
Formally: the ratio tends to 1. -/
def ErdosProblem380 : Prop :=
    ∀ (ε : ℚ), 0 < ε →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        0 < gpfSquareCount x ∧
          |(badCount x : ℚ) / (gpfSquareCount x : ℚ) - 1| < ε

/- ## Bad intervals and primes -/

/-- Bad intervals with `v < 2u` cannot contain primes. If `p` is prime
and `p ∈ [u,v]` with `v < 2u`, then the greatest prime factor P of ∏[u,v]
satisfies P ≥ p ≥ u, so v < 2P. Thus only P itself is divisible by P in [u,v].
Splitting the product as P * rest where P ∤ rest gives P² ∤ P * rest,
contradicting the bad condition. PROVED. -/
theorem bad_interval_no_prime (u v : ℕ) (hbad : IsBadInterval u v) :
    v < 2 * u →
      ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → False := by
  intro hv2u p hp hup hpv
  obtain ⟨huv, hP2⟩ := hbad
  set S := Finset.Icc u v with hS
  set prod := S.prod id with hprod_def
  set P := greatestPrimeFactor prod with hP_def
  -- Product ≥ 2 (contains prime p)
  have hprod_ge2 : 2 ≤ prod := by
    have hp_mem : p ∈ S := Finset.mem_Icc.mpr ⟨hup, hpv⟩
    calc prod = S.prod id := rfl
      _ ≥ id p := Finset.single_le_prod'
            (fun m hm => by
              rw [hS, Finset.mem_Icc] at hm
              simp only [id_eq]
              omega) hp_mem
      _ = p := rfl
      _ ≥ 2 := hp.two_le
  -- P is prime, divides product, and is the largest such
  have hPprime := gpf_prime prod hprod_ge2
  have hP_dvd := gpf_dvd prod hprod_ge2
  -- p divides the product (p ∈ S and prod = ∏ id)
  have hp_dvd : p ∣ prod := Finset.dvd_prod_of_mem id (Finset.mem_Icc.mpr ⟨hup, hpv⟩)
  -- P ≥ p ≥ u, so v < 2u ≤ 2P
  have hPge_p : p ≤ P := gpf_largest prod p hprod_ge2 hp hp_dvd
  have hPge_u : u ≤ P := le_trans hup hPge_p
  have hv_lt_2P : v < 2 * P := lt_of_lt_of_le hv2u (Nat.mul_le_mul_left 2 hPge_u)
  -- P ∈ [u,v]: P divides product, so P divides some m ∈ S with P ≤ m ≤ v
  have hP_mem : P ∈ S := by
    have hP_dvd_some := (hPprime.prime.dvd_finset_prod_iff id).mp hP_dvd
    obtain ⟨m, hm_mem, hP_dvd_m⟩ := hP_dvd_some
    have hm_bounds := Finset.mem_Icc.mp hm_mem
    have hP_le_m : P ≤ m := Nat.le_of_dvd (by omega) hP_dvd_m
    exact Finset.mem_Icc.mpr ⟨hPge_u, le_trans hP_le_m hm_bounds.2⟩
  -- Key: P is the ONLY element of S divisible by P
  -- (any kP with k≥2 gives kP ≥ 2P > v, out of range)
  have hP_unique : ∀ m ∈ S, P ∣ m → m = P := by
    intro m hm hPm
    have hm_bounds := Finset.mem_Icc.mp hm
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · have h0 : prod = 0 := Finset.prod_eq_zero hm rfl
        omega
      · exact h
    obtain ⟨k, rfl⟩ := hPm
    have hk2 : k < 2 := by
      by_contra hk
      push_neg at hk
      have h2Pk : 2 * P ≤ P * k := by
        rw [Nat.mul_comm 2 P]
        exact Nat.mul_le_mul_left P hk
      exact absurd (lt_of_le_of_lt (le_trans h2Pk hm_bounds.2) hv_lt_2P) (lt_irrefl _)
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp at hm_pos
    · rw [Nat.mul_one]
  -- Split: prod = P * rest
  set rest := (S.erase P).prod id with hrest_def
  have hprod_split : P * rest = prod := Finset.mul_prod_erase S id hP_mem
  -- P ∤ rest (no element of S \ {P} is divisible by P)
  have hP_ndvd_rest : ¬ P ∣ rest := by
    intro h
    have := (hPprime.prime.dvd_finset_prod_iff id).mp h
    obtain ⟨m, hm_erase, hP_dvd_m⟩ := this
    exact Finset.ne_of_mem_erase hm_erase (hP_unique m (Finset.mem_of_mem_erase hm_erase) hP_dvd_m)
  -- P² | prod = P * rest → P | rest (cancel P from both sides)
  have hP_dvd_rest : P ∣ rest := by
    have hP2_eq : P ^ 2 = P * P := sq P
    rw [← hprod_split] at hP2
    rw [hP2_eq] at hP2
    exact (mul_dvd_mul_iff_left hPprime.ne_zero).mp hP2
  -- Contradiction: P ∣ rest and P ∤ rest
  exact hP_ndvd_rest hP_dvd_rest

/-- Bad intervals contain no primes (version using Bertrand's postulate).
Strengthens bad_interval_no_prime by replacing the v < 2u hypothesis with 1 ≤ u.
(The hypothesis `1 ≤ u` is necessary: for `u = 0` the interval product is `0`,
`greatestPrimeFactor 0 = 0`, and `0² ∣ 0`, so `[0, v]` is vacuously "bad" yet
contains primes.)
Key insight: by Bertrand, there's a prime q > v/2 in [u,v] (if any prime exists),
so GPF ≥ q > v/2, making GPF the unique multiple of itself in the interval. -/
theorem bad_interval_no_prime_general (u v : ℕ) (hbad : IsBadInterval u v) (hu : 1 ≤ u) :
    ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → False := by
  intro p hp hup hpv
  have hv2 : 2 ≤ v := le_trans hp.two_le hpv
  -- By Bertrand's postulate applied to v/2: ∃ prime q with v/2 < q ≤ 2*(v/2) ≤ v
  have hvdiv : v / 2 ≠ 0 := by omega
  obtain ⟨q, hq_prime, hvq, hq2v⟩ := Nat.exists_prime_lt_and_le_two_mul (v / 2) hvdiv
  have hqv : q ≤ v := by omega
  -- Case split: q ≥ u or q < u
  by_cases hqu : u ≤ q
  · -- q ∈ [u,v], so GPF ≥ q > v/2, meaning 2*GPF > v
    obtain ⟨huv, hP2⟩ := hbad
    set S := Finset.Icc u v with hS
    set prod := S.prod id with hprod_def
    set P := greatestPrimeFactor prod with hP_def
    have hq_mem : q ∈ S := Finset.mem_Icc.mpr ⟨hqu, hqv⟩
    have hprod_ge2 : 2 ≤ prod := by
      calc prod = S.prod id := rfl
        _ ≥ id q := Finset.single_le_prod'
              (fun m hm => by
                rw [hS, Finset.mem_Icc] at hm
                simp only [id_eq]
                omega) hq_mem
        _ = q := rfl
        _ ≥ 2 := hq_prime.two_le
    have hPprime := gpf_prime prod hprod_ge2
    have hP_dvd := gpf_dvd prod hprod_ge2
    -- GPF ≥ q > v/2
    have hq_dvd : q ∣ prod := Finset.dvd_prod_of_mem id hq_mem
    have hPq : q ≤ P := gpf_largest prod q hprod_ge2 hq_prime hq_dvd
    -- 2P > v (from P ≥ q > v/2)
    have h2P : v < 2 * P := by omega
    -- P ∈ [u,v]
    have hP_mem : P ∈ S := by
      have hP_dvd_some := (hPprime.prime.dvd_finset_prod_iff id).mp hP_dvd
      obtain ⟨m, hm_mem, hP_dvd_m⟩ := hP_dvd_some
      have hm_bounds := Finset.mem_Icc.mp hm_mem
      have hP_le_m : P ≤ m := Nat.le_of_dvd (by omega) hP_dvd_m
      exact Finset.mem_Icc.mpr ⟨le_trans hqu hPq, le_trans hP_le_m hm_bounds.2⟩
    -- P is the only element of S divisible by P (2P > v)
    have hP_unique : ∀ m ∈ S, P ∣ m → m = P := by
      intro m hm hPm
      have hm_bounds := Finset.mem_Icc.mp hm
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · have h0 : prod = 0 := Finset.prod_eq_zero hm rfl
          omega
        · exact h
      obtain ⟨k, rfl⟩ := hPm
      have hk2 : k < 2 := by
        by_contra hk
        push_neg at hk
        have h2Pk : 2 * P ≤ P * k := by
          rw [Nat.mul_comm 2 P]
          exact Nat.mul_le_mul_left P hk
        exact absurd (lt_of_le_of_lt (le_trans h2Pk hm_bounds.2) h2P) (lt_irrefl _)
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp at hm_pos
      · rw [Nat.mul_one]
    -- Split: prod = P * rest, derive contradiction
    set rest := (S.erase P).prod id with hrest_def
    have hprod_split : P * rest = prod := Finset.mul_prod_erase S id hP_mem
    have hP_ndvd_rest : ¬ P ∣ rest := by
      intro h
      have := (hPprime.prime.dvd_finset_prod_iff id).mp h
      obtain ⟨m, hm_erase, hP_dvd_m⟩ := this
      exact Finset.ne_of_mem_erase hm_erase (hP_unique m (Finset.mem_of_mem_erase hm_erase) hP_dvd_m)
    have hP_dvd_rest : P ∣ rest := by
      have hP2_eq : P ^ 2 = P * P := sq P
      rw [← hprod_split] at hP2
      rw [hP2_eq] at hP2
      exact (mul_dvd_mul_iff_left hPprime.ne_zero).mp hP2
    exact hP_ndvd_rest hP_dvd_rest
  · -- q < u, and q > v/2, so v < 2u: use the conditional version
    push_neg at hqu
    exact bad_interval_no_prime u v hbad (by omega) p hp hup hpv

/-- Bad intervals satisfy v < 2u (for u ≥ 1), via Bertrand's postulate.
If v ≥ 2u, Bertrand gives a prime in (u, 2u] ⊆ [u, v], contradicting no-prime. -/
theorem bad_interval_v_bound (u v : ℕ) (hbad : IsBadInterval u v) (hu : 1 ≤ u) :
    v < 2 * u := by
  by_contra h
  push_neg at h
  obtain ⟨q, hq_prime, huq, hq2u⟩ := Nat.exists_prime_lt_and_le_two_mul u (by omega)
  exact bad_interval_no_prime_general u v hbad hu q hq_prime (by omega) (le_trans hq2u h)

/- ## Singleton intervals -/

/-- A singleton interval [n,n] is bad iff P(n)² | n (for n ≥ 2).
    This directly links bad intervals to the gpfSquare counting function. -/
theorem singleton_bad_iff (n : ℕ) (hn : 2 ≤ n) :
    IsBadInterval n n ↔ greatestPrimeFactor n ^ 2 ∣ n := by
  unfold IsBadInterval
  rw [Finset.Icc_self, Finset.prod_singleton, id_eq]
  simp

/-- Every n with P(n)² | n is in the bad interval [n,n]. -/
theorem gpfSquare_in_bad (n : ℕ) (hn : 2 ≤ n)
    (h : greatestPrimeFactor n ^ 2 ∣ n) : InBadInterval n :=
  ⟨n, n, le_refl n, le_refl n, (singleton_bad_iff n hn).mpr h⟩

/-- B(x) ≥ #{n ≤ x : P(n)² | n}: the bad count dominates the gpfSquare count.
    Each n ∈ [2,x] with P(n)²|n is witnessed by the singleton bad interval [n,n]. -/
theorem badCount_ge_gpfSquareCount (x : ℕ) :
    gpfSquareCount x ≤ badCount x := by
  unfold badCount gpfSquareCount
  apply Finset.card_le_card
  intro n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rintro ⟨⟨hn2, hnx⟩, hgpf⟩
  exact ⟨⟨by omega, hnx⟩, gpfSquare_in_bad n hn2 hgpf⟩

/- ## Known bounds -/

/-- The count `#{n ≤ x : P(n)² | n}` grows like
`x / exp(c √(log x · log log x))` for some `c > 0`.
In particular, it exceeds `x^{1-ε}` for any `ε > 0` and large enough `x`.
(Stated over `ℝ` with real exponentiation; the earlier `ℚ`-power spelling
was ill-typed — there is no `HPow ℚ ℚ ℚ`.) -/
axiom gpfSquare_asymptotic :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ε : ℝ), 0 < ε →
        ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
          (x : ℝ) ^ (1 - ε) ≤ (gpfSquareCount x : ℝ)

/-- Erdős–Graham: `B(x) > x^{1-o(1)}`.
Previously axiomatized; now derived from `gpfSquare_asymptotic` and
`badCount_ge_gpfSquareCount` via the chain `x^{1-ε} ≤ G(x) ≤ B(x)`. -/
theorem erdos_graham_lower :
    ∀ (ε : ℝ), 0 < ε →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (x : ℝ) ^ (1 - ε) ≤ (badCount x : ℝ) := by
  intro ε hε
  obtain ⟨_, _, hasy⟩ := gpfSquare_asymptotic
  obtain ⟨x₀, hx₀⟩ := hasy ε hε
  exact ⟨x₀, fun x hx =>
    le_trans (hx₀ x hx) (Nat.cast_le.mpr (badCount_ge_gpfSquareCount x))⟩

/- ## Very bad intervals and powerful numbers

Erdős and Graham also asked about "very bad" intervals `[u,v]` where
`∏{u ≤ m ≤ v} m` is powerful (every prime factor has exponent ≥ 2).
They conjectured that the count of `n ≤ x` in some very bad interval
is asymptotic to the count of powerful numbers `≤ x`, which is `∼ c√x`. -/

/-- A positive integer `n > 1` is powerful if every prime factor appears
    with exponent at least 2: `∀ p prime, p ∣ n → p² ∣ n`. -/
def IsPowerful (n : ℕ) : Prop :=
  1 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- An interval `[u, v]` is "very bad" if the product `∏{u ≤ m ≤ v} m`
    is powerful. Stronger than bad: all prime exponents ≥ 2, not just the
    largest. -/
def IsVeryBadInterval (u v : ℕ) : Prop :=
  u ≤ v ∧ IsPowerful ((Finset.Icc u v).prod id)

/-- An integer `n` is in a very bad interval if `∃ u ≤ n ≤ v` with
    `[u, v]` very bad. -/
def InVeryBadInterval (n : ℕ) : Prop :=
  ∃ (u v : ℕ), u ≤ n ∧ n ≤ v ∧ IsVeryBadInterval u v

open Classical in
/-- Count of integers `n ≤ x` in some very bad interval. -/
noncomputable def veryBadCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter InVeryBadInterval).card

open Classical in
/-- Count of powerful numbers in `[2, x]`. -/
noncomputable def powerfulCount (x : ℕ) : ℕ :=
  ((Finset.Icc 2 x).filter IsPowerful).card

/-- Every very bad interval is bad: if the product is powerful then
    `P² | product` where `P` is the greatest prime factor. -/
theorem veryBad_is_bad (u v : ℕ) (h : IsVeryBadInterval u v) :
    IsBadInterval u v := by
  obtain ⟨huv, hpow⟩ := h
  have hlt := hpow.1
  have h2 : 2 ≤ (Finset.Icc u v).prod id := by omega
  exact ⟨huv, hpow.2 _ (gpf_prime _ h2) (gpf_dvd _ h2)⟩

/-- Very bad intervals contain no primes (corollary). Here `1 ≤ u` is automatic:
a powerful product is `> 1`, hence nonzero, so `0 ∉ [u, v]`. -/
theorem veryBad_interval_no_prime (u v : ℕ) (hvb : IsVeryBadInterval u v) :
    ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → False := by
  have hu : 1 ≤ u := by
    by_contra h
    push_neg at h
    have hu0 : u = 0 := by omega
    subst hu0
    have h0 : (0 : ℕ) ∈ Finset.Icc 0 v := Finset.mem_Icc.mpr ⟨le_refl 0, Nat.zero_le v⟩
    have hz : (Finset.Icc 0 v).prod id = 0 := Finset.prod_eq_zero h0 rfl
    have h1 := hvb.2.1
    omega
  exact bad_interval_no_prime_general u v (veryBad_is_bad u v hvb) hu

/-- A singleton `[n, n]` is very bad iff `n` is powerful (for `n ≥ 2`). -/
theorem singleton_veryBad_iff (n : ℕ) (hn : 2 ≤ n) :
    IsVeryBadInterval n n ↔ IsPowerful n := by
  unfold IsVeryBadInterval
  rw [Finset.Icc_self, Finset.prod_singleton, id_eq]
  simp

/-- Every powerful `n ≥ 2` is in the very bad interval `[n, n]`. -/
theorem powerful_in_veryBad (n : ℕ) (hn : 2 ≤ n) (h : IsPowerful n) :
    InVeryBadInterval n :=
  ⟨n, n, le_refl n, le_refl n, (singleton_veryBad_iff n hn).mpr h⟩

/-- `veryBadCount(x) ≤ badCount(x)`: every very bad interval is bad. -/
theorem veryBadCount_le_badCount (x : ℕ) : veryBadCount x ≤ badCount x := by
  unfold veryBadCount badCount
  apply Finset.card_le_card
  intro n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rintro ⟨hn, hvb⟩
  refine ⟨hn, ?_⟩
  obtain ⟨u, v, hu, hv, hvb⟩ := hvb
  exact ⟨u, v, hu, hv, veryBad_is_bad u v hvb⟩

/-- `powerfulCount(x) ≤ veryBadCount(x)`: every powerful number is in
    the singleton very bad interval. -/
theorem veryBadCount_ge_powerfulCount (x : ℕ) :
    powerfulCount x ≤ veryBadCount x := by
  unfold veryBadCount powerfulCount
  apply Finset.card_le_card
  intro n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rintro ⟨⟨hn2, hnx⟩, hpow⟩
  exact ⟨⟨by omega, hnx⟩, powerful_in_veryBad n hn2 hpow⟩

/-- Full chain of counting inequalities:
    `powerfulCount ≤ veryBadCount ≤ badCount` and `gpfSquareCount ≤ badCount`. -/
theorem counting_chain (x : ℕ) :
    powerfulCount x ≤ veryBadCount x ∧
    veryBadCount x ≤ badCount x ∧
    gpfSquareCount x ≤ badCount x :=
  ⟨veryBadCount_ge_powerfulCount x, veryBadCount_le_badCount x, badCount_ge_gpfSquareCount x⟩

/-- Secondary conjecture: `veryBadCount(x) ∼ powerfulCount(x)`.
    The very bad count should be asymptotic to the powerful number count. -/
def VeryBadConjecture : Prop :=
  ∀ (ε : ℚ), 0 < ε →
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      0 < powerfulCount x ∧
        |(veryBadCount x : ℚ) / (powerfulCount x : ℚ) - 1| < ε
