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

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

open Nat Finset

/- ## Greatest prime factor

Previously axiomatized (4 axioms: definition + 3 properties).
Now defined concretely via `Nat.primeFactors` and `Finset.max'`,
with all properties proved from the definition. -/

/-- The greatest prime factor of `n`. Returns 0 for `n ≤ 1`.
    Defined as the maximum of the prime factor set.
    Previously an axiom; now concrete via Mathlib. -/
noncomputable def greatestPrimeFactor (n : ℕ) : ℕ :=
  if h : n > 1 then n.primeFactors.max' (Nat.primeFactors_nonempty h) else 0

/-- `greatestPrimeFactor n` is prime for `n ≥ 2`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_prime (n : ℕ) (hn : 2 ≤ n) :
    (greatestPrimeFactor n).Prime := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  have hmem := Finset.max'_mem n.primeFactors (Nat.primeFactors_nonempty (by omega : n > 1))
  exact (Nat.mem_primeFactors.mp hmem).1

/-- `greatestPrimeFactor n` divides `n`.
    Previously axiomatized; now proved from the definition. -/
theorem gpf_dvd (n : ℕ) (hn : 2 ≤ n) :
    greatestPrimeFactor n ∣ n := by
  unfold greatestPrimeFactor
  rw [dif_pos (by omega : n > 1)]
  have hmem := Finset.max'_mem n.primeFactors (Nat.primeFactors_nonempty (by omega : n > 1))
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
    let P := greatestPrimeFactor (Finset.Icc u v).prod id
    P ^ 2 ∣ (Finset.Icc u v).prod id

/-- An integer `n` is in a bad interval if there exist `u ≤ n ≤ v`
with `[u, v]` bad. -/
def InBadInterval (n : ℕ) : Prop :=
    ∃ (u v : ℕ), u ≤ n ∧ n ≤ v ∧ IsBadInterval u v

/- ## Counting functions -/

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

/- ## Known bounds -/

/-- Erdős–Graham: `B(x) > x^{1-o(1)}`, meaning `B(x)` is large. -/
axiom erdos_graham_lower :
    ∀ (ε : ℚ), 0 < ε →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (x : ℚ) ^ (1 - ε) ≤ (badCount x : ℚ)

/-- The count `#{n ≤ x : P(n)² | n}` grows like
`x / exp(c √(log x · log log x))` for some `c > 0`. -/
axiom gpfSquare_asymptotic :
    ∃ c : ℚ, 0 < c ∧
      ∀ (ε : ℚ), 0 < ε →
        ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
          (x : ℚ) ^ (1 - ε) ≤ (gpfSquareCount x : ℚ)

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
      _ ≥ id p := Finset.single_le_prod' (fun m hm => by simp [Finset.mem_Icc] at hm; omega) hp_mem
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
    obtain ⟨k, rfl⟩ := hPm
    have hk_pos : 0 < k := by
      by_contra h; push_neg at h; simp at h; omega
    have : k * P ≤ v := hm_bounds.2
    have : k * P < 2 * P := le_trans this (le_of_lt hv_lt_2P)
    have : k < 2 := by omega
    omega
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

/-- Bad intervals contain no primes (unconditional version using Bertrand's postulate).
Strengthens bad_interval_no_prime by removing the v < 2u hypothesis.
Key insight: by Bertrand, there's a prime q > v/2 in [u,v] (if any prime exists),
so GPF ≥ q > v/2, making GPF the unique multiple of itself in the interval. -/
theorem bad_interval_no_prime_general (u v : ℕ) (hbad : IsBadInterval u v) :
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
        _ ≥ id q := Finset.single_le_prod' (fun m hm => by simp [Finset.mem_Icc] at hm; omega) hq_mem
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
      obtain ⟨k, rfl⟩ := hPm
      have hk_pos : 0 < k := by
        by_contra h; push_neg at h; simp at h; omega
      have : k * P ≤ v := hm_bounds.2
      have : k * P < 2 * P := le_trans this (le_of_lt h2P)
      have : k < 2 := by omega
      omega
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
  exact bad_interval_no_prime_general u v hbad q hq_prime (by omega) (le_trans hq2u h)
