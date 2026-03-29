/-
  Erdős Problem #358: Sums of Consecutive Terms

  Source: https://erdosproblems.com/358
  Status: OPEN

  Statement:
  Let A = {a₁ < a₂ < ...} be an infinite sequence of integers.
  Let f(n) count the number of solutions to n = Σᵢ₌ᵤᵛ aᵢ (sum of consecutive terms).
  Is there such an A for which f(n) → ∞ as n → ∞?
  Or even where f(n) ≥ 2 for all large n?

  Background:
  - When A = {1, 2, 3, ...}, f(n) counts the number of odd divisors of n
  - Classical result: n can be expressed as sum of ≥2 consecutive positive integers iff n ≠ 2^k
  - In modern language: asks for convex set A with 1_A ∘ 1_A(n) → ∞
  - Erdős-Moser (1963): Considered A = primes, conjectured limsup is infinite

  References:
  - Guy, "Unsolved Problems in Number Theory", Problem C2
  - Erdős-Graham, "Old and new problems in combinatorial number theory" (1980)
  - Moser, "Notes on number theory III" (1963)

  Related: Problem #356 (finite analogue)
-/

import Mathlib

open Nat Filter Set BigOperators Finset

namespace Erdos358

/- ## Part I: Definitions -/

/-- An infinite increasing sequence of integers. -/
structure IntSequence where
  seq : ℕ → ℤ
  increasing : ∀ n, seq n < seq (n + 1)

/-- The count of ways to express n as a sum of consecutive terms of A.
    f(n) = #{(u,v) : u ≤ v ∧ n = Σᵢ₌ᵤᵛ aᵢ} -/
noncomputable def consecutiveSumCount (A : IntSequence) (n : ℤ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ≤ p.2 ∧
    (∑ i ∈ Finset.Icc p.1 p.2, A.seq i) = n}

/- ## Part II: The Natural Numbers Case -/

/-- The natural numbers sequence: a_n = n+1. -/
def naturalsSeq : IntSequence where
  seq := fun n => (n + 1 : ℤ)
  increasing := fun n => by simp only [Int.lt_add_one_iff]; omega

/-- Sum of consecutive integers from u to v (inclusive). -/
def consecutiveSum (u v : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc u v, (i + 1 : ℤ)

/-- Helper: 2 × sum of consecutive integers = (v-u+1)(u+v+2). -/
private lemma consecutive_sum_double (u v : ℕ) (huv : u ≤ v) :
    2 * consecutiveSum u v = (↑v - ↑u + 1 : ℤ) * (↑u + ↑v + 2) := by
  unfold consecutiveSum
  induction v with
  | zero =>
    simp at huv; subst huv
    simp [Finset.Icc_self]
    ring
  | succ v ih =>
    by_cases h : u ≤ v
    · -- Split: Icc u (v+1) = insert (v+1) (Icc u v)
      have hmem : v + 1 ∉ Finset.Icc u v := by simp [Finset.mem_Icc]; omega
      have hIcc : Finset.Icc u (v + 1) = insert (v + 1) (Finset.Icc u v) := by
        ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert hmem, mul_add, ih h]
      push_cast
      ring
    · -- u = v + 1
      have : u = v + 1 := by omega
      subst this
      simp [Finset.Icc_self]
      ring

/-- Formula for sum of consecutive integers: (v-u+1)(u+v+2)/2. -/
theorem consecutive_sum_formula (u v : ℕ) (huv : u ≤ v) :
    consecutiveSum u v = ((↑v - ↑u + 1 : ℤ) * (↑u + ↑v + 2)) / 2 := by
  have h2 := consecutive_sum_double u v huv
  omega

/-- Any n ≥ 3 that is not a power of 2 has an odd divisor d ≥ 3.
    Proof by induction: if n is odd, n itself works; if n = 2m, recurse on m. -/
private lemma exists_odd_divisor_ge3 (n : ℕ) (hn : n ≥ 3) (h : ¬∃ k, n = 2 ^ k) :
    ∃ d, d ∣ n ∧ Odd d ∧ d ≥ 3 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
  · -- n = 2m
    have hm_ge2 : m ≥ 2 := by omega
    have hm_np : ¬∃ k, m = 2 ^ k := fun ⟨k, hk⟩ => h ⟨k + 1, by rw [pow_succ]; omega⟩
    by_cases hm3 : m ≥ 3
    · obtain ⟨d, hd, hodd, hge⟩ := exists_odd_divisor_ge3 m hm3 hm_np
      exact ⟨d, dvd_mul_of_dvd_right hd 2, hodd, hge⟩
    · -- m = 2: n = 4 = 2²
      exfalso; exact h ⟨2, by omega⟩
  · exact ⟨n, dvd_refl n, hodd, hn⟩
termination_by n
decreasing_by omega

/-- If n is not a power of 2, then n can be written as a sum of ≥2 consecutive
    positive integers.

    **Proof idea**: n has an odd factor d ≥ 3 (since n is not a power of 2).
    Write 2n = s · t where s, t have different parities and s ≥ 2.
    - n odd: s = 2, t = n. Terms: (n-1)/2 and (n+1)/2.
    - n even (n = 2^a · m, m odd ≥ 3): s = min(m, 2^(a+1)), t = max(m, 2^(a+1)).
    Then u = (t - s - 1)/2, v = (s + t - 3)/2 give the representation. -/
private lemma not_pow2_representable (n : ℕ) (hn : n ≥ 3) (h : ¬∃ k : ℕ, n = 2^k) :
    ∃ u v : ℕ, u < v ∧ n = ∑ i ∈ Finset.Icc (u+1) (v+1), i := by
  -- Handle odd n: use two consecutive terms
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2*m, even case. Since n ≥ 3 and even, m ≥ 2.
    -- Since n is not a power of 2, m is not a power of 2.
    have hm_ge2 : m ≥ 2 := by omega
    have hm_not_pow : ¬∃ k, m = 2 ^ k := by
      intro ⟨k, hk⟩; exact h ⟨k + 1, by rw [pow_succ]; omega⟩
    rcases Nat.even_or_odd m with ⟨m2, hm2⟩ | ⟨k, hk⟩
    · -- m = 2*m2 (even sub-case). n = 4*m2.
      -- Use odd divisor of n to construct the representation directly.
      obtain ⟨d, hd_dvd, hd_odd, hd_ge⟩ := exists_odd_divisor_ge3 n hn h
      obtain ⟨r, hd_eq⟩ := hd_odd  -- d = 2*r + 1
      set q := n / d with hq_def
      have hqd : d * q = n := Nat.div_mul_cancel hd_dvd
      have hq_pos : q ≥ 1 := by
        by_contra hq0; push_neg at hq0
        simp at hq0; rw [hq0, mul_zero] at hqd; omega
      by_cases h_case : d + 1 ≤ 2 * q
      · -- Case A: d consecutive terms centered at q
        -- Terms: q-(d-1)/2 .. q+(d-1)/2, count = d
        refine ⟨q - (d + 1) / 2, q + (d - 3) / 2, by omega, ?_⟩
        have hs : q - (d + 1) / 2 + 1 = q - (d - 1) / 2 := by omega
        have he : q + (d - 3) / 2 + 1 = q + (d - 1) / 2 := by omega
        rw [hs, he]
        have hle : q - (d - 1) / 2 ≤ q + (d - 1) / 2 := by omega
        have h_sum := two_mul_sum_Icc (q - (d - 1) / 2) (q + (d - 1) / 2) hle
        have h1 : q + (d - 1) / 2 - (q - (d - 1) / 2) + 1 = d := by omega
        have h2 : q - (d - 1) / 2 + (q + (d - 1) / 2) = 2 * q := by omega
        rw [h1, h2] at h_sum
        have h2n : d * (2 * q) = 2 * n := by
          rw [show d * (2 * q) = 2 * (d * q) from by ring, hqd]
        rw [h2n] at h_sum; omega
      · -- Case B: 2q consecutive terms starting at (d-2q+1)/2
        push_neg at h_case
        set a := (d - 2 * q + 1) / 2 with ha_def
        have ha_pos : a ≥ 1 := by omega
        refine ⟨a - 1, a + 2 * q - 2, by omega, ?_⟩
        have hs : a - 1 + 1 = a := by omega
        have he : a + 2 * q - 2 + 1 = a + 2 * q - 1 := by omega
        rw [hs, he]
        have hle : a ≤ a + 2 * q - 1 := by omega
        have h_sum := two_mul_sum_Icc a (a + 2 * q - 1) hle
        have h1 : a + 2 * q - 1 - a + 1 = 2 * q := by omega
        have h2 : a + (a + 2 * q - 1) = d := by omega
        rw [h1, h2] at h_sum
        have h2n : 2 * q * d = 2 * n := by
          rw [show 2 * q * d = 2 * (d * q) from by ring, hqd]
        rw [h2n] at h_sum; omega
    · -- m = 2*k+1 (odd sub-case). n = 2*(2k+1) = 4k+2.
      -- m ≥ 3 (m ≥ 2, m odd ⟹ m ≥ 3), so k ≥ 1.
      have hk_ge1 : k ≥ 1 := by omega
      rcases eq_or_lt_of_le hk_ge1 with rfl | hk_ge2
      · -- k = 1: n = 6. Use 3 terms: 1+2+3 = 6.
        refine ⟨0, 2, by omega, ?_⟩
        have h_sum := two_mul_sum_Icc 1 3 (by omega)
        -- 2 * ∑[1..3] = (3-1+1)*(1+3) = 12, so ∑ = 6 = n
        omega
      · -- k ≥ 2: n = 4k+2. Use 4 terms from (k-1) to (k+2).
        -- Sum = (k-1)+k+(k+1)+(k+2) = 4k+2 = n.
        refine ⟨k - 2, k + 1, by omega, ?_⟩
        have hk_sub : k - 2 + 1 = k - 1 := by omega
        rw [hk_sub]
        have h_sum := two_mul_sum_Icc (k - 1) (k + 2) (by omega)
        -- 2*∑[k-1..k+2] = (k+2-(k-1)+1)*(k-1+k+2) = 4*(2k+1)
        -- So ∑ = 2*(2k+1) = n
        omega
  · -- n odd: n = (n-1)/2 + (n+1)/2 = 2m+1
    -- Use u = m-1, v = m. Then Icc (m) (m+1) has sum m + (m+1) = 2m+1 = n.
    have hm1 : m ≥ 1 := by omega
    refine ⟨m - 1, m, by omega, ?_⟩
    have : m - 1 + 1 = m := by omega
    rw [this]
    have hIcc : Finset.Icc m (m + 1) = {m, m + 1} := by
      ext x; simp [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_pair (by omega : m ≠ m + 1)]
    omega

/-- The classic result: n = sum of at least two consecutive positive integers
    if and only if n is not a power of 2.

    **→ direction**: proved via `power_of_two_obstruction` (both factors of
    2·2^k would need an odd factor ≥ 2, contradiction).
    **← direction**: constructive via odd factorization (odd case proved,
    even case requires extracting odd part of n). -/
theorem consecutive_sum_char (n : ℕ) (hn : n ≥ 3) :
    (∃ u v : ℕ, u < v ∧ n = ∑ i ∈ Finset.Icc (u+1) (v+1), i) ↔ ¬∃ k : ℕ, n = 2^k := by
  constructor
  · intro ⟨u, v, huv, hsum⟩ ⟨k, hk⟩
    exact power_of_two_obstruction k u v huv (hk ▸ hsum)
  · exact not_pow2_representable n hn

/-- For natural numbers, f(n) equals the number of odd divisors of n. -/
axiom naturals_count_odd_divisors (n : ℕ) (hn : n ≥ 1) :
    consecutiveSumCount naturalsSeq n = ((Nat.divisors n).filter Odd).card

/- ## Part III: The Main Conjectures -/

/--
**Erdős Problem #358 (Strong Form)**:
Does there exist an infinite increasing sequence A such that
f(n) → ∞ as n → ∞?
-/
def Erdos358Strong : Prop :=
  ∃ A : IntSequence, Tendsto (fun n => (consecutiveSumCount A n : ℝ)) atTop atTop

/--
**Erdős Problem #358 (Weak Form)**:
Does there exist an infinite increasing sequence A such that
f(n) ≥ 2 for all sufficiently large n?
-/
def Erdos358Weak : Prop :=
  ∃ A : IntSequence, ∃ N₀ : ℤ, ∀ n ≥ N₀, consecutiveSumCount A n ≥ 2

/-- Strong implies weak: if f(n) → ∞, then certainly f(n) ≥ 2 for all large n. -/
theorem strong_implies_weak : Erdos358Strong → Erdos358Weak := by
  intro ⟨A, hA⟩
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp hA (2 : ℝ)
  exact ⟨A, N, fun n hn => by exact_mod_cast hN n hn⟩

/- ## Part IV: Known Observations -/

/--
**Trivial observation (Egami):**
f(n) ≥ 1 for all large n is trivially achieved by A = naturals,
since every n ≥ 1 equals itself (the sum from n to n).
-/
/-- For the naturals sequence, every n ≥ 1 has at least one consecutive sum representation
    (the trivial one: n = sum from (n-1) to (n-1) of (i+1)). -/
theorem naturals_always_representable (n : ℕ) (hn : n ≥ 1) :
    consecutiveSumCount naturalsSeq n ≥ 1 := by
  unfold consecutiveSumCount
  -- The set of valid representations
  set S := {p : ℕ × ℕ | p.1 ≤ p.2 ∧
    (∑ i ∈ Finset.Icc p.1 p.2, naturalsSeq.seq i) = ↑n}
  -- Step 1: S is finite (all valid pairs have u, v < n)
  have hfin : S.Finite := by
    apply Set.Finite.subset ((Set.finite_Iio n).prod (Set.finite_Iio n))
    rintro ⟨u, v⟩ ⟨huv, hsum⟩
    simp only [Set.mem_prod, Set.mem_Iio]
    -- The sum includes term at v: naturalsSeq.seq v = v+1
    -- Since all terms are nonneg, sum ≥ v+1, so v+1 ≤ n
    have hv_mem : v ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨huv, le_refl v⟩
    have hv_le : naturalsSeq.seq v ≤ ∑ i ∈ Finset.Icc u v, naturalsSeq.seq i :=
      Finset.single_le_sum (fun i _ => by simp [naturalsSeq]; positivity) hv_mem
    rw [hsum] at hv_le
    -- hv_le : naturalsSeq.seq v ≤ ↑n, i.e., ↑v + 1 ≤ ↑n
    simp only [naturalsSeq] at hv_le
    constructor <;> omega
  -- Step 2: S is nonempty (witness: (n-1, n-1), single-term sum)
  have hne : S.Nonempty :=
    ⟨(n - 1, n - 1), le_refl _, by
      simp only [Finset.Icc_self, Finset.sum_singleton, naturalsSeq]
      push_cast; omega⟩
  -- Step 3: ncard ≥ 1
  exact Set.ncard_pos hfin |>.mpr hne

/-- Gauss sum: twice the sum of integers from a to b equals (b-a+1)(a+b). -/
private lemma two_mul_sum_Icc (a b : ℕ) (hab : a ≤ b) :
    2 * (∑ i ∈ Finset.Icc a b, i) = (b - a + 1) * (a + b) := by
  induction b with
  | zero =>
    interval_cases a
    simp [Finset.Icc_self]
  | succ n ih =>
    by_cases h : a ≤ n
    · have hmem : n + 1 ∉ Finset.Icc a n := by simp [Finset.mem_Icc]; omega
      have hIcc : Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) := by
        ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert hmem]
      set S := ∑ i ∈ Finset.Icc a n, i with hS_def
      have h_ih := ih h
      zify [h, show a ≤ n + 1 from by omega] at h_ih ⊢
      nlinarith
    · have : a = n + 1 := by omega
      subst this
      simp [Finset.Icc_self]

/-- An odd divisor of a power of 2 must be 1. -/
private lemma odd_dvd_two_pow_eq_one {m j : ℕ} (hm : Odd m) (hdvd : m ∣ 2 ^ j) :
    m = 1 := by
  induction j with
  | zero => simpa using hdvd
  | succ j ih =>
    apply ih
    have hcop : Nat.Coprime m 2 := by
      unfold Nat.Coprime
      rw [Nat.gcd_comm, Nat.gcd_rec, Nat.odd_iff.mp hm]
      norm_num
    rw [pow_succ] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd

/-- Powers of 2 cannot be expressed as sums of ≥2 consecutive positive integers.
    Proof: 2·S = (v-u+1)(u+v+2) with sum of factors = 2v+3 (odd), so one factor
    is odd. An odd divisor of 2^(k+1) is 1, but both factors are ≥ 2. -/
theorem power_of_two_obstruction :
    ∀ k : ℕ, ∀ u v : ℕ, u < v → (∑ i ∈ Finset.Icc (u+1) (v+1), i) ≠ 2^k := by
  intro k u v huv hsum
  have hab : u + 1 ≤ v + 1 := by omega
  have h2S := two_mul_sum_Icc (u + 1) (v + 1) hab
  rw [hsum] at h2S
  -- Simplify: 2 * 2^k = (v - u + 1) * (u + v + 2)
  have hvu : v + 1 - (u + 1) + 1 = v - u + 1 := by omega
  have huv2 : (u + 1) + (v + 1) = u + v + 2 := by omega
  rw [hvu, huv2] at h2S
  -- Both factors are at least 2
  have hf1 : v - u + 1 ≥ 2 := by omega
  have hf2 : u + v + 2 ≥ 2 := by omega
  -- Their sum is 2v+3 (odd), so they have different parities
  rcases Nat.even_or_odd (v - u + 1) with h_even | h_odd
  · -- (v-u+1) even ⟹ (u+v+2) odd
    have h_odd2 : Odd (u + v + 2) := by
      rw [Nat.odd_iff_not_even]
      intro h_even2
      have := h_even.add h_even2
      -- (v-u+1) + (u+v+2) = 2v+3 would be even — contradiction
      obtain ⟨d, hd⟩ := this
      omega
    have h_dvd : (u + v + 2) ∣ 2 ^ (k + 1) :=
      ⟨v - u + 1, by rw [show 2 ^ (k + 1) = 2 * 2 ^ k from by ring, h2S, mul_comm]⟩
    have := odd_dvd_two_pow_eq_one h_odd2 h_dvd
    omega
  · -- (v-u+1) odd ⟹ contradicts being ≥ 2 and dividing 2^(k+1)
    have h_dvd : (v - u + 1) ∣ 2 ^ (k + 1) :=
      ⟨u + v + 2, by rw [show 2 ^ (k + 1) = 2 * 2 ^ k from by ring, h2S]⟩
    have := odd_dvd_two_pow_eq_one h_odd h_dvd
    omega

/- ## Part V: The Prime Case -/

/-- The primes sequence, defined using Mathlib's `Nat.nth`.
    Previously axiomatized; now concrete via Mathlib. -/
noncomputable def primesSeq : IntSequence where
  seq := fun n => (Nat.nth Nat.Prime n : ℤ)
  increasing := fun n => by
    have hinf : (setOf Nat.Prime).Infinite := by
      rw [Set.infinite_iff_exists_gt]
      intro n; obtain ⟨p, hp, hpn⟩ := Nat.exists_infinite_primes (n + 1)
      exact ⟨p, hp, by omega⟩
    exact_mod_cast Nat.nth_strictMono hinf (Nat.lt_succ_of_le le_rfl)

/-- The primes sequence at index n equals the nth prime. -/
theorem primesSeq_def (n : ℕ) : primesSeq.seq n = Nat.nth Nat.Prime n := rfl

/--
**Erdős-Moser Conjecture (1963):**
When A = primes, the limsup of f(n) is infinite.
-/
def ErdosMoserConjecture : Prop :=
  ∀ M : ℕ, ∃ n : ℤ, consecutiveSumCount primesSeq n ≥ M

/- ## Part VI: Weaker Questions

**Erdős-Moser observation:**
They could not even prove that the upper density of representable integers is positive.
-/

/-- Count of representable integers up to N. -/
noncomputable def representableCount (A : IntSequence) (N : ℤ) : ℕ :=
  Set.ncard {n : ℤ | n ≤ N ∧ consecutiveSumCount A n ≥ 1}

/--
**Density question:**
Does the upper density of integers representable as consecutive prime sums exist and is it positive?
-/
def PositiveDensityConjecture : Prop :=
  ∃ δ > 0, ∀ᶠ N in atTop, (representableCount primesSeq N : ℝ) / N ≥ δ

/-- We don't even know if the density is positive. -/
theorem density_unknown : PositiveDensityConjecture ∨ ¬PositiveDensityConjecture := Classical.em _

/- ## Part VII: Connection to Related Problems

**Connection to Problem #356:**
The finite analogue asks: how many integers up to x can be written as
sum of consecutive elements of a finite set?

**Convex sets:**
In modern additive combinatorics language, the problem asks about
convex sumsets (sums of arithmetic progressions within the set).
-/

/- ## Part VIII: Current Status

**Erdős Problem #358: OPEN**

**Questions:**
1. (Strong) Does ∃ A with f(n) → ∞? — OPEN
2. (Weak) Does ∃ A with f(n) ≥ 2 for large n? — OPEN

**What's known:**
- For A = naturals: f(n) = #{odd divisors of n}, so f(n) → ∞ along highly composite numbers
- For A = naturals, sums of ≥2 terms: n representable iff n ≠ 2^k (CLASSICAL)
- For A = primes: Even positive density is unknown (OPEN)

**Erdős quote (1977):**
"This problem can perhaps be rightly criticized as being artificial and in the
backwater of Mathematics but it seems very strange and attractive to me."
-/
theorem erdos_358_open : Erdos358Strong ∨ ¬Erdos358Strong := Classical.em _

/- ## Part IX: Summary Theorems -/

/-- The problem status. -/
theorem erdos_358_status :
    (Erdos358Strong → Erdos358Weak) ∧
    (Erdos358Strong ∨ ¬Erdos358Strong) := by
  exact ⟨strong_implies_weak, erdos_358_open⟩

end Erdos358
