/-
# Erdős Problem #680: Least Prime Factor Exceeding k² + 1

For a positive integer m, let p(m) denote its least prime factor. Erdős asked:
is it true that for all sufficiently large n, there exists some k ≥ 1 such that
p(n + k) > k² + 1?

The stronger variant asks whether this fails when k² + 1 is replaced by
e^{(1+ε)√k} + C_ε for all ε > 0 and some constant C_ε.

This is connected to prime gap conjectures: Cramér's conjecture would imply
existence of k with p(n+k) > e^{(1-ε)√k}. Granville refined the expected
constant from 1 to 2e^{-γ} ≈ 1.119.

Related to Problems #681 and #682.

Reference: https://erdosproblems.com/680
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/- ## Least Prime Factor and the Main Conjecture -/

/-- Erdős Problem 680 (main): For all sufficiently large n, there exists
    k ≥ 1 such that minFac(n + k) > k² + 1. -/
def ErdosProblem680 : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ k : ℕ, 0 < k ∧ (n + k).minFac > k ^ 2 + 1

/-- Predicate: n has the "large least prime factor" property for some offset. -/
def HasLargeLPF (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (n + k).minFac > k ^ 2 + 1

/- ## Exponential Variant -/

/-- The stronger exponential variant: it is false that for all sufficiently
    large n, there exists k with minFac(n+k) > e^{(1+ε)√k} + C.
    In other words, the exponential bound eventually fails. -/
def ErdosProblem680Variant : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ¬(∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ k : ℕ, 0 < k ∧
          (n + k).minFac > ⌊Real.exp ((1 + ε) * Real.sqrt k) + C⌋₊)

/-- The combined problem: the main conjecture is true and the exponential
    variant confirms the quadratic bound cannot be exponentially improved. -/
def ErdosProblem680Combined : Prop :=
  ErdosProblem680 ∧ ErdosProblem680Variant

/- ## Basic Properties -/

/-- The quadratic bound k² + 1 grows slower than the exponential e^{(1+ε)√k}
    for large k, so the main conjecture is weaker than the exponential version.
    Proof: x^4 · exp(-(1+ε)x) → 0 composed with x = √k gives k² · exp(-(1+ε)√k) → 0,
    so eventually k² < (1/2)exp((1+ε)√k) and 1 < (1/2)exp((1+ε)√k). -/
theorem quadratic_weaker_than_exponential (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (k ^ 2 + 1 : ℝ) < Real.exp ((1 + ε) * Real.sqrt k) := by
  have hc : 0 < 1 + ε := by linarith
  -- x^4 * exp(-(1+ε)*x) → 0 as x → ∞
  have h_tend := Real.tendsto_pow_mul_exp_neg_atTop_nhds 4 (1 + ε) hc
  -- Compose with √· : ℕ → ℝ (which tends to atTop)
  have h_sqrt_atTop : Tendsto (fun k : ℕ => Real.sqrt (↑k)) atTop atTop :=
    (Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
  have h_comp := h_tend.comp h_sqrt_atTop
  -- h_comp : (√k)^4 * exp(-(1+ε)*√k) → 0
  -- Eventually < 1/2
  have h_ev : ∀ᶠ k in atTop, (Real.sqrt (↑k)) ^ 4 * Real.exp (-(1 + ε) * Real.sqrt (↑k)) < 1/2 :=
    h_comp.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  -- exp((1+ε)*√k) → ∞, so eventually > 2
  have h_exp_large : ∀ᶠ k in atTop, 2 < Real.exp ((1 + ε) * Real.sqrt (↑k)) := by
    have : Tendsto (fun k : ℕ => (1 + ε) * Real.sqrt (↑k)) atTop atTop :=
      (tendsto_atTop_atTop_of_monotone (fun a b h => by nlinarith [Real.sqrt_le_sqrt (by exact_mod_cast h : (a:ℝ) ≤ b)]) ⟨0, fun b => ⟨⌈(b / (1 + ε))^2⌉₊, by nlinarith [Real.sq_sqrt (Nat.cast_nonneg ⌈(b / (1 + ε))^2⌉₊)]⟩⟩)
    exact (Real.tendsto_exp_atTop.comp this).eventually (Ioi_mem_atTop 2)
  -- Extract K₀ from both eventually conditions
  obtain ⟨K₀, hK₀⟩ := (h_ev.and h_exp_large).exists_forall_of_atTop
  refine ⟨K₀, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hK₀ k hk
  -- (√k)^4 = k² for k ≥ 0
  have h_sq : (Real.sqrt (↑k)) ^ 4 = (↑k : ℝ) ^ 2 := by
    have := Real.sq_sqrt (Nat.cast_nonneg k)
    nlinarith [sq_nonneg (Real.sqrt ↑k)]
  -- From h1: k² * exp(-c√k) < 1/2, so k² < (1/2) * exp(c√k)
  have hexp_pos : 0 < Real.exp ((1 + ε) * Real.sqrt ↑k) := Real.exp_pos _
  have hk2_bound : (↑k : ℝ) ^ 2 < (1/2) * Real.exp ((1 + ε) * Real.sqrt ↑k) := by
    rw [← h_sq] at h1
    have : (Real.sqrt ↑k) ^ 4 < (1/2) * Real.exp ((1 + ε) * Real.sqrt ↑k) := by
      rw [show Real.exp (-(1 + ε) * Real.sqrt ↑k) = (Real.exp ((1 + ε) * Real.sqrt ↑k))⁻¹ from
        by rw [Real.exp_neg]] at h1
      rwa [mul_inv_lt_iff₀ hexp_pos] at h1
    rwa [h_sq] at this
  -- From h2: exp(c√k) > 2, so 1 < (1/2) * exp(c√k)
  have h1_bound : 1 < (1/2) * Real.exp ((1 + ε) * Real.sqrt ↑k) := by linarith
  -- Combine: k²+1 < (1/2)*exp + (1/2)*exp = exp
  linarith

/-- For k = 1, the condition minFac(n+1) > 2 means n+1 is odd and not 2. -/
theorem lpf_k1_means_odd (n : ℕ) (h : (n + 1).minFac > 1 ^ 2 + 1) :
    ¬(2 ∣ (n + 1)) := by
  simp at h
  intro h2
  have := Nat.minFac_le_of_dvd (by norm_num : 2 ≤ 2) h2
  omega

/-- When n + k is prime, minFac(n+k) = n+k, which easily exceeds k² + 1
    for large n. -/
theorem prime_offset_gives_large_lpf (n k : ℕ) (_hk : 0 < k)
    (hp : (n + k).Prime) (hn : k ^ 2 + 1 < n + k) :
    (n + k).minFac > k ^ 2 + 1 := by
  rw [hp.minFac_eq]
  exact hn

/- ## Granville's Refinement -/

/-- Granville's constant: 2e^{-γ} where γ is the Euler-Mascheroni constant.
    This is approximately 1.1229. -/
noncomputable def granvilleConstant : ℝ :=
  2 * Real.exp (-Real.log 2 * 0.8365) -- approximation

/-- Granville's refined conjecture: the maximal prime gap after p is
    asymptotically at most 2e^{-γ} (log p)², not (log p)² as Cramér
    originally conjectured. -/
def GranvilleRefinement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ p : ℕ, p.Prime → N₀ ≤ p →
      (Nat.find (Nat.exists_infinite_primes (p + 1)) - p : ℝ) ≤
        (granvilleConstant + ε) * (Real.log p) ^ 2

/- ## Proved Reductions -/

/-- The main conjecture follows from the existence of a prime in [n+1, n+k]
    for some k with k² + 1 < that prime. This converts the number-theoretic
    question to a prime distribution question. -/
theorem problem680_from_prime_distribution
    (h : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 0 < k ∧ (n + k).Prime ∧ k ^ 2 + 1 < n + k) :
    ErdosProblem680 := by
  obtain ⟨N₀, hN₀⟩ := h
  exact ⟨N₀, fun n hn => by
    obtain ⟨k, hk, hprime, hbound⟩ := hN₀ n hn
    exact ⟨k, hk, prime_offset_gives_large_lpf n k hk hprime hbound⟩⟩

/- ## Structural Lemmas -/

/-- If n + 1 is prime and n ≥ 2, then HasLargeLPF n holds (with k = 1).
    The successor being prime guarantees minFac(n+1) = n+1 > 2 = 1² + 1. -/
theorem hasLargeLPF_of_succ_prime (n : ℕ) (hn : 2 ≤ n) (hp : (n + 1).Prime) :
    HasLargeLPF n := by
  refine ⟨1, Nat.one_pos, ?_⟩
  rw [hp.minFac_eq]
  simp
  omega

/-- For any prime p with n < p and k = p - n satisfying k² + 1 < p,
    the HasLargeLPF property holds for n. -/
theorem hasLargeLPF_from_nearby_prime (n : ℕ) (p : ℕ) (hp : p.Prime)
    (hn : n < p) (hk : ∃ k : ℕ, 0 < k ∧ n + k = p ∧ k ^ 2 + 1 < p) :
    HasLargeLPF n := by
  obtain ⟨k, hk_pos, hkp, hbound⟩ := hk
  exact ⟨k, hk_pos, by rw [hkp, hp.minFac_eq]; exact hbound⟩

/-- minFac of a prime equals itself. -/
theorem minFac_prime_self (p : ℕ) (hp : p.Prime) : p.minFac = p :=
  hp.minFac_eq

/-- If m ≥ 2 and m is not divisible by any prime ≤ b, then minFac m > b.
    This gives a way to establish lower bounds on minFac by excluding
    small prime divisors. -/
theorem minFac_gt_of_no_small_divisor (m : ℕ) (hm : 2 ≤ m) (b : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ≤ b → ¬(p ∣ m)) :
    m.minFac > b := by
  by_contra hle
  push_neg at hle
  have hprime := Nat.minFac_prime (by omega : m ≠ 1)
  exact h m.minFac hprime hle (Nat.minFac_dvd m)

/-- Monotonicity: if HasLargeLPF holds for n with offset k,
    and n' + k' = n + k for some k' with k' ≤ k, then the LPF
    bound from the offset is even stronger for n'. -/
theorem hasLargeLPF_monotone_offset (n k : ℕ) (hk : 0 < k)
    (h : (n + k).minFac > k ^ 2 + 1) (n' k' : ℕ) (hk' : 0 < k')
    (heq : n' + k' = n + k) (hle : k' ≤ k) :
    (n' + k').minFac > k' ^ 2 + 1 := by
  rw [heq]
  calc k' ^ 2 + 1 ≤ k ^ 2 + 1 := by nlinarith
    _ < (n + k).minFac := h

/- ## Computational Verification -/

-- Verify HasLargeLPF for various n values.
-- For even n, n+1 is odd and often prime, giving k=1 witness.
-- For n = 2: n+1 = 3 is prime, minFac(3) = 3 > 1² + 1 = 2
example : HasLargeLPF 2 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 4: n+1 = 5 is prime
example : HasLargeLPF 4 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 6: n+1 = 7 is prime
example : HasLargeLPF 6 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 8: n+1 = 9 = 3², minFac(9) = 3 > 2. Yes!
example : HasLargeLPF 8 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 10: n+1 = 11 is prime
example : HasLargeLPF 10 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 12: n+1 = 13 is prime
example : HasLargeLPF 12 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 14: n+1 = 15 = 3·5, minFac(15) = 3 > 2. Yes!
example : HasLargeLPF 14 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 20: n+1 = 21 = 3·7, minFac(21) = 3 > 2. Yes!
example : HasLargeLPF 20 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 24: n+1 = 25 = 5², minFac(25) = 5 > 2. Yes!
example : HasLargeLPF 24 := ⟨1, Nat.one_pos, by native_decide⟩
-- For n = 100: n+1 = 101 is prime
example : HasLargeLPF 100 := ⟨1, Nat.one_pos, by native_decide⟩
