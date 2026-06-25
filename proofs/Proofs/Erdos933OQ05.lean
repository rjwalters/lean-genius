/-
  Erdős Problem #933 — Open Question #5 (verified resolution of the three sorries)

  Parent entry: `erdos-933` ("Smooth Part of Consecutive Products"), which is
  *axiomatized* and whose `conclusion.openQuestions[4]` asks:

    "Can the 3 sorries (`steinerberger_gives_large_smooth`, `power2_consecutive`,
     `power3_consecutive`) be resolved via Mathlib tactics?"

  Answer: YES. This file discharges all three with 0 axioms and 0 sorries, and in
  doing so gives a *fully verified* proof of the genuine Erdős/Steinerberger
  statement:

    For infinitely many n, the {2,3}-smooth part of n(n+1) exceeds n · log n.

  (Erdős, "Problems and results on consecutive integers" (1976): Mahler proved
   2^k·3^l < n^{1+o(1)}; Erdős noted it is "easy to see" that 2^k·3^l > n·log n for
   infinitely many n; Steinerberger gave the simple witness n = 2^{3^r}.)

  Mathematical note on the parent's framing.  For Steinerberger's witnesses
  n = 2^{3^r} one has 2^k·3^l = n·3^{r+1} and n·log n = n·3^r·log 2, so the ratio
  2^k·3^l/(n·log n) = 3/log 2 ≈ 4.33 — a CONSTANT exceeding 1, not tending to ∞.
  Thus this construction proves precisely the "infinitely often > n·log n" claim
  that Erdős actually stated; it does not by itself establish limsup = ∞.

  Engine.  The single nontrivial input is the lifting-the-exponent fact
    3^{r+1} ∣ 2^{3^r} + 1,
  proved here by an elementary induction from the factorisation
    a^3 + 1 = (a+1)(a^2 - a + 1),  with  3 ∣ a^2 - a + 1  whenever 3 ∣ a + 1.
-/

import Mathlib

open Nat Real

namespace Erdos933OQ05

/-! ## Part I: Basic definitions (mirroring the parent entry) -/

/-- The {2,3}-smooth part of `n`: the largest divisor of the form `2^a · 3^b`. -/
def smoothPart23 (n : ℕ) : ℕ := 2 ^ n.factorization 2 * 3 ^ n.factorization 3

/-- The {2,3}-smooth part of `n(n+1)`. -/
def consecutiveSmoothPart (n : ℕ) : ℕ := smoothPart23 (n * (n + 1))

/-! ## Part II: The lifting-the-exponent engine

`3^{r+1} ∣ 2^{3^r} + 1`, the divisibility that powers Steinerberger's witness. -/

/-- One inductive step of the LTE computation, stated over `ℤ` to dodge `ℕ`
    truncated subtraction.  If `3^{e+1} ∣ a + 1` then `3^{e+2} ∣ a^3 + 1`. -/
theorem lift3 (a : ℤ) (e : ℕ) (h : (3 : ℤ) ^ (e + 1) ∣ a + 1) :
    (3 : ℤ) ^ (e + 2) ∣ a ^ 3 + 1 := by
  obtain ⟨u, hu⟩ := h
  -- 3 ∣ a + 1 (since 3 ∣ 3^{e+1})
  have h3 : (3 : ℤ) ∣ a + 1 := (dvd_pow_self 3 (Nat.succ_ne_zero e)).trans ⟨u, hu⟩
  obtain ⟨t, ht⟩ := h3
  have e1 : a = 3 * t - 1 := by linarith
  refine ⟨u * (3 * t ^ 2 - 3 * t + 1), ?_⟩
  have factored : a ^ 3 + 1 = (a + 1) * (a ^ 2 - a + 1) := by ring
  rw [factored, hu, e1, pow_succ]; ring

/-- **LTE core.**  `3^{r+1}` divides `2^{3^r} + 1` for every `r`. -/
theorem lte_core (r : ℕ) : (3 : ℕ) ^ (r + 1) ∣ 2 ^ (3 ^ r) + 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    have ihZ : (3 : ℤ) ^ (r + 1) ∣ (2 : ℤ) ^ (3 ^ r) + 1 := by exact_mod_cast ih
    have hlift := lift3 ((2 : ℤ) ^ (3 ^ r)) r ihZ
    have hpow : (2 : ℕ) ^ (3 ^ (r + 1)) = (2 ^ (3 ^ r)) ^ 3 := by
      rw [pow_succ, pow_mul]
    rw [hpow]
    exact_mod_cast hlift

/-! ## Part III: resolving `power2_consecutive` and `power3_consecutive`

The two factorisation sorries of the parent file, for an arbitrary prime exponent. -/

/-- The exponent of a prime in `n(n+1)` is the sum of its exponents in `n` and
    `n+1` (the parent's `power2_consecutive` / `power3_consecutive`, uniformly). -/
theorem factorization_consecutive (p n : ℕ) :
    (n * (n + 1)).factorization p = n.factorization p + (n + 1).factorization p := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [Nat.factorization_mul h.ne' (Nat.succ_ne_zero n)]; simp

/-- The parent's `power2_consecutive`. -/
theorem power2_consecutive (n : ℕ) :
    (n * (n + 1)).factorization 2 = n.factorization 2 + (n + 1).factorization 2 :=
  factorization_consecutive 2 n

/-- The parent's `power3_consecutive`. -/
theorem power3_consecutive (n : ℕ) :
    (n * (n + 1)).factorization 3 = n.factorization 3 + (n + 1).factorization 3 :=
  factorization_consecutive 3 n

/-! ## Part IV: the smooth part of `2^{3^r} · (2^{3^r} + 1)` -/

/-- `2^e` carries exactly `e` factors of 2. -/
theorem fact2_pow2 (e : ℕ) : (2 ^ e).factorization 2 = e := by
  rw [Nat.Prime.factorization_pow Nat.prime_two]; simp

/-- **Resolving `steinerberger_gives_large_smooth` (ℕ form).**
    For `n = 2^{3^r}`, the {2,3}-smooth part of `n(n+1)` is at least `n · 3^{r+1}`. -/
theorem steinerberger_smooth_lower (r : ℕ) :
    2 ^ (3 ^ r) * 3 ^ (r + 1) ≤ consecutiveSmoothPart (2 ^ (3 ^ r)) := by
  have hn0 : (2 ^ (3 ^ r)) ≠ 0 := by positivity
  have hn1 : (2 ^ (3 ^ r)) + 1 ≠ 0 := Nat.succ_ne_zero _
  -- 2-part: at least 3^r (all of it already lives in n)
  have hv2 : 3 ^ r ≤ (2 ^ (3 ^ r) * (2 ^ (3 ^ r) + 1)).factorization 2 := by
    rw [power2_consecutive, fact2_pow2]; exact Nat.le_add_right _ _
  -- 3-part: at least r+1 (all of it lives in n+1, by the LTE core)
  have hv3n1 : r + 1 ≤ (2 ^ (3 ^ r) + 1).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn1).mp (lte_core r)
  have hv3 : r + 1 ≤ (2 ^ (3 ^ r) * (2 ^ (3 ^ r) + 1)).factorization 3 := by
    rw [power3_consecutive]; exact le_trans hv3n1 (Nat.le_add_left _ _)
  -- assemble the product bound
  have e2 : 2 ^ (3 ^ r) ≤ 2 ^ (2 ^ (3 ^ r) * (2 ^ (3 ^ r) + 1)).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) hv2
  have e3 : 3 ^ (r + 1) ≤ 3 ^ (2 ^ (3 ^ r) * (2 ^ (3 ^ r) + 1)).factorization 3 :=
    Nat.pow_le_pow_right (by norm_num) hv3
  calc 2 ^ (3 ^ r) * 3 ^ (r + 1)
      ≤ 2 ^ (2 ^ (3 ^ r) * (2 ^ (3 ^ r) + 1)).factorization 2
          * 3 ^ (2 ^ (3 ^ r) * (2 ^ (3 ^ r) + 1)).factorization 3 := Nat.mul_le_mul e2 e3
    _ = consecutiveSmoothPart (2 ^ (3 ^ r)) := rfl

/-! ## Part V: exceeding `n · log n`, and infinitely often -/

/-- For `n = 2^{3^r}`, the {2,3}-smooth part of `n(n+1)` strictly exceeds
    `n · log n`.  Quantitatively the smooth part is `≥ n · 3^{r+1}` while
    `n · log n = n · 3^r · log 2`, and `3^{r+1} > 3^r · log 2` because
    `3 > log 2`. -/
theorem steinerberger_exceeds (r : ℕ) :
    (2 ^ (3 ^ r) : ℝ) * Real.log (2 ^ (3 ^ r))
      < (consecutiveSmoothPart (2 ^ (3 ^ r)) : ℝ) := by
  set n : ℝ := (2 ^ (3 ^ r) : ℝ) with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  -- log (2^{3^r}) = 3^r · log 2
  have hlog : Real.log (2 ^ (3 ^ r)) = (3 ^ r : ℝ) * Real.log 2 := by
    rw [show ((2 : ℝ) ^ (3 ^ r)) = (2 : ℝ) ^ (3 ^ r : ℕ) from by norm_num,
      Real.log_pow]
    push_cast; ring
  -- 3 > log 2
  have hlog2 : Real.log 2 < 3 := by
    have : Real.log 2 < 1 := by
      have h2 : (2 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      calc Real.log 2 < Real.log (Real.exp 1) := by
            exact Real.log_lt_log (by norm_num) h2
        _ = 1 := Real.log_exp 1
    linarith
  -- n · log n < n · 3^{r+1} ≤ smooth part
  have step1 : n * Real.log (2 ^ (3 ^ r)) < n * (3 ^ (r + 1) : ℝ) := by
    rw [hlog]
    have h3r : (0 : ℝ) < (3 ^ r : ℝ) := by positivity
    have : (3 ^ r : ℝ) * Real.log 2 < (3 ^ (r + 1) : ℝ) := by
      rw [pow_succ]
      have : (3 ^ r : ℝ) * Real.log 2 < (3 ^ r : ℝ) * 3 := by
        apply mul_lt_mul_of_pos_left hlog2 h3r
      linarith
    apply mul_lt_mul_of_pos_left this hnpos
  have step2 : n * (3 ^ (r + 1) : ℝ) ≤ (consecutiveSmoothPart (2 ^ (3 ^ r)) : ℝ) := by
    have hnat := steinerberger_smooth_lower r
    have : ((2 ^ (3 ^ r) * 3 ^ (r + 1) : ℕ) : ℝ) ≤ (consecutiveSmoothPart (2 ^ (3 ^ r)) : ℝ) := by
      exact_mod_cast hnat
    rw [hn]; push_cast at this ⊢; linarith
  linarith [step1, step2]

/-- **Main verified result (genuine Erdős/Steinerberger claim).**
    For every `N` there is `n > N` whose consecutive product `n(n+1)` has
    {2,3}-smooth part exceeding `n · log n`.  In particular this holds for
    infinitely many `n`, with no axioms. -/
theorem smooth_part_exceeds_n_log_n_infinitely_often :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧
      (consecutiveSmoothPart n : ℝ) > (n : ℝ) * Real.log n := by
  intro N
  -- choose r with 2^{3^r} > N; r = N suffices since 2^{3^N} > N
  refine ⟨2 ^ (3 ^ N), ?_, ?_⟩
  · -- 2^{3^N} > N
    calc N < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ 2 ^ (3 ^ N) := Nat.pow_le_pow_right (by norm_num) (Nat.lt_pow_self (by norm_num)).le
  · have := steinerberger_exceeds N
    push_cast at this ⊢
    linarith

/-! ## Part VI: small sanity checks (kernel-decidable, axiom-free) -/

/-- The LTE core at `r = 2`: `3^3 = 27 ∣ 2^9 + 1 = 513`. -/
example : (3 : ℕ) ^ 3 ∣ 2 ^ (3 ^ 2) + 1 := by decide

/-- The LTE core at `r = 3`: `3^4 = 81 ∣ 2^27 + 1`. -/
example : (3 : ℕ) ^ 4 ∣ 2 ^ (3 ^ 3) + 1 := by decide

/-! ## Part VII: axiom audit -/

-- All main results depend only on the standard foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms lte_core
#print axioms steinerberger_smooth_lower
#print axioms steinerberger_exceeds
#print axioms smooth_part_exceeds_n_log_n_infinitely_often

end Erdos933OQ05
