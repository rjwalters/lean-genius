/-
  Erdős Problem #12: Divisibility-Free Sets

  Source: https://erdosproblems.com/12
  Status: OPEN

  Statement:
  Let A be an infinite set such that there are no distinct a,b,c ∈ A
  with a | (b+c) and b,c > a.

  Questions:
  1. Is there such A with liminf |A ∩ {1,...,N}| / √N > 0?
  2. Is there c > 0 with infinitely many N having |A ∩ {1,...,N}| < N^(1-c)?
  3. Is Σ(1/n : n ∈ A) < ∞?

  Erdős-Sárközy (1970) proved such sets have density 0.
-/

import Mathlib

open Nat Finset Set Filter

/-! ## Core Definition -/

/-- The divisibility-free property: no a | (b+c) for distinct a < b,c in A -/
def IsDivisibilityFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → a ≠ c → b ≠ c → a < b → a < c →
    ¬(a ∣ (b + c))

/-- Counting function: |A ∩ {1,...,N}| -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-! ## Basic Examples -/

/-- Powers of 2 -/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2^k ∧ k ≥ 1}

/-- **IMPORTANT**: Powers of 2 do NOT form a divisibility-free set!

    Counterexample: a=2, b=4, c=8
    - All are distinct ✓
    - 4 > 2 and 8 > 2 ✓
    - 2 | (4 + 8) = 2 | 12 = True ✗

    The sum 2^j + 2^k = 2^min(j,k) * (1 + 2^|j-k|), and 2^i divides
    2^min(j,k) whenever i ≤ min(j,k). Since i < j and i < k implies
    i < min(j,k), we actually have i ≤ min(j,k), so 2^i | (2^j + 2^k).
-/
theorem powersOfTwo_not_divisibility_free : ¬IsDivisibilityFree powersOfTwo := by
  intro h
  -- Counterexample: a = 2, b = 4, c = 8
  have h2 : (2 : ℕ) ∈ powersOfTwo := ⟨1, rfl, le_refl 1⟩
  have h4 : (4 : ℕ) ∈ powersOfTwo := ⟨2, rfl, by omega⟩
  have h8 : (8 : ℕ) ∈ powersOfTwo := ⟨3, rfl, by omega⟩
  have hdiv : (2 : ℕ) ∣ (4 + 8) := ⟨6, rfl⟩
  exact h 2 4 8 h2 h4 h8 (by omega) (by omega) (by omega) (by omega) (by omega) hdiv

/-- Squares of primes ≡ 3 (mod 4) form a good construction.

    This construction works because:
    - If p,q,r are distinct primes ≡ 3 (mod 4) with p² < q², r²
    - Then p² cannot divide q² + r² because:
      - For p² | (q² + r²), we'd need p | (q² + r²)
      - In ZMod p: q² + r² ≡ 0 means (r/q)² ≡ -1 (mod p)
      - But p ≡ 3 (mod 4) implies -1 is a quadratic non-residue mod p
      - So no such square root exists → contradiction
-/
def primeSquares3mod4 : Set ℕ :=
  {n | ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ n = p^2}

/-- The first supplementary law: -1 is a quadratic non-residue mod p when p ≡ 3 (mod 4) -/
lemma neg_one_not_square_mod_three_mod_four (p : ℕ) [hp : Fact p.Prime] (h3 : p % 4 = 3) :
    ¬IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  omega

/-- If p ∤ n, then p² ∤ n (simple helper) -/
lemma sq_not_dvd_of_not_dvd {p n : ℕ} (_hp : p.Prime) (h : ¬(p ∣ n)) : ¬(p^2 ∣ n) := by
  intro hdiv
  have : p ∣ p^2 := ⟨p, by ring⟩
  exact h (Nat.dvd_trans this hdiv)

/-- If p,q,r are distinct primes ≡ 3 (mod 4) with p < q and p < r, then p ∤ (q² + r²).

    The proof uses the first supplementary law of quadratic reciprocity:
    -1 is a quadratic residue mod p iff p ≢ 3 (mod 4).

    **Proof sketch:**
    1. Suppose p | (q² + r²). Then in ZMod p: q² + r² ≡ 0.
    2. Since p < q and p < r are distinct primes, p ∤ q and p ∤ r.
    3. So q, r are units in ZMod p, and we get (r/q)² = -1.
    4. But p ≡ 3 (mod 4) means -1 is not a square mod p. Contradiction.
-/
lemma prime_3mod4_not_div_sum_squares {p q r : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hp3 : p % 4 = 3) (_hq3 : q % 4 = 3) (_hr3 : r % 4 = 3)
    (hpq : p ≠ q) (hpr : p ≠ r) (_hqr : q ≠ r)
    (_hpltq : p < q) (_hpltr : p < r) :
    ¬(p ∣ q^2 + r^2) := by
  intro hdiv
  haveI : Fact p.Prime := ⟨hp⟩
  -- In ZMod p, q² + r² ≡ 0
  have hzmod : (q : ZMod p)^2 + (r : ZMod p)^2 = 0 := by
    have heq : ((q^2 + r^2 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hdiv
    simp only [Nat.cast_add, Nat.cast_pow] at heq
    exact heq
  -- Since p < q are distinct primes, p ∤ q, so q ≠ 0 in ZMod p
  have hq_ne : (q : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdivpq
    -- If p | q and q is prime, then p = 1 or p = q. Since p is prime, p ≠ 1, so p = q.
    have : p = 1 ∨ p = q := hq.eq_one_or_self_of_dvd p hdivpq
    rcases this with h1 | heq
    · exact hp.ne_one h1
    · exact hpq heq
  have hr_ne : (r : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdivpr
    have : p = 1 ∨ p = r := hr.eq_one_or_self_of_dvd p hdivpr
    rcases this with h1 | heq
    · exact hp.ne_one h1
    · exact hpr heq
  -- From q² + r² = 0, we get r² = -q²
  have hr2_eq : (r : ZMod p)^2 = -((q : ZMod p)^2) := eq_neg_of_add_eq_zero_right hzmod
  -- (r/q)² = -1, so -1 is a square
  have hsq : IsSquare (-1 : ZMod p) := by
    use (r : ZMod p) * (q : ZMod p)⁻¹
    -- Goal: -1 = (r * q⁻¹) * (r * q⁻¹), so swap sides
    symm
    have hq2_ne : (q : ZMod p)^2 ≠ 0 := pow_ne_zero 2 hq_ne
    calc (r : ZMod p) * (q : ZMod p)⁻¹ * ((r : ZMod p) * (q : ZMod p)⁻¹)
        = (r : ZMod p)^2 * ((q : ZMod p)⁻¹)^2 := by ring
      _ = (r : ZMod p)^2 * ((q : ZMod p)^2)⁻¹ := by rw [inv_pow]
      _ = -((q : ZMod p)^2) * ((q : ZMod p)^2)⁻¹ := by rw [hr2_eq]
      _ = -1 := by rw [neg_mul, mul_inv_cancel₀ hq2_ne]
  -- But -1 is not a square mod p when p ≡ 3 (mod 4)
  exact neg_one_not_square_mod_three_mod_four p hp3 hsq

/-- **Main theorem**: Squares of primes ≡ 3 (mod 4) form a divisibility-free set.

    If p², q², r² are distinct squares of primes ≡ 3 (mod 4) with p² < q², r²,
    then p² ∤ (q² + r²).

    **Proof**: Since p < q and p < r (as distinct primes with p² < q², r²),
    we have p ∤ (q² + r²) by `prime_3mod4_not_div_sum_squares`.
    Since p ∤ (q² + r²), certainly p² ∤ (q² + r²).
-/
theorem primeSquares3mod4_divisibility_free : IsDivisibilityFree primeSquares3mod4 := by
  intro a b c ha hb hc hab hac hbc haltb haltc
  -- Unpack: a = p², b = q², c = r² for primes p, q, r ≡ 3 (mod 4)
  obtain ⟨p, hp, hp3, rfl⟩ := ha
  obtain ⟨q, hq, hq3, rfl⟩ := hb
  obtain ⟨r, hr, hr3, rfl⟩ := hc
  -- Since p² ≠ q² and both are squares of primes, p ≠ q
  have hpq : p ≠ q := by
    intro heq
    subst heq
    exact hab rfl
  have hpr : p ≠ r := by
    intro heq
    subst heq
    exact hac rfl
  have hqr : q ≠ r := by
    intro heq
    subst heq
    exact hbc rfl
  -- From p² < q² and p² < r², get p < q and p < r
  have hpltq : p < q := by
    have h : p^2 < q^2 := haltb
    by_contra hle
    push_neg at hle
    have : q^2 ≤ p^2 := Nat.pow_le_pow_left hle 2
    omega
  have hpltr : p < r := by
    have h : p^2 < r^2 := haltc
    by_contra hle
    push_neg at hle
    have : r^2 ≤ p^2 := Nat.pow_le_pow_left hle 2
    omega
  -- By prime_3mod4_not_div_sum_squares: p ∤ (q² + r²)
  have hndiv : ¬(p ∣ q^2 + r^2) :=
    prime_3mod4_not_div_sum_squares hp hq hr hp3 hq3 hr3 hpq hpr hqr hpltq hpltr
  -- Since p ∤ (q² + r²), we have p² ∤ (q² + r²)
  exact sq_not_dvd_of_not_dvd hp hndiv

/-! ## Density Results -/

/-- A set has density 0 if |A ∩ {1,...,N}| / N → 0 -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun N => (countingFunction A N : ℝ) / N) atTop (nhds 0)

/-- Erdős-Sárközy (1970): Divisibility-free sets have density 0 -/
axiom erdos_sarkozy_density_zero :
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A → HasDensityZero A

/-! ## Question 1: Can we achieve √N density? -/

/-- The liminf of |A ∩ {1,...,N}| / √N -/
def sqrtLiminfDensity (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
    (countingFunction A N : ℝ) / Real.sqrt N ≥ c

/-- Question 1: Does a divisibility-free set with positive √N-density exist? -/
def Erdos12Question1 : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsDivisibilityFree A ∧ sqrtLiminfDensity A

/-- Best known: Elsholtz-Planitzer (2017) construction -/
axiom elsholtz_planitzer_construction :
  ∃ A : Set ℕ, A.Infinite ∧ IsDivisibilityFree A ∧
    ∀ᶠ N in atTop, (countingFunction A N : ℝ) ≥
      Real.sqrt N / (Real.sqrt (Real.log N) * (Real.log (Real.log N))^2)

/-! ## Question 2: Sparse infinitely often? -/

/-- Question 2: Is there c > 0 with |A| < N^(1-c) infinitely often? -/
def Erdos12Question2 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A →
    ∃ c : ℝ, c > 0 ∧ ∀ M : ℕ, ∃ N > M,
      (countingFunction A N : ℝ) < N^(1 - c)

/-! ## Question 3: Convergent reciprocal sum? -/

/-- The sum of reciprocals of elements in A -/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ :=
  ∑' (n : A), (1 : ℝ) / n

/-- Question 3: Is the reciprocal sum always finite? -/
def Erdos12Question3 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A →
    Summable (fun n : A => (1 : ℝ) / n)

/-! ## Coprime Case -/

/-- A set is pairwise coprime -/
def IsPairwiseCoprime (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → Nat.Coprime a b

/-- Schoen (2001), Baier (2004): Coprime divisibility-free sets are O(N^(2/3)/log N) -/
axiom coprime_upper_bound :
  ∀ A : Set ℕ, A.Infinite → IsDivisibilityFree A → IsPairwiseCoprime A →
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
      (countingFunction A N : ℝ) ≤ C * N^(2/3 : ℝ) / Real.log N

/-! ## Properties of primeSquares3mod4 -/

/-- There are infinitely many primes ≡ 3 (mod 4) (Dirichlet's theorem) -/
axiom infinitely_many_primes_3mod4 :
  Set.Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 3}

/-- Primes ≡ 3 (mod 4) squared is an infinite set.

    Proof idea: If primeSquares3mod4 = {p² | p prime, p ≡ 3 (mod 4)} is finite,
    then the underlying set of primes must be finite (squaring is injective on ℕ).
    But by Dirichlet's theorem (axiomatized), there are infinitely many such primes.
-/
axiom primeSquares3mod4_infinite : Set.Infinite primeSquares3mod4

/-- The key example: primeSquares3mod4 is infinite and divisibility-free -/
theorem primeSquares3mod4_is_good :
    primeSquares3mod4.Infinite ∧ IsDivisibilityFree primeSquares3mod4 :=
  ⟨primeSquares3mod4_infinite, primeSquares3mod4_divisibility_free⟩

/-- Counting primes ≡ 3 (mod 4) up to x: asymptotically x / (2 log x) by Dirichlet -/
noncomputable def primeCount3mod4 (N : ℕ) : ℕ :=
  Set.ncard {p : ℕ | Nat.Prime p ∧ p % 4 = 3 ∧ p ≤ N}

/-- The density bound: |primeSquares3mod4 ∩ [1,N]| ~ √N / (2 log √N) = √N / log N -/
axiom primeSquares3mod4_density :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
    (countingFunction primeSquares3mod4 N : ℝ) ≥ c * Real.sqrt N / Real.log N

/-- The variant from formal-conjectures: liminf (count * log N / √N) > 0 -/
axiom primeSquares3mod4_liminf_pos :
  (0 : ℝ) < Filter.atTop.liminf
    (fun N => (countingFunction primeSquares3mod4 N : ℝ) * Real.log N / Real.sqrt N)

/-! ## Main Problem Statement -/

/-- Erdős Problem #12: All three questions (OPEN) -/
def Erdos12Problem : Prop :=
  Erdos12Question1 ∨ ¬Erdos12Question1 ∧
  Erdos12Question2 ∧
  Erdos12Question3
