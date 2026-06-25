/-
Erdős Problem #318: Signed Unit Fractions with Zero Sum

Source: https://erdosproblems.com/318
Status: PARTIALLY SOLVED

Statement:
Let A ⊆ ℕ be an infinite arithmetic progression and f : A → {-1, 1} be a
non-constant function. Must there exist a finite non-empty S ⊂ A such that
  ∑_{n ∈ S} f(n)/n = 0?

Variations:
1. What if A is an arbitrary set of positive density?
2. What if A is the set of squares excluding 1?

Known Results:
- Erdős-Straus (1975): TRUE for A = ℕ
- Sattler (1975): TRUE for A = odd numbers
- Sattler (1982b): TRUE for any arithmetic progression
- Counterexample: FALSE for some positive-density sets (e.g., sets with exactly one even)
- Squares case: OPEN (Sattler announced proof but never published)

This is known as "Property P₁" in the literature.

References:
- Erdős, P. and Straus, E.G. (1975): Solution to Problem 387, Nieuw Arch. Wisk.
- Sattler, R. (1975): Solution to Problem 387, Nieuw Arch. Wisk.
- Sattler, R. (1982): On Erdős property P₁ for squarefree numbers
- Sattler, R. (1982b): On Erdős property P₁ for arithmetical sequence
- Erdős, P. and Graham, R. (1980): Old and new problems in combinatorial number theory
-/

import Mathlib

open Finset BigOperators Real

open scoped Classical

namespace Erdos318

/-
## Part I: Signed Unit Fractions

A signed unit fraction is ±1/n for positive integer n.
-/

/--
**Signed sum of unit fractions:**
Given a finite set S ⊆ ℕ and a sign function f : ℕ → {-1, 1},
compute ∑_{n ∈ S} f(n)/n.
-/
def signedUnitSum (S : Finset ℕ) (f : ℕ → ℤ) : ℚ :=
  ∑ n ∈ S, (f n : ℚ) / (n : ℚ)

/--
**Sign function type:**
A function is a valid sign function if it only takes values ±1.
-/
def IsSignFunction (f : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, f n = 1 ∨ f n = -1

/--
**Non-constant on a set:**
A sign function is non-constant on A if it takes both values.
-/
def IsNonConstant (A : Set ℕ) (f : ℕ → ℤ) : Prop :=
  (∃ a ∈ A, f a = 1) ∧ (∃ b ∈ A, f b = -1)

/-
## Part II: Property P₁

A set A has Property P₁ if every non-constant sign function admits a
finite zero-sum subset.
-/

/--
**Property P₁ (Erdős):**
A set A ⊆ ℕ has Property P₁ if: for every sign function f : A → {-1, 1}
that is non-constant on A, there exists a finite non-empty S ⊆ A with
∑_{n ∈ S} f(n)/n = 0.
-/
def HasPropertyP1 (A : Set ℕ) : Prop :=
  ∀ f : ℕ → ℤ, IsSignFunction f → IsNonConstant A f →
    ∃ S : Finset ℕ, S.Nonempty ∧ (↑S : Set ℕ) ⊆ A ∧ signedUnitSum S f = 0

/-
## Part III: Arithmetic Progressions
-/

/--
**Arithmetic progression:**
The set {a, a+d, a+2d, ...} for a, d > 0.
-/
def arithmeticProgression (a d : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k : ℕ, n = a + k * d}

/--
**The natural numbers:**
The set ℕ⁺ = {1, 2, 3, ...}.
-/
def positiveNaturals : Set ℕ := {n : ℕ | n ≥ 1}

/--
**Odd numbers:**
The set {1, 3, 5, 7, ...}.
-/
def oddNumbers : Set ℕ := {n : ℕ | n % 2 = 1}

/-
## Part IV: Known Results
-/

/--
**Erdős-Straus Theorem (1975):**
The natural numbers have Property P₁.
-/
axiom erdos_straus_1975 : HasPropertyP1 positiveNaturals

/--
**Sattler's Theorem for Odd Numbers (1975):**
The odd numbers have Property P₁.
-/
axiom sattler_odd_1975 : HasPropertyP1 oddNumbers

/--
**Sattler's Main Theorem (1982):**
Every infinite arithmetic progression has Property P₁.
-/
axiom sattler_1982 (a d : ℕ) (ha : a ≥ 1) (hd : d ≥ 1) :
    HasPropertyP1 (arithmeticProgression a d)

/-
## Part V: Main Theorem
-/

/--
**Erdős Problem #318: Arithmetic Progressions**

The answer to the main question is YES: every infinite arithmetic
progression has Property P₁.
-/
theorem erdos_318_arithmetic_progression :
    ∀ a d : ℕ, a ≥ 1 → d ≥ 1 → HasPropertyP1 (arithmeticProgression a d) := by
  intro a d ha hd
  exact sattler_1982 a d ha hd

/-
## Part VI: Positive Density - Counterexamples
-/

/--
**Positive density:**
A set A ⊆ ℕ has positive density if lim inf |A ∩ [1,n]|/n > 0.
-/
def hasPositiveDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    (Finset.filter (· ∈ A) (Finset.range (n + 1))).card ≥ δ * n

/--
**Counterexample construction:**
Sets with exactly one even number fail Property P₁.
-/
def counterexampleSet (m : ℕ) : Set ℕ :=
  {n : ℕ | n % 2 = 1 ∨ n = 2 * m}

/--
**Counterexample has positive density:**
The set of odd numbers plus one even has density ≥ 1/4.
Proof: odd numbers in {0,...,n} number (n+1)/2 ≥ n/4 elements; all are in the set.
-/
theorem counterexample_positive_density (m : ℕ) (hm : m ≥ 1) :
    hasPositiveDensity (counterexampleSet m) := by
  -- Use density δ = 1/4 and threshold N = 2
  refine ⟨1/4, by norm_num, 2, fun n hn => ?_⟩
  -- All odd numbers are in counterexampleSet m
  have h_sub : (Finset.range (n + 1)).filter (fun k => k % 2 = 1) ⊆
               (Finset.range (n + 1)).filter (· ∈ counterexampleSet m) := by
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, Or.inl hk.2⟩
  have h_card : (Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card ≤
                (Finset.filter (· ∈ counterexampleSet m) (Finset.range (n + 1))).card :=
    Finset.card_le_card h_sub
  -- Count of odds in range(n+1) = (n+1)/2
  have h_odd_count : (Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card =
                     (n + 1) / 2 := by
    have key : ∀ k : ℕ, ((Finset.range k).filter (fun j => j % 2 = 1)).card = k / 2 := by
      intro k
      induction k with
      | zero => simp
      | succ j ihj =>
        rw [Finset.range_succ, Finset.filter_insert]
        split_ifs with hmod
        · rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_filter, Finset.mem_range])]
          omega
        · omega
    exact key (n + 1)
  -- (n+1)/2 * 4 ≥ n, so ((n+1)/2 : ℕ) : ℝ ≥ 1/4 * n
  have h_nat : (n + 1) / 2 * 4 ≥ n := by omega
  have h_real : (((n + 1) / 2 : ℕ) : ℝ) ≥ 1 / 4 * n := by
    have h_nat' : n ≤ 4 * ((n + 1) / 2) := by omega
    have h : (n : ℝ) ≤ 4 * (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h_nat'
    linarith
  calc ((Finset.filter (· ∈ counterexampleSet m) (Finset.range (n + 1))).card : ℝ)
      ≥ ((Finset.filter (fun k => k % 2 = 1) (Finset.range (n + 1))).card : ℝ) := by
          exact_mod_cast h_card
    _ = (((n + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h_odd_count
    _ ≥ 1 / 4 * n := h_real

/--
**Parity obstruction (key lemma).**

A finite sum of unit fractions with *odd* denominators can never equal `1/(2m)`
for `m ≥ 1`.

Proof: clear denominators by the (odd) product `D = ∏_{n ∈ T} n`. The equation
`∑_{n ∈ T} 1/n = 1/(2m)` becomes `∑_{n ∈ T} 2m·(D/n) = D` after multiplying by
`2m·D`. The left-hand side is a sum of *even* integers (each divisible by `2`),
hence even; the right-hand side `D` is a product of odd numbers, hence *odd*.
An even integer cannot equal an odd one. (The empty sum is `0 ≠ 1/(2m) > 0`.)
-/
theorem odd_unit_sum_ne_even_unit
    (T : Finset ℕ) (hodd : ∀ n ∈ T, n % 2 = 1) (m : ℕ) (hm : m ≥ 1) :
    ∑ n ∈ T, (1 : ℚ) / n ≠ 1 / (2 * m) := by
  intro hsum
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- empty sum is 0, but 1/(2m) > 0
    subst hT
    simp only [Finset.sum_empty] at hsum
    have hmpos : (0 : ℚ) < 2 * m := by
      have : (1 : ℚ) ≤ m := by exact_mod_cast hm
      linarith
    have hpos : (0 : ℚ) < 1 / (2 * m) := by positivity
    rw [← hsum] at hpos
    exact lt_irrefl 0 hpos
  · -- nonempty: parity contradiction
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    set D : ℕ := ∏ n ∈ T, n with hD
    have hdvd : ∀ n ∈ T, n ∣ D := fun n hn => by rw [hD]; exact Finset.dvd_prod_of_mem _ hn
    have hn0 : ∀ n ∈ T, n ≠ 0 := fun n hn => by have := hodd n hn; omega
    have hDodd : Odd D := by
      rw [hD]
      exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
        (fun i hi => Nat.odd_iff.mpr (hodd i hi))
    -- N = ∑ 2m·(D/n) is even, and (N : ℚ) = D, so D is even — contradicting D odd.
    set N : ℕ := ∑ n ∈ T, 2 * m * (D / n) with hN
    have hcast : (N : ℚ) = (D : ℚ) := by
      have hterm : ∀ n ∈ T, ((2 * m * (D / n) : ℕ) : ℚ) = 2 * m * D * (1 / n) := by
        intro n hn
        rw [Nat.cast_mul, Nat.cast_mul,
            Nat.cast_div (hdvd n hn) (by exact_mod_cast hn0 n hn)]
        ring
      rw [hN, Nat.cast_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum]
      have h2m : (2 * (m : ℚ)) ≠ 0 := mul_ne_zero two_ne_zero hmQ
      field_simp
    have hND : N = D := by exact_mod_cast hcast
    have h2N : 2 ∣ N := by
      rw [hN]
      exact Finset.dvd_sum (fun n _ => (dvd_mul_right 2 m).mul_right (D / n))
    have h2D : 2 ∣ D := hND ▸ h2N
    have hDmod : D % 2 = 1 := Nat.odd_iff.mp hDodd
    omega

/--
**Counterexample fails P₁ (now a theorem, previously an axiom).**

The set `counterexampleSet m = odds ∪ {2m}` does not have Property P₁.

Witness: the sign function `f` that is `+1` on odd numbers and `-1` on even
numbers. It is non-constant on the set (`+1` at `1`, `-1` at `2m`). For any
finite nonempty `S ⊆ odds ∪ {2m}`:
* if `2m ∉ S`, every term is `+1/n > 0`, so the sum is strictly positive;
* if `2m ∈ S`, the sum is `(∑_{odd n ∈ S} 1/n) - 1/(2m)`, and the parity
  obstruction `odd_unit_sum_ne_even_unit` rules out `∑ 1/n = 1/(2m)`.

In both cases the signed sum is nonzero, so `f` admits no zero-sum subset.
-/
theorem counterexample_fails_P1 (m : ℕ) (hm : m ≥ 1) :
    ¬HasPropertyP1 (counterexampleSet m) := by
  intro hP1
  -- Bad sign function: +1 on odd numbers, -1 on even numbers.
  set f : ℕ → ℤ := fun n => if n % 2 = 1 then 1 else -1 with hf
  have hf_odd : ∀ n, n % 2 = 1 → f n = 1 := by intro n h; simp [hf, h]
  have hf_even : ∀ n, ¬ n % 2 = 1 → f n = -1 := by intro n h; simp [hf, h]
  have hsign : IsSignFunction f := by
    intro n; by_cases h : n % 2 = 1
    · exact Or.inl (hf_odd n h)
    · exact Or.inr (hf_even n h)
  have h2m_even : ¬ (2 * m) % 2 = 1 := by omega
  have hnc : IsNonConstant (counterexampleSet m) f :=
    ⟨⟨1, Or.inl (by decide), hf_odd 1 (by decide)⟩,
     ⟨2 * m, Or.inr rfl, hf_even (2 * m) h2m_even⟩⟩
  obtain ⟨S, hSne, hSsub, hS0⟩ := hP1 f hsign hnc
  -- Each element of S is odd or equals 2m, and is positive.
  have hSmem : ∀ n ∈ S, n % 2 = 1 ∨ n = 2 * m := fun n hn => hSsub hn
  have hSpos : ∀ n ∈ S, 0 < n := by
    intro n hn; rcases hSmem n hn with h | h <;> omega
  have hTodd : ∀ n ∈ S.filter (fun n => n % 2 = 1), n % 2 = 1 :=
    fun n hn => (Finset.mem_filter.mp hn).2
  by_cases h2mS : (2 * m) ∈ S
  · -- 2m ∈ S: isolate the even term, reduce to the parity lemma.
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun n => n % 2 = 1)
      (fun n => (f n : ℚ) / n)
    have hE : S.filter (fun n => ¬ n % 2 = 1) = {2 * m} := by
      apply Finset.ext; intro a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨haS, hae⟩
        rcases hSmem a haS with h | h
        · exact absurd h hae
        · exact h
      · rintro rfl; exact ⟨h2mS, h2m_even⟩
    have hTsum : ∑ n ∈ S.filter (fun n => n % 2 = 1), (f n : ℚ) / n
               = ∑ n ∈ S.filter (fun n => n % 2 = 1), (1 : ℚ) / n := by
      apply Finset.sum_congr rfl
      intro n hn; rw [hf_odd n (hTodd n hn)]; simp
    have hEsum : ∑ n ∈ S.filter (fun n => ¬ n % 2 = 1), (f n : ℚ) / n = -(1 / (2 * m)) := by
      rw [hE, Finset.sum_singleton, hf_even (2 * m) h2m_even]; push_cast; ring
    have hS0' : (∑ n ∈ S, (f n : ℚ) / n) = 0 := hS0
    rw [← hsplit, hTsum, hEsum] at hS0'
    have hTeq : ∑ n ∈ S.filter (fun n => n % 2 = 1), (1 : ℚ) / n = 1 / (2 * m) := by
      linarith [hS0']
    exact odd_unit_sum_ne_even_unit (S.filter (fun n => n % 2 = 1)) hTodd m hm hTeq
  · -- 2m ∉ S: every element is odd, every sign is +1, sum is strictly positive.
    have hall_odd : ∀ n ∈ S, n % 2 = 1 := by
      intro n hn; rcases hSmem n hn with h | h
      · exact h
      · exact absurd (h ▸ hn) h2mS
    have heq : (∑ n ∈ S, (f n : ℚ) / n) = ∑ n ∈ S, (1 : ℚ) / n := by
      apply Finset.sum_congr rfl
      intro n hn; rw [hf_odd n (hall_odd n hn)]; simp
    have hS0' : (∑ n ∈ S, (f n : ℚ) / n) = 0 := hS0
    rw [heq] at hS0'
    have hpos : 0 < ∑ n ∈ S, (1 : ℚ) / n := by
      apply Finset.sum_pos _ hSne
      intro n hn
      have : (0 : ℚ) < n := by exact_mod_cast hSpos n hn
      positivity
    rw [hS0'] at hpos
    exact lt_irrefl 0 hpos

/--
**Positive density is not sufficient:**
There exist positive-density sets without Property P₁.
-/
theorem positive_density_insufficient :
    ∃ A : Set ℕ, hasPositiveDensity A ∧ ¬HasPropertyP1 A := by
  use counterexampleSet 1
  constructor
  · exact counterexample_positive_density 1 (by norm_num)
  · exact counterexample_fails_P1 1 (by norm_num)

/-
## Part VII: The Squares Question (OPEN)
-/

/--
**Squares excluding 1:**
The set {4, 9, 16, 25, ...} = {n² : n ≥ 2}.
-/
def squaresExcludingOne : Set ℕ :=
  {n : ℕ | ∃ k : ℕ, k ≥ 2 ∧ n = k^2}

/--
**Why exclude 1:**
We must exclude 1 because ∑_{k≥2} 1/k² < 1, so no finite sum of
+1/k² terms can equal any sum involving -1/1 = -1.
Proof: ∑_{k≥2} 1/k² = π²/6 - 1, and π < 3.15 gives π²/6 - 1 < 1.
-/
theorem sum_reciprocal_squares_less_than_one :
    ∑' (k : ℕ), (if k ≥ 2 then (1 : ℝ) / k^2 else 0) < 1 := by
  -- Full Basel sum = π²/6
  have h_full_sum : ∑' n : ℕ, (1 : ℝ) / n^2 = Real.pi^2 / 6 := hasSum_zeta_two.tsum_eq
  -- The k<2 part HasSum 1: n=0 gives 0, n=1 gives 1
  have h_lt2_hassum : HasSum (fun n : ℕ => if n < 2 then (1 : ℝ) / n^2 else 0) 1 := by
    have heq : (fun n : ℕ => if n < 2 then (1 : ℝ) / n^2 else 0) = fun n => if n = 1 then 1 else 0 := by
      ext n; rcases n with _ | _ | n
      · norm_num
      · norm_num
      · simp [show ¬(n + 2 < 2) from by omega, show ¬(n + 2 = 1) from by omega]
    rw [heq]
    exact hasSum_single 1 (fun b hb => if_neg hb)
  -- Summability of each piece
  have h_summ_ge2 : Summable (fun n : ℕ => if n ≥ 2 then (1 : ℝ) / n^2 else 0) :=
    Summable.of_nonneg_of_le
      (fun n => by split_ifs <;> norm_num)
      (fun n => by split_ifs <;> [exact le_refl _; exact div_nonneg one_pos.le (sq_nonneg _)])
      hasSum_zeta_two.summable
  have h_summ_lt2 := h_lt2_hassum.summable
  -- Decompose: 1/n² = (k≥2 part) + (k<2 part)
  have h_split : ∀ n : ℕ, (1 : ℝ) / n^2 =
      (if n ≥ 2 then (1 : ℝ) / n^2 else 0) + (if n < 2 then (1 : ℝ) / n^2 else 0) := by
    intro n
    by_cases h : n ≥ 2
    · simp [h, show ¬(n < 2) from by omega]
    · simp [h, show n < 2 from by omega]
  -- Add the two tsum pieces to get the full sum
  have h_add := Summable.tsum_add h_summ_ge2 h_summ_lt2
  simp_rw [← h_split] at h_add
  -- The k≥2 sum = π²/6 - 1
  have h_val : ∑' n : ℕ, (if n ≥ 2 then (1 : ℝ) / n^2 else 0) = Real.pi^2 / 6 - 1 := by
    have hlt2 := h_lt2_hassum.tsum_eq
    linarith [h_add.symm.trans h_full_sum, hlt2]
  rw [h_val]
  -- π < 3.15 ⟹ π²/6 - 1 < 9.9225/6 - 1 < 1
  have hpi := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/--
**Erdős Problem #318: Squares Case (OPEN)**

Does the set of squares excluding 1 have Property P₁?

Sattler announced a proof in 1982 papers but never published it.
This remains an open problem.
-/
def erdos_318_squares_conjecture : Prop :=
  HasPropertyP1 squaresExcludingOne

/-
**Open status of the squares case.**

The squares case is genuinely OPEN: it is not known whether
`erdos_318_squares_conjecture` is true or false (Sattler announced a proof in
1982 but never published it). We therefore deliberately state *no* axiom about
its truth value — the open question is faithfully recorded simply by the
definition `erdos_318_squares_conjecture` being left unproven.

(A previous version of this file asserted the axiom
`¬∃ (proof : erdos_318_squares_conjecture), True`, which is mathematically
incorrect: it claims the conjecture is *false*. That overclaiming axiom has been
removed.)
-/

/-
## Part VIII: Key Lemmas and Techniques
-/

/--
**Common denominator technique:**
If ∑_{n ∈ S} f(n)/n = 0, then ∑_{n ∈ S} f(n) · (∏_{m ∈ S} m)/n = 0.

This transforms the rational equation into an integer equation.
Proof: n | P = ∏_{m∈S} m for each n ∈ S, so f(n)*P/n is exact. The sum
cast to ℚ equals (∑ f(n)/n) * P = 0; injectivity ℤ → ℚ gives the ℤ result.
-/
theorem zero_sum_integer_form (S : Finset ℕ) (f : ℕ → ℤ) (hS : S.Nonempty)
    (h0 : ∀ n ∈ S, n ≠ 0) (hzero : signedUnitSum S f = 0) :
    ∑ n ∈ S, f n * (∏ m ∈ S, m) / n = 0 := by
  -- Each n ∈ S divides ∏ m ∈ S, m as integers
  have hP : ∀ n ∈ S, (n : ℤ) ∣ (↑(∏ m ∈ S, m) : ℤ) :=
    fun n hn => by exact_mod_cast Finset.dvd_prod_of_mem _ hn
  -- Cast the integer sum to ℚ: it equals (signedUnitSum) * P, term by term.
  have hcast : (((∑ n ∈ S, f n * (∏ m ∈ S, m) / n : ℤ)) : ℚ)
      = (∑ n ∈ S, (f n : ℚ) / (n : ℚ)) * (↑(∏ m ∈ S, m) : ℚ) := by
    rw [Int.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    -- f n * P / n = f n * (P / n) since n | P (exact division)
    rw [Int.mul_ediv_assoc _ (hP n hn), Int.cast_mul,
        Int.cast_div (hP n hn) (by exact_mod_cast (h0 n hn))]
    push_cast
    ring
  -- The ℚ-cast of the integer sum is 0, hence the integer sum is 0.
  have hsu : (∑ n ∈ S, (f n : ℚ) / (n : ℚ)) = 0 := hzero
  have hzeroℚ : (((∑ n ∈ S, f n * (∏ m ∈ S, m) / n : ℤ)) : ℚ) = 0 := by
    rw [hcast, hsu, zero_mul]
  exact_mod_cast hzeroℚ

/--
**Parity obstruction:**
For P₁ to fail, there's typically a parity obstruction from
the denominators.
-/
def parityObstruction (A : Set ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ (∀ a ∈ A, p ∣ a) ∧
    ¬∃ S : Finset ℕ, S.card ≥ 2 ∧ (↑S : Set ℕ) ⊆ A ∧
      (∃ a b : ℕ, a ∈ S ∧ b ∈ S ∧ (∀ q : ℕ, Nat.Prime q → q ∣ a → q ∣ b))

/-
## Part IX: Relationship to Egyptian Fractions
-/

/--
**Egyptian fraction representation:**
Property P₁ is related to signed Egyptian fraction representations.
An Egyptian fraction is a sum of distinct unit fractions.
-/
def isEgyptianRepresentation (S : Finset ℕ) (q : ℚ) : Prop :=
  ∑ n ∈ S, (1 : ℚ) / n = q

/--
**Signed Egyptian fractions:**
With signs, we ask if 0 has a signed Egyptian representation.
-/
def hasSignedZeroRepresentation (A : Set ℕ) (f : ℕ → ℤ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧ (↑S : Set ℕ) ⊆ A ∧ signedUnitSum S f = 0

/-
## Part X: Main Results Summary
-/

/--
**Erdős Problem #318: Summary**

1. **Arithmetic progressions:** Property P₁ holds (Sattler 1982)
2. **Natural numbers:** Property P₁ holds (Erdős-Straus 1975)
3. **Odd numbers:** Property P₁ holds (Sattler 1975)
4. **Positive density:** NOT sufficient - counterexamples exist
5. **Squares excluding 1:** OPEN

The main question about arithmetic progressions is SOLVED.
The question about squares remains OPEN.
-/
theorem erdos_318_summary :
    -- Arithmetic progressions satisfy P₁
    (∀ a d : ℕ, a ≥ 1 → d ≥ 1 → HasPropertyP1 (arithmeticProgression a d)) ∧
    -- Natural numbers satisfy P₁
    HasPropertyP1 positiveNaturals ∧
    -- Odd numbers satisfy P₁
    HasPropertyP1 oddNumbers ∧
    -- But positive density alone is insufficient
    (∃ A : Set ℕ, hasPositiveDensity A ∧ ¬HasPropertyP1 A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact erdos_318_arithmetic_progression
  · exact erdos_straus_1975
  · exact sattler_odd_1975
  · exact positive_density_insufficient

/-
**Problem Status:**
- Arithmetic progressions: SOLVED (YES, Sattler 1982)
- Positive density: SOLVED (NO, counterexamples exist)
- Squares: OPEN (announced proof never appeared)
-/
/-
  Problem Status (mixed):
  - Arithmetic progressions: SOLVED (YES, Sattler 1982)
  - Positive density: SOLVED (NO, counterexamples exist)
  - Squares: OPEN (announced proof never appeared)
-/

end Erdos318
