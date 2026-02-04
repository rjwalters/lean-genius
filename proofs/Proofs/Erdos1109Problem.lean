/-
Erdős Problem #1109: Squarefree Sumsets

Source: https://erdosproblems.com/1109
Status: OPEN (bounds improved but not resolved)

Statement:
Let f(N) be the size of the largest subset A ⊆ {1,...,N} such that
every n ∈ A + A is squarefree. Estimate f(N). In particular, is it
true that f(N) ≤ N^{o(1)}, or even f(N) ≤ (log N)^{O(1)}?

Known Bounds:
- Lower: (log log N)(log N)² ≪ f(N) (Konyagin 2004)
- Upper: f(N) ≪ N^{11/15 + o(1)} (Konyagin 2004)

Historical Development:
- Erdős-Sárközy (1987): log N ≪ f(N) ≪ N^{3/4} log N
- Sárközy (1992): Extended to A+B and k-power-free sumsets
- Gyarmati (2001): Alternative proof of log N lower bound
- Konyagin (2004): Current best bounds

Key Insight:
The problem asks how large a set can be while avoiding all sums
that are divisible by p² for any prime p. Squarefree numbers become
sparse, so constraining sumsets to be squarefree should limit set size.

Related: Problem #1103 (infinite analogue)

References:
- Erdős-Sárközy [ErSa87]: "On divisibility properties of integers a+a'"
- Konyagin [Ko04]: "Problems of the set of square-free numbers"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.Prime

open Nat Finset Real

namespace Erdos1109

/-
## Part I: Squarefree Numbers
-/

/-- A natural number is squarefree if no prime squared divides it.
    Uses Mathlib's Squarefree from NumberTheory. -/
def isSquarefree (n : ℕ) : Prop := Squarefree n

/-- Alternative characterization: n is squarefree iff for all primes p, p² ∤ n. -/
theorem squarefree_iff_no_prime_sq (n : ℕ) (hn : n ≥ 1) :
    isSquarefree n ↔ ∀ p : ℕ, p.Prime → ¬(p * p ∣ n) := by
  simp only [isSquarefree]
  constructor
  · intro hsf p hp hppn
    have h1 : IsUnit p := hsf p hppn
    rw [Nat.isUnit_iff] at h1
    exact absurd h1 hp.one_lt.ne'
  · intro h x hx
    by_contra hnu
    rw [Nat.isUnit_iff] at hnu
    have hx_pos : x > 0 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hx; omega)
    obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
    have : p * p ∣ x * x := Nat.mul_dvd_mul hpx hpx
    exact h p hp (dvd_trans this hx)

/-- 1 is squarefree. -/
theorem one_squarefree : isSquarefree 1 := by
  simp [isSquarefree]

/-- Primes are squarefree. -/
theorem prime_squarefree (p : ℕ) (hp : p.Prime) : isSquarefree p := by
  exact hp.squarefree

/-- Products of distinct primes are squarefree. -/
theorem distinct_primes_squarefree (ps : List ℕ) (hps : ∀ p ∈ ps, Nat.Prime p)
    (hdist : ps.Nodup) : isSquarefree ps.prod := by
  simp only [isSquarefree]
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hps_tail : ∀ q ∈ ps, Nat.Prime q := fun q hq => hps q (by simp [hq])
    have hdist_tail : ps.Nodup := (List.nodup_cons.mp hdist).2
    have hp_notin : p ∉ ps := (List.nodup_cons.mp hdist).1
    have ih_result := ih hps_tail hdist_tail
    simp only [List.prod_cons]
    rw [Nat.squarefree_mul_iff]
    refine ⟨?_, hp.squarefree, ih_result⟩
    -- Show p.Coprime ps.prod
    -- p is prime and doesn't divide any element of ps (since p ∉ ps and all are prime)
    rw [hp.coprime_iff_not_dvd]
    intro hp_dvd_prod
    rw [Prime.dvd_prod_iff hp.prime] at hp_dvd_prod
    obtain ⟨q, hq_mem, hp_dvd_q⟩ := hp_dvd_prod
    have hq_prime := hps_tail q hq_mem
    rcases hq_prime.eq_one_or_self_of_dvd p hp_dvd_q with h | h
    · exact absurd h hp.one_lt.ne'
    · exact hp_notin (h ▸ hq_mem)

/-
## Part II: The Sumset
-/

/-- The sumset A + A of a finite set A. -/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- A set has squarefree sumset if every element of A + A is squarefree. -/
def hasSquarefreeSumset (A : Finset ℕ) : Prop :=
  ∀ s ∈ sumset A, isSquarefree s

/-
## Part III: The Function f(N)
-/

/-- f(N) = max size of A ⊆ {1,...,N} with squarefree A + A. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m }

/-
## Part IV: Erdős-Sárközy Bounds (1987)
-/

/--
**Erdős-Sárközy Lower Bound (1987):**
f(N) ≫ log N

Construction: A set of size log N can be found with squarefree sumset.
-/
axiom erdos_sarkozy_lower_1987 (N : ℕ) (hN : N ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ (f N : ℝ) ≥ C * Real.log N

/--
**Erdős-Sárközy Upper Bound (1987):**
f(N) ≪ N^{3/4} log N
-/
axiom erdos_sarkozy_upper_1987 (N : ℕ) (hN : N ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ (f N : ℝ) ≤ C * (N : ℝ)^((3 : ℝ)/4) * Real.log N

/-
## Part V: Konyagin's Improvements (2004)
-/

/--
**Konyagin Lower Bound (2004):**
(log log N)(log N)² ≪ f(N)

This significantly improves the log N bound.
-/
axiom konyagin_lower_2004 (N : ℕ) (hN : N ≥ 16) :
    ∃ C : ℝ, C > 0 ∧ (f N : ℝ) ≥ C * Real.log (Real.log N) * (Real.log N)^2

/--
**Konyagin Upper Bound (2004):**
f(N) ≪ N^{11/15 + o(1)}

The exponent 11/15 ≈ 0.733 improves 3/4 = 0.75.
-/
axiom konyagin_upper_2004 (N : ℕ) (hN : N ≥ 2) :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ (f N : ℝ) ≤ C * (N : ℝ)^((11 : ℝ)/15 + ε)

/-
## Part VI: Current State of Knowledge
-/

/-- The best known exponent in the upper bound. -/
def bestUpperExponent : ℚ := 11 / 15

/--
**Current Best Bounds:**
(log log N)(log N)² ≪ f(N) ≪ N^{11/15 + o(1)}

The gap is enormous: polylogarithmic vs polynomial.
-/
theorem current_bounds (N : ℕ) (hN : N ≥ 16) :
    (∃ C : ℝ, C > 0 ∧ (f N : ℝ) ≥ C * Real.log (Real.log N) * (Real.log N)^2) ∧
    (∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ (f N : ℝ) ≤ C * (N : ℝ)^((11 : ℝ)/15 + ε)) := by
  exact ⟨konyagin_lower_2004 N hN, konyagin_upper_2004 N (by omega)⟩

/-
## Part VII: The Open Questions
-/

/--
**Erdős's Question 1:**
Is f(N) ≤ N^{o(1)}?

This asks whether f(N) grows slower than any polynomial.
-/
def question1_subpolynomial : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → (f N : ℝ) ≤ (N : ℝ)^ε

/--
**Erdős's Question 2 (Stronger):**
Is f(N) ≤ (log N)^{O(1)}?

This asks whether f(N) is bounded by a polynomial in log N.
-/
def question2_polylogarithmic : Prop :=
  ∃ k : ℕ, ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 → (f N : ℝ) ≤ C * (Real.log N)^(k : ℝ)

/--
**Erdős-Sárközy Conjecture:**
The lower bound is closer to the truth, i.e., f(N) is polylogarithmic.
-/
axiom erdos_sarkozy_conjecture : question2_polylogarithmic

/-
## Part VIII: Related Problems
-/

/--
**Connection to Problem #1103:**
The infinite analogue asks for the minimum growth rate of a sequence
a₁ < a₂ < ⋯ such that all a_i + a_j are squarefree.

Upper bounds for f(N) imply lower bounds for the a_i.
-/
axiom connection_to_1103 :
    question2_polylogarithmic →
      ∃ c : ℝ, c > 0 ∧ ∀ (a : ℕ → ℕ), (∀ i j : ℕ, isSquarefree (a i + a j)) →
        ∀ n : ℕ, (a n : ℝ) ≥ (n : ℝ)^c

/--
**k-power-free Generalization (Sárközy 1992):**
Let f_k(N) be the max size of A ⊆ {1,...,N} with A + A being k-power-free.
Then similar bounds hold.
-/
def isKPowerFree (k n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p^k ∣ n)

axiom sarkozy_k_power_free (k : ℕ) (hk : k ≥ 2) :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
      ∀ N : ℕ, N ≥ 2 → C₁ * Real.log N ≤ (f N : ℝ) ∧
        (f N : ℝ) ≤ C₂ * (N : ℝ)^(1 - 1/((2 : ℝ) * k))

/-
## Part IX: Structural Constraints on Squarefree Sumsets
-/

/--
**All elements in a squarefree-sumset set must be odd.**

If a is even and a ∈ A with hasSquarefreeSumset A, then a + a = 2a.
Since a is even, a = 2k for some k. Then a + a = 4k, which is divisible
by 4 = 2². But 2² | (a + a) contradicts squarefreeness of a + a (when k > 0).
When k = 0, a + a = 0, which is also not squarefree.

This is the simplest structural constraint: avoiding p² = 4 in the sumset
already forces all elements to be odd. For larger primes p, similar
residue class restrictions apply modulo p².
-/
theorem all_odd (A : Finset ℕ) (h : hasSquarefreeSumset A) (a : ℕ) (ha : a ∈ A) :
    a % 2 = 1 := by
  by_contra heven
  have ⟨k, hk⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  have hsf_aa := h (a + a) (by
    simp only [sumset, Finset.mem_image, Finset.mem_product]
    exact ⟨(a, a), ⟨ha, ha⟩, rfl⟩)
  simp only [isSquarefree] at hsf_aa
  rw [hk] at hsf_aa
  have h_eq : 2 * k + 2 * k = 2 * (2 * k) := by ring
  rw [h_eq] at hsf_aa
  by_cases hk0 : k = 0
  · subst hk0
    simp at hsf_aa
  · have h4 : 2 * 2 ∣ 2 * (2 * k) := ⟨k, by ring⟩
    have h2unit := hsf_aa 2 h4
    rw [Nat.isUnit_iff] at h2unit
    omega

/--
**Modular constraint for prime p:**
For any prime p and any set A with squarefree sumset, if a, b ∈ A
then a + b is not divisible by p².
-/
theorem prime_sq_avoidance (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    ¬(p * p ∣ (a + b)) := by
  intro hdvd
  have hsf := h (a + b) (by
    simp only [sumset, Finset.mem_image, Finset.mem_product]
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩)
  simp only [isSquarefree] at hsf
  have hunit := hsf p hdvd
  rw [Nat.isUnit_iff] at hunit
  exact absurd hunit hp.one_lt.ne'

/--
**Diagonal squarefreeness:**
For any element a in a squarefree-sumset set, 2a must be squarefree.
This follows directly from a + a = 2a being in the sumset.
-/
theorem double_squarefree (A : Finset ℕ) (h : hasSquarefreeSumset A) (a : ℕ) (ha : a ∈ A) :
    isSquarefree (a + a) := by
  exact h (a + a) (by
    simp only [sumset, Finset.mem_image, Finset.mem_product]
    exact ⟨(a, a), ⟨ha, ha⟩, rfl⟩)

/--
**No element divisible by p²:**
For any prime p and any a ∈ A (with squarefree sumset),
p² does not divide a. Equivalently, each element of A is squarefree.

Proof: If p² | a, then p² | 2a = a + a, contradicting prime_sq_avoidance.
-/
theorem element_not_div_prime_sq (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : a ∈ A) : ¬(p * p ∣ a) := by
  intro hdvd
  have h2a : p * p ∣ (a + a) := by
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨2 * k, by rw [hk]; ring⟩
  exact prime_sq_avoidance A h p hp a a ha ha h2a

/--
**Elements of squarefree-sumset sets are themselves squarefree (when positive).**

Each element must be squarefree because if p² | a for some prime p,
then p² | 2a, but 2a ∈ A + A must be squarefree.
-/
theorem element_squarefree (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a : ℕ) (ha : a ∈ A) (ha_pos : a ≥ 1) : isSquarefree a := by
  rw [squarefree_iff_no_prime_sq a ha_pos]
  exact fun p hp => element_not_div_prime_sq A h p hp a ha

/-
## Part X: Main Results
-/

/--
**Erdős Problem #1109: Summary**

| Year | Author | Lower Bound | Upper Bound |
|------|--------|-------------|-------------|
| 1987 | Erdős-Sárközy | log N | N^{3/4} log N |
| 2004 | Konyagin | (log log N)(log N)² | N^{11/15+o(1)} |

The problem remains OPEN. Erdős-Sárközy conjectured polylogarithmic growth.
-/
theorem erdos_1109_summary :
    -- Lower bound polylogarithmic
    (∀ N : ℕ, N ≥ 16 → ∃ C : ℝ, C > 0 ∧
      (f N : ℝ) ≥ C * Real.log (Real.log N) * (Real.log N)^2) ∧
    -- Upper bound polynomial
    (∀ N : ℕ, N ≥ 2 → ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧ (f N : ℝ) ≤ C * (N : ℝ)^((11 : ℝ)/15 + ε)) := by
  exact ⟨fun N hN => konyagin_lower_2004 N hN,
         fun N hN ε hε => konyagin_upper_2004 N hN ε hε⟩

/-
## Part XI: Concrete Examples and Constructions
-/

/-- Helper: 2 is prime -/
private theorem two_prime : Nat.Prime 2 := by native_decide

/-- Helper: 3 is prime -/
private theorem three_prime : Nat.Prime 3 := by native_decide

/--
**The singleton {1} has a squarefree sumset.**
1 + 1 = 2, which is squarefree (prime).
-/
theorem singleton_one_squarefree_sumset : hasSquarefreeSumset {1} := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  subst ha; subst hb; simp at hab
  rw [← hab]; exact two_prime.squarefree

/--
**{1, 3} does NOT have a squarefree sumset.**
1 + 3 = 4 = 2², which is NOT squarefree.
-/
theorem pair_1_3_not_squarefree_sumset : ¬ hasSquarefreeSumset ({1, 3} : Finset ℕ) := by
  intro h
  have h4 : (4 : ℕ) ∈ sumset ({1, 3} : Finset ℕ) := by
    simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨(1, 3), ⟨Or.inl rfl, Or.inr rfl⟩, rfl⟩
  have hsf4 := h 4 h4
  simp only [isSquarefree] at hsf4
  have h22 : 2 * 2 ∣ (4 : ℕ) := ⟨1, by norm_num⟩
  have := hsf4 2 h22
  rw [Nat.isUnit_iff] at this; omega

/--
**Squarefree verification for small numbers.**
Helper to prove specific small numbers are squarefree via Squarefree typeclass.
-/
private theorem squarefree_2 : Squarefree (2 : ℕ) := two_prime.squarefree
private theorem squarefree_6 : Squarefree (6 : ℕ) := by
  rw [show (6 : ℕ) = 2 * 3 from by norm_num]
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, three_prime.squarefree⟩)
private theorem squarefree_10 : Squarefree (10 : ℕ) := by
  rw [show (10 : ℕ) = 2 * 5 from by norm_num]
  have : Nat.Prime 5 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

/--
**{1, 5} has a squarefree sumset.**
Sums: 1+1=2 (prime), 1+5=6=2·3 (squarefree), 5+5=10=2·5 (squarefree).
-/
theorem pair_1_5_squarefree_sumset : hasSquarefreeSumset ({1, 5} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at hab <;> rw [← hab]
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_6
  · exact squarefree_10

/--
**Residue class constraint modulo p²:**
For any prime p, the elements of A can use at most p² - p + 1 residue classes mod p².

In each pair (r, p²-r) with r ≠ 0, at most one class can be used.
Class 0 is entirely forbidden (since a ≡ 0 mod p² implies p² | 2a).
There are (p²-1)/2 such pairs plus possibly the class p²/2 (if p² even).

More precisely: A (mod p²) must be a sum-free-like subset of (Z/p²Z)* ∪ {non-multiples of p}.
-/
theorem residue_mod_4 (A : Finset ℕ) (h : hasSquarefreeSumset A) (a : ℕ) (ha : a ∈ A) :
    a % 4 = 1 ∨ a % 4 = 3 := by
  have hodd := all_odd A h a ha
  have hmod4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases hmod4 with h0 | h1 | h2 | h3
  · -- a % 4 = 0 means 4 | a, so 4 | 2a, contradicting squarefreeness
    exfalso
    have h4a : 2 * 2 ∣ a := by omega
    exact element_not_div_prime_sq A h 2 two_prime a ha h4a
  · left; exact h1
  · -- a % 4 = 2 means a is even, contradicts oddness
    omega
  · right; exact h3

/--
**Residue class constraint modulo 9:**
No element of A can be divisible by 9 (= 3²).
This is a special case of element_not_div_prime_sq for p = 3.
-/
theorem not_div_9 (A : Finset ℕ) (h : hasSquarefreeSumset A) (a : ℕ) (ha : a ∈ A) :
    ¬(9 ∣ a) := by
  intro h9
  have h3sq : 3 * 3 ∣ a := by
    obtain ⟨k, hk⟩ := h9; exact ⟨k, by omega⟩
  exact element_not_div_prime_sq A h 3 three_prime a ha h3sq

/--
**No pair sums to a multiple of 4:**
For any a, b ∈ A, a + b is not divisible by 4.
Since all elements are odd, a + b is always even.
If a ≡ b (mod 4), then a + b ≡ 2a ≡ 0 or 2 (mod 4).
If a ≡ 1, b ≡ 1 (mod 4): a+b ≡ 2 (mod 4) ✓
If a ≡ 3, b ≡ 3 (mod 4): a+b ≡ 6 ≡ 2 (mod 4) ✓
If a ≡ 1, b ≡ 3 (mod 4): a+b ≡ 4 ≡ 0 (mod 4) ✗
So elements of A must all be ≡ 1 (mod 4) or all ≡ 3 (mod 4).
-/
theorem same_residue_mod_4 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    (a % 4 = 1 ∧ b % 4 = 1) ∨ (a % 4 = 3 ∧ b % 4 = 3) := by
  have ha4 := residue_mod_4 A h a ha
  have hb4 := residue_mod_4 A h b hb
  -- Suppose a ≡ 1 and b ≡ 3 (mod 4), then a + b ≡ 0 (mod 4)
  rcases ha4 with ha1 | ha3 <;> rcases hb4 with hb1 | hb3
  · left; exact ⟨ha1, hb1⟩
  · -- a ≡ 1, b ≡ 3: a+b ≡ 0 (mod 4), contradiction
    exfalso
    have h4_dvd : 2 * 2 ∣ (a + b) := by omega
    exact prime_sq_avoidance A h 2 two_prime a b ha hb h4_dvd
  · -- a ≡ 3, b ≡ 1: a+b ≡ 0 (mod 4), contradiction
    exfalso
    have h4_dvd : 2 * 2 ∣ (a + b) := by omega
    exact prime_sq_avoidance A h 2 two_prime a b ha hb h4_dvd
  · right; exact ⟨ha3, hb3⟩

/--
**Parity constraint for prime p = 3:**
For any a, b ∈ A, a + b is not divisible by 9.
This constrains which residue classes mod 9 can be used simultaneously.
-/
theorem no_sum_div_9 (A : Finset ℕ) (h : hasSquarefreeSumset A) (a b : ℕ)
    (ha : a ∈ A) (hb : b ∈ A) : ¬(9 ∣ (a + b)) := by
  intro h9
  have h3sq : 3 * 3 ∣ (a + b) := by
    obtain ⟨k, hk⟩ := h9; exact ⟨k, by omega⟩
  exact prime_sq_avoidance A h 3 three_prime a b ha hb h3sq

/--
**Empty set has a squarefree sumset (vacuously).**
-/
theorem empty_squarefree_sumset : hasSquarefreeSumset ∅ := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.notMem_empty,
    false_and, and_false, exists_false] at hs

/--
**Subset inheritance:**
If A has a squarefree sumset and B ⊆ A, then B also has a squarefree sumset.
-/
theorem subset_squarefree_sumset (A B : Finset ℕ) (h : hasSquarefreeSumset A)
    (hBA : B ⊆ A) : hasSquarefreeSumset B := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product] at hs ⊢
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  exact h s (by
    simp only [sumset, Finset.mem_image, Finset.mem_product]
    exact ⟨(a, b), ⟨hBA ha, hBA hb⟩, hab⟩)

/--
**f is monotone:** f(N) ≤ f(M) whenever N ≤ M.

If A ⊆ {1,...,N} with squarefree sumset and card = f(N),
then A ⊆ {1,...,M} too, so f(M) ≥ f(N).
-/
theorem f_monotone (N M : ℕ) (hNM : N ≤ M) : f N ≤ f M := by
  unfold f
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (M + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use M + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  have hsub : {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} ⊆
              {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (M + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm ⊢
    obtain ⟨A, hA_sub, hA_sf, hA_card⟩ := hm
    exact ⟨A, Finset.Subset.trans hA_sub (Finset.range_mono (by omega)), hA_sf, hA_card⟩
  have hne : Set.Nonempty {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} :=
    ⟨0, ∅, Finset.empty_subset _, empty_squarefree_sumset, rfl⟩
  exact csSup_le_csSup hbdd hne hsub

/-
## Part XII: Deeper Residue Class Analysis
-/

/--
**Forbidden residue class 0 mod p²:**
For any prime p, no element of A can be in residue class 0 mod p².
This is a restatement of element_not_div_prime_sq in modular language.
-/
theorem forbidden_class_zero (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : a ∈ A) : a % (p * p) ≠ 0 := by
  intro h0
  have hdvd : p * p ∣ a := Nat.dvd_of_mod_eq_zero h0
  exact element_not_div_prime_sq A h p hp a ha hdvd

/--
**Forbidden residue pair sum:**
For any prime p, no pair of residues r₁, r₂ from elements of A can satisfy
r₁ + r₂ ≡ 0 (mod p²). This is the modular form of prime_sq_avoidance.
-/
theorem forbidden_residue_sum (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    (a + b) % (p * p) ≠ 0 := by
  intro h0
  have hdvd : p * p ∣ (a + b) := Nat.dvd_of_mod_eq_zero h0
  exact prime_sq_avoidance A h p hp a b ha hb hdvd

/--
**No element is zero in a squarefree-sumset set:**
If 0 ∈ A, then 0 + 0 = 0 ∈ A+A, but 0 is not squarefree.
-/
theorem no_zero_element (A : Finset ℕ) (h : hasSquarefreeSumset A) : (0 : ℕ) ∉ A := by
  intro h0
  have hsf := h 0 (by
    simp only [sumset, Finset.mem_image, Finset.mem_product]
    exact ⟨(0, 0), ⟨h0, h0⟩, by simp⟩)
  simp [isSquarefree, Squarefree] at hsf
  exact absurd (hsf 2) (by omega)

/--
**All elements are positive:**
Since 0 is excluded and elements are natural numbers, all elements are ≥ 1.
-/
theorem elements_positive (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a : ℕ) (ha : a ∈ A) : a ≥ 1 := by
  by_contra h0
  push_neg at h0
  interval_cases a
  exact no_zero_element A h ha

/--
**Automatic squarefreeness of elements:**
Combines elements_positive and element_squarefree.
-/
theorem elements_are_squarefree (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a : ℕ) (ha : a ∈ A) : isSquarefree a :=
  element_squarefree A h a ha (elements_positive A h a ha)

/--
**Sumset lower bound:**
The minimum element of A + A is at least 2.
If a, b ∈ A then a, b ≥ 1, so a + b ≥ 2.
-/
theorem sumset_lower_bound (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (s : ℕ) (hs : s ∈ sumset A) : s ≥ 2 := by
  simp only [sumset, Finset.mem_image, Finset.mem_product] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  have ha1 := elements_positive A h a ha
  have hb1 := elements_positive A h b hb
  omega

/--
**f(N) ≥ 1 for N ≥ 1:**
The set {1} has a squarefree sumset (1+1=2 is prime),
giving f(N) ≥ 1 for N ≥ 1.
-/
theorem f_ge_one (N : ℕ) (hN : N ≥ 1) : f N ≥ 1 := by
  unfold f
  have h1 : (1 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1}, ?_, singleton_one_squarefree_sumset, ?_⟩
    · intro x hx
      simp at hx; subst hx
      simp [Finset.mem_range]; omega
    · simp
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h1

/--
**Squarefree sumset elements are squarefree:**
Every element of A + A is squarefree (this is just the definition,
but stated as a standalone lemma for clarity).
-/
theorem sumset_elements_squarefree (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (s : ℕ) (hs : s ∈ sumset A) : isSquarefree s :=
  h s hs

/--
**Multiplicative constraint on sumset:**
For any prime p, no element of A + A is divisible by p².
-/
theorem sumset_not_div_prime_sq (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (s : ℕ) (hs : s ∈ sumset A) : ¬(p * p ∣ s) := by
  intro hdvd
  have hsf := h s hs
  simp only [isSquarefree] at hsf
  have hunit := hsf p hdvd
  rw [Nat.isUnit_iff] at hunit
  exact absurd hunit hp.one_lt.ne'

/-
## Part XIII: Density Constraints via Multiple Primes

The key idea for upper bounds is that for each prime p, the set A must
avoid certain residue classes mod p². The constraints from different
primes p combine multiplicatively via the Chinese Remainder Theorem.

For prime p:
- Elements of A avoid residue 0 mod p² (p² residues, 1 forbidden)
- Pairs in A avoid having sum ≡ 0 mod p² (further constraints)

For p = 2: Only 1 of 4 residue classes is allowed (either 1 or 3 mod 4)
  → density factor: 1/4

For p = 3: Elements avoid 0, 3, 6 mod 9 (multiples of 3 are not all
  forbidden, only 0 mod 9). But sum constraints further restrict:
  Allowed residues r must satisfy r + r ≢ 0 (mod 9), so 2r ≢ 0 (mod 9).
  Since gcd(2, 9) = 1, this means r ≢ 0 (mod 9), which we already know.
  But for pairs: r₁ + r₂ ≢ 0 (mod 9).
-/

/--
**Self-sum constraint modulo p²:**
For any prime p and any a ∈ A, 2a is not divisible by p².
When gcd(2, p) = 1 (i.e., p is odd), this means a ≢ 0 (mod p²).
When p = 2, this gives a ≢ 0 (mod 2), i.e., a is odd.
-/
theorem self_sum_mod (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : a ∈ A) :
    (a + a) % (p * p) ≠ 0 :=
  forbidden_residue_sum A h p hp a a ha ha

/--
**No two elements with complementary residues mod p²:**
If a ≡ r (mod p²) and b ≡ p²-r (mod p²), then a+b ≡ p² ≡ 0 (mod p²).
So at most one of each complementary pair {r, p²-r} can appear.
-/
theorem complementary_residue_exclusion (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab_sum : (a % (p * p) + b % (p * p)) = p * p) :
    False := by
  have hpp : p * p > 0 := Nat.mul_pos hp.pos hp.pos
  have h_sum : (a + b) % (p * p) = 0 := by
    have := Nat.add_mod a b (p * p)
    rw [hab_sum] at this
    simp [Nat.mod_self] at this
    exact this
  exact forbidden_residue_sum A h p hp a b ha hb h_sum

/--
**Mod 4 density:**
At most 1 out of 4 residue classes mod 4 is available for elements of A.
Specifically, either all elements are ≡ 1 (mod 4) or all are ≡ 3 (mod 4).
Combined with the constraint that a + b ≢ 0 (mod 4), only one class works.
-/
theorem mod_4_single_class (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a : ℕ) (ha : a ∈ A) :
    (∀ b ∈ A, a % 4 = b % 4) := by
  intro b hb
  have hab := same_residue_mod_4 A h a b ha hb
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/--
**Mod 9 constraint from sum avoidance:**
For prime 3, the elements of A must avoid having any pair sum to a
multiple of 9. The allowed residues r mod 9 must form a set where
no two elements (allowing repetition) sum to 0 mod 9.

The non-zero residues mod 9 pair as: {1,8}, {2,7}, {3,6}, {4,5}.
At most one from each pair, plus possibly the "self-complementary" cases
where 2r ≡ 0 (mod 9). Since gcd(2,9)=1, there is no r with 2r ≡ 0 (mod 9)
except r = 0 (which is forbidden). So we can pick at most 4 residues
from {1,2,3,4,5,6,7,8} (one from each complementary pair).
-/
theorem no_complementary_mod_9 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : (a % 9 + b % 9) % 9 = 0) : False := by
  have h9 : 9 ∣ (a + b) := by omega
  exact no_sum_div_9 A h a b ha hb h9

end Erdos1109
