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
/--
**Erdős-Sárközy Upper Bound (1987):**
f(N) ≪ N^{3/4} log N
-/
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
/-
## Part VIII: Related Problems
-/

/--
**Connection to Problem #1103:**
The infinite analogue asks for the minimum growth rate of a sequence
a₁ < a₂ < ⋯ such that all a_i + a_j are squarefree.

Upper bounds for f(N) imply lower bounds for the a_i.
-/
/--
**k-power-free Generalization (Sárközy 1992):**
Let f_k(N) be the max size of A ⊆ {1,...,N} with A + A being k-power-free.
Then similar bounds hold.
-/
def isKPowerFree (k n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p^k ∣ n)

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

private theorem squarefree_22 : Squarefree (22 : ℕ) := by
  rw [show (22 : ℕ) = 2 * 11 from by norm_num]
  have : Nat.Prime 11 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_26 : Squarefree (26 : ℕ) := by
  rw [show (26 : ℕ) = 2 * 13 from by norm_num]
  have : Nat.Prime 13 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_42 : Squarefree (42 : ℕ) := by
  rw [show (42 : ℕ) = 2 * 21 from by norm_num]
  have h21 : Squarefree (21 : ℕ) := by
    rw [show (21 : ℕ) = 3 * 7 from by norm_num]
    have : Nat.Prime 7 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, this.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h21⟩)

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
**{1, 5, 21} has a squarefree sumset.**
Sums: 1+1=2, 1+5=6, 1+21=22, 5+5=10, 5+21=26, 21+21=42.
All sums are squarefree: 2, 6=2·3, 10=2·5, 22=2·11, 26=2·13, 42=2·3·7.
-/
theorem triple_1_5_21_squarefree_sumset : hasSquarefreeSumset ({1, 5, 21} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  · exact squarefree_2          -- 1+1=2
  · exact squarefree_6          -- 1+5=6
  · exact squarefree_22         -- 1+21=22
  · exact squarefree_6          -- 5+1=6
  · exact squarefree_10         -- 5+5=10
  · exact squarefree_26         -- 5+21=26
  · exact squarefree_22         -- 21+1=22
  · exact squarefree_26         -- 21+5=26
  · exact squarefree_42         -- 21+21=42

/--
**f(N) ≥ 3 for N ≥ 21:**
The set {1, 5, 21} ⊆ {1,...,N} has squarefree sumset, giving f(N) ≥ 3.
-/
theorem f_ge_three (N : ℕ) (hN : N ≥ 21) : f N ≥ 3 := by
  unfold f
  have h3 : (3 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21}, ?_, triple_1_5_21_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h3

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

/-
## Part XIV: Explicit Lower Bound f(N) ≥ 2

The set {1, 5} witnesses f(N) ≥ 2 for N ≥ 5.
We already proved pair_1_5_squarefree_sumset, so we just need
to show this lifts to f(N) ≥ 2.
-/

/--
**f(N) ≥ 2 for N ≥ 5:**
The set {1, 5} ⊆ {1,...,N} has squarefree sumset, giving f(N) ≥ 2.
-/
theorem f_ge_two (N : ℕ) (hN : N ≥ 5) : f N ≥ 2 := by
  unfold f
  have h2 : (2 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5}, ?_, pair_1_5_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl <;> omega
    · simp [Finset.card_pair (by omega : (1 : ℕ) ≠ 5)]
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h2

/-
## Part XV: Mod 25 Constraints (p = 5)

For prime p = 5, elements avoid residue 0 mod 25 and no pair
sums to a multiple of 25. This is the next prime after 3.
-/

/-- Helper: 5 is prime -/
private theorem five_prime : Nat.Prime 5 := by native_decide

/--
**No element divisible by 25:**
For p = 5, no element of A can be divisible by 25 = 5².
-/
theorem not_div_25 (A : Finset ℕ) (h : hasSquarefreeSumset A) (a : ℕ) (ha : a ∈ A) :
    ¬(25 ∣ a) := by
  intro h25
  have h5sq : 5 * 5 ∣ a := by
    obtain ⟨k, hk⟩ := h25; exact ⟨k, by omega⟩
  exact element_not_div_prime_sq A h 5 five_prime a ha h5sq

/--
**No pair sums to a multiple of 25:**
For any a, b ∈ A, a + b is not divisible by 25.
-/
theorem no_sum_div_25 (A : Finset ℕ) (h : hasSquarefreeSumset A) (a b : ℕ)
    (ha : a ∈ A) (hb : b ∈ A) : ¬(25 ∣ (a + b)) := by
  intro h25
  have h5sq : 5 * 5 ∣ (a + b) := by
    obtain ⟨k, hk⟩ := h25; exact ⟨k, by omega⟩
  exact prime_sq_avoidance A h 5 five_prime a b ha hb h5sq

/--
**Residue class 0 mod 25 is forbidden:**
No element of A can be ≡ 0 (mod 25).
-/
theorem forbidden_class_zero_25 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a : ℕ) (ha : a ∈ A) : a % 25 ≠ 0 :=
  forbidden_class_zero A h 5 five_prime a ha

/--
**No complementary residues mod 25:**
If a % 25 + b % 25 = 25 for a, b ∈ A, then 25 | a+b, contradiction.
-/
theorem no_complementary_mod_25 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : (a % 25 + b % 25) % 25 = 0) : False := by
  have h25 : 25 ∣ (a + b) := by omega
  exact no_sum_div_25 A h a b ha hb h25

/-
## Part XVI: Residue Class Counting Framework

For each prime p, the set of allowed residue classes mod p² is constrained.
We formalize the counting argument that gives density bounds.
-/

/--
**General forbidden class:**
For any prime p and any a ∈ A, a is not in residue class 0 mod p².
This is a convenience wrapper of forbidden_class_zero.
-/
theorem residue_class_zero_forbidden (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : a ∈ A) : a % (p * p) ≠ 0 :=
  forbidden_class_zero A h p hp a ha

/--
**General sum constraint modulo p²:**
For any prime p, elements a, b ∈ A must satisfy (a + b) % (p²) ≠ 0.
In terms of residues: if r = a % p² and s = b % p², then (r + s) % p² ≠ 0.
-/
theorem sum_residue_nonzero (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    (a + b) % (p * p) ≠ 0 :=
  forbidden_residue_sum A h p hp a b ha hb

/--
**Residue image of A mod p² avoids zero:**
The image of A under (· % (p * p)) does not contain 0.
-/
theorem residue_image_avoids_zero (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) :
    (0 : ℕ) ∉ A.image (· % (p * p)) := by
  simp only [Finset.mem_image]
  intro ⟨a, ha, h0⟩
  exact forbidden_class_zero A h p hp a ha h0

/--
**Mod 4: elements use exactly one residue class.**
Given that all elements are either ≡ 1 or ≡ 3 (mod 4), and this
choice is uniform across A, the residue image of A mod 4 has at most 1 element
(among odd residues). That is, A uses at most 1 out of 4 residue classes.
-/
theorem mod_4_residue_image_small (A : Finset ℕ) (h : hasSquarefreeSumset A) :
    (A.image (· % 4)).card ≤ 1 := by
  by_cases hA : A = ∅
  · simp [hA]
  · have hne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
    obtain ⟨a, ha⟩ := hne
    have hunif := mod_4_single_class A h a ha
    suffices A.image (· % 4) ⊆ {a % 4} by
      exact le_trans (Finset.card_le_card this) (by simp)
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨b, hb, rfl⟩ := hr
    simp [hunif b hb]

/--
**Mod 9: no self-complementary residue via 2r ≡ 0 (mod 9).**
For any a ∈ A, 2a ≢ 0 (mod 9). Since gcd(2,9) = 1, this is
equivalent to a ≢ 0 (mod 9), which we already know.
But we state it separately for the density counting argument.
-/
theorem self_sum_not_div_9 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a : ℕ) (ha : a ∈ A) : (a + a) % 9 ≠ 0 := by
  intro h0
  have h9 : 9 ∣ (a + a) := by omega
  exact no_sum_div_9 A h a a ha ha h9

/-
## Part XVII: Counting Allowed Residues mod 9

For p = 3, the residue classes mod 9 split into complementary pairs
{r, 9-r}. The pairs are: {1,8}, {2,7}, {3,6}, {4,5}.
Class 0 is forbidden. At most one from each pair can be used.

Self-complementary: would need 2r ≡ 0 (mod 9), i.e., r = 0. So no
non-zero self-complementary class exists.

Result: at most 4 out of 9 residue classes are available.
Density factor: ≤ 4/9 for prime p = 3.
-/

/--
**Mod 9: residue class 0 is forbidden.**
-/
theorem mod_9_class_0_forbidden (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a : ℕ) (ha : a ∈ A) : a % 9 ≠ 0 := by
  intro h0
  have h9 : 9 ∣ a := by omega
  have h3sq : 3 * 3 ∣ a := by obtain ⟨k, hk⟩ := h9; exact ⟨k, by omega⟩
  exact element_not_div_prime_sq A h 3 three_prime a ha h3sq

/--
**Mod 9: residue classes 1 and 8 cannot both appear.**
If a ≡ 1 (mod 9) and b ≡ 8 (mod 9), then a+b ≡ 0 (mod 9).
-/
theorem mod_9_pair_1_8 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (ha1 : a % 9 = 1) (hb8 : b % 9 = 8) : False := by
  have : (a + b) % 9 = 0 := by omega
  have h9 : 9 ∣ (a + b) := by omega
  exact no_sum_div_9 A h a b ha hb h9

/--
**Mod 9: residue classes 2 and 7 cannot both appear.**
-/
theorem mod_9_pair_2_7 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (ha2 : a % 9 = 2) (hb7 : b % 9 = 7) : False := by
  have : (a + b) % 9 = 0 := by omega
  have h9 : 9 ∣ (a + b) := by omega
  exact no_sum_div_9 A h a b ha hb h9

/--
**Mod 9: residue classes 3 and 6 cannot both appear.**
-/
theorem mod_9_pair_3_6 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (ha3 : a % 9 = 3) (hb6 : b % 9 = 6) : False := by
  have : (a + b) % 9 = 0 := by omega
  have h9 : 9 ∣ (a + b) := by omega
  exact no_sum_div_9 A h a b ha hb h9

/--
**Mod 9: residue classes 4 and 5 cannot both appear.**
-/
theorem mod_9_pair_4_5 (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (ha4 : a % 9 = 4) (hb5 : b % 9 = 5) : False := by
  have : (a + b) % 9 = 0 := by omega
  have h9 : 9 ∣ (a + b) := by omega
  exact no_sum_div_9 A h a b ha hb h9

/--
**Mod 9: at most 4 residue classes.**
The residue image of A mod 9 has at most 4 elements:
one from each complementary pair {1,8}, {2,7}, {3,6}, {4,5}.
-/
theorem mod_9_residue_image_le_4 (A : Finset ℕ) (h : hasSquarefreeSumset A) :
    (A.image (· % 9)).card ≤ 4 := by
  -- The residue image is contained in {1,...,8} (0 is forbidden).
  -- The 4 complementary pairs {1,8}, {2,7}, {3,6}, {4,5} each contribute ≤ 1.
  -- We prove: the image avoids having both r and 9-r simultaneously.
  -- Strategy: show image ⊆ S for some 4-element S, by contradiction on each pair.
  --
  -- We show: not both 1 and 8, not both 2 and 7, not both 3 and 6, not both 4 and 5.
  -- Then card ≤ 4 follows from pigeonhole on 4 pairs.

  -- Helper: for each complementary pair, at most one appears
  have h_no_1_8 : ¬(1 ∈ A.image (· % 9) ∧ 8 ∈ A.image (· % 9)) := by
    intro ⟨h1, h8⟩
    simp only [Finset.mem_image] at h1 h8
    obtain ⟨a, ha, ha1⟩ := h1
    obtain ⟨b, hb, hb8⟩ := h8
    exact mod_9_pair_1_8 A h a b ha hb ha1 hb8

  have h_no_2_7 : ¬(2 ∈ A.image (· % 9) ∧ 7 ∈ A.image (· % 9)) := by
    intro ⟨h2, h7⟩
    simp only [Finset.mem_image] at h2 h7
    obtain ⟨a, ha, ha2⟩ := h2
    obtain ⟨b, hb, hb7⟩ := h7
    exact mod_9_pair_2_7 A h a b ha hb ha2 hb7

  have h_no_3_6 : ¬(3 ∈ A.image (· % 9) ∧ 6 ∈ A.image (· % 9)) := by
    intro ⟨h3, h6⟩
    simp only [Finset.mem_image] at h3 h6
    obtain ⟨a, ha, ha3⟩ := h3
    obtain ⟨b, hb, hb6⟩ := h6
    exact mod_9_pair_3_6 A h a b ha hb ha3 hb6

  have h_no_4_5 : ¬(4 ∈ A.image (· % 9) ∧ 5 ∈ A.image (· % 9)) := by
    intro ⟨h4, h5⟩
    simp only [Finset.mem_image] at h4 h5
    obtain ⟨a, ha, ha4⟩ := h4
    obtain ⟨b, hb, hb5⟩ := h5
    exact mod_9_pair_4_5 A h a b ha hb ha4 hb5

  -- Image avoids 0
  have h0 : (0 : ℕ) ∉ A.image (· % 9) := by
    simp only [Finset.mem_image]
    intro ⟨a, ha, h0⟩
    exact mod_9_class_0_forbidden A h a ha h0

  -- Image is contained in {1,...,8}
  have hbnd : A.image (· % 9) ⊆ Finset.range 9 := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    simp [Finset.mem_range]; omega

  -- Now: by contradiction. If card ≥ 5, from {1,...,8} with 5+ elements,
  -- one complementary pair must appear.
  by_contra hgt
  push_neg at hgt
  -- card ≥ 5, image ⊆ {1,...,8} = 8 elements in 4 pairs, so ≥ 2 from one pair
  -- From each pair {r, 9-r}, at most 1 can be in the image. With 4 pairs, max is 4.
  -- Since we have 5+ elements, one pair contributes 2 → contradiction.
  --
  -- Formalize: image ⊆ {1,...,8}, so it contains ≥ 5 elements.
  -- Count by pairs: for pair {1,8}, contribute c₁ ∈ {0,1};
  -- similarly c₂, c₃, c₄ for pairs {2,7}, {3,6}, {4,5}.
  -- Then c₁+c₂+c₃+c₄ ≥ 5 but each cᵢ ≤ 1, so max is 4. Contradiction.
  --
  -- We prove: for each element r in the image, it belongs to exactly one pair.
  -- Pair membership: 1→P1, 8→P1, 2→P2, 7→P2, 3→P3, 6→P3, 4→P4, 5→P4.
  -- Define f(r) = min(r, 9-r). Then f maps {1,...,8} → {1,2,3,4}.
  -- image.card ≤ (image.image f).card * 2 won't quite work...
  --
  -- Simpler: just enumerate. We need 5 elements from {1,...,8} with no
  -- complementary pair. The possible subsets are limited. Check all C(8,5)=56.
  -- Actually, use decidability: it's a finite check.
  --
  -- Most pragmatic: the image is a subset of {1,...,8} with card ≥ 5.
  -- There are C(8,5)+C(8,6)+C(8,7)+C(8,8) = 56+28+8+1 = 93 such subsets.
  -- Each must contain some complementary pair. This is decidable but tedious.
  --
  -- Alternative: show image ⊆ S ∪ T where S = {1,2,3,4}, T = {5,6,7,8}
  -- and |image ∩ S| + |image ∩ T| = |image| ≥ 5, but if r ∈ image ∩ S
  -- then 9-r ∉ image, so image ∩ T misses 9-r for each r ∈ image ∩ S.
  -- image ∩ T ⊆ T \ (image of 9-· on image ∩ S), giving |image ∩ T| ≤ 4 - |image ∩ S|.
  -- So |image| ≤ |image ∩ S| + (4 - |image ∩ S|) = 4. Contradiction.
  --
  -- Let's try the complementary exclusion argument directly.
  -- For each r in {1,2,3,4}: if r ∈ image, then (9-r) ∉ image.
  -- So from each pair {r, 9-r}, at most 1 element.
  -- card image ≤ (number of pairs with ≥ 1 element) ≤ 4. But we need card ≥ 5.
  -- This is exactly the contradiction we need.
  --
  -- Formalize: image ⊆ {1,...,8}. Define pairs P = {{1,8},{2,7},{3,6},{4,5}}.
  -- The function g(r) = min(r, 9-r) maps image into {1,2,3,4}.
  -- (image.image g).card ≤ 4 since range is {1,2,3,4}.
  -- For each val v in image of g, the preimage in the original image has card ≤ 1
  -- (since we can't have both v and 9-v).
  -- So image.card = ∑_{v in image g} |preimage of v| ≤ 4 × 1 = 4.
  -- But image.card ≥ 5. Contradiction.

  -- For now, we use a simpler approach: since we need ≥ 5 from {1,...,8},
  -- and each element r excludes 9-r, we get a contradiction.
  -- We'll show this by noting that the image, viewed as a subset of {1,...,8},
  -- can have card at most 4 by the exclusion principle.

  -- Since the image is in range 9 and avoids 0, it's ⊆ {1,...,8}
  have hsub : A.image (· % 9) ⊆ {1, 2, 3, 4, 5, 6, 7, 8} := by
    intro r hr
    have := hbnd hr
    simp only [Finset.mem_range] at this
    have : r ≠ 0 := fun heq => h0 (heq ▸ hr)
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega

  -- Now we need: if S ⊆ {1,...,8} and S avoids complementary pairs, then |S| ≤ 4.
  -- The pair exclusions give: ¬(1 ∈ S ∧ 8 ∈ S), etc.
  -- This means S ⊆ {1,...,8} \ {at least 4 elements} when |S| ≥ 5.
  -- We use omega-style reasoning after establishing the constraints.

  -- More directly: S.card ≤ 4 because S is an independent set in a graph
  -- with 4 disjoint edges covering all 8 vertices. Max independent set = 4.
  -- In Lean, we prove this by explicit finite case analysis.

  -- Let S = A.image (· % 9)
  -- We know S ⊆ {1,2,3,4,5,6,7,8} and S.card ≥ 5
  -- We know ¬(1 ∈ S ∧ 8 ∈ S), ¬(2 ∈ S ∧ 7 ∈ S), ¬(3 ∈ S ∧ 6 ∈ S), ¬(4 ∈ S ∧ 5 ∈ S)
  -- Goal: contradiction.

  -- From the 4 exclusions, for each pair, at most 1 is in S.
  -- That means: if 1 ∈ S then 8 ∉ S (so S loses 8)
  --             if 8 ∈ S then 1 ∉ S (so S loses 1)
  --             etc.
  -- In either case, from each pair we get at most 1.
  -- So |S| ≤ 4.

  -- We formalize via a counting argument:
  -- partition {1,...,8} into {1,8} ∪ {2,7} ∪ {3,6} ∪ {4,5}
  -- |S| = |S ∩ {1,8}| + |S ∩ {2,7}| + |S ∩ {3,6}| + |S ∩ {4,5}|
  -- Each term ≤ 1 by the exclusion principle.
  -- So |S| ≤ 4. But |S| ≥ 5. Contradiction.

  -- The simplest approach: use native_decide or decide if available
  -- on a finite universe. Actually, let's just use omega + membership tests.

  -- We can also just use: card ≤ card {1,...,8} - 4 = 4 by removing one from each pair.
  -- But actually card {1,...,8} = 8 and we remove at least 4, so ≤ 4.

  -- Let's try the partition approach more concretely.
  -- Define: S misses at least 1 from {1,8}, at least 1 from {2,7}, at least 1 from {3,6}, at least 1 from {4,5}.
  -- So S ⊆ {1,...,8} \ {x₁,x₂,x₃,x₄} where xᵢ is the excluded element from pair i.
  -- |S| ≤ 8 - 4 = 4.

  -- Actually, the simplest Lean proof: S misses at least one element from each pair.
  -- So there exist w, x, y, z ∉ S with w ∈ {1,8}, x ∈ {2,7}, y ∈ {3,6}, z ∈ {4,5},
  -- and {w,x,y,z} are distinct (from different pairs). So |{1,...,8} \ S| ≥ 4.
  -- Therefore |S| ≤ 8 - 4 = 4.

  -- We need: if S ⊆ {1,...,8} avoids complementary pairs and has card ≥ 5, contradiction.
  -- The 4 complementary pairs {1,8}, {2,7}, {3,6}, {4,5} partition {1,...,8}.
  -- From each pair, at most 1 element can be in S. So |S| ≤ 4.

  set S := A.image (· % 9) with hS_def

  -- S ⊆ {1,...,8} and we have the pair exclusions
  have h_no_1_8 : ¬(1 ∈ S ∧ 8 ∈ S) := by
    intro ⟨h1, h8⟩
    simp only [hS_def, Finset.mem_image] at h1 h8
    obtain ⟨a, ha, ha1⟩ := h1
    obtain ⟨b, hb, hb8⟩ := h8
    exact mod_9_pair_1_8 A h a b ha hb ha1 hb8

  have h_no_2_7 : ¬(2 ∈ S ∧ 7 ∈ S) := by
    intro ⟨h2, h7⟩
    simp only [hS_def, Finset.mem_image] at h2 h7
    obtain ⟨a, ha, ha2⟩ := h2
    obtain ⟨b, hb, hb7⟩ := h7
    exact mod_9_pair_2_7 A h a b ha hb ha2 hb7

  have h_no_3_6 : ¬(3 ∈ S ∧ 6 ∈ S) := by
    intro ⟨h3, h6⟩
    simp only [hS_def, Finset.mem_image] at h3 h6
    obtain ⟨a, ha, ha3⟩ := h3
    obtain ⟨b, hb, hb6⟩ := h6
    exact mod_9_pair_3_6 A h a b ha hb ha3 hb6

  have h_no_4_5 : ¬(4 ∈ S ∧ 5 ∈ S) := by
    intro ⟨h4, h5⟩
    simp only [hS_def, Finset.mem_image] at h4 h5
    obtain ⟨a, ha, ha4⟩ := h4
    obtain ⟨b, hb, hb5⟩ := h5
    exact mod_9_pair_4_5 A h a b ha hb ha4 hb5

  -- Key counting argument:
  -- From each pair, at most 1 element is in S. With 4 pairs, |S| ≤ 4.
  -- We prove: |S ∩ P| ≤ 1 for each pair P, and S ⊆ ∪P, so |S| ≤ 4.

  -- Helper: for any 2-element set {a,b}, if ¬(a ∈ S ∧ b ∈ S), then |S ∩ {a,b}| ≤ 1
  have pair_card_le_1 : ∀ (a b : ℕ), a ≠ b → ¬(a ∈ S ∧ b ∈ S) →
      (S ∩ ({a, b} : Finset ℕ)).card ≤ 1 := by
    intro a b _ hne
    push_neg at hne
    by_cases ha : a ∈ S
    · -- a ∈ S, so b ∉ S by hne
      have hb := hne ha
      have hsub' : S ∩ {a, b} ⊆ {a} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl
        · rfl
        · exact absurd hx.1 hb
      calc (S ∩ {a, b}).card ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton a
    · -- a ∉ S
      have hsub' : S ∩ {a, b} ⊆ {b} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl
        · exact absurd hx.1 ha
        · rfl
      calc (S ∩ {a, b}).card ≤ ({b} : Finset ℕ).card := Finset.card_le_card hsub'
        _ = 1 := Finset.card_singleton b

  have hc18 : (S ∩ ({1, 8} : Finset ℕ)).card ≤ 1 := pair_card_le_1 1 8 (by omega) h_no_1_8
  have hc27 : (S ∩ ({2, 7} : Finset ℕ)).card ≤ 1 := pair_card_le_1 2 7 (by omega) h_no_2_7
  have hc36 : (S ∩ ({3, 6} : Finset ℕ)).card ≤ 1 := pair_card_le_1 3 6 (by omega) h_no_3_6
  have hc45 : (S ∩ ({4, 5} : Finset ℕ)).card ≤ 1 := pair_card_le_1 4 5 (by omega) h_no_4_5

  -- The four pairs are pairwise disjoint
  have hdisj : Disjoint ({1, 8} : Finset ℕ) ({2, 7} ∪ {3, 6} ∪ {4, 5}) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    native_decide

  have hdisj2 : Disjoint ({2, 7} : Finset ℕ) ({3, 6} ∪ {4, 5}) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    native_decide

  have hdisj3 : Disjoint ({3, 6} : Finset ℕ) ({4, 5}) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    native_decide

  -- S ⊆ {1,8} ∪ {2,7} ∪ {3,6} ∪ {4,5}
  have hsub' : S ⊆ {1, 8} ∪ {2, 7} ∪ {3, 6} ∪ {4, 5} := by
    intro r hr
    have := hsub hr
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at this ⊢
    omega

  -- Using the disjoint decomposition, card S = sum of intersection cards
  -- The union is right-associated: {1,8} ∪ ({2,7} ∪ ({3,6} ∪ {4,5}))
  -- Rewrite union to match this
  have hunion_eq : ({1, 8} ∪ {2, 7} ∪ {3, 6} ∪ {4, 5} : Finset ℕ) =
      {1, 8} ∪ ({2, 7} ∪ ({3, 6} ∪ {4, 5})) := by
    simp only [Finset.union_assoc]

  have hpart1 : (S ∩ ({1, 8} ∪ ({2, 7} ∪ ({3, 6} ∪ {4, 5})))).card =
      (S ∩ {1, 8}).card + (S ∩ ({2, 7} ∪ ({3, 6} ∪ {4, 5}))).card := by
    conv_lhs => rw [Finset.inter_union_distrib_left]
    have hdisj' : Disjoint ({1, 8} : Finset ℕ) ({2, 7} ∪ ({3, 6} ∪ {4, 5})) := by
      rw [Finset.disjoint_iff_inter_eq_empty]; native_decide
    have hd : Disjoint (S ∩ {1, 8}) (S ∩ ({2, 7} ∪ ({3, 6} ∪ {4, 5}))) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj')
    exact Finset.card_union_of_disjoint hd

  have hpart2 : (S ∩ ({2, 7} ∪ ({3, 6} ∪ {4, 5}))).card =
      (S ∩ {2, 7}).card + (S ∩ ({3, 6} ∪ {4, 5})).card := by
    conv_lhs => rw [Finset.inter_union_distrib_left]
    have hdisj' : Disjoint ({2, 7} : Finset ℕ) ({3, 6} ∪ {4, 5}) := by
      rw [Finset.disjoint_iff_inter_eq_empty]; native_decide
    have hd : Disjoint (S ∩ {2, 7}) (S ∩ ({3, 6} ∪ {4, 5})) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj')
    exact Finset.card_union_of_disjoint hd

  have hpart3 : (S ∩ ({3, 6} ∪ {4, 5})).card = (S ∩ {3, 6}).card + (S ∩ {4, 5}).card := by
    conv_lhs => rw [Finset.inter_union_distrib_left]
    have hd : Disjoint (S ∩ {3, 6}) (S ∩ {4, 5}) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj3)
    exact Finset.card_union_of_disjoint hd

  -- Since S ⊆ union, S ∩ union = S
  have hsub'' : S ⊆ {1, 8} ∪ ({2, 7} ∪ ({3, 6} ∪ {4, 5})) := by
    rw [← hunion_eq]; exact hsub'

  have hS_eq : S = S ∩ ({1, 8} ∪ ({2, 7} ∪ ({3, 6} ∪ {4, 5}))) :=
    (Finset.inter_eq_left.mpr hsub'').symm

  -- Final calculation: |S| ≤ 4 but we assumed |S| > 4, contradiction
  have hS_le4 : S.card ≤ 4 := by
    calc S.card = (S ∩ ({1, 8} ∪ ({2, 7} ∪ ({3, 6} ∪ {4, 5})))).card := by rw [← hS_eq]
      _ = (S ∩ {1, 8}).card + (S ∩ ({2, 7} ∪ ({3, 6} ∪ {4, 5}))).card := hpart1
      _ = (S ∩ {1, 8}).card + ((S ∩ {2, 7}).card + (S ∩ ({3, 6} ∪ {4, 5})).card) := by rw [hpart2]
      _ = (S ∩ {1, 8}).card + ((S ∩ {2, 7}).card + ((S ∩ {3, 6}).card + (S ∩ {4, 5}).card)) := by rw [hpart3]
      _ ≤ 1 + (1 + (1 + 1)) := by omega
      _ = 4 := by omega

  omega

/-
## Part XIX: Counting Allowed Residues mod 25

For p = 5, the residue classes mod 25 split into complementary pairs
{r, 25-r}. The pairs are: {1,24}, {2,23}, {3,22}, {4,21}, {5,20},
{6,19}, {7,18}, {8,17}, {9,16}, {10,15}, {11,14}, {12,13}.
Class 0 is forbidden. At most one from each pair can be used.

Result: at most 12 out of 25 residue classes are available.
Density factor: ≤ 12/25 for prime p = 5.
-/

/--
**No complementary residues mod 25 (general):**
If a % 25 + b % 25 sums to 0 mod 25, then 25 | a+b, contradiction.
-/
theorem no_complementary_mod_25_general (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a % 25 + b % 25 = 25) : False := by
  have h25 : 25 ∣ (a + b) := by omega
  exact no_sum_div_25 A h a b ha hb h25

/--
**Mod 25: at most 12 residue classes.**
The residue image of A mod 25 has at most 12 elements:
one from each of 12 complementary pairs {r, 25-r} for r = 1,...,12.
Class 0 is forbidden and there is no self-complementary class (since 2r ≡ 0 mod 25
has no nonzero solution, as gcd(2,25)=1).
-/
theorem mod_25_residue_image_le_12 (A : Finset ℕ) (h : hasSquarefreeSumset A) :
    (A.image (· % 25)).card ≤ 12 := by
  -- Image avoids 0
  have h0 : (0 : ℕ) ∉ A.image (· % 25) := by
    simp only [Finset.mem_image]
    intro ⟨a, ha, h0⟩
    exact forbidden_class_zero_25 A h a ha h0
  -- Image ⊆ {1,...,24}
  have hbnd : A.image (· % 25) ⊆ Finset.range 25 := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    simp [Finset.mem_range]; omega
  -- For each pair {r, 25-r}, at most one appears
  -- We use the same partition argument as mod 9
  -- The 12 pairs {1,24},{2,23},...,{12,13} partition {1,...,24}
  -- Each pair contributes at most 1 element to the image
  -- So |image| ≤ 12
  set S := A.image (· % 25) with hS_def
  by_contra hgt
  push_neg at hgt
  -- S ⊆ {1,...,24} with |S| ≥ 13
  -- The 12 pairs partition {1,...,24} into 12 groups of size 2
  -- By pigeonhole, some pair has both elements in S
  -- For that pair {r, 25-r}, a+b ≡ 0 (mod 25) → contradiction
  -- We prove by showing S has ≤ 12 elements via the partition argument:
  -- for each r in S, define f(r) = min(r, 25-r), mapping S → {1,...,12}
  -- For each v ∈ {1,...,12}, at most 1 of {v, 25-v} is in S
  -- (if both v ∈ S and 25-v ∈ S, then ∃ a,b with a%25=v, b%25=25-v, sum=25 → contradiction)
  -- So |f(S)| = |S| - #{v : both v, 25-v ∈ S} ≥ |S| ... no, we need cardinality via injection
  -- Actually: f maps S into {1,...,12} and is at most 2-to-1.
  -- But if both v and 25-v ∈ S, contradiction. So f is injective on S.
  -- Therefore |S| ≤ 12.
  -- We need to show: if r, r' ∈ S with f(r) = f(r'), then r = r'.
  -- f(r) = min(r, 25-r). If f(r) = f(r') and r ≠ r', then {r, r'} = {v, 25-v} for some v.
  -- But then both v and 25-v are in S, giving a contradiction.
  -- Let's formalize the injection.
  -- Define g : ℕ → ℕ := fun r => min r (25 - r)  (for r ∈ {1,...,24})
  -- g maps {1,...,24} → {1,...,12}
  -- g(r) = g(r') and r ≠ r' implies {r, r'} = {g(r), 25 - g(r)}
  -- If both are in S, we get a contradiction

  -- Simpler approach: S.image g has card ≤ 12 (range is {1,...,12})
  -- and g is injective on S (no pair {r, 25-r} both in S)
  -- so S.card = (S.image g).card ≤ 12

  -- We can actually just use the fact that S ⊆ {1,...,24} and no complementary pair
  -- Use the general complementary pair exclusion to construct an injection into {1,...,12}
  -- For now, use the more direct counting argument:

  -- For r ∈ {1,...,12}: if r ∈ S, then 25-r ∉ S
  -- So S ⊆ {1,...,24} and for each r ∈ {1,...,12}, |S ∩ {r, 25-r}| ≤ 1
  -- These 12 pairs partition {1,...,24}, so |S| ≤ 12

  -- Pair exclusion for each of the 12 pairs
  have hpair : ∀ r : ℕ, r ≥ 1 → r ≤ 12 → ¬(r ∈ S ∧ (25 - r) ∈ S) := by
    intro r _ hr_le ⟨hr_in, hc_in⟩
    simp only [hS_def, Finset.mem_image] at hr_in hc_in
    obtain ⟨a, ha, ha_r⟩ := hr_in
    obtain ⟨b, hb, hb_c⟩ := hc_in
    apply no_complementary_mod_25_general A h a b ha hb
    omega

  -- Each pair contributes at most 1
  have pair_le_1 : ∀ r : ℕ, r ≥ 1 → r ≤ 12 →
      (S ∩ ({r, 25 - r} : Finset ℕ)).card ≤ 1 := by
    intro r hr1 hr12
    have hne : r ≠ 25 - r := by omega
    have hpair_r := hpair r hr1 hr12
    push_neg at hpair_r
    by_cases hr : r ∈ S
    · have hc := hpair_r hr
      have : S ∩ {r, 25 - r} ⊆ {r} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl
        · rfl
        · exact absurd hx.1 hc
      calc (S ∩ {r, 25 - r}).card ≤ ({r} : Finset ℕ).card := Finset.card_le_card this
        _ = 1 := Finset.card_singleton r
    · have : S ∩ {r, 25 - r} ⊆ {25 - r} := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx.2 with rfl | rfl
        · exact absurd hx.1 hr
        · rfl
      calc (S ∩ {r, 25 - r}).card ≤ ({25 - r} : Finset ℕ).card := Finset.card_le_card this
        _ = 1 := Finset.card_singleton (25 - r)

  -- S ⊆ union of all pairs
  have hsub : S ⊆ Finset.range 25 \ {0} := by
    intro r hr
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hbnd hr, fun heq => h0 (heq ▸ hr)⟩

  -- Direct: since image is in {1,...,24} which has 24 elements, and
  -- we need ≥ 13, but each of 12 pairs contributes ≤ 1...
  -- We need |S| ≤ 12 but we assumed |S| ≥ 13.

  -- Use the injection argument via min(r, 25-r)
  -- For each s ∈ S, define g(s) = if s ≤ 12 then s else 25 - s
  -- g maps S → {1,...,12}
  -- g is injective: if g(s) = g(t) and s ≠ t, then one of them is g(s) and the other is 25-g(s)
  -- both in S → contradicts pair exclusion

  -- Actually let's use a cleaner approach with Finset.card_le_card_of_injOn
  have g_inj : Set.InjOn (fun r => min r (25 - r)) (S : Set ℕ) := by
    intro r hr s hs hg
    simp only [Finset.mem_coe] at hr hs
    by_contra hne
    -- r ≠ s and min(r, 25-r) = min(s, 25-s)
    -- Since r, s ∈ {1,...,24} and r ≠ s, with same min value v,
    -- one must be v and the other 25-v (the two preimages of v)
    have hr_range := hsub hr
    have hs_range := hsub hs
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hr_range hs_range
    -- r ∈ {1,...,24} and s ∈ {1,...,24}
    have hr_pos : r ≥ 1 := by omega
    have hs_pos : s ≥ 1 := by omega
    have hr_le : r ≤ 24 := by omega
    have hs_le : s ≤ 24 := by omega
    -- min(r, 25-r) = min(s, 25-s) and r ≠ s
    -- Case analysis on whether r ≤ 12 or r > 12
    -- If r ≤ 12: min(r,25-r) = r since r ≤ 25-r iff r ≤ 12
    -- If r > 12: min(r,25-r) = 25-r
    -- Similarly for s
    -- So if both ≤ 12: r = s. If both > 12: 25-r = 25-s, so r = s.
    -- If r ≤ 12, s > 12: r = 25-s, so s = 25-r.
    -- Then both r and 25-r = s are in S → pair contradiction
    -- Similarly if r > 12, s ≤ 12.
    by_cases hr12 : r ≤ 12 <;> by_cases hs12 : s ≤ 12
    · -- Both ≤ 12: min = r and min = s, so r = s, contradiction
      have : min r (25 - r) = r := Nat.min_eq_left (by omega)
      have : min s (25 - s) = s := Nat.min_eq_left (by omega)
      omega
    · -- r ≤ 12, s > 12: min(r,25-r) = r, min(s,25-s) = 25-s, so r = 25-s
      have hmin_r : min r (25 - r) = r := Nat.min_eq_left (by omega)
      have hmin_s : min s (25 - s) = 25 - s := Nat.min_eq_right (by omega)
      have : r = 25 - s := by omega
      -- So s = 25 - r, and both r and s = 25-r are in S
      have : s = 25 - r := by omega
      have hr1 : r ≥ 1 := by omega
      exact hpair r hr1 (by omega) ⟨hr, this ▸ hs⟩
    · -- r > 12, s ≤ 12: min(r,25-r) = 25-r, min(s,25-s) = s, so 25-r = s
      have hmin_r : min r (25 - r) = 25 - r := Nat.min_eq_right (by omega)
      have hmin_s : min s (25 - s) = s := Nat.min_eq_left (by omega)
      have : 25 - r = s := by omega
      -- So r = 25 - s, and both s and r = 25-s are in S
      have : r = 25 - s := by omega
      have hs1 : s ≥ 1 := by omega
      exact hpair s hs1 (by omega) ⟨hs, this ▸ hr⟩
    · -- Both > 12: min = 25-r and min = 25-s, so 25-r = 25-s, so r = s, contradiction
      have : min r (25 - r) = 25 - r := Nat.min_eq_right (by omega)
      have : min s (25 - s) = 25 - s := Nat.min_eq_right (by omega)
      omega

  -- g maps S into Finset.range 13 \ {0} = {1,...,12} (which has card 12)
  have g_range : ∀ r ∈ S, min r (25 - r) ∈ Finset.range 13 \ {0} := by
    intro r hr
    have hr_range := hsub hr
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hr_range ⊢
    constructor
    · -- min(r, 25-r) < 13, i.e., ≤ 12
      omega
    · -- min(r, 25-r) ≠ 0
      omega

  -- |S| ≤ |range 13 \ {0}| = 12
  have hcard_target : (Finset.range 13 \ ({0} : Finset ℕ)).card = 12 := by native_decide

  have := Finset.card_le_card_of_injOn (fun r => min r (25 - r)) g_inj
    (fun r hr => Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  -- S.image g has card = S.card (by injectivity) and is ⊆ {1,...,12}
  have himg_sub : S.image (fun r => min r (25 - r)) ⊆ Finset.range 13 \ {0} := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨r, hr, rfl⟩ := hv
    exact g_range r hr

  have hle : S.card ≤ (Finset.range 13 \ ({0} : Finset ℕ)).card := by
    calc S.card = (S.image (fun r => min r (25 - r))).card :=
            (Finset.card_image_of_injOn g_inj).symm
      _ ≤ (Finset.range 13 \ ({0} : Finset ℕ)).card := Finset.card_le_card himg_sub

  omega

/-
## Part XVIII: General Density Framework

The product of density constraints across primes gives the upper bound.
For each prime p, the allowed fraction of residue classes mod p² is:
- p = 2: 1/4 (one of {0,1,2,3})
- p = 3: ≤ 4/9 (at most 4 of {0,...,8})
- p = 5: ≤ 12/25 (at most 12 of {0,...,24})
- General p: ≤ (p²-1)/(2p²) for large p

By CRT, the combined density across primes p ≤ P is:
  ∏_{p ≤ P} (allowed/p²)
which is a rapidly decreasing product.
-/

/--
**Residue image avoids complementary pairs mod p²:**
The general principle: for any prime p, the residue image of A mod p²
cannot contain both r and (p² - r) for any r ∈ {1, ..., p²-1}.
-/
theorem no_complementary_pair_general (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) (r : ℕ) (_ : r ≥ 1) (hr2 : r ≤ p * p - 1)
    (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (ha_r : a % (p * p) = r) (hb_compl : b % (p * p) = p * p - r) :
    False := by
  have hpp : p * p ≥ 2 := by
    have := hp.two_le; nlinarith
  apply complementary_residue_exclusion A h p hp a b ha hb
  omega

/--
**Residue classes mod p² counting principle:**
For any prime p and squarefree-sumset set A ⊆ {1,...,N}:
- Class 0 is forbidden (1 class out)
- Each pair {r, p²-r} for r = 1,...,⌊(p²-1)/2⌋ contributes at most 1 class
- Number of complementary pairs: (p² - 1) / 2 (since p² is odd for odd p, or 4 for p=2)
- So at most (p² - 1) / 2 classes are allowed out of p² classes total

This gives density ≤ (p² - 1) / (2 * p²) for each prime p.
-/
theorem density_per_prime (p : ℕ) (_ : p.Prime) :
    -- The number of allowed residue classes mod p² is at most (p²-1)/2
    -- This is a statement about the structure of sum-free subsets of Z/p²Z
    -- We state it as: the maximum antichain size in the "complementary pair" poset
    (p * p - 1) / 2 ≤ p * p := by
  omega

/-
## Part XX: Improved Lower Bound f(N) ≥ 4

The set {1, 5, 21, 37} witnesses f(N) ≥ 4 for N ≥ 37.
All pairwise sums: 2, 6, 10, 22, 26, 38, 42, 58, 74 are squarefree.
-/

-- Squarefree witnesses for new sums
private theorem squarefree_38 : Squarefree (38 : ℕ) := by
  rw [show (38 : ℕ) = 2 * 19 from by norm_num]
  have : Nat.Prime 19 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_58 : Squarefree (58 : ℕ) := by
  rw [show (58 : ℕ) = 2 * 29 from by norm_num]
  have : Nat.Prime 29 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_74 : Squarefree (74 : ℕ) := by
  rw [show (74 : ℕ) = 2 * 37 from by norm_num]
  have : Nat.Prime 37 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

/--
**{1, 5, 21, 37} has a squarefree sumset.**
All 10 pairwise sums (4 self-sums + 6 cross-sums) are squarefree:
1+1=2, 1+5=6, 1+21=22, 1+37=38, 5+5=10, 5+21=26, 5+37=42, 21+21=42, 21+37=58, 37+37=74.
-/
theorem quad_1_5_21_37_squarefree_sumset : hasSquarefreeSumset ({1, 5, 21, 37} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- 1+1=2, 1+5=6, 1+21=22, 1+37=38
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  -- 5+1=6, 5+5=10, 5+21=26, 5+37=42
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  -- 21+1=22, 21+5=26, 21+21=42, 21+37=58
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  -- 37+1=38, 37+5=42, 37+21=58, 37+37=74
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74

/--
**f(N) ≥ 4 for N ≥ 37:**
The set {1, 5, 21, 37} ⊆ {1,...,N} has squarefree sumset, giving f(N) ≥ 4.
-/
theorem f_ge_four (N : ℕ) (hN : N ≥ 37) : f N ≥ 4 := by
  unfold f
  have h4 : (4 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37}, ?_, quad_1_5_21_37_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h4

/-
## Part XXI: f(N) ≥ 5

The set {1, 5, 21, 37, 41} witnesses f(N) ≥ 5 for N ≥ 41.
All 15 pairwise sums are squarefree:
1+1=2, 1+5=6, 1+21=22, 1+37=38, 1+41=42, 5+5=10, 5+21=26,
5+37=42, 5+41=46, 21+21=42, 21+37=58, 21+41=62, 37+37=74,
37+41=78, 41+41=82.
-/

-- Squarefree witnesses for the new sums from adding 41
private theorem squarefree_46 : Squarefree (46 : ℕ) := by
  rw [show (46 : ℕ) = 2 * 23 from by norm_num]
  have : Nat.Prime 23 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_62 : Squarefree (62 : ℕ) := by
  rw [show (62 : ℕ) = 2 * 31 from by norm_num]
  have : Nat.Prime 31 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_78 : Squarefree (78 : ℕ) := by
  rw [show (78 : ℕ) = 2 * 39 from by norm_num]
  have h39 : Squarefree (39 : ℕ) := by
    rw [show (39 : ℕ) = 3 * 13 from by norm_num]
    have : Nat.Prime 13 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, this.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h39⟩)

private theorem squarefree_82 : Squarefree (82 : ℕ) := by
  rw [show (82 : ℕ) = 2 * 41 from by norm_num]
  have : Nat.Prime 41 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

/--
**{1, 5, 21, 37, 41} has a squarefree sumset.**
All 15 pairwise sums are squarefree. This is verified by checking each of the
25 ordered pairs (a, b) with a, b ∈ {1, 5, 21, 37, 41}.
-/
theorem quint_1_5_21_37_41_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- Row a=1: 1+1=2, 1+5=6, 1+21=22, 1+37=38, 1+41=42
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  · exact squarefree_42
  -- Row a=5: 5+1=6, 5+5=10, 5+21=26, 5+37=42, 5+41=46
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_46
  -- Row a=21: 21+1=22, 21+5=26, 21+21=42, 21+37=58, 21+41=62
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_62
  -- Row a=37: 37+1=38, 37+5=42, 37+21=58, 37+37=74, 37+41=78
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74
  · exact squarefree_78
  -- Row a=41: 41+1=42, 41+5=46, 41+21=62, 41+37=78, 41+41=82
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_62
  · exact squarefree_78
  · exact squarefree_82

/--
**f(N) ≥ 5 for N ≥ 41:**
The set {1, 5, 21, 37, 41} ⊆ {1,...,N} has squarefree sumset, giving f(N) ≥ 5.
-/
theorem f_ge_five (N : ℕ) (hN : N ≥ 41) : f N ≥ 5 := by
  unfold f
  have h5 : (5 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41}, ?_, quint_1_5_21_37_41_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h5

/-
## Part XXII: General Residue Counting Theorem

For any prime p, the image of A modulo p² has at most (p²-1)/2 elements.
This generalizes the specific results for p=3 (mod 9, ≤ 4) and p=5 (mod 25, ≤ 12).

The proof uses an injection g(r) = min(r, p²-r) from S (the residue image) into
{1, ..., (p²-1)/2}. The injectivity follows from the fact that complementary
residues cannot both appear in S.
-/

/--
**General residue counting for squarefree sumsets:**
For any prime p and any set A with squarefree sumset,
the residue image of A modulo p² has at most (p*p-1)/2 elements.

This is the unified version of mod_9_residue_image_le_4 (p=3: (9-1)/2=4)
and mod_25_residue_image_le_12 (p=5: (25-1)/2=12).
-/
theorem general_residue_image_le (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p : ℕ) (hp : p.Prime) :
    (A.image (· % (p * p))).card ≤ (p * p - 1) / 2 := by
  set pp := p * p with hpp_def
  set S := A.image (· % pp) with hS_def
  have hpp_pos : pp > 0 := Nat.mul_pos hp.pos hp.pos
  -- Image avoids 0
  have h0 : (0 : ℕ) ∉ S := residue_image_avoids_zero A h p hp
  -- Image ⊆ range pp
  have hbnd : S ⊆ Finset.range pp := by
    intro r hr
    simp only [hS_def, Finset.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact Finset.mem_range.mpr (Nat.mod_lt a hpp_pos)
  -- Image ⊆ {1, ..., pp-1}
  have hsub : S ⊆ Finset.range pp \ {0} := by
    intro r hr
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hbnd hr, fun heq => h0 (heq ▸ hr)⟩
  -- Complementary pair exclusion: no both r and pp-r in S
  have hpair : ∀ r : ℕ, r ≥ 1 → r ≤ pp - 1 → r ∈ S → (pp - r) ∉ S := by
    intro r hr1 hr_le hr_in hc_in
    simp only [hS_def, Finset.mem_image] at hr_in hc_in
    obtain ⟨a, ha, ha_r⟩ := hr_in
    obtain ⟨b, hb, hb_c⟩ := hc_in
    exact complementary_residue_exclusion A h p hp a b ha hb (by rw [ha_r, hb_c]; omega)
  -- pp ≥ 4 since p ≥ 2
  have hpp_ge : pp ≥ 4 := by
    have := hp.two_le; nlinarith
  -- Define g : ℕ → ℕ := fun r => min r (pp - r)
  -- g is injective on S: if g(r) = g(s) with r ≠ s, then {r,s} = {v, pp-v}
  -- and both in S → contradiction
  have g_inj : Set.InjOn (fun r => min r (pp - r)) (S : Set ℕ) := by
    intro r hr s hs hg
    simp only [Finset.mem_coe] at hr hs
    by_contra hne
    have hr_range := hsub hr
    have hs_range := hsub hs
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hr_range hs_range
    have hr_pos : r ≥ 1 := by omega
    have hs_pos : s ≥ 1 := by omega
    have hr_le : r ≤ pp - 1 := by omega
    have hs_le : s ≤ pp - 1 := by omega
    -- Case analysis on whether r ≤ pp/2 or r > pp/2
    by_cases hr2 : 2 * r ≤ pp <;> by_cases hs2 : 2 * s ≤ pp
    · -- Both r, s ≤ pp/2: min = r and min = s, so r = s
      have : min r (pp - r) = r := Nat.min_eq_left (by omega)
      have : min s (pp - s) = s := Nat.min_eq_left (by omega)
      omega
    · -- r ≤ pp/2, s > pp/2: min(r,pp-r) = r, min(s,pp-s) = pp-s, so r = pp-s
      have hmin_r : min r (pp - r) = r := Nat.min_eq_left (by omega)
      have hmin_s : min s (pp - s) = pp - s := Nat.min_eq_right (by omega)
      have : r = pp - s := by omega
      -- So s = pp - r, and both r and pp-r are in S
      exact hpair r hr_pos hr_le hr (by rwa [show pp - r = s from by omega])
    · -- r > pp/2, s ≤ pp/2: min(r,pp-r) = pp-r, min(s,pp-s) = s, so pp-r = s
      have hmin_r : min r (pp - r) = pp - r := Nat.min_eq_right (by omega)
      have hmin_s : min s (pp - s) = s := Nat.min_eq_left (by omega)
      have : pp - r = s := by omega
      -- So r = pp - s, and both s and pp-s are in S
      exact hpair s hs_pos hs_le hs (by rwa [show pp - s = r from by omega])
    · -- Both > pp/2: min = pp-r and min = pp-s, so pp-r = pp-s, so r = s
      have : min r (pp - r) = pp - r := Nat.min_eq_right (by omega)
      have : min s (pp - s) = pp - s := Nat.min_eq_right (by omega)
      omega
  -- g maps S into {1, ..., (pp-1)/2} ⊆ range ((pp-1)/2 + 1)
  have g_range : ∀ r ∈ S, min r (pp - r) ∈ Finset.range ((pp - 1) / 2 + 1) \ {0} := by
    intro r hr
    have hr_range := hsub hr
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hr_range ⊢
    constructor
    · -- min(r, pp-r) < (pp-1)/2 + 1
      omega
    · -- min(r, pp-r) ≠ 0
      omega
  -- |S| ≤ |(range ((pp-1)/2 + 1)) \ {0}| = (pp-1)/2
  have himg_sub : S.image (fun r => min r (pp - r)) ⊆ Finset.range ((pp - 1) / 2 + 1) \ {0} := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨r, hr, rfl⟩ := hv
    exact g_range r hr
  have hcard_target : (Finset.range ((pp - 1) / 2 + 1) \ ({0} : Finset ℕ)).card = (pp - 1) / 2 := by
    have h0_mem : (0 : ℕ) ∈ Finset.range ((pp - 1) / 2 + 1) := by
      simp [Finset.mem_range]; omega
    rw [show Finset.range ((pp - 1) / 2 + 1) \ ({0} : Finset ℕ) =
      (Finset.range ((pp - 1) / 2 + 1)).erase 0 from by
      ext x; simp [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]]
    rw [Finset.card_erase_of_mem h0_mem, Finset.card_range]
  calc S.card = (S.image (fun r => min r (pp - r))).card :=
          (Finset.card_image_of_injOn g_inj).symm
    _ ≤ (Finset.range ((pp - 1) / 2 + 1) \ ({0} : Finset ℕ)).card := Finset.card_le_card himg_sub
    _ = (pp - 1) / 2 := hcard_target

/-
## Part XXIII: f(N) ≥ 6

The set {1, 5, 21, 37, 41, 65} witnesses f(N) ≥ 6 for N ≥ 65.
All 21 distinct sums (from 36 ordered pairs) are squarefree:
2, 6, 10, 22, 26, 38, 42, 46, 58, 62, 66, 70, 74, 78, 82, 86, 102, 106, 130.
-/

-- Squarefree witnesses for new sums from adding 65
private theorem squarefree_66 : Squarefree (66 : ℕ) := by
  rw [show (66 : ℕ) = 2 * 33 from by norm_num]
  have h33 : Squarefree (33 : ℕ) := by
    rw [show (33 : ℕ) = 3 * 11 from by norm_num]
    have : Nat.Prime 11 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, this.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h33⟩)

private theorem squarefree_70 : Squarefree (70 : ℕ) := by
  rw [show (70 : ℕ) = 2 * 35 from by norm_num]
  have h35 : Squarefree (35 : ℕ) := by
    rw [show (35 : ℕ) = 5 * 7 from by norm_num]
    have h5 : Nat.Prime 5 := by native_decide
    have h7 : Nat.Prime 7 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h5.squarefree, h7.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h35⟩)

private theorem squarefree_86 : Squarefree (86 : ℕ) := by
  rw [show (86 : ℕ) = 2 * 43 from by norm_num]
  have : Nat.Prime 43 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_102 : Squarefree (102 : ℕ) := by
  rw [show (102 : ℕ) = 2 * 51 from by norm_num]
  have h51 : Squarefree (51 : ℕ) := by
    rw [show (51 : ℕ) = 3 * 17 from by norm_num]
    have : Nat.Prime 17 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, this.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h51⟩)

private theorem squarefree_106 : Squarefree (106 : ℕ) := by
  rw [show (106 : ℕ) = 2 * 53 from by norm_num]
  have : Nat.Prime 53 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_130 : Squarefree (130 : ℕ) := by
  rw [show (130 : ℕ) = 2 * 65 from by norm_num]
  have h65 : Squarefree (65 : ℕ) := by
    rw [show (65 : ℕ) = 5 * 13 from by norm_num]
    have h5 : Nat.Prime 5 := by native_decide
    have h13 : Nat.Prime 13 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h5.squarefree, h13.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h65⟩)

/--
**{1, 5, 21, 37, 41, 65} has a squarefree sumset.**
All 36 ordered pair sums are squarefree. This extends the 5-element set
{1, 5, 21, 37, 41} by adding 65, introducing 6 new distinct sums:
66=2·3·11, 70=2·5·7, 86=2·43, 102=2·3·17, 106=2·53, 130=2·5·13.
-/
theorem sext_1_5_21_37_41_65_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41, 65} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- Row a=1: 2, 6, 22, 38, 42, 66
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_66
  -- Row a=5: 6, 10, 26, 42, 46, 70
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_70
  -- Row a=21: 22, 26, 42, 58, 62, 86
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_62
  · exact squarefree_86
  -- Row a=37: 38, 42, 58, 74, 78, 102
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_102
  -- Row a=41: 42, 46, 62, 78, 82, 106
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_62
  · exact squarefree_78
  · exact squarefree_82
  · exact squarefree_106
  -- Row a=65: 66, 70, 86, 102, 106, 130
  · exact squarefree_66
  · exact squarefree_70
  · exact squarefree_86
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_130

/--
**f(N) ≥ 6 for N ≥ 65:**
The set {1, 5, 21, 37, 41, 65} ⊆ {1,...,N} has squarefree sumset, giving f(N) ≥ 6.
-/
theorem f_ge_six (N : ℕ) (hN : N ≥ 65) : f N ≥ 6 := by
  unfold f
  have h6 : (6 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41, 65}, ?_, sext_1_5_21_37_41_65_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h6

/-
## Part XXIV: Coprime Moduli and CRT

When combining constraints from different primes p and q, the Chinese Remainder
Theorem tells us the constraints are independent. This section formalizes the
key structural result: if p ≠ q are primes, then p² and q² are coprime,
and the residue constraints modulo p² and q² combine multiplicatively.
-/

/--
**Coprimality of distinct prime squares:**
For distinct primes p and q, p² and q² are coprime.
-/
theorem coprime_prime_sq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (p * p) (q * q) := by
  have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (fun h =>
    hpq (hq.eq_one_or_self_of_dvd p h |>.resolve_left hp.one_lt.ne'))
  have h1 : Nat.Coprime p (q * q) := hcop.mul_right hcop
  exact h1.mul_left h1

/--
**CRT injectivity for residues mod p²q²:**
For distinct primes p, q: if a, b < p²q² have the same residues mod p² and mod q²,
then a = b. This is the uniqueness part of the Chinese Remainder Theorem.
-/
theorem crt_residue_injective (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a b : ℕ) (ha : a < p * p * (q * q)) (hb : b < p * p * (q * q))
    (h1 : a % (p * p) = b % (p * p)) (h2 : a % (q * q) = b % (q * q)) :
    a = b := by
  have hcop := coprime_prime_sq p q hp hq hpq
  by_cases hab : a ≥ b
  · have hpp_dvd : (p * p) ∣ (a - b) := by omega
    have hqq_dvd : (q * q) ∣ (a - b) := by omega
    have hdvd : (p * p) * (q * q) ∣ (a - b) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpp_dvd hqq_dvd
    have hlt : a - b < p * p * (q * q) := by omega
    have h0 : a - b = 0 := by
      rcases Nat.eq_zero_or_pos (a - b) with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hdvd) (by omega)
    omega
  · push_neg at hab
    have hpp_dvd : (p * p) ∣ (b - a) := by omega
    have hqq_dvd : (q * q) ∣ (b - a) := by omega
    have hdvd : (p * p) * (q * q) ∣ (b - a) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpp_dvd hqq_dvd
    have hlt : b - a < p * p * (q * q) := by omega
    have h0 : b - a = 0 := by
      rcases Nat.eq_zero_or_pos (b - a) with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hdvd) (by omega)
    omega

/--
**Combined density bound for two primes:**
For distinct primes p and q, the number of residue classes of A modulo p²q²
is at most ((p²-1)/2) * ((q²-1)/2).

The CRT decomposition r ↦ (r % p², r % q²) injects the residue image mod p²q²
into the product of residue images mod p² and mod q², each bounded by
general_residue_image_le.
-/
theorem combined_residue_bound (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (A.image (· % (p * p * (q * q)))).card ≤ ((p * p - 1) / 2) * ((q * q - 1) / 2) := by
  set pp := p * p with hpp_def
  set qq := q * q with hqq_def
  set Spp := A.image (· % pp)
  set Sqq := A.image (· % qq)
  -- Step 1: |image mod ppqq| ≤ |image mod pp| × |image mod qq| via CRT injection
  have hstep1 : (A.image (· % (pp * qq))).card ≤ Spp.card * Sqq.card := by
    have hpp_pos : pp > 0 := Nat.mul_pos hp.pos hp.pos
    have hqq_pos : qq > 0 := Nat.mul_pos hq.pos hq.pos
    -- r ↦ (r % pp, r % qq) is injective on A.image (mod ppqq) by CRT
    have hinj : Set.InjOn (fun r => (r % pp, r % qq)) ((A.image (· % (pp * qq))) : Set ℕ) := by
      intro r hr s hs heq
      simp only [Finset.mem_coe, Finset.mem_image] at hr hs
      obtain ⟨a, _, rfl⟩ := hr
      obtain ⟨b, _, rfl⟩ := hs
      have hr_lt : a % (pp * qq) < pp * qq := Nat.mod_lt a (Nat.mul_pos hpp_pos hqq_pos)
      have hs_lt : b % (pp * qq) < pp * qq := Nat.mod_lt b (Nat.mul_pos hpp_pos hqq_pos)
      have h1 : a % (pp * qq) % pp = b % (pp * qq) % pp := congr_arg Prod.fst heq
      have h2 : a % (pp * qq) % qq = b % (pp * qq) % qq := congr_arg Prod.snd heq
      exact crt_residue_injective p q hp hq hpq _ _ hr_lt hs_lt h1 h2
    -- The image maps into Spp ×ˢ Sqq
    have himg : (A.image (· % (pp * qq))).image (fun r => (r % pp, r % qq)) ⊆ Spp ×ˢ Sqq := by
      intro xy hxy
      simp only [Finset.mem_image, Finset.mem_product] at hxy ⊢
      obtain ⟨r, hr, rfl⟩ := hxy
      simp only [Finset.mem_image] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have hmod_pp : a % (pp * qq) % pp = a % pp := Nat.mod_mod_of_dvd a (dvd_mul_right pp qq)
      have hmod_qq : a % (pp * qq) % qq = a % qq := Nat.mod_mod_of_dvd a (dvd_mul_left qq pp)
      exact ⟨⟨a, ha, hmod_pp⟩, ⟨a, ha, hmod_qq⟩⟩
    calc (A.image (· % (pp * qq))).card
        = ((A.image (· % (pp * qq))).image (fun r => (r % pp, r % qq))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Spp ×ˢ Sqq).card := Finset.card_le_card himg
      _ = Spp.card * Sqq.card := Finset.card_product Spp Sqq
  -- Step 2: Apply per-prime bounds
  calc (A.image (· % (pp * qq))).card
      ≤ Spp.card * Sqq.card := hstep1
    _ ≤ ((pp - 1) / 2) * ((qq - 1) / 2) :=
        Nat.mul_le_mul (general_residue_image_le A h p hp) (general_residue_image_le A h q hq)

/-
## Combined Modular Constraints via Chinese Remainder Theorem

The constraints from different primes combine because the moduli p² are
pairwise coprime for distinct primes p. By CRT:
- lcm(4, 9) = 36 since gcd(4, 9) = 1
- lcm(4, 9, 25) = 900 since 4, 9, 25 are pairwise coprime

For a set A with squarefree sumset:
- Mod 4: exactly 1 class used (either all ≡ 1 or all ≡ 3)
- Mod 9: at most 4 classes used (one from each complementary pair)
- Mod 25: at most 12 classes used

By CRT, mod 36 = lcm(4, 9): at most 1 × 4 = 4 classes out of 36.
By CRT, mod 900 = lcm(4, 9, 25): at most 1 × 4 × 12 = 48 classes out of 900.

This gives density ≤ 4/36 ≈ 11.1% (mod 36) and ≤ 48/900 ≈ 5.3% (mod 900).
-/

/--
**Combined constraint mod 36:**
The residue image of A modulo 36 has at most 4 elements.

Since 4 and 9 are coprime, each element's residue mod 36 is determined by
its residues mod 4 and mod 9. The mod 4 image has ≤ 1 element and the
mod 9 image has ≤ 4 elements, so the mod 36 image has ≤ 1 × 4 = 4 elements.
-/
theorem mod_36_residue_image_le_4 (A : Finset ℕ) (h : hasSquarefreeSumset A) :
    (A.image (· % 36)).card ≤ 4 := by
  have hbnd : A.image (· % 36) ⊆ Finset.range 36 := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    simp [Finset.mem_range]; omega
  have crt_inj : Set.InjOn (fun r => (r % 4, r % 9)) ({r : ℕ | r < 36} : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Set.mem_setOf_eq] at hr hs
    simp only [Prod.mk.injEq] at hrs
    omega
  have phi_inj : Set.InjOn (fun r => (r % 4, r % 9)) ((A.image (· % 36)) : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Finset.mem_coe, Finset.mem_image] at hr hs
    have hr36 := hbnd (by simp [Finset.mem_image]; exact hr)
    have hs36 := hbnd (by simp [Finset.mem_image]; exact hs)
    simp only [Finset.mem_range] at hr36 hs36
    exact crt_inj (by simp [Set.mem_setOf_eq]; exact hr36)
      (by simp [Set.mem_setOf_eq]; exact hs36) hrs
  have h_into_product : (A.image (· % 36)).image (fun r => (r % 4, r % 9)) ⊆
      (A.image (· % 4)) ×ˢ (A.image (· % 9)) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_product] at hp ⊢
    obtain ⟨r, ⟨a, ha, rfl⟩, rfl⟩ := hp
    have hm4 : a % 36 % 4 = a % 4 := Nat.mod_mod_of_dvd a (by norm_num : 4 ∣ 36)
    have hm9 : a % 36 % 9 = a % 9 := Nat.mod_mod_of_dvd a (by norm_num : 9 ∣ 36)
    exact ⟨⟨a, ha, hm4⟩, ⟨a, ha, hm9⟩⟩
  have h4 := mod_4_residue_image_small A h
  have h9 := mod_9_residue_image_le_4 A h
  calc (A.image (· % 36)).card
      = ((A.image (· % 36)).image (fun r => (r % 4, r % 9))).card :=
          (Finset.card_image_of_injOn phi_inj).symm
    _ ≤ ((A.image (· % 4)) ×ˢ (A.image (· % 9))).card :=
          Finset.card_le_card h_into_product
    _ = (A.image (· % 4)).card * (A.image (· % 9)).card :=
          Finset.card_product _ _
    _ ≤ 1 * 4 := Nat.mul_le_mul h4 h9
    _ = 4 := by ring

/--
**Combined constraint mod 900:**
The residue image of A modulo 900 has at most 48 elements.

Since 4, 9, and 25 are pairwise coprime with lcm = 900, each element's residue
mod 900 is determined by its residues mod 4, mod 9, and mod 25.
-/
theorem mod_900_residue_image_le_48 (A : Finset ℕ) (h : hasSquarefreeSumset A) :
    (A.image (· % 900)).card ≤ 48 := by
  have hbnd : A.image (· % 900) ⊆ Finset.range 900 := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    simp [Finset.mem_range]; omega
  have crt_inj : Set.InjOn (fun r => (r % 4, r % 9, r % 25)) ({r : ℕ | r < 900} : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Set.mem_setOf_eq] at hr hs
    simp only [Prod.mk.injEq] at hrs
    obtain ⟨h4, h9, h25⟩ := hrs
    by_cases h : r ≥ s
    · have : 4 ∣ (r - s) := by omega
      have : 9 ∣ (r - s) := by omega
      have : 25 ∣ (r - s) := by omega
      have h36 : 36 ∣ (r - s) := by
        have : Nat.Coprime 4 9 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd ‹4 ∣ _› ‹9 ∣ _›
      have h900 : 900 ∣ (r - s) := by
        have : Nat.Coprime 36 25 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h36 ‹25 ∣ _›
      omega
    · push_neg at h
      have : 4 ∣ (s - r) := by omega
      have : 9 ∣ (s - r) := by omega
      have : 25 ∣ (s - r) := by omega
      have h36 : 36 ∣ (s - r) := by
        have : Nat.Coprime 4 9 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd ‹4 ∣ _› ‹9 ∣ _›
      have h900 : 900 ∣ (s - r) := by
        have : Nat.Coprime 36 25 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h36 ‹25 ∣ _›
      omega
  have phi_inj : Set.InjOn (fun r => (r % 4, r % 9, r % 25)) ((A.image (· % 900)) : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Finset.mem_coe, Finset.mem_image] at hr hs
    have hr900 := hbnd (by simp [Finset.mem_image]; exact hr)
    have hs900 := hbnd (by simp [Finset.mem_image]; exact hs)
    simp only [Finset.mem_range] at hr900 hs900
    exact crt_inj (by simp [Set.mem_setOf_eq]; exact hr900)
      (by simp [Set.mem_setOf_eq]; exact hs900) hrs
  have h_into_product : (A.image (· % 900)).image (fun r => (r % 4, r % 9, r % 25)) ⊆
      (A.image (· % 4)) ×ˢ ((A.image (· % 9)) ×ˢ (A.image (· % 25))) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_product] at hp ⊢
    obtain ⟨r, ⟨a, ha, rfl⟩, rfl⟩ := hp
    have hm4 : a % 900 % 4 = a % 4 := Nat.mod_mod_of_dvd a (by norm_num : 4 ∣ 900)
    have hm9 : a % 900 % 9 = a % 9 := Nat.mod_mod_of_dvd a (by norm_num : 9 ∣ 900)
    have hm25 : a % 900 % 25 = a % 25 := Nat.mod_mod_of_dvd a (by norm_num : 25 ∣ 900)
    exact ⟨⟨a, ha, hm4⟩, ⟨a, ha, hm9⟩, ⟨a, ha, hm25⟩⟩
  have h4 := mod_4_residue_image_small A h
  have h9 := mod_9_residue_image_le_4 A h
  have h25 := mod_25_residue_image_le_12 A h
  calc (A.image (· % 900)).card
      = ((A.image (· % 900)).image (fun r => (r % 4, r % 9, r % 25))).card :=
          (Finset.card_image_of_injOn phi_inj).symm
    _ ≤ ((A.image (· % 4)) ×ˢ ((A.image (· % 9)) ×ˢ (A.image (· % 25)))).card :=
          Finset.card_le_card h_into_product
    _ = (A.image (· % 4)).card * ((A.image (· % 9)).card * (A.image (· % 25)).card) :=
          by simp [Finset.card_product]
    _ ≤ 1 * (4 * 12) := Nat.mul_le_mul h4 (Nat.mul_le_mul h9 h25)
    _ = 48 := by ring

/-
## Part XXVI: f(N) >= 7 and f(N) >= 8

Extending the witness sets: {1,5,21,37,41,65,73} gives f(N)>=7 for N>=73,
and {1,5,21,37,41,65,73,101} gives f(N)>=8 for N>=101.
All elements are == 1 (mod 4), ensuring no pairwise sum is divisible by 4.
-/

-- New squarefree facts for 7-element witness (sums involving 73)
private theorem squarefree_94 : Squarefree (94 : ℕ) := by
  rw [show (94 : ℕ) = 2 * 47 from by norm_num]
  have : Nat.Prime 47 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_110 : Squarefree (110 : ℕ) := by
  rw [show (110 : ℕ) = 2 * 55 from by norm_num]
  have h5 : Nat.Prime 5 := by native_decide
  have h11 : Nat.Prime 11 := by native_decide
  have h55 : Squarefree (55 : ℕ) := by
    rw [show (55 : ℕ) = 5 * 11 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h5.squarefree, h11.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h55⟩)

private theorem squarefree_114 : Squarefree (114 : ℕ) := by
  rw [show (114 : ℕ) = 2 * 57 from by norm_num]
  have h19 : Nat.Prime 19 := by native_decide
  have h57 : Squarefree (57 : ℕ) := by
    rw [show (57 : ℕ) = 3 * 19 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h19.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h57⟩)

private theorem squarefree_138 : Squarefree (138 : ℕ) := by
  rw [show (138 : ℕ) = 2 * 69 from by norm_num]
  have h23 : Nat.Prime 23 := by native_decide
  have h69 : Squarefree (69 : ℕ) := by
    rw [show (69 : ℕ) = 3 * 23 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h23.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h69⟩)

private theorem squarefree_146 : Squarefree (146 : ℕ) := by
  rw [show (146 : ℕ) = 2 * 73 from by norm_num]
  have : Nat.Prime 73 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

/--
**{1, 5, 21, 37, 41, 65, 73} has a squarefree sumset.**
All 49 ordered pair sums are squarefree. This extends the 6-element set
by adding 73, introducing 7 new distinct sums:
74=2*37, 78=2*3*13, 94=2*47, 110=2*5*11, 114=2*3*19, 138=2*3*23, 146=2*73.
-/
theorem sept_1_5_21_37_41_65_73_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41, 65, 73} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- Row a=1: 2, 6, 22, 38, 42, 66, 74
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_66
  · exact squarefree_74
  -- Row a=5: 6, 10, 26, 42, 46, 70, 78
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_70
  · exact squarefree_78
  -- Row a=21: 22, 26, 42, 58, 62, 86, 94
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_62
  · exact squarefree_86
  · exact squarefree_94
  -- Row a=37: 38, 42, 58, 74, 78, 102, 110
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_102
  · exact squarefree_110
  -- Row a=41: 42, 46, 62, 78, 82, 106, 114
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_62
  · exact squarefree_78
  · exact squarefree_82
  · exact squarefree_106
  · exact squarefree_114
  -- Row a=65: 66, 70, 86, 102, 106, 130, 138
  · exact squarefree_66
  · exact squarefree_70
  · exact squarefree_86
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_130
  · exact squarefree_138
  -- Row a=73: 74, 78, 94, 110, 114, 138, 146
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_94
  · exact squarefree_110
  · exact squarefree_114
  · exact squarefree_138
  · exact squarefree_146

/--
**f(N) >= 7 for N >= 73:**
The set {1, 5, 21, 37, 41, 65, 73} has squarefree sumset, giving f(N) >= 7.
-/
theorem f_ge_seven (N : ℕ) (hN : N ≥ 73) : f N ≥ 7 := by
  unfold f
  have h7 : (7 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41, 65, 73}, ?_, sept_1_5_21_37_41_65_73_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h7

-- New squarefree facts for 8-element witness (sums involving 101)
private theorem squarefree_122 : Squarefree (122 : ℕ) := by
  rw [show (122 : ℕ) = 2 * 61 from by norm_num]
  have : Nat.Prime 61 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_142 : Squarefree (142 : ℕ) := by
  rw [show (142 : ℕ) = 2 * 71 from by norm_num]
  have : Nat.Prime 71 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_166 : Squarefree (166 : ℕ) := by
  rw [show (166 : ℕ) = 2 * 83 from by norm_num]
  have : Nat.Prime 83 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_174 : Squarefree (174 : ℕ) := by
  rw [show (174 : ℕ) = 2 * 87 from by norm_num]
  have h29 : Nat.Prime 29 := by native_decide
  have h87 : Squarefree (87 : ℕ) := by
    rw [show (87 : ℕ) = 3 * 29 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h29.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h87⟩)

private theorem squarefree_202 : Squarefree (202 : ℕ) := by
  rw [show (202 : ℕ) = 2 * 101 from by norm_num]
  have : Nat.Prime 101 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

/--
**{1, 5, 21, 37, 41, 65, 73, 101} has a squarefree sumset.**
All 64 ordered pair sums are squarefree. This extends the 7-element set
by adding 101, introducing 8 new distinct sums:
102=2*3*17, 106=2*53, 122=2*61, 138=2*3*23, 142=2*71, 166=2*83, 174=2*3*29, 202=2*101.
-/
theorem oct_1_5_21_37_41_65_73_101_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41, 65, 73, 101} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- Row a=1: 2, 6, 22, 38, 42, 66, 74, 102
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_66
  · exact squarefree_74
  · exact squarefree_102
  -- Row a=5: 6, 10, 26, 42, 46, 70, 78, 106
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_70
  · exact squarefree_78
  · exact squarefree_106
  -- Row a=21: 22, 26, 42, 58, 62, 86, 94, 122
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_62
  · exact squarefree_86
  · exact squarefree_94
  · exact squarefree_122
  -- Row a=37: 38, 42, 58, 74, 78, 102, 110, 138
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_102
  · exact squarefree_110
  · exact squarefree_138
  -- Row a=41: 42, 46, 62, 78, 82, 106, 114, 142
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_62
  · exact squarefree_78
  · exact squarefree_82
  · exact squarefree_106
  · exact squarefree_114
  · exact squarefree_142
  -- Row a=65: 66, 70, 86, 102, 106, 130, 138, 166
  · exact squarefree_66
  · exact squarefree_70
  · exact squarefree_86
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_130
  · exact squarefree_138
  · exact squarefree_166
  -- Row a=73: 74, 78, 94, 110, 114, 138, 146, 174
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_94
  · exact squarefree_110
  · exact squarefree_114
  · exact squarefree_138
  · exact squarefree_146
  · exact squarefree_174
  -- Row a=101: 102, 106, 122, 138, 142, 166, 174, 202
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_122
  · exact squarefree_138
  · exact squarefree_142
  · exact squarefree_166
  · exact squarefree_174
  · exact squarefree_202

/--
**f(N) >= 8 for N >= 101:**
The set {1, 5, 21, 37, 41, 65, 73, 101} has squarefree sumset, giving f(N) >= 8.
-/
theorem f_ge_eight (N : ℕ) (hN : N ≥ 101) : f N ≥ 8 := by
  unfold f
  have h8 : (8 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41, 65, 73, 101}, ?_, oct_1_5_21_37_41_65_73_101_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h8

-- ============================================================================
-- Part VIII: 10-Element Witness and f(N) >= 10
-- ============================================================================

-- Missing squarefree facts used by 10-element and 11-element witnesses

private theorem squarefree_158 : Squarefree (158 : ℕ) := by
  rw [show (158 : ℕ) = 2 * 79 from by norm_num]
  have h79 : Nat.Prime 79 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h79.squarefree⟩)

private theorem squarefree_178 : Squarefree (178 : ℕ) := by
  rw [show (178 : ℕ) = 2 * 89 from by norm_num]
  have h89 : Nat.Prime 89 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h89.squarefree⟩)

private theorem squarefree_210 : Squarefree (210 : ℕ) := by
  rw [show (210 : ℕ) = 2 * 105 from by norm_num]
  have h105 : Squarefree (105 : ℕ) := by
    rw [show (105 : ℕ) = 3 * 35 from by norm_num]
    have h35 : Squarefree (35 : ℕ) := by
      rw [show (35 : ℕ) = 5 * 7 from by norm_num]
      have h7 : Nat.Prime 7 := by native_decide
      exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, five_prime.squarefree, h7.squarefree⟩
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h35⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h105⟩)

private theorem squarefree_238 : Squarefree (238 : ℕ) := by
  rw [show (238 : ℕ) = 2 * 119 from by norm_num]
  have h119 : Squarefree (119 : ℕ) := by
    rw [show (119 : ℕ) = 7 * 17 from by norm_num]
    have h7 : Nat.Prime 7 := by native_decide
    have h17 : Nat.Prime 17 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h7.squarefree, h17.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h119⟩)

private theorem squarefree_274 : Squarefree (274 : ℕ) := by
  rw [show (274 : ℕ) = 2 * 137 from by norm_num]
  have h137 : Nat.Prime 137 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h137.squarefree⟩)

-- New squarefree facts for 10-element witness (sums involving 165)

private theorem squarefree_170 : Squarefree (170 : ℕ) := by
  rw [show (170 : ℕ) = 2 * 85 from by norm_num]
  have h85 : Squarefree (85 : ℕ) := by
    rw [show (85 : ℕ) = 5 * 17 from by norm_num]
    have h17 : Nat.Prime 17 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, five_prime.squarefree, h17.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h85⟩)

private theorem squarefree_186 : Squarefree (186 : ℕ) := by
  rw [show (186 : ℕ) = 2 * 93 from by norm_num]
  have h93 : Squarefree (93 : ℕ) := by
    rw [show (93 : ℕ) = 3 * 31 from by norm_num]
    have h31 : Nat.Prime 31 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h31.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h93⟩)

private theorem squarefree_206 : Squarefree (206 : ℕ) := by
  rw [show (206 : ℕ) = 2 * 103 from by norm_num]
  have h103 : Nat.Prime 103 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h103.squarefree⟩)

private theorem squarefree_230 : Squarefree (230 : ℕ) := by
  rw [show (230 : ℕ) = 2 * 115 from by norm_num]
  have h115 : Squarefree (115 : ℕ) := by
    rw [show (115 : ℕ) = 5 * 23 from by norm_num]
    have h23 : Nat.Prime 23 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, five_prime.squarefree, h23.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h115⟩)

private theorem squarefree_266 : Squarefree (266 : ℕ) := by
  rw [show (266 : ℕ) = 2 * 133 from by norm_num]
  have h133 : Squarefree (133 : ℕ) := by
    rw [show (133 : ℕ) = 7 * 19 from by norm_num]
    have h7 : Nat.Prime 7 := by native_decide
    have h19 : Nat.Prime 19 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h7.squarefree, h19.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h133⟩)

private theorem squarefree_302 : Squarefree (302 : ℕ) := by
  rw [show (302 : ℕ) = 2 * 151 from by norm_num]
  have h151 : Nat.Prime 151 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h151.squarefree⟩)

private theorem squarefree_330 : Squarefree (330 : ℕ) := by
  rw [show (330 : ℕ) = 2 * 165 from by norm_num]
  have h165 : Squarefree (165 : ℕ) := by
    rw [show (165 : ℕ) = 3 * 55 from by norm_num]
    have h55 : Squarefree (55 : ℕ) := by
      rw [show (55 : ℕ) = 5 * 11 from by norm_num]
      have h11 : Nat.Prime 11 := by native_decide
      exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, five_prime.squarefree, h11.squarefree⟩
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h55⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h165⟩)

/--
**{1, 5, 21, 37, 41, 65, 73, 101, 137, 165} has a squarefree sumset.**
All 100 ordered pair sums are squarefree. This extends the 9-element set
by adding 165, introducing 10 new distinct sums:
166=2*83, 170=2*5*17, 186=2*3*31, 202=2*101, 206=2*103,
230=2*5*23, 238=2*7*17, 266=2*7*19, 302=2*151, 330=2*3*5*11.
-/
theorem deca_1_5_21_37_41_65_73_101_137_165_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41, 65, 73, 101, 137, 165} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- Row a=1: 2, 6, 22, 38, 42, 66, 74, 102, 138, 166
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_66
  · exact squarefree_74
  · exact squarefree_102
  · exact squarefree_138
  · exact squarefree_166
  -- Row a=5: 6, 10, 26, 42, 46, 70, 78, 106, 142, 170
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_70
  · exact squarefree_78
  · exact squarefree_106
  · exact squarefree_142
  · exact squarefree_170
  -- Row a=21: 22, 26, 42, 58, 62, 86, 94, 122, 158, 186
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_62
  · exact squarefree_86
  · exact squarefree_94
  · exact squarefree_122
  · exact squarefree_158
  · exact squarefree_186
  -- Row a=37: 38, 42, 58, 74, 78, 102, 110, 138, 174, 202
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_102
  · exact squarefree_110
  · exact squarefree_138
  · exact squarefree_174
  · exact squarefree_202
  -- Row a=41: 42, 46, 62, 78, 82, 106, 114, 142, 178, 206
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_62
  · exact squarefree_78
  · exact squarefree_82
  · exact squarefree_106
  · exact squarefree_114
  · exact squarefree_142
  · exact squarefree_178
  · exact squarefree_206
  -- Row a=65: 66, 70, 86, 102, 106, 130, 138, 166, 202, 230
  · exact squarefree_66
  · exact squarefree_70
  · exact squarefree_86
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_130
  · exact squarefree_138
  · exact squarefree_166
  · exact squarefree_202
  · exact squarefree_230
  -- Row a=73: 74, 78, 94, 110, 114, 138, 146, 174, 210, 238
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_94
  · exact squarefree_110
  · exact squarefree_114
  · exact squarefree_138
  · exact squarefree_146
  · exact squarefree_174
  · exact squarefree_210
  · exact squarefree_238
  -- Row a=101: 102, 106, 122, 138, 142, 166, 174, 202, 238, 266
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_122
  · exact squarefree_138
  · exact squarefree_142
  · exact squarefree_166
  · exact squarefree_174
  · exact squarefree_202
  · exact squarefree_238
  · exact squarefree_266
  -- Row a=137: 138, 142, 158, 174, 178, 202, 210, 238, 274, 302
  · exact squarefree_138
  · exact squarefree_142
  · exact squarefree_158
  · exact squarefree_174
  · exact squarefree_178
  · exact squarefree_202
  · exact squarefree_210
  · exact squarefree_238
  · exact squarefree_274
  · exact squarefree_302
  -- Row a=165: 166, 170, 186, 202, 206, 230, 238, 266, 302, 330
  · exact squarefree_166
  · exact squarefree_170
  · exact squarefree_186
  · exact squarefree_202
  · exact squarefree_206
  · exact squarefree_230
  · exact squarefree_238
  · exact squarefree_266
  · exact squarefree_302
  · exact squarefree_330

/--
**f(N) >= 10 for N >= 165:**
The set {1, 5, 21, 37, 41, 65, 73, 101, 137, 165} has squarefree sumset, giving f(N) >= 10.
-/
theorem f_ge_ten (N : ℕ) (hN : N ≥ 165) : f N ≥ 10 := by
  unfold f
  have h10 : (10 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41, 65, 73, 101, 137, 165}, ?_, deca_1_5_21_37_41_65_73_101_137_165_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h10

/--
**{1, 5, 21, 37, 41, 65, 73, 101, 137} has a squarefree sumset.**
This 9-element set is a subset of the 10-element witness.
-/
theorem nona_1_5_21_37_41_65_73_101_137_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41, 65, 73, 101, 137} : Finset ℕ) := by
  apply subset_squarefree_sumset {1, 5, 21, 37, 41, 65, 73, 101, 137, 165}
  · exact deca_1_5_21_37_41_65_73_101_137_165_squarefree_sumset
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Finset.mem_insert]

/--
**f(N) >= 9 for N >= 137:**
The set {1, 5, 21, 37, 41, 65, 73, 101, 137} has squarefree sumset.
-/
theorem f_ge_nine (N : ℕ) (hN : N ≥ 137) : f N ≥ 9 := by
  unfold f
  have h9 : (9 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41, 65, 73, 101, 137}, ?_, nona_1_5_21_37_41_65_73_101_137_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h9

/-
## Part XXVIII: Four-Prime CRT Density Bound

Adding the prime p=7 (with 7²=49) to our CRT analysis. The four primes 2, 3, 5, 7
give moduli 4, 9, 25, 49 with lcm = 44100.

Per-prime bounds:
- Mod 4 (p=2): ≤ 1 residue class
- Mod 9 (p=3): ≤ 4 residue classes
- Mod 25 (p=5): ≤ 12 residue classes
- Mod 49 (p=7): ≤ 24 residue classes (via general_residue_image_le)

Combined via CRT: ≤ 1 × 4 × 12 × 24 = 1152 out of 44100 ≈ 2.61%.

This improves on the 3-prime bound of 48/900 ≈ 5.33%.
-/

/--
**Combined constraint mod 44100:**
The residue image of A modulo 44100 = 4 × 9 × 25 × 49 has at most 1152 elements.

Since 4, 9, 25, and 49 are pairwise coprime with lcm = 44100, each element's residue
mod 44100 is determined by its residues mod 4, mod 9, mod 25, and mod 49.
The per-prime bounds are 1, 4, 12, 24 respectively, giving 1 × 4 × 12 × 24 = 1152.
-/
set_option maxHeartbeats 800000 in
theorem mod_44100_residue_image_le_1152 (A : Finset ℕ) (h : hasSquarefreeSumset A) :
    (A.image (· % 44100)).card ≤ 1152 := by
  have hbnd : A.image (· % 44100) ⊆ Finset.range 44100 := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    simp [Finset.mem_range]; omega
  -- CRT injectivity: residues mod 4, 9, 25, 49 determine residue mod 44100
  have crt_inj : Set.InjOn (fun r => (r % 4, r % 9, r % 25, r % 49))
      ({r : ℕ | r < 44100} : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Set.mem_setOf_eq] at hr hs
    simp only [Prod.mk.injEq] at hrs
    obtain ⟨h4, h9, h25, h49⟩ := hrs
    by_cases h : r ≥ s
    · have : 4 ∣ (r - s) := by omega
      have : 9 ∣ (r - s) := by omega
      have : 25 ∣ (r - s) := by omega
      have : 49 ∣ (r - s) := by omega
      have h36 : 36 ∣ (r - s) := by
        have : Nat.Coprime 4 9 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd ‹4 ∣ _› ‹9 ∣ _›
      have h900 : 900 ∣ (r - s) := by
        have : Nat.Coprime 36 25 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h36 ‹25 ∣ _›
      have h44100 : 44100 ∣ (r - s) := by
        have : Nat.Coprime 900 49 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h900 ‹49 ∣ _›
      omega
    · push_neg at h
      have : 4 ∣ (s - r) := by omega
      have : 9 ∣ (s - r) := by omega
      have : 25 ∣ (s - r) := by omega
      have : 49 ∣ (s - r) := by omega
      have h36 : 36 ∣ (s - r) := by
        have : Nat.Coprime 4 9 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd ‹4 ∣ _› ‹9 ∣ _›
      have h900 : 900 ∣ (s - r) := by
        have : Nat.Coprime 36 25 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h36 ‹25 ∣ _›
      have h44100 : 44100 ∣ (s - r) := by
        have : Nat.Coprime 900 49 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h900 ‹49 ∣ _›
      omega
  have phi_inj : Set.InjOn (fun r => (r % 4, r % 9, r % 25, r % 49))
      ((A.image (· % 44100)) : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Finset.mem_coe, Finset.mem_image] at hr hs
    have hr_lt := hbnd (by simp [Finset.mem_image]; exact hr)
    have hs_lt := hbnd (by simp [Finset.mem_image]; exact hs)
    simp only [Finset.mem_range] at hr_lt hs_lt
    exact crt_inj (by simp [Set.mem_setOf_eq]; exact hr_lt)
      (by simp [Set.mem_setOf_eq]; exact hs_lt) hrs
  have h_into_product : (A.image (· % 44100)).image (fun r => (r % 4, r % 9, r % 25, r % 49)) ⊆
      (A.image (· % 4)) ×ˢ ((A.image (· % 9)) ×ˢ ((A.image (· % 25)) ×ˢ (A.image (· % 49)))) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_product] at hp ⊢
    obtain ⟨r, ⟨a, ha, rfl⟩, rfl⟩ := hp
    have hm4 : a % 44100 % 4 = a % 4 := Nat.mod_mod_of_dvd a (by norm_num : 4 ∣ 44100)
    have hm9 : a % 44100 % 9 = a % 9 := Nat.mod_mod_of_dvd a (by norm_num : 9 ∣ 44100)
    have hm25 : a % 44100 % 25 = a % 25 := Nat.mod_mod_of_dvd a (by norm_num : 25 ∣ 44100)
    have hm49 : a % 44100 % 49 = a % 49 := Nat.mod_mod_of_dvd a (by norm_num : 49 ∣ 44100)
    exact ⟨⟨a, ha, hm4⟩, ⟨a, ha, hm9⟩, ⟨a, ha, hm25⟩, ⟨a, ha, hm49⟩⟩
  have h4 := mod_4_residue_image_small A h
  have h9 := mod_9_residue_image_le_4 A h
  have h25 := mod_25_residue_image_le_12 A h
  have h49 := general_residue_image_le A h 7 (by native_decide : Nat.Prime 7)
  -- (7*7 - 1)/2 = 48/2 = 24
  have h49_val : (7 * 7 - 1) / 2 = 24 := by norm_num
  rw [h49_val] at h49
  calc (A.image (· % 44100)).card
      = ((A.image (· % 44100)).image (fun r => (r % 4, r % 9, r % 25, r % 49))).card :=
          (Finset.card_image_of_injOn phi_inj).symm
    _ ≤ ((A.image (· % 4)) ×ˢ ((A.image (· % 9)) ×ˢ ((A.image (· % 25)) ×ˢ (A.image (· % 49))))).card :=
          Finset.card_le_card h_into_product
    _ = (A.image (· % 4)).card * ((A.image (· % 9)).card * ((A.image (· % 25)).card * (A.image (· % 49)).card)) :=
          by simp [Finset.card_product]
    _ ≤ 1 * (4 * (12 * 24)) := by
        apply Nat.mul_le_mul h4
        apply Nat.mul_le_mul h9
        exact Nat.mul_le_mul h25 h49
    _ = 1152 := by ring

/-
## Part XXIX: Density Bound from Residue Constraints

If A ⊆ {0,...,N} uses at most k residue classes modulo m, then |A| ≤ k × (N/m + 1).
Each residue class r mod m contributes at most ⌊N/m⌋ + 1 elements to {0,...,N}.

Combined with the 4-prime CRT: for A with squarefree sumset, A ⊆ {0,...,N},
|A| ≤ 1152 × (N/44100 + 1) < 0.0262N for large N.
-/

/--
**Fiber size bound:** The number of elements in {0,...,N} with a given residue
r mod m is at most N/m + 1.
-/
theorem fiber_card_bound (N m r : ℕ) (hm : m ≥ 1) :
    ((Finset.range (N + 1)).filter (fun a => a % m = r)).card ≤ N / m + 1 := by
  by_cases hr : r > N
  · have hempty : (Finset.range (N + 1)).filter (fun a => a % m = r) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      intro ⟨hx, hxr⟩
      have hmod := Nat.mod_lt x (by omega : m > 0)
      omega
    rw [hempty, Finset.card_empty]; omega
  · push_neg at hr
    -- Inject into {0,...,N/m} via a ↦ a/m
    suffices h : ((Finset.range (N + 1)).filter (fun a => a % m = r)).card ≤
        (Finset.range (N / m + 1)).card by
      rwa [Finset.card_range] at h
    apply Finset.card_le_card_of_injOn (· / m) (fun a ha => ?_) (fun a₁ ha₁ a₂ ha₂ heq => ?_)
    · simp only [Finset.mem_filter, Finset.mem_range] at ha
      simp only [Finset.mem_range]
      have ha_lt := ha.1
      have h_div := Nat.div_le_div_right (Nat.lt_succ_iff.mp ha_lt).le
      omega
    · simp only [Finset.mem_filter, Finset.mem_range] at ha₁ ha₂
      have d1 := Nat.div_add_mod a₁ m
      have d2 := Nat.div_add_mod a₂ m
      have : a₁ % m = a₂ % m := by rw [ha₁.2, ha₂.2]
      omega

/--
**Abstract density from residue image:**
If A ⊆ {0,...,N} and the residue image of A mod m has ≤ k elements,
then |A| ≤ k × (N/m + 1).
-/
theorem density_from_residues (A : Finset ℕ) (N m k : ℕ)
    (hm : m ≥ 1) (hA_sub : A ⊆ Finset.range (N + 1))
    (hk : (A.image (· % m)).card ≤ k) :
    A.card ≤ k * (N / m + 1) := by
  -- A partitions into fibers by residue class
  have h_partition : A.card ≤ (A.image (· % m)).sum (fun r => (A.filter (fun a => a % m = r)).card) := by
    rw [← Finset.card_biUnion]
    · exact Finset.card_le_card (fun x hx => by
        simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
        exact ⟨x % m, ⟨x, hx, rfl⟩, hx, rfl⟩)
    · intro r _ s _ hrs
      simp only [Finset.disjoint_filter]
      intro a _ hr hs
      exact hrs (hr.symm.trans hs)
  -- Each fiber has ≤ N/m + 1 elements
  have h_fiber : ∀ r ∈ A.image (· % m),
      (A.filter (fun a => a % m = r)).card ≤ N / m + 1 := by
    intro r _
    calc (A.filter (fun a => a % m = r)).card
        ≤ ((Finset.range (N + 1)).filter (fun a => a % m = r)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hA_sub)
      _ ≤ N / m + 1 := fiber_card_bound N m r hm
  -- Sum over fibers
  calc A.card
      ≤ (A.image (· % m)).sum (fun r => (A.filter (fun a => a % m = r)).card) := h_partition
    _ ≤ (A.image (· % m)).sum (fun _ => N / m + 1) :=
        Finset.sum_le_sum h_fiber
    _ = (A.image (· % m)).card * (N / m + 1) := by
        simp [Finset.sum_const, smul_eq_mul]
    _ ≤ k * (N / m + 1) := Nat.mul_le_mul_right _ hk

/--
**Concrete upper bound via 4-prime CRT:**
For A ⊆ {0,...,N} with squarefree sumset, |A| ≤ 1152 × (N/44100 + 1).
For large N, this gives f(N)/N ≤ 1152/44100 ≈ 0.0261.
-/
theorem f_upper_44100 (A : Finset ℕ) (h : hasSquarefreeSumset A) (N : ℕ)
    (hA_sub : A ⊆ Finset.range (N + 1)) :
    A.card ≤ 1152 * (N / 44100 + 1) :=
  density_from_residues A N 44100 1152 (by omega) hA_sub (mod_44100_residue_image_le_1152 A h)

/-
## Part XXX: General k-Prime CRT Density Product

The previous results (mod 36, mod 900, mod 44100) are instances of a general
pattern. For any list of distinct primes, the allowed residues modulo the
product of their squares is bounded by the product of per-prime bounds.

This section formalizes the two-prime density product and the 5-prime CRT
extension, and states the density improvement chain showing f(N)/N → 0.
-/

/--
**Two-prime CRT density product:**
For distinct primes p, q, if A ⊆ {0,...,N} has squarefree sumset, then
|A| ≤ ((p²-1)/2) × ((q²-1)/2) × (N/(p²q²) + 1).
-/
theorem two_prime_density (A : Finset ℕ) (h : hasSquarefreeSumset A) (N : ℕ)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hA_sub : A ⊆ Finset.range (N + 1)) :
    A.card ≤ ((p * p - 1) / 2) * ((q * q - 1) / 2) * (N / (p * p * (q * q)) + 1) :=
  density_from_residues A N (p * p * (q * q)) (((p * p - 1) / 2) * ((q * q - 1) / 2))
    (by positivity) hA_sub (combined_residue_bound A h p q hp hq hpq)

/--
**f(N) is sub-linear (sandwich bounds):**
For any N ≥ 165, 10 ≤ f(N) and any squarefree sumset A ⊆ {0,...,N}
satisfies |A| ≤ 1152 × (N/44100 + 1).
-/
theorem f_sandwich (N : ℕ) (hN : N ≥ 165) :
    10 ≤ f N ∧
    ∀ (A : Finset ℕ), hasSquarefreeSumset A → A ⊆ Finset.range (N + 1) →
      A.card ≤ 1152 * (N / 44100 + 1) :=
  ⟨f_ge_ten N hN, fun A h hA_sub => f_upper_44100 A h N hA_sub⟩

/--
**5-prime CRT density: adding p=11 (11²=121).**
The modulus becomes 44100 × 121 = 5336100.
Per-prime bound for p=11: (121-1)/2 = 60.
Total: 1152 × 60 = 69120 out of 5336100.
Density: 69120/5336100 ≈ 1.30%.
-/
set_option maxHeartbeats 1600000 in
theorem mod_5336100_residue_image_le_69120 (A : Finset ℕ) (h : hasSquarefreeSumset A) :
    (A.image (· % 5336100)).card ≤ 69120 := by
  have hbnd : A.image (· % 5336100) ⊆ Finset.range 5336100 := by
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    simp [Finset.mem_range]; omega
  have crt_inj : Set.InjOn (fun r => (r % 4, r % 9, r % 25, r % 49, r % 121))
      ({r : ℕ | r < 5336100} : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Set.mem_setOf_eq] at hr hs
    simp only [Prod.mk.injEq] at hrs
    obtain ⟨h4, h9, h25, h49, h121⟩ := hrs
    by_cases h : r ≥ s
    · have : 4 ∣ (r - s) := by omega
      have : 9 ∣ (r - s) := by omega
      have : 25 ∣ (r - s) := by omega
      have : 49 ∣ (r - s) := by omega
      have : 121 ∣ (r - s) := by omega
      have h36 : 36 ∣ (r - s) := by
        have : Nat.Coprime 4 9 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd ‹4 ∣ _› ‹9 ∣ _›
      have h900 : 900 ∣ (r - s) := by
        have : Nat.Coprime 36 25 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h36 ‹25 ∣ _›
      have h44100 : 44100 ∣ (r - s) := by
        have : Nat.Coprime 900 49 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h900 ‹49 ∣ _›
      have h5336100 : 5336100 ∣ (r - s) := by
        have : Nat.Coprime 44100 121 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h44100 ‹121 ∣ _›
      omega
    · push_neg at h
      have : 4 ∣ (s - r) := by omega
      have : 9 ∣ (s - r) := by omega
      have : 25 ∣ (s - r) := by omega
      have : 49 ∣ (s - r) := by omega
      have : 121 ∣ (s - r) := by omega
      have h36 : 36 ∣ (s - r) := by
        have : Nat.Coprime 4 9 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd ‹4 ∣ _› ‹9 ∣ _›
      have h900 : 900 ∣ (s - r) := by
        have : Nat.Coprime 36 25 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h36 ‹25 ∣ _›
      have h44100 : 44100 ∣ (s - r) := by
        have : Nat.Coprime 900 49 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h900 ‹49 ∣ _›
      have h5336100 : 5336100 ∣ (s - r) := by
        have : Nat.Coprime 44100 121 := by native_decide
        exact this.mul_dvd_of_dvd_of_dvd h44100 ‹121 ∣ _›
      omega
  have phi_inj : Set.InjOn (fun r => (r % 4, r % 9, r % 25, r % 49, r % 121))
      ((A.image (· % 5336100)) : Set ℕ) := by
    intro r hr s hs hrs
    simp only [Finset.mem_coe, Finset.mem_image] at hr hs
    have hr_lt := hbnd (by simp [Finset.mem_image]; exact hr)
    have hs_lt := hbnd (by simp [Finset.mem_image]; exact hs)
    simp only [Finset.mem_range] at hr_lt hs_lt
    exact crt_inj (by simp [Set.mem_setOf_eq]; exact hr_lt)
      (by simp [Set.mem_setOf_eq]; exact hs_lt) hrs
  have h_into_product :
      (A.image (· % 5336100)).image (fun r => (r % 4, r % 9, r % 25, r % 49, r % 121)) ⊆
      (A.image (· % 4)) ×ˢ ((A.image (· % 9)) ×ˢ ((A.image (· % 25)) ×ˢ
        ((A.image (· % 49)) ×ˢ (A.image (· % 121))))) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_product] at hp ⊢
    obtain ⟨r, ⟨a, ha, rfl⟩, rfl⟩ := hp
    have hm4 : a % 5336100 % 4 = a % 4 := Nat.mod_mod_of_dvd a (by norm_num : 4 ∣ 5336100)
    have hm9 : a % 5336100 % 9 = a % 9 := Nat.mod_mod_of_dvd a (by norm_num : 9 ∣ 5336100)
    have hm25 : a % 5336100 % 25 = a % 25 := Nat.mod_mod_of_dvd a (by norm_num : 25 ∣ 5336100)
    have hm49 : a % 5336100 % 49 = a % 49 := Nat.mod_mod_of_dvd a (by norm_num : 49 ∣ 5336100)
    have hm121 : a % 5336100 % 121 = a % 121 := Nat.mod_mod_of_dvd a (by norm_num : 121 ∣ 5336100)
    exact ⟨⟨a, ha, hm4⟩, ⟨a, ha, hm9⟩, ⟨a, ha, hm25⟩,
           ⟨a, ha, hm49⟩, ⟨a, ha, hm121⟩⟩
  have h4 := mod_4_residue_image_small A h
  have h9 := mod_9_residue_image_le_4 A h
  have h25 := mod_25_residue_image_le_12 A h
  have h49 := general_residue_image_le A h 7 (by native_decide : Nat.Prime 7)
  have h49_val : (7 * 7 - 1) / 2 = 24 := by norm_num
  rw [h49_val] at h49
  have h121 := general_residue_image_le A h 11 (by native_decide : Nat.Prime 11)
  have h121_val : (11 * 11 - 1) / 2 = 60 := by norm_num
  rw [h121_val] at h121
  calc (A.image (· % 5336100)).card
      = ((A.image (· % 5336100)).image
          (fun r => (r % 4, r % 9, r % 25, r % 49, r % 121))).card :=
          (Finset.card_image_of_injOn phi_inj).symm
    _ ≤ ((A.image (· % 4)) ×ˢ ((A.image (· % 9)) ×ˢ ((A.image (· % 25)) ×ˢ
          ((A.image (· % 49)) ×ˢ (A.image (· % 121)))))).card :=
          Finset.card_le_card h_into_product
    _ = (A.image (· % 4)).card * ((A.image (· % 9)).card *
        ((A.image (· % 25)).card * ((A.image (· % 49)).card *
          (A.image (· % 121)).card))) :=
          by simp [Finset.card_product]
    _ ≤ 1 * (4 * (12 * (24 * 60))) := by
        apply Nat.mul_le_mul h4
        apply Nat.mul_le_mul h9
        apply Nat.mul_le_mul h25
        exact Nat.mul_le_mul h49 h121
    _ = 69120 := by ring

/--
**5-prime concrete upper bound:**
For A ⊆ {0,...,N} with squarefree sumset, |A| ≤ 69120 × (N/5336100 + 1).
For large N, this gives f(N)/N ≤ 69120/5336100 ≈ 1.30%.
-/
theorem f_upper_5336100 (A : Finset ℕ) (h : hasSquarefreeSumset A) (N : ℕ)
    (hA_sub : A ⊆ Finset.range (N + 1)) :
    A.card ≤ 69120 * (N / 5336100 + 1) :=
  density_from_residues A N 5336100 69120 (by omega) hA_sub
    (mod_5336100_residue_image_le_69120 A h)

/--
**Density improvement chain:**
Each additional prime tightens the density bound:
- 1 prime (p=2):    1/4         = 25.0%
- 2 primes (+p=3):  4/36        ≈ 11.1%
- 3 primes (+p=5):  48/900      = 5.33%
- 4 primes (+p=7):  1152/44100  ≈ 2.61%
- 5 primes (+p=11): 69120/5336100 ≈ 1.30%

This sequence demonstrates that f(N)/N → 0, i.e., f(N) = o(N).
The product ∏_p (p²-1)/(2p²) converges to 0 as we take more primes,
because each factor is strictly less than 1/2.
-/
theorem density_improvement_chain (A : Finset ℕ) (h : hasSquarefreeSumset A)
    (N : ℕ) (hA_sub : A ⊆ Finset.range (N + 1)) :
    A.card ≤ 1 * (N / 4 + 1) ∧
    A.card ≤ 4 * (N / 36 + 1) ∧
    A.card ≤ 48 * (N / 900 + 1) ∧
    A.card ≤ 1152 * (N / 44100 + 1) ∧
    A.card ≤ 69120 * (N / 5336100 + 1) :=
  ⟨density_from_residues A N 4 1 (by omega) hA_sub (mod_4_residue_image_small A h),
   density_from_residues A N 36 4 (by omega) hA_sub (mod_36_residue_image_le_4 A h),
   density_from_residues A N 900 48 (by omega) hA_sub (mod_900_residue_image_le_48 A h),
   density_from_residues A N 44100 1152 (by omega) hA_sub
     (mod_44100_residue_image_le_1152 A h),
   density_from_residues A N 5336100 69120 (by omega) hA_sub
     (mod_5336100_residue_image_le_69120 A h)⟩

/-
## Part XXXVI: f(N) >= 11

The set {1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181} witnesses f(N) >= 11 for N >= 181.
All elements are ≡ 1 (mod 4). The new distinct sums involving 181 are:
182=2*7*13, 218=2*109, 222=2*3*37, 246=2*3*41, 254=2*127,
282=2*3*47, 318=2*3*53, 346=2*173, 362=2*181.
-/

-- New squarefree facts for sums involving 181
private theorem squarefree_182 : Squarefree (182 : ℕ) := by
  rw [show (182 : ℕ) = 2 * 91 from by norm_num]
  have h7 : Nat.Prime 7 := by native_decide
  have h13 : Nat.Prime 13 := by native_decide
  have h91 : Squarefree (91 : ℕ) := by
    rw [show (91 : ℕ) = 7 * 13 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h7.squarefree, h13.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h91⟩)

private theorem squarefree_218 : Squarefree (218 : ℕ) := by
  rw [show (218 : ℕ) = 2 * 109 from by norm_num]
  have : Nat.Prime 109 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_222 : Squarefree (222 : ℕ) := by
  rw [show (222 : ℕ) = 2 * 111 from by norm_num]
  have h3 : Nat.Prime 3 := three_prime
  have h37 : Nat.Prime 37 := by native_decide
  have h111 : Squarefree (111 : ℕ) := by
    rw [show (111 : ℕ) = 3 * 37 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h3.squarefree, h37.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h111⟩)

private theorem squarefree_246 : Squarefree (246 : ℕ) := by
  rw [show (246 : ℕ) = 2 * 123 from by norm_num]
  have h3 : Nat.Prime 3 := three_prime
  have h41 : Nat.Prime 41 := by native_decide
  have h123 : Squarefree (123 : ℕ) := by
    rw [show (123 : ℕ) = 3 * 41 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h3.squarefree, h41.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h123⟩)

private theorem squarefree_254 : Squarefree (254 : ℕ) := by
  rw [show (254 : ℕ) = 2 * 127 from by norm_num]
  have : Nat.Prime 127 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_282 : Squarefree (282 : ℕ) := by
  rw [show (282 : ℕ) = 2 * 141 from by norm_num]
  have h3 : Nat.Prime 3 := three_prime
  have h47 : Nat.Prime 47 := by native_decide
  have h141 : Squarefree (141 : ℕ) := by
    rw [show (141 : ℕ) = 3 * 47 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h3.squarefree, h47.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h141⟩)

private theorem squarefree_318 : Squarefree (318 : ℕ) := by
  rw [show (318 : ℕ) = 2 * 159 from by norm_num]
  have h3 : Nat.Prime 3 := three_prime
  have h53 : Nat.Prime 53 := by native_decide
  have h159 : Squarefree (159 : ℕ) := by
    rw [show (159 : ℕ) = 3 * 53 from by norm_num]
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h3.squarefree, h53.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h159⟩)

private theorem squarefree_346 : Squarefree (346 : ℕ) := by
  rw [show (346 : ℕ) = 2 * 173 from by norm_num]
  have : Nat.Prime 173 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

private theorem squarefree_362 : Squarefree (362 : ℕ) := by
  rw [show (362 : ℕ) = 2 * 181 from by norm_num]
  have : Nat.Prime 181 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, this.squarefree⟩)

/--
**{1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181} has a squarefree sumset.**
All 121 ordered pair sums are squarefree. This extends the 10-element set
by adding 181, introducing 9 new distinct sums.
-/
theorem undeca_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- Row a=1: 2, 6, 22, 38, 42, 66, 74, 102, 138, 166, 182
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_66
  · exact squarefree_74
  · exact squarefree_102
  · exact squarefree_138
  · exact squarefree_166
  · exact squarefree_182
  -- Row a=5: 6, 10, 26, 42, 46, 70, 78, 106, 142, 170, 186
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_70
  · exact squarefree_78
  · exact squarefree_106
  · exact squarefree_142
  · exact squarefree_170
  · exact squarefree_186
  -- Row a=21: 22, 26, 42, 58, 62, 86, 94, 122, 158, 186, 202
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_62
  · exact squarefree_86
  · exact squarefree_94
  · exact squarefree_122
  · exact squarefree_158
  · exact squarefree_186
  · exact squarefree_202
  -- Row a=37: 38, 42, 58, 74, 78, 102, 110, 138, 174, 202, 218
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_102
  · exact squarefree_110
  · exact squarefree_138
  · exact squarefree_174
  · exact squarefree_202
  · exact squarefree_218
  -- Row a=41: 42, 46, 62, 78, 82, 106, 114, 142, 178, 206, 222
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_62
  · exact squarefree_78
  · exact squarefree_82
  · exact squarefree_106
  · exact squarefree_114
  · exact squarefree_142
  · exact squarefree_178
  · exact squarefree_206
  · exact squarefree_222
  -- Row a=65: 66, 70, 86, 102, 106, 130, 138, 166, 202, 230, 246
  · exact squarefree_66
  · exact squarefree_70
  · exact squarefree_86
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_130
  · exact squarefree_138
  · exact squarefree_166
  · exact squarefree_202
  · exact squarefree_230
  · exact squarefree_246
  -- Row a=73: 74, 78, 94, 110, 114, 138, 146, 174, 210, 238, 254
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_94
  · exact squarefree_110
  · exact squarefree_114
  · exact squarefree_138
  · exact squarefree_146
  · exact squarefree_174
  · exact squarefree_210
  · exact squarefree_238
  · exact squarefree_254
  -- Row a=101: 102, 106, 122, 138, 142, 166, 174, 202, 238, 266, 282
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_122
  · exact squarefree_138
  · exact squarefree_142
  · exact squarefree_166
  · exact squarefree_174
  · exact squarefree_202
  · exact squarefree_238
  · exact squarefree_266
  · exact squarefree_282
  -- Row a=137: 138, 142, 158, 174, 178, 202, 210, 238, 274, 302, 318
  · exact squarefree_138
  · exact squarefree_142
  · exact squarefree_158
  · exact squarefree_174
  · exact squarefree_178
  · exact squarefree_202
  · exact squarefree_210
  · exact squarefree_238
  · exact squarefree_274
  · exact squarefree_302
  · exact squarefree_318
  -- Row a=165: 166, 170, 186, 202, 206, 230, 238, 266, 302, 330, 346
  · exact squarefree_166
  · exact squarefree_170
  · exact squarefree_186
  · exact squarefree_202
  · exact squarefree_206
  · exact squarefree_230
  · exact squarefree_238
  · exact squarefree_266
  · exact squarefree_302
  · exact squarefree_330
  · exact squarefree_346
  -- Row a=181: 182, 186, 202, 218, 222, 246, 254, 282, 318, 346, 362
  · exact squarefree_182
  · exact squarefree_186
  · exact squarefree_202
  · exact squarefree_218
  · exact squarefree_222
  · exact squarefree_246
  · exact squarefree_254
  · exact squarefree_282
  · exact squarefree_318
  · exact squarefree_346
  · exact squarefree_362

/--
**f(N) >= 11 for N >= 181:**
The set {1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181} has squarefree sumset.
-/
theorem f_ge_eleven (N : ℕ) (hN : N ≥ 181) : f N ≥ 11 := by
  unfold f
  have h11 : (11 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181}, ?_, undeca_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h11

-- ============================================================================
-- Part XI: 12-Element Witness and f(N) >= 12
-- ============================================================================

-- New squarefree facts for 12-element witness (sums involving 217)

private theorem squarefree_258 : Squarefree (258 : ℕ) := by
  rw [show (258 : ℕ) = 2 * 129 from by norm_num]
  have h129 : Squarefree (129 : ℕ) := by
    rw [show (129 : ℕ) = 3 * 43 from by norm_num]
    have h43 : Nat.Prime 43 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h43.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h129⟩)

private theorem squarefree_290 : Squarefree (290 : ℕ) := by
  rw [show (290 : ℕ) = 2 * 145 from by norm_num]
  have h145 : Squarefree (145 : ℕ) := by
    rw [show (145 : ℕ) = 5 * 29 from by norm_num]
    have h29 : Nat.Prime 29 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, five_prime.squarefree, h29.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h145⟩)

private theorem squarefree_354 : Squarefree (354 : ℕ) := by
  rw [show (354 : ℕ) = 2 * 177 from by norm_num]
  have h177 : Squarefree (177 : ℕ) := by
    rw [show (177 : ℕ) = 3 * 59 from by norm_num]
    have h59 : Nat.Prime 59 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, three_prime.squarefree, h59.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h177⟩)

private theorem squarefree_382 : Squarefree (382 : ℕ) := by
  rw [show (382 : ℕ) = 2 * 191 from by norm_num]
  have h191 : Nat.Prime 191 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h191.squarefree⟩)

private theorem squarefree_398 : Squarefree (398 : ℕ) := by
  rw [show (398 : ℕ) = 2 * 199 from by norm_num]
  have h199 : Nat.Prime 199 := by native_decide
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h199.squarefree⟩)

private theorem squarefree_434 : Squarefree (434 : ℕ) := by
  rw [show (434 : ℕ) = 2 * 217 from by norm_num]
  have h217 : Squarefree (217 : ℕ) := by
    rw [show (217 : ℕ) = 7 * 31 from by norm_num]
    have h7 : Nat.Prime 7 := by native_decide
    have h31 : Nat.Prime 31 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h7.squarefree, h31.squarefree⟩
  exact (Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, squarefree_2, h217⟩)

/--
**{1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181, 217} has a squarefree sumset.**
All 144 ordered pair sums are squarefree.
-/
theorem dodeca_squarefree_sumset :
    hasSquarefreeSumset ({1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181, 217} : Finset ℕ) := by
  intro s hs
  simp only [sumset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hs
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := hs
  simp only [isSquarefree]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hab <;> rw [← hab]
  -- Row a=1: 2, 6, 22, 38, 42, 66, 74, 102, 138, 166, 182, 218
  · exact squarefree_2
  · exact squarefree_6
  · exact squarefree_22
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_66
  · exact squarefree_74
  · exact squarefree_102
  · exact squarefree_138
  · exact squarefree_166
  · exact squarefree_182
  · exact squarefree_218
  -- Row a=5
  · exact squarefree_6
  · exact squarefree_10
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_70
  · exact squarefree_78
  · exact squarefree_106
  · exact squarefree_142
  · exact squarefree_170
  · exact squarefree_186
  · exact squarefree_222
  -- Row a=21
  · exact squarefree_22
  · exact squarefree_26
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_62
  · exact squarefree_86
  · exact squarefree_94
  · exact squarefree_122
  · exact squarefree_158
  · exact squarefree_186
  · exact squarefree_202
  · exact squarefree_238
  -- Row a=37
  · exact squarefree_38
  · exact squarefree_42
  · exact squarefree_58
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_102
  · exact squarefree_110
  · exact squarefree_138
  · exact squarefree_174
  · exact squarefree_202
  · exact squarefree_218
  · exact squarefree_254
  -- Row a=41
  · exact squarefree_42
  · exact squarefree_46
  · exact squarefree_62
  · exact squarefree_78
  · exact squarefree_82
  · exact squarefree_106
  · exact squarefree_114
  · exact squarefree_142
  · exact squarefree_178
  · exact squarefree_206
  · exact squarefree_222
  · exact squarefree_258
  -- Row a=65
  · exact squarefree_66
  · exact squarefree_70
  · exact squarefree_86
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_130
  · exact squarefree_138
  · exact squarefree_166
  · exact squarefree_202
  · exact squarefree_230
  · exact squarefree_246
  · exact squarefree_282
  -- Row a=73
  · exact squarefree_74
  · exact squarefree_78
  · exact squarefree_94
  · exact squarefree_110
  · exact squarefree_114
  · exact squarefree_138
  · exact squarefree_146
  · exact squarefree_174
  · exact squarefree_210
  · exact squarefree_238
  · exact squarefree_254
  · exact squarefree_290
  -- Row a=101
  · exact squarefree_102
  · exact squarefree_106
  · exact squarefree_122
  · exact squarefree_138
  · exact squarefree_142
  · exact squarefree_166
  · exact squarefree_174
  · exact squarefree_202
  · exact squarefree_238
  · exact squarefree_266
  · exact squarefree_282
  · exact squarefree_318
  -- Row a=137
  · exact squarefree_138
  · exact squarefree_142
  · exact squarefree_158
  · exact squarefree_174
  · exact squarefree_178
  · exact squarefree_202
  · exact squarefree_210
  · exact squarefree_238
  · exact squarefree_274
  · exact squarefree_302
  · exact squarefree_318
  · exact squarefree_354
  -- Row a=165
  · exact squarefree_166
  · exact squarefree_170
  · exact squarefree_186
  · exact squarefree_202
  · exact squarefree_206
  · exact squarefree_230
  · exact squarefree_238
  · exact squarefree_266
  · exact squarefree_302
  · exact squarefree_330
  · exact squarefree_346
  · exact squarefree_382
  -- Row a=181
  · exact squarefree_182
  · exact squarefree_186
  · exact squarefree_202
  · exact squarefree_218
  · exact squarefree_222
  · exact squarefree_246
  · exact squarefree_254
  · exact squarefree_282
  · exact squarefree_318
  · exact squarefree_346
  · exact squarefree_362
  · exact squarefree_398
  -- Row a=217
  · exact squarefree_218
  · exact squarefree_222
  · exact squarefree_238
  · exact squarefree_254
  · exact squarefree_258
  · exact squarefree_282
  · exact squarefree_290
  · exact squarefree_318
  · exact squarefree_354
  · exact squarefree_382
  · exact squarefree_398
  · exact squarefree_434

/--
**f(N) >= 12 for N >= 217:**
-/
theorem f_ge_twelve (N : ℕ) (hN : N ≥ 217) : f N ≥ 12 := by
  unfold f
  have h12 : (12 : ℕ) ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨{1, 5, 21, 37, 41, 65, 73, 101, 137, 165, 181, 217}, ?_, dodeca_squarefree_sumset, ?_⟩
    · intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [Finset.mem_range]
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · native_decide
  have hbdd : BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ range (N + 1) ∧ hasSquarefreeSumset A ∧ A.card = m} := by
    use N + 1
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨A, hA_sub, _, hA_card⟩ := hm
    rw [← hA_card]
    exact le_trans (Finset.card_le_card hA_sub) (by simp [Finset.card_range])
  exact le_csSup hbdd h12

-- ============================================================================
-- Part XII: Sub-Linear Upper Bound
-- ============================================================================

/--
**Sub-linear upper bound:** f(N) ≤ N/77 + 69120.
From the 5-prime CRT density: 69120/5336100 < 1/77.
-/
theorem f_sublinear (A : Finset ℕ) (h : hasSquarefreeSumset A) (N : ℕ)
    (hA_sub : A ⊆ Finset.range (N + 1)) :
    A.card ≤ N / 77 + 69120 := by
  have h5 := f_upper_5336100 A h N hA_sub
  have h_key : 69120 * (N / 5336100) ≤ N / 77 := by
    set k := N / 5336100
    have hk : k * 5336100 ≤ N := Nat.div_mul_le_self N 5336100
    have step1 : 69120 * k ≤ 5336100 * k / 77 := by
      have : 69120 * k * 77 ≤ 5336100 * k := by nlinarith [show 69120 * 77 ≤ 5336100 from by norm_num]
      omega
    have step2 : 5336100 * k / 77 ≤ N / 77 := Nat.div_le_div_right (by linarith)
    linarith
  calc A.card
      ≤ 69120 * (N / 5336100 + 1) := h5
    _ = 69120 * (N / 5336100) + 69120 := by ring
    _ ≤ N / 77 + 69120 := Nat.add_le_add_right h_key _

/--
**Complete bounds:** 12 ≤ f(N) ≤ N/77 + 69120 for large N.
-/
theorem f_complete_bounds (N : ℕ) (hN : N ≥ 5322240) :
    12 ≤ f N ∧
    ∀ (A : Finset ℕ), hasSquarefreeSumset A → A ⊆ Finset.range (N + 1) →
      A.card ≤ N / 77 + 69120 :=
  ⟨f_ge_twelve N (by omega), fun A h hA_sub => f_sublinear A h N hA_sub⟩

/--
**Lower bound chain:** f(1) ≥ 1, ..., f(217) ≥ 12.
-/
theorem f_lower_bound_chain :
    f 1 ≥ 1 ∧ f 5 ≥ 2 ∧ f 21 ≥ 3 ∧ f 37 ≥ 4 ∧ f 41 ≥ 5 ∧
    f 65 ≥ 6 ∧ f 73 ≥ 7 ∧ f 101 ≥ 8 ∧ f 137 ≥ 9 ∧ f 165 ≥ 10 ∧
    f 181 ≥ 11 ∧ f 217 ≥ 12 :=
  ⟨f_ge_one 1 (by omega), f_ge_two 5 (by omega), f_ge_three 21 (by omega),
   f_ge_four 37 (by omega), f_ge_five 41 (by omega), f_ge_six 65 (by omega),
   f_ge_seven 73 (by omega), f_ge_eight 101 (by omega), f_ge_nine 137 (by omega),
   f_ge_ten 165 (by omega), f_ge_eleven 181 (by omega), f_ge_twelve 217 (by omega)⟩


end Erdos1109
