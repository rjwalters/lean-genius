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
axiom distinct_primes_squarefree (ps : List ℕ) (hps : ∀ p ∈ ps, Nat.Prime p)
    (hdist : ps.Nodup) : isSquarefree ps.prod

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

end Erdos1109
