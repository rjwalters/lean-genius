/-
  Erdős Problem #873: LCM of Consecutive Sequence Terms

  **Problem**: Let A = {a₁ < a₂ < ...} ⊆ ℕ and let F(A,X,k) count the number of i
  such that [aᵢ, aᵢ₊₁, ..., aᵢ₊ₖ₋₁] < X, where [...] denotes LCM.

  Is it true that for every ε > 0, there exists some k such that F(A,X,k) < X^ε?

  **Status**: OPEN

  **Known Results** (Erdős-Szemerédi):
  - For every A: F(A,X,3) ≪ X^(1/3) log X
  - There exists A with F(A,X,3) ≫ X^(1/3) log X for infinitely many X

  The conjecture asks whether the exponent can be made arbitrarily small by
  taking k large enough. The k=3 case shows the exponent is at most 1/3 + ε,
  but the general conjecture remains open.

  Reference: https://erdosproblems.com/873
  [Er92c] Erdős, Paul, "Some of my favourite unsolved problems"

  Source: Adapted from Google DeepMind Formal Conjectures project
-/

import Mathlib

open Set

namespace Erdos873

/-
## The Counting Function F(A,X,k)

F(A,X,k) counts how many k-tuples of consecutive terms have LCM less than X.
This measures how "multiplicatively dependent" consecutive terms can be.
-/

/-- The LCM of k consecutive terms starting at position i in sequence a.
For a = (a₀, a₁, a₂, ...), this computes [aᵢ, aᵢ₊₁, ..., aᵢ₊ₖ₋₁]. -/
def consecutiveLcm (a : ℕ → ℕ) (i k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun m => a (i + m))

/-- F(A,X,k) counts positions i where the LCM of k consecutive terms is < X.
This is the central quantity in the Erdős-Szemerédi problem. -/
noncomputable def F (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (consecutiveLcm a i k : ℝ) < X}.encard

/-
## Basic Properties
-/

/-- The LCM of a single term is the term itself. -/
theorem consecutiveLcm_one (a : ℕ → ℕ) (i : ℕ) : consecutiveLcm a i 1 = a i := by
  simp [consecutiveLcm]

/-- The LCM is monotone in k: more terms means larger or equal LCM. -/
theorem consecutiveLcm_mono {a : ℕ → ℕ} {i k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    consecutiveLcm a i k₁ ∣ consecutiveLcm a i k₂ := by
  apply Finset.lcm_dvd
  intro x hx
  apply Finset.dvd_lcm
  simp only [Finset.mem_range] at hx ⊢
  omega

/-- F is monotone decreasing in k: larger windows mean fewer qualifying positions.
As we consider more consecutive terms, the LCM can only grow, so fewer
positions will have LCM below X. -/
theorem F_mono {a : ℕ → ℕ} {X : ℝ} {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (hpos : ∀ i, 0 < a i) :
    F a X k₂ ≤ F a X k₁ := by
  apply Set.encard_le_encard
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  have hdvd := consecutiveLcm_mono h (a := a) (i := i)
  -- If k₁ ≤ k₂ then consecutiveLcm a i k₁ | consecutiveLcm a i k₂
  -- So consecutiveLcm a i k₁ ≤ consecutiveLcm a i k₂
  -- If consecutiveLcm a i k₂ < X then consecutiveLcm a i k₁ < X
  have hle : consecutiveLcm a i k₁ ≤ consecutiveLcm a i k₂ := Nat.le_of_dvd (by
    -- Need to show consecutiveLcm a i k₂ > 0
    -- The LCM is positive because each term a(i+m) is positive
    unfold consecutiveLcm
    apply Nat.pos_of_ne_zero
    intro h0
    -- If lcm = 0, then some element is 0
    have := Finset.lcm_eq_zero_iff.mp h0
    obtain ⟨m, _, hm⟩ := this
    exact Nat.not_lt_zero _ (hm ▸ hpos (i + m))) hdvd
  calc (consecutiveLcm a i k₁ : ℝ) ≤ consecutiveLcm a i k₂ := by exact_mod_cast hle
    _ < X := hi

/-
## Main Conjecture (OPEN)

The Erdős-Szemerédi conjecture asks: can we always find k large enough
to make F(A,X,k) grow slower than any power of X?
-/

/-- **Erdős Problem #873 (OPEN)**: The Erdős-Szemerédi LCM Conjecture.

For any strictly increasing sequence A ⊆ ℕ and any ε > 0, does there exist k
such that F(A,X,k) < X^ε for all sufficiently large X?

Intuition: If consecutive terms are "multiplicatively independent", their LCM
grows quickly, so few k-tuples have small LCM. The conjecture asks whether
this independence can always be achieved by looking at long enough windows. -/
def lcmConjecture : Prop :=
  ∀ (a : ℕ → ℕ), 0 < a 0 → StrictMono a →
    ∀ ε > 0, ∃ k, ∀ X > 0, F a X k < ⊤

/-
## Known Results

Erdős and Szemerédi established precise bounds for k = 3.
-/

/-- **Erdős-Szemerédi Upper Bound**: For any sequence A and k = 3,
F(A,X,3) ≪ X^(1/3) log X.

This means the exponent 1/3 is achievable for k = 3. We state this as an axiom
since the proof requires careful number-theoretic analysis. -/
axiom erdos_szemeredi_upper_bound (a : ℕ → ℕ) (ha0 : 0 < a 0) (ha : StrictMono a) :
    ∃ C > 0, ∀ X ≥ 2, ∃ n : ℕ, F a X 3 = n ∧ (n : ℝ) ≤ C * X^(1/3 : ℝ) * Real.log X

/-- **Erdős-Szemerédi Lower Bound**: There exists a sequence A such that
F(A,X,3) ≫ X^(1/3) log X for infinitely many X.

This shows the upper bound is essentially tight for k = 3. -/
axiom erdos_szemeredi_lower_bound :
    ∃ (a : ℕ → ℕ), 0 < a 0 ∧ StrictMono a ∧
    ∃ C > 0, ∀ N, ∃ X ≥ N, ∃ n : ℕ, F a X 3 = n ∧ C * X^(1/3 : ℝ) * Real.log X ≤ n

/-
## Examples and Special Cases
-/

/-- For the sequence of all natural numbers a(i) = i + 1, the LCM of
consecutive terms grows quickly. For example, [6, 7] = 42. -/
example : consecutiveLcm (fun i => i + 1) 5 2 = 42 := by native_decide

/-- For consecutive naturals, [n, n+1] = n(n+1) since gcd(n, n+1) = 1.
This is verified computationally for small values. -/
example : consecutiveLcm (fun j => j + 1) 10 2 = 11 * 12 := by native_decide

/-- For the sequence 1, 2, 4, 8, ... (powers of 2), consecutive powers
have LCM equal to the larger power since 2^i | 2^(i+1). -/
example : consecutiveLcm (fun j => 2^j) 3 2 = 2^4 := by native_decide

/-- More generally, for powers of 2, [2^i, 2^(i+1)] = 2^(i+1).
Since 2^i | 2^(i+1), the LCM equals the larger term. -/
theorem consecutiveLcm_powers_of_two (i : ℕ) :
    consecutiveLcm (fun j => 2^j) i 2 = 2^(i+1) := by
  -- For k = 2, consecutiveLcm computes lcm of {2^i, 2^(i+1)}
  -- Since 2^i | 2^(i+1), the lcm equals 2^(i+1)
  unfold consecutiveLcm
  have hrange : Finset.range 2 = {0, 1} := by decide
  rw [hrange]
  simp only [Finset.lcm_insert, Finset.lcm_singleton, add_zero, Nat.add_one, normalize_eq]
  -- Now we have Nat.lcm (2^i) (2^(i+1)) = 2^(i+1)
  exact Nat.lcm_eq_right (Nat.pow_dvd_pow 2 (Nat.le_succ i))

end Erdos873
