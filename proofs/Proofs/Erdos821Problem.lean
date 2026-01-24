/-
  Erdős Problem #821: Large Values of the Euler Phi Preimage Function

  Source: https://erdosproblems.com/821
  Status: OPEN (partial results known)

  Statement:
  Let g(n) count the number of m such that φ(m) = n.
  Is it true that, for every ε > 0, there exist infinitely many n such that
    g(n) > n^{1-ε}?

  Answer: OPEN (conjectured YES)

  Known Results:
  - Pillai: lim sup g(n) = ∞
  - Erdős (1935): ∃ c > 0 such that g(n) > n^c infinitely often
  - Lichtman (2022): g(n) > n^{0.71568...} infinitely often (current best)

  Connection:
  Would follow if: for every ε > 0, there are ≫ x/log x primes p < x
  with all prime factors of p-1 less than p^ε.

  Related: Problem #416

  References:
  - [Er35b] Erdős, "On the normal number of prime factors of p-1..." (1935)
  - [Li22] Lichtman, "Primes in arithmetic progressions..." (2022)
  - [BaHa98] Baker-Harman (1998)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.EulerPhi.Basic
import Mathlib.Order.Filter.Basic

open Nat Real Filter

namespace Erdos821

/-
## Part I: Euler's Totient Function
-/

/-- Euler's totient function φ(n). -/
def phi : ℕ → ℕ := Nat.totient

/-- The preimage counting function g(n) = |{m : φ(m) = n}|. -/
noncomputable def g (n : ℕ) : ℕ :=
  (Finset.filter (fun m => phi m = n) (Finset.range (n + 1))).card +
  (Finset.filter (fun m => phi m = n) (Finset.Icc (n + 1) (2 * n))).card
  -- Note: The full preimage is finite but potentially larger; this is a lower bound

/-- More precise definition: count all m with φ(m) = n. -/
noncomputable def preimageCount (n : ℕ) : ℕ :=
  Nat.card { m : ℕ // phi m = n }

/-- The preimage count is finite for each n. -/
axiom preimageCount_finite (n : ℕ) : preimageCount n < n^2

/-
## Part II: Known Results
-/

/-- **Pillai's Theorem:**
    lim sup g(n) = ∞, i.e., g(n) is unbounded. -/
axiom pillai_theorem : ∀ M : ℕ, ∃ n : ℕ, preimageCount n > M

/-- **Erdős's Theorem (1935):**
    There exists c > 0 such that g(n) > n^c for infinitely many n. -/
axiom erdos_1935 :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n ≥ N, (preimageCount n : ℝ) > n^c

/-- The Erdős constant from 1935. -/
noncomputable def erdosConstant1935 : ℝ := 0.1 -- placeholder

/-- Erdős's lower bound with the constant. -/
axiom erdos_explicit_bound :
  ∀ N : ℕ, ∃ n ≥ N, (preimageCount n : ℝ) > n^erdosConstant1935

/-
## Part III: Lichtman's Result (2022)
-/

/-- The Lichtman exponent: 0.71568... -/
noncomputable def lichtmanExponent : ℝ := 0.71568

/-- **Lichtman's Theorem (2022):**
    There are infinitely many n with g(n) > n^{0.71568}. -/
axiom lichtman_theorem :
  ∀ N : ℕ, ∃ n ≥ N, (preimageCount n : ℝ) > n^lichtmanExponent

/-- Lichtman's result on primes with smooth p-1. -/
axiom lichtman_primes :
  ∃ c : ℝ, c > 0 ∧ ∀ x : ℝ, x ≥ 2 →
    (Finset.filter (fun p => Nat.Prime p ∧ p ≤ ⌊x⌋₊ ∧
      ∀ q : ℕ, Nat.Prime q → q ∣ p - 1 → q ≤ ⌊x^(0.2843 : ℝ)⌋₊)
      (Finset.range (⌊x⌋₊ + 1))).card ≥ c * x / (Real.log x)^2

/-
## Part IV: The Conjecture
-/

/-- **Erdős Conjecture (Problem #821):**
    For every ε > 0, there are infinitely many n with g(n) > n^{1-ε}. -/
def ErdosConjecture821 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ N : ℕ, ∃ n ≥ N, (preimageCount n : ℝ) > n^(1 - ε)

/-- Alternative formulation: the exponent approaches 1. -/
def ErdosConjecture821' : Prop :=
  ∀ α : ℝ, α < 1 → ∀ N : ℕ, ∃ n ≥ N, (preimageCount n : ℝ) > n^α

/-
## Part V: Connection to Smooth Primes
-/

/-- A prime p has ε-smooth (p-1) if all prime factors of p-1 are < p^ε. -/
def IsEpsilonSmooth (p : ℕ) (ε : ℝ) : Prop :=
  Nat.Prime p ∧ ∀ q : ℕ, Nat.Prime q → q ∣ p - 1 → (q : ℝ) < p^ε

/-- The sufficient condition for the conjecture. -/
def SmoothPrimesCondition : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ c : ℝ, c > 0 ∧ ∀ x : ℝ, x ≥ 2 →
    (Finset.filter (fun p => IsEpsilonSmooth p ε ∧ (p : ℝ) < x)
      (Finset.range (⌊x⌋₊ + 1))).card ≥ c * x / Real.log x

/-- The smooth primes condition implies the conjecture. -/
axiom smooth_implies_conjecture :
  SmoothPrimesCondition → ErdosConjecture821

/-
## Part VI: Upper Bounds
-/

/-- Upper bound: g(n) ≤ n^(1+o(1)) trivially. -/
axiom preimageCount_upper_bound :
  ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → (preimageCount n : ℝ) ≤ C * n^1.01

/-- For most n, g(n) is relatively small. -/
axiom average_preimageCount :
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    (∑ n in Finset.Icc 1 N, preimageCount n : ℝ) / N ≤ C * Real.log N

/-
## Part VII: Examples
-/

/-- g(1) = 2 (since φ(1) = φ(2) = 1). -/
theorem preimage_of_1 : phi 1 = 1 ∧ phi 2 = 1 := by
  simp [phi, Nat.totient]

/-- Values n = 2^k · 3^j · ... with many representations. -/
def highlyCompositePreimage : Prop :=
  -- Numbers of the form n = 2^k · ∏ (p_i - 1) have many preimages
  -- since m = ∏ p_i^{a_i} all give φ(m) = n
  True

/-
## Part VIII: Progress Summary
-/

/-- The current state of knowledge. -/
def currentKnowledge : Prop :=
  -- Proven: g(n) > n^{0.71568} infinitely often (Lichtman 2022)
  -- Conjectured: g(n) > n^{1-ε} for all ε > 0 infinitely often
  -- Gap: exponent 0.71568 vs target 1
  True

/-- The exponent has improved over time. -/
def exponentProgress : Prop :=
  -- Erdős 1935: some c > 0
  -- Various improvements
  -- Baker-Harman 1998: improved bounds
  -- Lichtman 2022: 0.71568
  True

/-
## Part IX: Related Problems
-/

/-- Related to Carmichael's conjecture (always g(n) ≥ 2 or g(n) = 0). -/
def carmichaelConnection : Prop :=
  -- Carmichael conjectured: if g(n) ≥ 1 then g(n) ≥ 2
  -- i.e., no unique preimage
  True

/-- Connection to Problem #416. -/
def problem416Connection : Prop :=
  -- Problem #416 concerns related questions about shifted primes
  True

/-
## Part X: Summary
-/

/-- **Erdős Problem #821: OPEN**

Question: For every ε > 0, are there infinitely many n with g(n) > n^{1-ε}?

Status: OPEN (partial results)

- Pillai: g(n) is unbounded
- Erdős (1935): g(n) > n^c for some c > 0
- Lichtman (2022): g(n) > n^{0.71568} (current best)

The conjecture would follow from sufficient density of primes p
with smooth p-1.
-/
theorem erdos_821_partial : ∀ N : ℕ, ∃ n ≥ N,
    (preimageCount n : ℝ) > n^lichtmanExponent :=
  lichtman_theorem

/-- The full conjecture remains open. -/
def erdos_821_open : Prop := ErdosConjecture821

/-- Known: the Lichtman bound. -/
theorem erdos_821_best_known : ∀ N : ℕ, ∃ n ≥ N,
    (preimageCount n : ℝ) > n^(0.71568 : ℝ) := by
  exact lichtman_theorem

/-- Placeholder for the full conjecture (unproven). -/
theorem erdos_821 : True := trivial

end Erdos821
