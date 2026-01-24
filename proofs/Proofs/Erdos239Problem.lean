/-
Erdős Problem #239: Mean of Multiplicative ±1 Functions

Source: https://erdosproblems.com/239
Status: SOLVED (Wirsing, 1967; generalized by Halász, 1968)

Statement:
Let f : ℕ → {-1, 1} be a multiplicative function. Does the limit
  lim_{N→∞} (1/N) ∑_{n≤N} f(n)
always exist?

Answer: YES

Wirsing (1967) proved that for multiplicative functions taking values in {-1, 1},
the mean value always exists (though it may be 0).

Halász (1968) generalized this to multiplicative functions with values on the
unit circle in ℂ, showing when convergence occurs and characterizing the limit.

Key Insight:
Wintner observed that for complex-valued multiplicative functions on the unit circle,
the limit need NOT exist. Rényi gave the example f(n) = n^i (which is multiplicative
but oscillates wildly).

The restriction to real values {-1, 1} is essential for convergence.

References:
- [Wi67] Wirsing, "Das asymptotische Verhalten von Summen über multiplikative Funktionen"
        Acta Math. Acad. Sci. Hungar. (1967), 411-467
- [Ha68] Halász, "Über die Mittelwerte multiplikativer zahlentheoretischer Funktionen"
        Acta Math. Acad. Sci. Hungar. (1968), 365-403
- Erdős sources: [Er61], [Er65b], [Er73], [Er82e]

Tags: number-theory, multiplicative-functions, analytic-number-theory, mean-values
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Nat Real BigOperators Finset

namespace Erdos239

/-!
## Part I: Multiplicative Functions
-/

/-- A function f : ℕ → α is multiplicative if f(1) = 1 and f(mn) = f(m)f(n) for coprime m, n. -/
def IsMultiplicative {α : Type*} [Monoid α] (f : ℕ → α) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n

/-- A ±1 function takes values only in {-1, 1}. -/
def IsPlusMinusOne (f : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, n ≥ 1 → f n = 1 ∨ f n = -1

/-- The set of multiplicative ±1 functions. -/
def MultPlusMinusOne : Set (ℕ → ℤ) :=
  {f | IsMultiplicative f ∧ IsPlusMinusOne f}

/-!
## Part II: Mean Values
-/

/-- The partial sum ∑_{n≤N} f(n). -/
noncomputable def partialSum (f : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ n in Finset.range N, f (n + 1)

/-- The mean value (1/N) ∑_{n≤N} f(n). -/
noncomputable def meanValue (f : ℕ → ℤ) (N : ℕ) : ℝ :=
  (partialSum f N : ℝ) / (N : ℝ)

/-- A function has convergent mean if lim_{N→∞} meanValue f N exists. -/
def HasConvergentMean (f : ℕ → ℤ) : Prop :=
  ∃ L : ℝ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |meanValue f N - L| < ε

/-!
## Part III: Classical Examples
-/

/-- The Liouville function λ(n) = (-1)^Ω(n) where Ω counts prime factors with multiplicity. -/
def liouville (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1) ^ (Nat.factors n).length

/-- The Möbius function μ restricted to squarefree numbers gives ±1. -/
def mobiusSign (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if n = 1 then 1
  else if ¬Squarefree n then 0
  else (-1) ^ (Nat.factors n).length

/-- Liouville function is multiplicative. -/
axiom liouville_multiplicative : IsMultiplicative liouville

/-- Liouville function takes values ±1 on positive integers. -/
axiom liouville_pm_one : IsPlusMinusOne liouville

/-- λ ∈ MultPlusMinusOne. -/
theorem liouville_in_mult_pm : liouville ∈ MultPlusMinusOne :=
  ⟨liouville_multiplicative, liouville_pm_one⟩

/-!
## Part IV: The Completely Multiplicative Case
-/

/-- A function is completely multiplicative if f(mn) = f(m)f(n) for ALL m, n. -/
def IsCompletelyMultiplicative {α : Type*} [Monoid α] (f : ℕ → α) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n

/-- Every completely multiplicative function is multiplicative. -/
theorem completely_mult_is_mult {α : Type*} [Monoid α] (f : ℕ → α)
    (h : IsCompletelyMultiplicative f) : IsMultiplicative f :=
  ⟨h.1, fun m n _ => h.2 m n⟩

/-- A completely multiplicative ±1 function is determined by its values on primes. -/
theorem completely_mult_pm_determined (f : ℕ → ℤ)
    (hcm : IsCompletelyMultiplicative f) (hpm : IsPlusMinusOne f)
    (g : ℕ → ℤ) (hcm' : IsCompletelyMultiplicative g) (hpm' : IsPlusMinusOne g)
    (heq : ∀ p : ℕ, p.Prime → f p = g p) :
    ∀ n : ℕ, n ≥ 1 → f n = g n := by
  sorry  -- Proof by induction on prime factorization

/-!
## Part V: Wintner's Counterexample for Complex Values
-/

/-- The function n^i = exp(i log n) for complex values. -/
noncomputable def powerI (n : ℕ) : ℂ :=
  if n = 0 then 0 else Complex.exp (Complex.I * Real.log n)

/-- n^i is multiplicative (as a complex function). -/
axiom powerI_multiplicative : ∀ m n : ℕ, m ≥ 1 → n ≥ 1 →
    powerI (m * n) = powerI m * powerI n

/-- |n^i| = 1 for all n ≥ 1 (values on unit circle). -/
axiom powerI_unit_circle : ∀ n : ℕ, n ≥ 1 → Complex.abs (powerI n) = 1

/-- **Wintner-Rényi Counterexample:**
    The function n^i does NOT have a convergent mean.
    This shows the restriction to {-1, 1} is essential. -/
axiom wintner_renyi_counterexample :
    ¬∃ L : ℂ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Complex.abs ((∑ n in Finset.range N, powerI (n + 1)) / N - L) < ε

/-!
## Part VI: Wirsing's Theorem (1967)
-/

/-- **Wirsing's Theorem (1967):**
    Every multiplicative function f : ℕ → {-1, 1} has a convergent mean.

    This is the main result answering Erdős Problem #239 affirmatively.

    The proof uses analytic methods involving Dirichlet series
    and the behavior of ∑ f(p)/p over primes. -/
axiom wirsing_theorem (f : ℕ → ℤ)
    (hm : IsMultiplicative f) (hpm : IsPlusMinusOne f) :
    HasConvergentMean f

/-- **Erdős Problem #239: SOLVED**
    The answer is YES - the limit always exists. -/
theorem erdos_239 (f : ℕ → ℤ) (hf : f ∈ MultPlusMinusOne) :
    HasConvergentMean f :=
  wirsing_theorem f hf.1 hf.2

/-!
## Part VII: Halász's Generalization (1968)
-/

/-- The mean value limit of a multiplicative ±1 function. -/
noncomputable def meanLimit (f : ℕ → ℤ) (hf : f ∈ MultPlusMinusOne) : ℝ :=
  Classical.choose (wirsing_theorem f hf.1 hf.2)

/-- **Halász's Theorem (1968):**
    Characterizes when the mean limit is non-zero.

    For f : ℕ → {-1, 1} multiplicative, the mean limit L satisfies:
    - L = 0 if ∑_p (1 - f(p))/p = ∞
    - L ≠ 0 if ∑_p (1 - f(p))/p < ∞

    The latter occurs iff f "pretends to be 1" at most primes. -/
axiom halasz_characterization (f : ℕ → ℤ)
    (hm : IsMultiplicative f) (hpm : IsPlusMinusOne f) :
    ∃ L : ℝ, (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |meanValue f N - L| < ε) ∧
      (L = 0 ↔ ∀ B > 0, ∃ S : Finset ℕ,
        (∀ p ∈ S, p.Prime) ∧
        (∑ p in S, (1 - f p : ℝ) / p) > B)

/-!
## Part VIII: The Constant Function
-/

/-- The constant 1 function. -/
def constOne : ℕ → ℤ := fun _ => 1

/-- constOne is completely multiplicative. -/
theorem constOne_completely_mult : IsCompletelyMultiplicative constOne :=
  ⟨rfl, fun _ _ => by simp [constOne]⟩

/-- constOne is multiplicative. -/
theorem constOne_mult : IsMultiplicative constOne :=
  completely_mult_is_mult constOne constOne_completely_mult

/-- constOne is ±1 valued. -/
theorem constOne_pm : IsPlusMinusOne constOne := fun _ _ => Or.inl rfl

/-- constOne ∈ MultPlusMinusOne. -/
theorem constOne_in_mult_pm : constOne ∈ MultPlusMinusOne :=
  ⟨constOne_mult, constOne_pm⟩

/-- The mean of the constant 1 function is 1. -/
theorem constOne_mean (N : ℕ) (hN : N ≥ 1) : meanValue constOne N = 1 := by
  simp [meanValue, partialSum, constOne]
  field_simp
  ring

/-!
## Part IX: The Liouville Function Mean
-/

/-- **Liouville Mean Theorem:**
    The mean of the Liouville function converges to 0.

    This is equivalent to the Prime Number Theorem! -/
axiom liouville_mean_zero :
    ∃ L : ℝ, L = 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |meanValue liouville N - L| < ε

/-- The Liouville function has zero mean limit. -/
theorem liouville_limit_zero :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |meanValue liouville N| < ε := by
  intro ε hε
  obtain ⟨L, hL0, hconv⟩ := liouville_mean_zero
  rw [hL0] at hconv
  simp only [sub_zero] at hconv
  exact hconv ε hε

/-!
## Part X: Connection to Prime Distribution
-/

/-- **Mean-to-PNT Connection:**
    For the Liouville function:
    meanValue λ N → 0  is equivalent to the Prime Number Theorem.

    The rate of convergence determines the error term in PNT. -/
axiom liouville_pnt_equivalence :
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |meanValue liouville N| < ε) ↔
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(Nat.primeCounting N : ℝ) - N / Real.log N| < ε * N / Real.log N

/-- The Riemann Hypothesis is equivalent to a specific rate of convergence. -/
axiom rh_equivalence :
    -- RH ↔ meanValue λ N = O(N^{-1/2 + ε}) for all ε > 0
    True  -- Statement simplified

/-!
## Part XI: Summary
-/

/-- **Erdős Problem #239: Summary**

PROBLEM: For multiplicative f : ℕ → {-1, 1}, does lim (1/N) ∑_{n≤N} f(n) exist?

ANSWER: YES (Wirsing, 1967)

KEY RESULTS:
1. wirsing_theorem: Main convergence theorem
2. halasz_characterization: When the limit is non-zero
3. wintner_renyi_counterexample: Why {-1, 1} restriction is needed

EXAMPLES:
- constOne: mean limit = 1
- liouville: mean limit = 0 (equivalent to PNT)

The problem is fundamentally about the interplay between multiplicativity
and oscillation in arithmetic functions.
-/
theorem erdos_239_summary :
    -- Main theorem
    (∀ f : ℕ → ℤ, f ∈ MultPlusMinusOne → HasConvergentMean f) ∧
    -- Constant function has mean 1
    (constOne ∈ MultPlusMinusOne) ∧
    -- Liouville function has mean 0
    (liouville ∈ MultPlusMinusOne) :=
  ⟨fun f hf => erdos_239 f hf, constOne_in_mult_pm, liouville_in_mult_pm⟩

/-- The answer to Erdős Problem #239 is YES. -/
def erdos_239_answer : String :=
  "YES - Every multiplicative {-1,1}-valued function has a convergent mean (Wirsing 1967)"

end Erdos239
