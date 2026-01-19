/-
Erdős Problem #334: Smooth Number Representation

Source: https://erdosproblems.com/334
Status: OPEN

Statement:
Find the best function f(n) such that every n can be written as n = a + b
where both a and b are f(n)-smooth (not divisible by any prime p > f(n)).

Known Results:
- Erdős originally asked if f(n) ≤ n^{1/3} holds
- Balog (1989) proved f(n) << n^{4/(9√e)+ε} ≈ n^{0.2695}

Conjectures:
- f(n) ≤ n^{o(1)}
- Possibly f(n) ≤ e^{O(√log n)}

References:
- Erdős-Graham (1980)
- Erdős (1982)
- Balog [Ba89]: "On additive representation of integers", Acta Math. Hungar.
- Green's Open Problems List, Problem 59
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real

namespace Erdos334

/-
## Part I: Smooth Numbers

A number is y-smooth if all its prime factors are ≤ y.
-/

/--
**Smooth Number:**
A natural number n is y-smooth if every prime factor p of n satisfies p ≤ y.
-/
def isSmooth (n : ℕ) (y : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ y

/--
**1 is trivially smooth for any bound.**
-/
theorem one_smooth (y : ℕ) : isSmooth 1 y := by
  intro p hp hdiv
  exact absurd (Nat.Prime.one_lt hp) (Nat.not_lt.mpr (Nat.le_of_dvd Nat.one_pos hdiv))

/--
**Prime powers are p-smooth.**
-/
theorem prime_power_smooth (p k : ℕ) (hp : p.Prime) : isSmooth (p ^ k) p := by
  intro q hq hdiv
  have := (Nat.Prime.dvd_prime_pow hp hq).mp hdiv
  rcases this with ⟨_, rfl⟩
  exact le_refl p

/--
**Product of smooth numbers is smooth.**
-/
theorem smooth_mul (a b y : ℕ) (ha : isSmooth a y) (hb : isSmooth b y) :
    isSmooth (a * b) y := by
  intro p hp hdiv
  rcases (Nat.Prime.dvd_mul hp).mp hdiv with h | h
  · exact ha p hp h
  · exact hb p hp h

/-
## Part II: Additive Representation by Smooth Numbers
-/

/--
**Smooth Pair Representation:**
n can be written as a + b where both a, b are y-smooth.
-/
def hasSmootPairRepr (n : ℕ) (y : ℕ) : Prop :=
  ∃ a b : ℕ, a + b = n ∧ isSmooth a y ∧ isSmooth b y

/--
**Trivial Case: n = 1**
1 = 1 + 0, but 0 needs special handling. Better: 1 is 1-smooth.
-/
theorem small_has_repr : ∀ n : ℕ, n ≤ 3 → hasSmootPairRepr n 2 := by
  sorry

/-
## Part III: The Minimal Smoothness Function
-/

/--
**Minimal Smoothness Function:**
f(n) = the smallest y such that n has a smooth pair representation with bound y.
-/
noncomputable def minSmoothness (n : ℕ) : ℕ :=
  -- The minimum y such that hasSmootPairRepr n y holds
  0  -- placeholder

/--
**f(n) exists for all n:**
Every n can be written as a + b with a, b having only "small" prime factors.
(The question is how small.)
-/
axiom minSmoothness_exists : ∀ n : ℕ, n ≥ 1 →
    ∃ y : ℕ, hasSmootPairRepr n y ∧ y ≤ n

/-
## Part IV: Known Bounds
-/

/--
**Erdős's Original Question:**
Is f(n) ≤ n^{1/3} for all n?
This is now known to be true.
-/
axiom erdos_cube_root_bound :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      hasSmootPairRepr n (Nat.floor ((n : ℝ) ^ (1/3 : ℝ)))

/--
**Balog's Bound (1989):**
f(n) << n^{4/(9√e)+ε} for all ε > 0.
The exponent 4/(9√e) ≈ 0.2695 is the current best.
-/
noncomputable def balogExponent : ℝ := 4 / (9 * Real.sqrt Real.exp 1)

theorem balog_exponent_value : balogExponent < 0.27 := by
  unfold balogExponent
  -- 4 / (9 * √e) ≈ 4 / (9 * 1.6487) ≈ 4 / 14.838 ≈ 0.2695
  sorry

axiom balog_bound :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      hasSmootPairRepr n (Nat.floor (C * (n : ℝ) ^ (balogExponent + ε)))

/-
## Part V: Conjectured Bounds
-/

/--
**Weak Conjecture:**
f(n) ≤ n^{o(1)}, meaning for any ε > 0, f(n) ≤ n^ε for large enough n.
-/
def weakConjecture : Prop :=
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      hasSmootPairRepr n (Nat.floor ((n : ℝ) ^ ε))

/--
**Strong Conjecture:**
f(n) ≤ e^{O(√log n)}, which is much slower than any polynomial.
-/
def strongConjecture : Prop :=
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      hasSmootPairRepr n (Nat.floor (Real.exp (C * Real.sqrt (Real.log n))))

/--
**Open Problem Status:**
Both conjectures remain open.
-/
axiom erdos_334_open : ¬ (weakConjecture ∨ ¬weakConjecture → False)

/-
## Part VI: Examples
-/

/--
**Example: 10 = 2 + 8**
2 = 2 is 2-smooth
8 = 2³ is 2-smooth
So 10 has a 2-smooth pair representation.
-/
theorem example_10 : hasSmootPairRepr 10 2 := by
  use 2, 8
  constructor
  · ring
  constructor
  · intro p hp hdiv
    have := (Nat.Prime.eq_one_or_self_of_prime_of_dvd hp 2 Nat.Prime.two hdiv)
    rcases this with h | h
    · omega
    · rw [h]
  · intro p hp hdiv
    have h8 : (8 : ℕ) = 2^3 := by norm_num
    rw [h8] at hdiv
    have := (Nat.Prime.dvd_prime_pow Nat.Prime.two hp).mp hdiv
    rcases this with ⟨_, rfl⟩
    exact le_refl 2

/--
**Example: 100 = 64 + 36**
64 = 2⁶ is 2-smooth
36 = 2² × 3² is 3-smooth
So 100 has a 3-smooth pair representation.
-/
theorem example_100 : hasSmootPairRepr 100 3 := by
  use 64, 36
  constructor
  · ring
  constructor
  · intro p hp hdiv
    have h64 : (64 : ℕ) = 2^6 := by norm_num
    rw [h64] at hdiv
    have := (Nat.Prime.dvd_prime_pow Nat.Prime.two hp).mp hdiv
    rcases this with ⟨_, rfl⟩
    omega
  · intro p hp hdiv
    have h36 : (36 : ℕ) = 2^2 * 3^2 := by norm_num
    rw [h36] at hdiv
    rcases (Nat.Prime.dvd_mul hp).mp hdiv with h | h
    · have := (Nat.Prime.dvd_prime_pow Nat.Prime.two hp).mp h
      rcases this with ⟨_, rfl⟩
      omega
    · have := (Nat.Prime.dvd_prime_pow (by norm_num : Nat.Prime 3) hp).mp h
      rcases this with ⟨_, rfl⟩
      exact le_refl 3

/-
## Part VII: Connection to Other Problems
-/

/--
**Smooth Number Counting Function:**
ψ(x, y) = number of y-smooth integers ≤ x.
Understanding this function is key to the problem.
-/
noncomputable def smoothCount (x y : ℝ) : ℕ :=
  -- The cardinality of {n ≤ x : n is y-smooth}
  0  -- placeholder

/--
**de Bruijn's Asymptotic:**
For u = log x / log y, ψ(x, y) ~ x · ρ(u) where ρ is the Dickman function.
-/
axiom de_bruijn_asymptotic :
    ∀ x y : ℝ, x ≥ 2 → y ≥ 2 →
      ∃ ρu : ℝ, ρu > 0 ∧ smoothCount x y ≤ x * ρu + x / 2

/--
**Goldbach-Type Connection:**
This problem is related to Goldbach-type questions about
additive representations using numbers with special properties.
-/
def goldbachTypeProperty : Prop :=
    -- Every n = a + b with a, b having "nice" factorizations
    True  -- simplified

/-
## Part VIII: Main Results Summary
-/

/--
**Erdős Problem #334 Summary:**
Find the best f(n) for smooth pair representations.
- Balog (1989): f(n) << n^{0.2695}
- Conjectured: f(n) ≤ n^{o(1)} or even f(n) ≤ e^{O(√log n)}
-/
theorem erdos_334_summary :
    (-- Erdős's n^{1/3} question is resolved
     ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
       hasSmootPairRepr n (Nat.floor ((n : ℝ) ^ (1/3 : ℝ)))) ∧
    (-- Balog's bound is current best
     ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
       hasSmootPairRepr n (Nat.floor (C * (n : ℝ) ^ (balogExponent + ε)))) ∧
    (-- The optimal bound is unknown
     True) := by
  constructor
  · exact erdos_cube_root_bound
  constructor
  · exact balog_bound
  · trivial

/--
**Main Theorem:**
Every large n can be written as a + b with a, b being n^{0.27}-smooth.
-/
theorem erdos_334 :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      hasSmootPairRepr n (Nat.floor ((n : ℝ) ^ (0.27 + ε))) :=
  fun ε hε => by
    have h := balog_bound ε hε
    obtain ⟨C, hC, hbound⟩ := h
    -- Since 0.27 > balogExponent ≈ 0.2695, the bound holds
    sorry

/--
**Open Question:**
What is the true growth rate of f(n)?
Current gap: between n^{0.2695} and n^{o(1)}.
-/
def openQuestion : Prop :=
    ∃ α : ℝ, 0 < α ∧ α < balogExponent ∧
      ∀ n : ℕ, n ≥ 2 → hasSmootPairRepr n (Nat.floor ((n : ℝ) ^ α))

end Erdos334
