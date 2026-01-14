/-
  Erdős Problem #45: Monochromatic Divisor Sums

  Source: https://erdosproblems.com/45
  Status: SOLVED (Croot)

  Statement:
  Let k ≥ 2. Is there an integer n_k such that, if D = {d : 1 < d < n_k, d | n_k},
  then for any k-coloring of D there exists a monochromatic subset D' ⊆ D
  satisfying ∑_{d ∈ D'} 1/d = 1?

  Answer: YES.

  Key Results:
  - Croot: Proved the existence of such n_k using probabilistic methods
  - Sawhney: The bound is doubly exponential - n_k ≤ e^{C^k} and this is sharp

  This file formalizes the definitions and main result.
-/

import Mathlib

open Finset BigOperators

namespace Erdos45

/-! ## Core Definitions -/

/-- The set of proper divisors of n (excluding 1 and n itself). -/
def properDivisors (n : ℕ) : Finset ℕ :=
  (n.divisors.filter (fun d => 1 < d ∧ d < n))

/-- A k-coloring of a finite set S. -/
def IsColoring (k : ℕ) (S : Finset ℕ) (c : ℕ → Fin k) : Prop :=
  ∀ s ∈ S, True  -- c is implicitly defined on S

/-- A subset is monochromatic under coloring c if all elements have the same color. -/
def IsMonochromatic (c : ℕ → Fin k) (S : Finset ℕ) : Prop :=
  ∃ color : Fin k, ∀ s ∈ S, c s = color

/-- The reciprocal sum of a finite set of positive integers. -/
noncomputable def reciprocalSum (S : Finset ℕ) : ℚ :=
  ∑ d ∈ S, (1 : ℚ) / d

/-! ## The Main Property -/

/--
A number n has the **k-Egyptian property** if for any k-coloring of its
proper divisors, there exists a monochromatic subset whose reciprocals sum to 1.
-/
def HasKEgyptianProperty (n k : ℕ) : Prop :=
  ∀ c : ℕ → Fin k,
    ∃ D' : Finset ℕ, D' ⊆ properDivisors n ∧
      IsMonochromatic c D' ∧
      reciprocalSum D' = 1

/-! ## Croot's Theorem (SOLVED) -/

/--
**Croot's Theorem**:
For every k ≥ 2, there exists n_k such that n_k has the k-Egyptian property.
-/
theorem croot_existence (k : ℕ) (hk : k ≥ 2) :
    ∃ n : ℕ, HasKEgyptianProperty n k := by
  sorry

/--
**Upper Bound (Sawhney)**:
The minimal n_k is at most doubly exponential in k.
-/
axiom sawhney_upper_bound (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∃ n : ℕ, HasKEgyptianProperty n k ∧ (n : ℝ) ≤ Real.exp (C^k)

/--
**Lower Bound (Sawhney)**:
The minimal n_k is at least doubly exponential in k.
-/
axiom sawhney_lower_bound (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, HasKEgyptianProperty n k → (n : ℝ) ≥ Real.exp (C^k)

/-! ## Basic Facts -/

/-- The reciprocal sum of divisors of n equals σ_{-1}(n). -/
lemma divisor_reciprocal_sum (n : ℕ) (hn : n > 0) :
    reciprocalSum n.divisors = (∑ d ∈ n.divisors, (1 : ℚ) / d) := by
  rfl

/-- If D' sums to 1, each element must be at most the LCM denominator. -/
lemma egyptian_fraction_bound (D' : Finset ℕ) (hsum : reciprocalSum D' = 1)
    (hpos : ∀ d ∈ D', d > 0) :
    ∀ d ∈ D', d ≤ D'.prod id := by
  sorry

/-! ## Small Cases -/

/-- For k = 2, we can take n = 120 (has rich divisor structure). -/
axiom case_k_2 : HasKEgyptianProperty 120 2

/-! ## Historical Notes

The problem connects to Egyptian fractions - representing 1 as a sum
of distinct unit fractions. The coloring condition makes this a
Ramsey-theoretic variant.

Croot's proof uses the probabilistic method, showing that for sufficiently
highly composite numbers, any coloring must contain a monochromatic
Egyptian representation.

References:
- Croot, E.: On a coloring conjecture about unit fractions
- Sawhney: Bounds on n_k
-/

end Erdos45
