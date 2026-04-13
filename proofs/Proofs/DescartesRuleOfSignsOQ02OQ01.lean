/-
# Proving Budan's Upper Bound (OQ-02-OQ-01)

## Research Question

Can the `budan_upper_bound_axiom` from OQ-02 be fully proved in Lean?

## Proof Strategy

The proof proceeds by strong induction on degree(p):

**Base case (deg ≤ 0):** Constant polynomials have no roots, so the bound holds trivially.

**Inductive step:** Assume the bound holds for all polynomials of degree < deg(p).
  1. If p has no roots in (a, b], the bound holds (0 ≤ V_p(a) - V_p(b)).
  2. If p has a root r in (a, b]:
     a. Factor: p(x) = (x - r) · q(x) where deg(q) < deg(p)
     b. By Rolle's theorem: between consecutive roots of p,
        the derivative p' has a root
     c. Apply the inductive hypothesis to p' on sub-intervals
     d. Account for sign changes using the derivative chain

The key technical ingredients are:
- `Rolle's theorem` (from Mathlib: `exists_deriv_eq_zero`)
- The relationship between sign changes of p and p'
- Strong induction on polynomial degree

## Status

SURVEY — proof scaffold with building blocks identified.
Proving the full induction is estimated at 200-400 lines.

Source: Extension of Descartes Rule OQ-02
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

set_option maxHeartbeats 400000

namespace BudanUpperBound

open Polynomial

-- Import definitions from OQ-02
-- (In a real build, these would be imported; here we restate the key ones)

/-- The k-th iterated derivative of a polynomial. -/
noncomputable def iterDeriv (p : ℝ[X]) : ℕ → ℝ[X]
  | 0 => p
  | k + 1 => derivative (iterDeriv p k)

-- ============================================================================
-- § 1. BUILDING BLOCKS: Degree and Derivative Properties
-- ============================================================================

/-- Constant polynomials have no roots. -/
theorem constant_no_roots (p : ℝ[X]) (hp : p.natDegree = 0) (x : ℝ) (hpne : p ≠ 0) :
    p.eval x ≠ 0 := by
  rw [eq_C_of_natDegree_eq_zero hp]
  simp [Polynomial.eval_C]
  intro h
  apply hpne
  rw [eq_C_of_natDegree_eq_zero hp, h, map_zero]

/-- Linear polynomials have at most one root. -/
theorem linear_at_most_one_root (p : ℝ[X]) (hp : p.natDegree = 1) (a b : ℝ) (_hab : a < b) :
    Set.ncard {x : ℝ | a < x ∧ x ≤ b ∧ p.eval x = 0} ≤ 1 := by
  -- A degree-1 polynomial has at most 1 root anywhere, so at most 1 in any interval.
  -- Strategy: show the set is subsingleton (any two elements are equal).
  have hp_ne : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  apply Set.Subsingleton.ncard_le_one
  intro x ⟨_, _, hx⟩ y ⟨_, _, hy⟩
  -- x and y are both roots of p. Since p has degree 1, it has at most 1 root.
  -- Two distinct roots would give card(roots) ≥ 2 > 1 = natDegree, contradiction.
  by_contra hne
  have hx_mem : x ∈ p.roots := (Polynomial.mem_roots hp_ne).mpr hx
  have hy_mem : y ∈ p.roots := (Polynomial.mem_roots hp_ne).mpr hy
  have hcard := Polynomial.card_roots_le_degree p
  -- {x, y} as a multiset has card ≥ 2 since x ≠ y
  have h2 : 2 ≤ (p.roots.toFinset).card := by
    have hx_fs : x ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr hx_mem
    have hy_fs : y ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr hy_mem
    calc 2 = ({x, y} : Finset ℝ).card := by rw [Finset.card_pair hne]
      _ ≤ p.roots.toFinset.card := Finset.card_le_card (by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption)
  have h3 : p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le_card _
  rw [hp] at hcard; omega

/-- Rolle's theorem for polynomials: if p has roots at r₁ < r₂,
    then p' has a root in (r₁, r₂).
    Proved from Mathlib's `exists_deriv_eq_zero`. -/
theorem rolle_polynomial (p : ℝ[X]) (r₁ r₂ : ℝ) (hr : r₁ < r₂)
    (h₁ : p.eval r₁ = 0) (h₂ : p.eval r₂ = 0) :
    ∃ c, r₁ < c ∧ c < r₂ ∧ (derivative p).eval c = 0 := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc r₁ r₂) :=
    p.continuous.continuousOn
  have heq : p.eval r₁ = p.eval r₂ := h₁.trans h₂.symm
  obtain ⟨c, ⟨hac, hcb⟩, hderiv⟩ := exists_deriv_eq_zero hr hcont heq
  exact ⟨c, hac, hcb, by simp only [Polynomial.deriv] at hderiv; exact hderiv⟩

-- ============================================================================
-- § 2. SIGN CHANGE PROPERTIES
-- ============================================================================

/-- When a polynomial changes sign between a and b, it has a root in (a, b).
    Proved from the intermediate value theorem for continuous functions. -/
theorem root_of_sign_change (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c, a < c ∧ c < b ∧ p.eval c = 0 := by
  have hcont : Continuous (fun x => p.eval x) := p.continuous
  -- IVT: there exists c in [a,b] with p.eval c = 0
  have := intermediate_value_Icc (le_of_lt hab) hcont.continuousOn
  -- p.eval a < 0 < p.eval b, so 0 is in the range on [a,b]
  have h0_mem : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) := by
    constructor <;> linarith
  obtain ⟨c, ⟨hca, hcb⟩, hc⟩ := this h0_mem
  -- c ∈ [a, b] and p.eval c = 0. Need c ∈ (a, b).
  have hca' : a < c := by
    rcases eq_or_lt_of_le hca with rfl | h
    · linarith -- p.eval a < 0 but p.eval c = 0
    · exact h
  have hcb' : c < b := by
    rcases eq_or_lt_of_le hcb with rfl | h
    · linarith -- p.eval b > 0 but p.eval c = 0
    · exact h
  exact ⟨c, hca', hcb', hc⟩

/-- Removing a root factor reduces sign changes.
    If p(r) = 0 and p = (x - r) · q, then the sign changes of q at r
    relate to those of p. -/
/- sign_changes_factor: if p = (x - r) · q with p(r) = 0, then
    the sign changes of q at r relate appropriately to those of p. -/

-- ============================================================================
-- § 3. THE INDUCTION FRAMEWORK
-- ============================================================================

/- **Key Lemma** (inductive_step_derivative): for the inductive step, if r₁ < r₂
    are consecutive roots of p in (a, b], then p' has at least one root in (r₁, r₂)
    by Rolle, and the budanCount for p' accounts for roots correctly.
    (Full formalization needs budanCount definition.) -/

-- ============================================================================
-- § 4. WHAT REMAINS
-- ============================================================================

/-
## Proof Completion Roadmap

### Step 1: Formalize the sign-change counting
- Need to connect `budanCount` from OQ-02 with the derivative sequence
- Show how factoring out a root affects sign changes
- **Estimated**: 80-120 lines

### Step 2: Base cases (degree 0 and 1)
- Degree 0: constant, no roots → bound trivially holds
- Degree 1: linear, at most one root → bound holds by direct computation
- **Estimated**: 40-60 lines

### Step 3: Inductive step via Rolle
- Apply Rolle's theorem between consecutive roots
- Use IH on the derivative p' for sub-intervals
- Account for sign changes across the root factoring
- **Estimated**: 100-200 lines

### Step 4: Assembly
- Combine base cases and inductive step with strong induction
- **Estimated**: 20-30 lines

### Total: 240-410 lines

### Key Dependencies:
1. `exists_deriv_eq_zero` (Rolle's theorem from Mathlib)
2. IVT for polynomials (from Mathlib's `Polynomial.isRoot_of_...` or IVT)
3. `Polynomial.natDegree_derivative_le` (from Mathlib)
4. The sign-change counting infrastructure from OQ-02

### Recommended Approach:
Start with the base cases (easiest), then rolle_polynomial (using Mathlib),
then the sign-change accounting (hardest), then assembly.
-/

end BudanUpperBound
