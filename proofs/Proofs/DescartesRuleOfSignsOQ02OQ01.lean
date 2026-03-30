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

-- ============================================================================
-- § 3. BUDAN-FOURIER SIGN VARIATION COUNT
-- ============================================================================

/-- Count adjacent sign differences in a list of ±1 values. -/
def countAdjacentDiffs : List ℤ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (if a ≠ b then 1 else 0) + countAdjacentDiffs (b :: rest)

/-- Count sign changes in a list of reals, ignoring zeros. -/
noncomputable def signChangesInList (l : List ℝ) : ℕ :=
  let nonzero := l.filter (· ≠ 0)
  let signs := nonzero.map (fun x => if x > 0 then (1 : ℤ) else -1)
  countAdjacentDiffs signs

/-- Sign changes in a singleton list is always 0. -/
private theorem signChangesInList_singleton (v : ℝ) :
    signChangesInList [v] = 0 := by
  unfold signChangesInList
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp [countAdjacentDiffs]

/-- The Budan-Fourier evaluation sequence at point x:
    [p(x), p'(x), ..., p⁽ⁿ⁾(x)]. -/
noncomputable def budanSequence (p : ℝ[X]) (n : ℕ) (x : ℝ) : List ℝ :=
  (List.range (n + 1)).map (fun k => (iterDeriv p k).eval x)

/-- The Budan-Fourier sign variation count V_p(x). -/
noncomputable def budanCount (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChangesInList (budanSequence p p.natDegree x)

-- ============================================================================
-- § 4. ROOT COUNTING IN INTERVALS
-- ============================================================================

/-- Count of roots of p in (a, b], with multiplicity. -/
noncomputable def rootsInInterval (p : ℝ[X]) (a b : ℝ) : ℕ :=
  if p = 0 then 0
  else Multiset.card (p.roots.filter (fun r => a < r ∧ r ≤ b))

-- ============================================================================
-- § 5. BASE CASES
-- ============================================================================

/-- A nonzero degree-0 polynomial has 0 roots in any interval. -/
private theorem rootsInInterval_deg_zero (p : ℝ[X]) (hp : p ≠ 0)
    (hdeg : p.natDegree = 0) (a b : ℝ) :
    rootsInInterval p a b = 0 := by
  simp only [rootsInInterval, hp, ↓reduceIte, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  exfalso
  exact constant_no_roots p hdeg r hp ((Polynomial.mem_roots hp).mp hr)

/-- A polynomial with natDegree 0 has budanCount 0 at any point. -/
private theorem budanCount_deg_zero (p : ℝ[X]) (hdeg : p.natDegree = 0) (x : ℝ) :
    budanCount p x = 0 := by
  unfold budanCount budanSequence
  rw [hdeg]
  simp only [List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, show iterDeriv p 0 = p from rfl]
  exact signChangesInList_singleton (p.eval x)

/-- **Base case (deg = 0)**: Constant polynomials satisfy Budan's upper bound.
    rootsInInterval = 0 and budanCount = 0, so 0 ≤ 0 - 0. -/
theorem budan_upper_bound_deg0 (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (_hab : a < b)
    (hdeg : p.natDegree = 0) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
  rw [rootsInInterval_deg_zero p hp hdeg, budanCount_deg_zero p hdeg]; omega

-- ============================================================================
-- § 6. BUDAN'S UPPER BOUND — MAIN THEOREM
-- ============================================================================

/-- **Budan's Theorem (Upper Bound)**

The number of roots of p in (a, b], counted with multiplicity, is at most
V_p(a) - V_p(b), where V_p(x) counts sign changes in the Budan-Fourier
derivative sequence [p(x), p'(x), ..., p⁽ⁿ⁾(x)].

**Proof**: Induction on deg(p).
- **Base (deg = 0)**: Proved — constant nonzero polynomials have no roots.
- **Inductive step (deg ≥ 1)**: Uses Rolle's theorem between consecutive
  roots of p, applies IH to derivative p' (lower degree), and accounts
  for sign changes across the derivative chain.

**Status**: Base case fully proved. Inductive step needs sign-change
accounting lemma relating V_p(x) to V_{p'}(x) and root decomposition.
Estimated 150-250 additional lines. Building blocks (Rolle, IVT, linear
root bound) are ready in §1-§2 above. -/
theorem budan_upper_bound (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
  -- Induction on degree. IH applies to derivative (lower degree).
  suffices h : ∀ n (q : ℝ[X]), q ≠ 0 → q.natDegree ≤ n →
      ∀ a b : ℝ, a < b →
      rootsInInterval q a b ≤ budanCount q a - budanCount q b from
    h p.natDegree p hp le_rfl a b hab
  intro n
  induction n with
  | zero =>
    intro q hq hdeg a' b' hab'
    exact budan_upper_bound_deg0 q hq a' b' hab' (Nat.le_zero.mp hdeg)
  | succ n ih =>
    intro q hq hdeg a' b' hab'
    by_cases h0 : q.natDegree = 0
    · exact budan_upper_bound_deg0 q hq a' b' hab' h0
    · -- q has degree 1..n+1. The derivative q' has degree ≤ n.
      -- By IH: rootsInInterval q' a' b' ≤ budanCount q' a' - budanCount q' b'
      -- Remaining work:
      --   1. Relate budanCount q x to budanCount (derivative q) x
      --   2. Apply Rolle to get root count relationship
      --   3. Combine sign-change and root-count bounds
      sorry

/-
## Remaining Work for the Inductive Step

### Key lemmas needed (estimated 150-250 lines total):

1. **V_p vs V_{p'} relationship** (~60-100 lines):
   budanCount p x = budanCount (derivative p) x + ε(x)
   where ε(x) ∈ {0, 1} depends on signs of p(x) and p'(x).

2. **Root decomposition via Rolle** (~40-60 lines):
   If p has k roots in (a,b], then p' has ≥ k-1 roots in (a,b].
   Therefore: rootsInInterval p a b ≤ rootsInInterval (derivative p) a b + 1.

3. **Sign-change bookkeeping at endpoints** (~30-50 lines):
   Track ε(a) - ε(b) across the interval to close the bound.

4. **Assembly** (~20-40 lines):
   Combine: rootsInInterval p ≤ rootsInInterval p' + 1
                              ≤ (budanCount p' a - budanCount p' b) + 1
                              ≤ budanCount p a - budanCount p b

### Building blocks available (§1-§2):
- rolle_polynomial: Between two roots of p, p' has a root
- root_of_sign_change: IVT — sign change implies root
- linear_at_most_one_root: Degree-1 has ≤ 1 root in interval
- constant_no_roots: Degree-0 has no roots
-/

end BudanUpperBound
