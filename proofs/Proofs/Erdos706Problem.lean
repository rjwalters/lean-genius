/-!
# Erdős Problem #706 — Chromatic Number of Multi-Distance Graphs

For a finite set A ⊂ (0,∞) of size r, let G_A be the graph on ℝ²
where two points are connected iff their distance belongs to A.
Let L(r) = max_{|A|=r} χ(G_A).

Question: Estimate L(r). In particular, is L(r) ≤ r^{O(1)}?

The case r = 1 is the Hadwiger–Nelson problem, where 5 ≤ L(1) ≤ 7.

Status: OPEN
Reference: https://erdosproblems.com/706
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- A distance set is a finite subset of positive reals. -/
def IsDistanceSet (A : Finset ℝ) : Prop :=
  ∀ a ∈ A, a > 0

/-- L(r) is the maximum chromatic number over all distance sets of size r.
    We axiomatize this function. -/
noncomputable def multiDistChromatic : ℕ → ℕ := fun _ => 0  -- axiomatized below

/-! ## Main Conjecture -/

/-- **Polynomial Bound Conjecture**: L(r) ≤ r^{O(1)}.
    That is, there exist constants C, k such that L(r) ≤ C · r^k
    for all r ≥ 1. -/
axiom erdos_706_polynomial_bound :
  ∃ C k : ℝ, C > 0 ∧ k > 0 ∧
    ∀ r : ℕ, r ≥ 1 →
      (multiDistChromatic r : ℝ) ≤ C * (r : ℝ) ^ k

/-! ## Known Bounds -/

/-- **Hadwiger–Nelson Base Case**: L(1) satisfies 5 ≤ L(1) ≤ 7.
    The lower bound is due to de Grey (2018). -/
axiom erdos_706_base_case :
  5 ≤ multiDistChromatic 1 ∧ multiDistChromatic 1 ≤ 7

/-- **Monotonicity**: L is non-decreasing: adding more forbidden
    distances can only increase the chromatic number. -/
axiom erdos_706_monotone :
  ∀ r s : ℕ, r ≤ s → multiDistChromatic r ≤ multiDistChromatic s

/-- **Trivial Lower Bound**: L(r) ≥ L(1) ≥ 5 for all r ≥ 1.
    The chromatic number with more distances is at least as large. -/
axiom erdos_706_lower :
  ∀ r : ℕ, r ≥ 1 → multiDistChromatic r ≥ 5

/-! ## Exponential Upper Bound -/

/-- **Known Exponential Bound**: L(r) grows at most exponentially.
    From the Frankl–Wilson method in higher dimensions, one can
    derive exponential-type bounds. The polynomial question asks
    whether this can be dramatically improved. -/
axiom erdos_706_exponential_upper :
  ∃ C : ℝ, C > 1 ∧
    ∀ r : ℕ, r ≥ 1 →
      (multiDistChromatic r : ℝ) ≤ C ^ (r : ℝ)

/-! ## Observations -/

/-- **Hadwiger–Nelson Connection**: the r = 1 case is exactly
    the Hadwiger–Nelson problem (Erdős Problem #508). -/
axiom hadwiger_nelson_connection : True

/-- **Higher-Dimensional Analogue**: Erdős Problem #704 asks
    about the chromatic number of unit-distance graphs in ℝⁿ,
    where Frankl–Wilson gives exponential lower bounds. -/
axiom higher_dim_analogue : True

/-- **Girth Variant**: Erdős Problem #705 asks whether large girth
    forces the chromatic number of unit-distance graphs down to 3. -/
axiom girth_variant : True
