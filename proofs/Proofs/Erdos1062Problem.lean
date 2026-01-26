/-!
# Erdős Problem #1062: Maximum "No Divides Two Others" Sets

Let f(n) be the maximum size of A ⊆ {1,…,n} such that no element
divides two distinct others. How large is f(n)? Is lim f(n)/n irrational?

## Status: OPEN

## References
- Guy (2004), Problem B24
- Lebensold (1976), bounds 0.6725n ≤ f(n) ≤ 0.6736n
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section I: The Divisibility Condition
-/

/-- A set A has the "no divides two others" property if no element
divides two distinct other elements. Equivalently, each element
has at most one proper multiple in A. -/
def NoDividesTwoOthers (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ∣ b → a ∣ c → a ≠ b → a ≠ c → b ≠ c → False

/-!
## Section II: The Extremal Function
-/

/-- f(n): the maximum size of a subset of {1,…,n} satisfying
the "no divides two others" property. -/
noncomputable def maxNDTOSize (n : ℕ) : ℕ :=
  Finset.sup
    ((Finset.Icc 1 n).powerset.filter (fun A => NoDividesTwoOthers A))
    Finset.card

/-!
## Section III: Lower Bound Construction
-/

/-- The interval [m+1, 3m+2] has no element dividing two others,
since the ratio max/min < 3, so each element has at most one
multiple in the range. This gives f(n) ≥ ⌈2n/3⌉. -/
axiom lower_bound_construction (n : ℕ) (hn : n ≥ 3) :
  maxNDTOSize n ≥ (2 * n + 2) / 3

/-!
## Section IV: Lebensold's Bounds
-/

/-- Lebensold (1976): for large n, f(n) ≥ 0.6725n. -/
axiom lebensold_lower_bound :
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    (maxNDTOSize n : ℝ) ≥ 0.6725 * n

/-- Lebensold (1976): for large n, f(n) ≤ 0.6736n. -/
axiom lebensold_upper_bound :
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    (maxNDTOSize n : ℝ) ≤ 0.6736 * n

/-!
## Section V: The Conjectures
-/

/-- The limiting density lim f(n)/n exists and lies in [0.6725, 0.6736]. -/
axiom limiting_density_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (maxNDTOSize n : ℝ) / n)
    Filter.atTop (nhds L) ∧
    0.6725 ≤ L ∧ L ≤ 0.6736

/-- **Erdős Problem #1062**: Is the limiting density irrational? -/
def ErdosProblem1062 : Prop :=
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (maxNDTOSize n : ℝ) / n)
    Filter.atTop (nhds L) ∧
    Irrational L

/-!
## Section VI: Comparison with Primitive Sets
-/

/-- A primitive set has no element dividing any other. This is strictly
stronger than NoDividesTwoOthers. -/
def IsPrimitiveFinset (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → ¬(a ∣ b)

/-- Every primitive set satisfies "no divides two others". -/
theorem primitive_implies_ndto (A : Finset ℕ) :
    IsPrimitiveFinset A → NoDividesTwoOthers A := by
  intro hprim a b c ha hb hc hab _ hab' _ _
  exact hprim a b ha hb hab' hab

/-- The "no divides two others" condition is strictly weaker:
{2, 6, 9} satisfies it (2 divides only 6, not 9) but is not
primitive (since 2 ∣ 6). -/
axiom ndto_strictly_weaker :
  NoDividesTwoOthers ({2, 6, 9} : Finset ℕ) ∧
    ¬IsPrimitiveFinset ({2, 6, 9} : Finset ℕ)
