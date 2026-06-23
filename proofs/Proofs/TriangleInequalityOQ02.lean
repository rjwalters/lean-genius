/-
# Ultrametric Triangle Inequality in p-adic Analysis (OQ-02)

The p-adic numbers ℚ_[p] satisfy the **ultrametric (strong) triangle inequality**:

  ‖q + r‖_p ≤ max(‖q‖_p, ‖r‖_p)

This is much stronger than the ordinary triangle inequality ‖q + r‖ ≤ ‖q‖ + ‖r‖,
and implies a beautiful equality when the norms differ:

  ‖q‖_p ≠ ‖r‖_p  →  ‖q + r‖_p = max(‖q‖_p, ‖r‖_p)

This OQ proves the ultrametric inequality and its equality case for:
- `ℚ_[p]` (the p-adic completion of ℚ)
- `ℤ_[p]` (the p-adic integers)
- The p-adic norm `padicNorm p` on ℚ (the precursor)

and shows these follow from the properties of the p-adic valuation.

**Status**: Complete — 0 sorries, 0 axioms
**Extends**: TriangleInequalityOQ03.lean (abstract ultrametric spaces)
-/

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

namespace TriangleInequalityOQ02

-- ══════════════════════════════════════════════════════════════════
-- § Part I: The p-adic Norm on ℚ
-- ══════════════════════════════════════════════════════════════════

/-
The p-adic norm `padicNorm p : ℚ → ℚ` is defined via the p-adic valuation:
  padicNorm p q = p^(-padicValRat p q)  if q ≠ 0
  padicNorm p 0 = 0

The ultrametric inequality for this norm follows from the key property of
p-adic valuations: v_p(q + r) ≥ min(v_p(q), v_p(r)) for q + r ≠ 0.
-/

/-- The ultrametric (strong) triangle inequality for the p-adic norm on ℚ.
    This is the foundational form from which all others follow. -/
theorem padicNorm_ultrametric (p : ℕ) [Fact (Nat.Prime p)] (q r : ℚ) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  padicNorm.nonarchimedean

/-- **Equality case**: when the p-adic norms differ, the norm of the sum
    equals the larger of the two. This is the surprising "isosceles triangle"
    phenomenon: in p-adic geometry, no triangle is scalene. -/
theorem padicNorm_add_eq_max_of_ne (p : ℕ) [Fact (Nat.Prime p)] {q r : ℚ}
    (h : padicNorm p q ≠ padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) :=
  padicNorm.add_eq_max_of_ne h

/-- The p-adic norm of a difference satisfies the same ultrametric inequality.
    Note: padicNorm p (-r) = padicNorm p r, so subtraction is not "worse" than addition. -/
theorem padicNorm_sub_ultrametric (p : ℕ) [Fact (Nat.Prime p)] (q r : ℚ) :
    padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) :=
  padicNorm.sub

-- ══════════════════════════════════════════════════════════════════
-- § Part II: The p-adic Field ℚ_[p]
-- ══════════════════════════════════════════════════════════════════

/-
`ℚ_[p]` is the completion of ℚ under the p-adic norm. Its norm ‖·‖
extends the p-adic norm and satisfies the same ultrametric inequality.
-/

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The ultrametric inequality for the completed p-adic field ℚ_[p]. -/
theorem padic_ultrametric (q r : ℚ_[p]) :
    ‖q + r‖ ≤ max ‖q‖ ‖r‖ :=
  Padic.nonarchimedean q r

/-- **The equality case for ℚ_[p]**: if the norms of q and r differ, then
    the norm of q + r equals the maximum. This is the p-adic "isosceles" property. -/
theorem padic_add_eq_max_of_ne {q r : ℚ_[p]} (h : ‖q‖ ≠ ‖r‖) :
    ‖q + r‖ = max ‖q‖ ‖r‖ :=
  Padic.add_eq_max_of_ne h

/-- **First consequence**: if ‖q‖ < ‖r‖, then ‖q + r‖ = ‖r‖.
    The sum is dominated by the element with larger p-adic norm. -/
theorem padic_add_norm_of_lt {q r : ℚ_[p]} (h : ‖q‖ < ‖r‖) :
    ‖q + r‖ = ‖r‖ := by
  have hne : ‖q‖ ≠ ‖r‖ := h.ne
  rw [padic_add_eq_max_of_ne hne, max_eq_right h.le]

/-- **Symmetry**: if ‖q‖ > ‖r‖, then ‖q + r‖ = ‖q‖.
    Equivalently: ‖q + r‖ always equals the larger of the two norms (when they differ). -/
theorem padic_add_norm_of_gt {q r : ℚ_[p]} (h : ‖r‖ < ‖q‖) :
    ‖q + r‖ = ‖q‖ := by
  have hne : ‖q‖ ≠ ‖r‖ := h.ne'
  rw [padic_add_eq_max_of_ne hne, max_eq_left h.le]

-- ══════════════════════════════════════════════════════════════════
-- § Part III: The p-adic Integers ℤ_[p]
-- ══════════════════════════════════════════════════════════════════

/-
ℤ_[p] = {x : ℚ_[p] | ‖x‖ ≤ 1} is a subring closed under the ultrametric.
The ultrametric inequality holds here too, and ‖n‖ ≤ 1 for all n ∈ ℤ
(integers are "small" in the p-adic metric).
-/

/-- The ultrametric inequality for the p-adic integers ℤ_[p]. -/
theorem padicInt_ultrametric (q r : ℤ_[p]) :
    ‖q + r‖ ≤ max ‖q‖ ‖r‖ :=
  PadicInt.nonarchimedean q r

/-- The p-adic integers are exactly the elements with ‖x‖ ≤ 1. -/
theorem padicInt_norm_le_one (x : ℤ_[p]) : ‖x‖ ≤ 1 :=
  x.norm_le_one

/-- For rational integers, the p-adic norm is at most 1. This reflects that
    large numbers (in the Archimedean sense) are "small" p-adically. -/
theorem rational_int_norm_le_one (n : ℤ) : padicNorm p (n : ℚ) ≤ 1 :=
  padicNorm.of_int n

-- ══════════════════════════════════════════════════════════════════
-- § Part IV: Telescoping and Applications
-- ══════════════════════════════════════════════════════════════════

/-
The ultrametric inequality has remarkable cascading properties.
Iterating: ‖q₁ + q₂ + ... + qₙ‖ ≤ max_i ‖qᵢ‖.
-/

/-- Ultrametric inequality for a sum of three elements. -/
theorem padic_ultrametric_three (q r s : ℚ_[p]) :
    ‖q + r + s‖ ≤ max (max ‖q‖ ‖r‖) ‖s‖ :=
  (padic_ultrametric (q + r) s).trans (by
    apply max_le_max_right
    exact padic_ultrametric q r)

/-- The p-adic norm of a subtraction: the norm of q - r is at most max(‖q‖, ‖r‖).
    This makes the ultrametric inequality symmetric: going from q to r is as
    "easy" as going from r to q. -/
theorem padic_sub_ultrametric (q r : ℚ_[p]) :
    ‖q - r‖ ≤ max ‖q‖ ‖r‖ :=
  calc ‖q - r‖ = ‖q + (-r)‖ := by rw [sub_eq_add_neg]
    _ ≤ max ‖q‖ ‖-r‖ := padic_ultrametric q (-r)
    _ = max ‖q‖ ‖r‖ := by rw [norm_neg]

/-- The p-adic norm is an ultrametric: d(x, z) ≤ max(d(x, y), d(y, z)).
    This expresses the strong triangle inequality in metric space terms. -/
theorem padic_dist_ultrametric (x y z : ℚ_[p]) :
    dist x z ≤ max (dist x y) (dist y z) := by
  simp only [dist_eq_norm]
  calc ‖x - z‖ = ‖(x - y) + (y - z)‖ := by ring_nf
    _ ≤ max ‖x - y‖ ‖y - z‖ := padic_ultrametric _ _

-- ══════════════════════════════════════════════════════════════════
-- § Part V: The Valuation Perspective
-- ══════════════════════════════════════════════════════════════════

/-
The ultrametric inequality is equivalent to the **ultrametric valuation property**:

  v_p(q + r) ≥ min(v_p(q), v_p(r))

where v_p is the p-adic valuation (number of times p divides q).
Since padicNorm p q = p^(-v_p(q)), the inequality reverses:
a larger valuation means a smaller norm.
-/

/-- The p-adic valuation on ℚ satisfies the ultrametric property:
    v_p(q + r) ≥ min(v_p(q), v_p(r)) when q + r ≠ 0.
    This is the algebraic foundation for the norm ultrametric inequality. -/
theorem padicValRat_ultrametric (q r : ℚ) (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  padicValRat.min_le_padicValRat_add hqr

/-
## Why the Ultrametric Holds

The ultrametric property for p-adic norms follows from the valuation:

1. v_p(m + n) ≥ min(v_p(m), v_p(n))  [carries don't decrease the valuation]
2. padicNorm p q = p^(-v_p(q))          [norm is exponential of negated valuation]
3. p^(-v) decreasing in v               [so ‖q + r‖ = p^(-v_p(q+r)) ≤ p^(-min(v_p(q),v_p(r)))]
4. p^(-min(a,b)) = max(p^(-a), p^(-b)) [min of valuation ↔ max of norm]

Step 1 is the key arithmetic fact: when you add numbers with the same prime factor,
the sum has at least as many factors of p as each summand.
-/

end TriangleInequalityOQ02
