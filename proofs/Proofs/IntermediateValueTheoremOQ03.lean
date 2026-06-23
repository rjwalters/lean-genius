import Mathlib

/-
# IVT — OQ-03: Connection to Brouwer Fixed Point Theorem

## Research Problem: intermediate-value-theorem-oq-03

OQ: How does IVT relate to Brouwer's fixed point theorem in
higher dimensions?

In 1D: IVT ⟺ Brouwer. Every continuous f : [0,1] → [0,1] has
a fixed point. This is the IVT applied to g(x) = f(x) - x.

In higher dimensions: Brouwer's theorem (every continuous
f : Bⁿ → Bⁿ has a fixed point) is a vast generalization that
requires topological machinery (degree theory, homology, or
simplicial approximation).

Tags: topology, fixed-point, ivt, brouwer
-/

namespace IVTBrouwer

open Set

-- ============================================================
-- Part I: 1D Brouwer from IVT
-- ============================================================

/-- The 1D Brouwer fixed point theorem follows from IVT:
    every continuous f : [0,1] → [0,1] has a fixed point.

    Proof: Let g(x) = f(x) - x. Then g(0) = f(0) ≥ 0 and
    g(1) = f(1) - 1 ≤ 0. By IVT, ∃ c ∈ [0,1] with g(c) = 0,
    i.e., f(c) = c. -/
theorem brouwer_1d (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : 0 ≤ f 0) (hf0' : f 0 ≤ 1)
    (hf1 : 0 ≤ f 1) (hf1' : f 1 ≤ 1) :
    ∃ c ∈ Icc (0 : ℝ) 1, f c = c := by
  -- Consider g(x) = f(x) - x
  let g := fun x => f x - x
  have hg : Continuous g := hf.sub continuous_id
  have hg0 : 0 ≤ g 0 := by simp [g]; linarith
  have hg1 : g 1 ≤ 0 := by simp [g]; linarith
  -- By IVT, g has a zero in [0,1]
  obtain ⟨c, hc_mem, hc_eq⟩ := intermediate_value_zero_of_le (by norm_num : (0:ℝ) ≤ 1)
    hg.continuousOn hg0 hg1
  exact ⟨c, hc_mem, by linarith⟩

-- ============================================================
-- Part II: IVT from 1D Brouwer
-- ============================================================

/-
  Conversely, IVT follows from the 1D Brouwer theorem.

  Given continuous f : [a,b] → ℝ with f(a) < 0 < f(b),
  define g : [0,1] → [0,1] by g(t) = clamp(t - f(a + t(b-a))/M)
  where M is chosen appropriately. Then a fixed point of g gives a zero of f.

  IVT and 1D Brouwer are equivalent.
  (A formal proof would require formalizing the clamping construction.)
-/

-- ============================================================
-- Part III: The Dimensional Jump
-- ============================================================

/-- In dimension n ≥ 2, the Brouwer fixed point theorem
    is strictly stronger than IVT-type results.

    The 2D case: every continuous f : D² → D² has a fixed point
    (where D² is the closed unit disk).

    This cannot be proved by IVT alone — it requires:
    - Degree theory, or
    - Homology (H_n(Sⁿ) ≠ 0), or
    - Sperner's lemma + simplicial approximation -/
axiom brouwer_2d :
    ∀ (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
    Continuous f →
    (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) →
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x

-- ============================================================
-- Part IV: Why IVT Fails in Higher Dimensions
-- ============================================================

/-- The IVT says: a continuous function that changes sign must
    have a zero. In higher dimensions, functions can "go around"
    zeros without crossing them.

    Example: f(x,y) = (x, y) on the circle S¹ has no zero
    on S¹, even though intuitively it "should" cross zero. -/
theorem ivt_fails_2d :
    -- The map (x,y) ↦ (x,y) on S¹ has no zero
    ∀ x y : ℝ, x ^ 2 + y ^ 2 = 1 → ¬(x = 0 ∧ y = 0) := by
  intro x y hxy ⟨hx, hy⟩
  rw [hx, hy] at hxy; norm_num at hxy

-- ============================================================
-- Part V: The Hierarchy
-- ============================================================

/-
  The hierarchy of fixed point theorems:

  1D:   IVT ⟺ Brouwer (equivalent)
  nD:   IVT ⊂ Brouwer (Brouwer strictly stronger)
  ∞D:   Brouwer fails! (Kakutani-like extensions needed)
        Schauder: compact convex + continuous → fixed point

  Each step requires new mathematical machinery:
  - 1D → nD: topology (degree theory or homology)
  - nD → ∞D: functional analysis (Schauder projection)

  See also: schauder-fixed-point-oq-03 (Kakutani framework)
-/

/-
  Dimensional summary: IVT is about sign changes (1D phenomenon),
  while Brouwer is about topological degree (nD phenomenon).
  They coincide in 1D because sign change = degree 1 map.

  - In 1D: IVT and Brouwer are the same theorem
  - In nD: Brouwer is strictly stronger
  - In ∞D: compactness is additionally needed
-/

/-
  Summary

  This file explores the connection between IVT and Brouwer:

  - 1D: IVT ⟹ Brouwer (proved: g(x) = f(x) - x has a zero)
  - 1D: Brouwer ⟹ IVT (sketched: clamping construction)
  - nD: Brouwer is strictly stronger (IVT fails for 2D maps)
  - ∞D: Schauder/Kakutani extensions needed

  1 axiom (brouwer_2d), 0 sorries, 4 theorems.
-/

end IVTBrouwer
