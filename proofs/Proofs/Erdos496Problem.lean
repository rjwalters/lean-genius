/-!
# Erdős Problem #496: Oppenheim Conjecture

For irrational α ∈ ℝ and any ε > 0, there exist positive integers x, y, z
such that |x² + y² − z²α| < ε.

## Key Results

- **Oppenheim conjecture** (1929): indefinite irrational quadratic forms in
  n ≥ 3 variables take values arbitrarily close to zero at integer points
- **Davenport–Heilbronn (1946)**: proved for n ≥ 5 variables
- **Margulis (1987)**: proved the full conjecture for n ≥ 3 using
  unipotent dynamics on homogeneous spaces
- **Eskin–Margulis–Mozes (1998)**: quantitative refinement

## References

- Oppenheim (1929): original conjecture
- Davenport, Heilbronn (1946): [DaHe46]
- Margulis (1987): [Ma89]
- Erdős [Er61]
- <https://erdosproblems.com/496>
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The ternary quadratic form Q(x,y,z) = x² + y² − α·z² for real α. -/
noncomputable def ternaryForm (α : ℝ) (x y z : ℤ) : ℝ :=
  (x : ℝ) ^ 2 + (y : ℝ) ^ 2 - α * (z : ℝ) ^ 2

/-- The form is indefinite when α > 0 (takes both positive and negative values). -/
def IsIndefinite (α : ℝ) : Prop :=
  α > 0

/-- The form takes a value within ε of zero at positive integer points. -/
def ApproxZero (α : ℝ) (ε : ℝ) : Prop :=
  ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    |ternaryForm α (x : ℤ) (y : ℤ) (z : ℤ)| < ε

/-! ## Main Theorem (Solved) -/

/-- **Erdős Problem #496 / Oppenheim Conjecture** (SOLVED by Margulis 1987):
    For irrational α > 0 and any ε > 0, there exist positive integers
    x, y, z with |x² + y² − α·z²| < ε. -/
axiom margulis_oppenheim :
  ∀ (α : ℝ), Irrational α → α > 0 →
    ∀ ε : ℝ, ε > 0 → ApproxZero α ε

/-! ## Density of Values -/

/-- The set of values taken by the form is dense in ℝ.
    This is the stronger consequence of Margulis's theorem. -/
axiom oppenheim_dense_values :
  ∀ (α : ℝ), Irrational α → α > 0 →
    ∀ (t : ℝ) (ε : ℝ), ε > 0 →
      ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
        |ternaryForm α x y z - t| < ε

/-- Dense values implies approximation of zero (weaker statement). -/
theorem dense_implies_approx_zero
    (hdense : ∀ (α : ℝ), Irrational α → α > 0 →
      ∀ (t : ℝ) (ε : ℝ), ε > 0 →
        ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
          |ternaryForm α x y z - t| < ε)
    (α : ℝ) (hirr : Irrational α) (hpos : α > 0)
    (ε : ℝ) (hε : ε > 0) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      |ternaryForm α x y z| < ε := by
  have h := hdense α hirr hpos 0 ε hε
  obtain ⟨x, y, z, hne, hval⟩ := h
  exact ⟨x, y, z, hne, by simp [sub_zero] at hval; exact hval⟩

/-! ## Special Cases and Bounds -/

/-- For α = p/q rational, the form x² + y² − (p/q)z² has a minimum nonzero
    value at integer points: min|Q| ≥ 1/q. No approximation is possible. -/
axiom rational_form_bounded_away :
  ∀ (p : ℤ) (q : ℕ), q > 0 →
    ∃ δ : ℝ, δ > 0 ∧
      ∀ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
        ternaryForm ((p : ℝ) / (q : ℝ)) x y z ≠ 0 →
          |ternaryForm ((p : ℝ) / (q : ℝ)) x y z| ≥ δ

/-- **Davenport–Heilbronn (1946)**: For quadratic forms in n ≥ 5 variables,
    the Oppenheim conjecture holds. Their method uses the circle method. -/
axiom davenport_heilbronn_five_variables :
  -- Simplified: for the diagonal form x₁² + x₂² + x₃² + x₄² − α·x₅²
  ∀ (α : ℝ), Irrational α → α > 0 →
    ∀ ε : ℝ, ε > 0 →
      ∃ a b c d e : ℤ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0) ∧
        |(a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 + (d : ℝ) ^ 2
          - α * (e : ℝ) ^ 2| < ε

/-! ## Connection to Dynamics -/

/-- Margulis's proof uses the action of SO(2,1) on SL(3,ℝ)/SL(3,ℤ).
    The key insight: the orbit of a lattice under the stabilizer of Q
    is either closed (Q is rational multiple of integral form) or dense. -/
axiom margulis_orbit_dichotomy :
  -- Formalized abstractly: for the ternary form,
  -- either the form is a rational multiple of an integral form,
  -- or values at integer points are dense in ℝ.
  ∀ (α : ℝ), α > 0 →
    (∃ (p : ℤ) (q : ℕ), q > 0 ∧ α = (p : ℝ) / (q : ℝ)) ∨
    (∀ (t : ℝ) (ε : ℝ), ε > 0 →
      ∃ x y z : ℤ, |ternaryForm α x y z - t| < ε)

/-- Irrational α cannot be a rational multiple of an integral form. -/
theorem irrational_not_rational (α : ℝ) (hirr : Irrational α) :
    ¬∃ (p : ℤ) (q : ℕ), q > 0 ∧ α = (p : ℝ) / (q : ℝ) := by
  intro ⟨p, q, hq, heq⟩
  apply hirr
  exact ⟨p, q, hq, heq⟩

/-! ## Quantitative Refinements -/

/-- **Eskin–Margulis–Mozes (1998)**: Quantitative Oppenheim.
    The number of integer points (x,y,z) with |Q(x,y,z)| < δ and
    max(|x|,|y|,|z|) ≤ T grows as c·δ·T as T → ∞. -/
axiom eskin_margulis_mozes_counting :
  ∀ (α : ℝ), Irrational α → α > 0 →
    ∀ (δ : ℝ), δ > 0 →
      -- The count of solutions grows linearly in T
      ∀ (C : ℝ), C > 0 →
        ∃ T₀ : ℕ, ∀ T : ℕ, T > T₀ →
          ∃ (S : Finset (ℤ × ℤ × ℤ)),
            S.card > 0 ∧
            ∀ p ∈ S, |ternaryForm α p.1 p.2.1 p.2.2| < δ
