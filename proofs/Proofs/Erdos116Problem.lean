/-!
# Erdős Problem #116 — Measure of Polynomial Sublevel Sets

Let p(z) = ∏(z - zᵢ) for |zᵢ| ≤ 1. Is the 1-dimensional Lebesgue measure
of {z ∈ ℂ : |p(z)| < 1} at least n^{-O(1)}? Or even (log n)^{-O(1)}?

PROVED:
- Pommerenke: |{|p(z)| < 1}| ≥ c/n⁴
- Krishnapur–Lundberg–Ramachandran: |{|p(z)| < 1}| ≥ c/log n (optimal up to log log)

Upper bounds:
- Pólya: |{|p(z)| < 1}| ≤ π (achieved when all zᵢ coincide)
- Krishnapur–Lundberg–Ramachandran: |{|p(z)| < 1}| ≤ C/log log n

A conjecture of Erdős, Herzog, and Piranian.

Reference: https://erdosproblems.com/116
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! ## Monic Polynomials with Roots in the Unit Disk -/

/-- A monic polynomial of degree n with all roots in the closed unit disk -/
structure UnitDiskPoly (n : ℕ) where
  roots : Fin n → ℂ
  roots_in_disk : ∀ i, Complex.abs (roots i) ≤ 1

/-- The polynomial p(z) = ∏(z - zᵢ) -/
noncomputable def UnitDiskPoly.eval (P : UnitDiskPoly n) (z : ℂ) : ℂ :=
  Finset.univ.prod (fun i => z - P.roots i)

/-- The sublevel set {z ∈ ℂ : |p(z)| < 1} -/
def UnitDiskPoly.sublevelSet (P : UnitDiskPoly n) : Set ℂ :=
  {z : ℂ | Complex.abs (P.eval z) < 1}

/-! ## The Measure of the Sublevel Set -/

/-- The 1-dimensional Lebesgue measure of the sublevel set,
    viewed as a subset of ℝ² via the identification ℂ ≅ ℝ² -/
noncomputable def sublevelMeasure (P : UnitDiskPoly n) : ℝ :=
  (MeasureTheory.MeasureSpace.volume (α := ℝ × ℝ)
    {p : ℝ × ℝ | Complex.abs (P.eval ⟨p.1, p.2⟩) < 1}).toReal

/-! ## Pommerenke's Bound -/

/-- Pommerenke's bound: the sublevel measure is at least c/n⁴ -/
axiom pommerenke_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ (n : ℕ) (hn : 1 ≤ n) (P : UnitDiskPoly n),
      c / (n : ℝ) ^ 4 ≤ sublevelMeasure P

/-! ## Krishnapur–Lundberg–Ramachandran Bounds -/

/-- KLR lower bound: the sublevel measure is at least c/log n.
    This proves the Erdős–Herzog–Piranian conjecture. -/
axiom klr_lower_bound :
  ∃ c : ℝ, c > 0 ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (P : UnitDiskPoly n),
      c / Real.log (n : ℝ) ≤ sublevelMeasure P

/-- KLR upper bound: there exist polynomials with sublevel measure
    at most C/log log n, showing the lower bound is nearly tight -/
axiom klr_upper_bound :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (hn : 3 ≤ n),
      ∃ P : UnitDiskPoly n,
        sublevelMeasure P ≤ C / Real.log (Real.log (n : ℝ))

/-! ## Pólya's Upper Bound -/

/-- Pólya's bound: the sublevel measure is at most π, and equality holds
    only when all roots coincide (p(z) = (z - z₀)ⁿ for some |z₀| ≤ 1) -/
axiom polya_upper_bound (n : ℕ) (hn : 1 ≤ n) (P : UnitDiskPoly n) :
  sublevelMeasure P ≤ Real.pi

/-! ## The Erdős–Herzog–Piranian Conjecture (PROVED) -/

/-- Erdős Problem 116 (Erdős–Herzog–Piranian, PROVED):
    The sublevel measure |{|p(z)| < 1}| is at least (log n)^{-O(1)}.
    Proved by Krishnapur, Lundberg, and Ramachandran with
    the optimal bound c/log n. -/
axiom ErdosProblem116 :
  ∃ c : ℝ, c > 0 ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (P : UnitDiskPoly n),
      c / Real.log (n : ℝ) ≤ sublevelMeasure P

/-- The remaining open question: determine which polynomials
    minimize the sublevel measure -/
axiom minimizer_characterization :
  ∀ (n : ℕ) (hn : 3 ≤ n),
    ∃ P₀ : UnitDiskPoly n,
      ∀ P : UnitDiskPoly n,
        sublevelMeasure P₀ ≤ sublevelMeasure P
