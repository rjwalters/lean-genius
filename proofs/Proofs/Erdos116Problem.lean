/-
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

import Mathlib

/-- v4.31 migration compat: `Complex.abs` was removed from Mathlib in favor of `‖·‖`. -/
noncomputable def Complex.abs (z : ℂ) : ℝ := ‖z‖


/- ## Monic Polynomials with Roots in the Unit Disk -/

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

/- ## The Measure of the Sublevel Set -/

/-- The 1-dimensional Lebesgue measure of the sublevel set,
    viewed as a subset of ℝ² via the identification ℂ ≅ ℝ² -/
noncomputable def sublevelMeasure (P : UnitDiskPoly n) : ℝ :=
  (MeasureTheory.MeasureSpace.volume (α := ℝ × ℝ)
    {p : ℝ × ℝ | Complex.abs (P.eval ⟨p.1, p.2⟩) < 1}).toReal

/- ## Pommerenke's Bound -/

/-  Pommerenke's bound: the sublevel measure is at least c/n⁴ -/

/- ## Krishnapur–Lundberg–Ramachandran Bounds -/

/-  KLR lower bound: the sublevel measure is at least c/log n.
    This proves the Erdős–Herzog–Piranian conjecture. -/

/-  KLR upper bound: there exist polynomials with sublevel measure
    at most C/log log n, showing the lower bound is nearly tight -/

/- ## Pólya's Upper Bound -/

/-  Pólya's bound: the sublevel measure is at most π, and equality holds
    only when all roots coincide (p(z) = (z - z₀)ⁿ for some |z₀| ≤ 1) -/

/- ## Foundational Structure Lemmas (axiom-free)

The deep quantitative bounds above (Pommerenke `c/n⁴`, KLR `c/log n`,
KLR `C/log log n`, Pólya `π`) rest on logarithmic-potential and measure
machinery not presently available in Mathlib, so they are stated only in
the header prose. What *is* machine-checkable here is the basic geometry of
the lemniscate `{|p(z)| < 1}` directly from the root factorization. These
lemmas are proved with no axioms and no `sorry`. -/

/-- Evaluating `p` at one of its own roots gives `0`: the factor `(zᵢ - zᵢ)`
    vanishes, so the whole product does. -/
@[simp] theorem UnitDiskPoly.eval_root_eq_zero (P : UnitDiskPoly n) (i : Fin n) :
    P.eval (P.roots i) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

/-- Every root lies in the sublevel set: `|p(zᵢ)| = 0 < 1`. -/
theorem UnitDiskPoly.root_mem_sublevelSet (P : UnitDiskPoly n) (i : Fin n) :
    P.roots i ∈ P.sublevelSet := by
  show Complex.abs (P.eval (P.roots i)) < 1
  rw [P.eval_root_eq_zero i]
  simp [Complex.abs]

/-- For a positive-degree polynomial the sublevel set is nonempty — it contains
    every root. -/
theorem UnitDiskPoly.sublevelSet_nonempty (P : UnitDiskPoly n) (hn : 0 < n) :
    P.sublevelSet.Nonempty :=
  ⟨P.roots ⟨0, hn⟩, P.root_mem_sublevelSet ⟨0, hn⟩⟩

/-- The degenerate degree-`0` polynomial is the empty product `p ≡ 1`. -/
@[simp] theorem UnitDiskPoly.eval_of_degree_zero (P : UnitDiskPoly 0) (z : ℂ) :
    P.eval z = 1 := by
  simp [UnitDiskPoly.eval]

/-- In degree `0`, `p ≡ 1`, so `{|p(z)| < 1}` is empty: the boundary case that
    makes the positive-degree hypothesis in `sublevelSet_nonempty` essential. -/
theorem UnitDiskPoly.sublevelSet_of_degree_zero (P : UnitDiskPoly 0) :
    P.sublevelSet = (∅ : Set ℂ) := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  show ¬ Complex.abs (P.eval z) < 1
  rw [P.eval_of_degree_zero z]
  simp [Complex.abs]

/-- The sublevel measure is always nonnegative (it is the real part of an
    `ℝ≥0∞`-valued measure). -/
theorem UnitDiskPoly.sublevelMeasure_nonneg (P : UnitDiskPoly n) :
    0 ≤ sublevelMeasure P :=
  ENNReal.toReal_nonneg

/- ## The Erdős–Herzog–Piranian Conjecture (PROVED) -/

/-  Erdős Problem 116 (Erdős–Herzog–Piranian, PROVED):
    The sublevel measure |{|p(z)| < 1}| is at least (log n)^{-O(1)}.
    Proved by Krishnapur, Lundberg, and Ramachandran with
    the optimal bound c/log n. -/

/- The remaining open question: determine which polynomials
    minimize the sublevel measure -/
