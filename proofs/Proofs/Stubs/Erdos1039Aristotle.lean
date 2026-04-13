/-
  Aristotle targets for Erdős Problem #1039
  Routine supporting lemmas for automated proof search.
  See Erdos1039Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT area_implies_disc_bound (geometric measure theory — hard)
  - NOT degree_one_optimal (complex analysis — hard)
  - NOT clustered_implies_large_disc (geometric — hard)
  - NOT ehpConjecture (open)
  - Routine: inscribed disc properties, bound positivity, polynomial evaluation
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1039Aristotle

open Complex

/-- A monic polynomial with roots in the unit disc. -/
structure UnitDiscPolynomial where
  degree : ℕ
  roots : Fin degree → ℂ
  roots_in_disc : ∀ i, Complex.abs (roots i) ≤ 1

variable (f : UnitDiscPolynomial)

/-- The polynomial as a function ℂ → ℂ. -/
noncomputable def UnitDiscPolynomial.eval (z : ℂ) : ℂ :=
  ∏ i : Fin f.degree, (z - f.roots i)

/-- The sublevel set {z : |f(z)| < 1}. -/
def sublevelSet : Set ℂ :=
  {z : ℂ | Complex.abs (f.eval z) < 1}

/-- A disc of radius r centered at c is inscribed in S. -/
def isInscribedDisc (S : Set ℂ) (c : ℂ) (r : ℝ) : Prop :=
  r > 0 ∧ ∀ z : ℂ, Complex.abs (z - c) < r → z ∈ S

/-- Pommerenke bound: 1/(2en²). -/
noncomputable def pommerenkeBound (n : ℕ) : ℝ :=
  1 / (2 * Real.exp 1 * n^2)

/-- Benchmark upper bound: π/(2n). -/
noncomputable def benchmarkBound (n : ℕ) : ℝ :=
  Real.pi / (2 * n)

-- Routine: An inscribed disc has positive radius.
-- By definition, isInscribedDisc requires r > 0.
theorem isInscribedDisc_pos {S : Set ℂ} {c : ℂ} {r : ℝ}
    (h : isInscribedDisc S c r) : r > 0 := h.1

-- Routine: If D is inscribed in S and S ⊆ T, then D is inscribed in T.
-- Any point in D is in S (since D ⊆ S ⊆ T).
theorem isInscribedDisc_subset {S T : Set ℂ} (hST : S ⊆ T)
    {c : ℂ} {r : ℝ} (h : isInscribedDisc S c r) :
    isInscribedDisc T c r :=
  ⟨h.1, fun z hz => hST (h.2 z hz)⟩

-- Routine: The Pommerenke bound is positive for n > 0.
-- 1 / (2 * exp(1) * n²) > 0 since all factors are positive.
theorem pommerenkeBound_pos (n : ℕ) (hn : n > 0) : pommerenkeBound n > 0 := by
  simp [pommerenkeBound]
  positivity

-- Routine: The benchmark bound is positive for n > 0.
-- π / (2n) > 0 since π > 0 and n > 0.
theorem benchmarkBound_pos (n : ℕ) (hn : n > 0) : benchmarkBound n > 0 := by
  simp [benchmarkBound]
  positivity

-- Routine: For n ≥ 1, the Pommerenke bound is at most 1/(2e).
-- 1/(2e * n²) ≤ 1/(2e * 1²) = 1/(2e) since n² ≥ 1.
theorem pommerenkeBound_le_half_e (n : ℕ) (hn : n ≥ 1) :
    pommerenkeBound n ≤ 1 / (2 * Real.exp 1) := by
  simp [pommerenkeBound]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [Real.exp_pos 1]

-- Routine: All roots lie in the closed unit disc.
-- This follows directly from the roots_in_disc field.
theorem roots_in_disc (i : Fin f.degree) : Complex.abs (f.roots i) ≤ 1 :=
  f.roots_in_disc i

-- Routine: For degree 0, the polynomial evaluates to 1 (empty product).
-- ∏ i : Fin 0, (...) = 1 by definition of empty product.
theorem eval_degree_zero (f : UnitDiscPolynomial) (hf : f.degree = 0) (z : ℂ) :
    f.eval z = 1 := by
  simp [UnitDiscPolynomial.eval, hf]

-- Routine: π > 0.
theorem pi_pos : Real.pi > 0 := Real.pi_pos

-- Routine: exp(1) > 0.
theorem exp_one_pos : Real.exp 1 > 0 := Real.exp_pos 1

-- Routine: For n ≥ 3, log n > 0.
theorem log_pos_of_ge_3 (n : ℕ) (hn : n ≥ 3) : Real.log n > 0 := by
  apply Real.log_pos
  exact_mod_cast show 1 < n by omega

end Erdos1039Aristotle
