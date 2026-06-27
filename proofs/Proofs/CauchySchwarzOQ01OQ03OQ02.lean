/-
  Entropic Uncertainty — Finite Shannon-Entropy Infrastructure
  (toward Erdős/Cauchy–Schwarz OQ chain `cauchy-schwarz-oq-01-oq-03-oq-02`)

  Source question (parent `cauchy-schwarz-oq-01-oq-03`, "Heisenberg Uncertainty from
  Complex Cauchy–Schwarz"): can the **entropic uncertainty principle** (Maassen–Uffink
  1988) — `H(p) + H(q) ≥ -2 ln c` for the outcome distributions of two orthonormal bases
  with maximal overlap `c` — be formalized in Lean 4?

  STATUS OF THE FULL THEOREM: BLOCKED on Mathlib. The sharp Maassen–Uffink constant
  follows from the Hausdorff–Young inequality, equivalently a Riesz–Thorin interpolation
  argument; as of Mathlib v4.26.0 there is **no** interpolation theory and **no** Lp→Lp'
  Fourier bound. (Deutsch's interpolation-free precursor `≥ -2 ln((1+c)/2)` is tractable
  in principle but still a substantial standalone development.)

  WHAT IS PROVABLE NOW, and is built here (0 axioms, 0 sorries): the finite-dimensional
  Shannon-entropy framework that any version of the entropic uncertainty relation needs —
  Shannon entropy of a probability vector via Mathlib's `Real.negMulLog`, its
  nonnegativity, and the **maximum-entropy bound** `H(p) ≤ log n` (Jensen on the concavity
  of `negMulLog`; equality at the uniform distribution). This is the "entropy half" of an
  entropic uncertainty relation, and a reusable building block for the eventual proof.
-/

import Mathlib

open Finset

namespace CauchySchwarzOQ01OQ03OQ02

variable {ι : Type*} [Fintype ι]

/-- Shannon entropy of a finite probability vector `p` (in nats):
`H(p) = ∑ᵢ negMulLog(pᵢ) = -∑ᵢ pᵢ log pᵢ`, using Mathlib's `Real.negMulLog`. -/
noncomputable def shannonEntropy (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Entropy of a vector with entries in `[0,1]` is nonnegative (each `negMulLog` term is). -/
theorem shannonEntropy_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) :
    0 ≤ shannonEntropy p := by
  refine Finset.sum_nonneg fun i _ => ?_
  exact Real.negMulLog_nonneg (h0 i) (h1 i)

/-- **Maximum-entropy bound.** A probability vector on `n = card ι` outcomes has
`H(p) ≤ log n`, with equality for the uniform distribution. Proof: Jensen's inequality
applied to the concave function `negMulLog` with uniform weights `1/n`.

This is the entropy ceiling that bounds either marginal in an entropic uncertainty
relation; the genuinely hard content of Maassen–Uffink is the *lower* bound on the sum
`H(p) + H(q)`, which is interpolation-gated and not yet available in Mathlib. -/
theorem shannonEntropy_le_log_card [Nonempty ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) := by
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- Jensen for the concave `negMulLog` with uniform weights `1/n`.
  have hjensen :
      (∑ i : ι, ((n : ℝ)⁻¹) • Real.negMulLog (p i))
        ≤ Real.negMulLog (∑ i : ι, ((n : ℝ)⁻¹) • p i) := by
    refine Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun _ => (n : ℝ)⁻¹) (p := p) ?_ ?_ ?_
    · intro i _; positivity
    · -- weights sum to 1
      rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
      field_simp
    · intro i _; exact Set.mem_Ici.mpr (h0 i)
  -- Evaluate the weighted mean: `∑ (1/n)•pᵢ = 1/n`.
  have hmean : (∑ i : ι, ((n : ℝ)⁻¹) • p i) = (n : ℝ)⁻¹ := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
  -- `negMulLog (1/n) = (1/n) * log n`.
  have hval : Real.negMulLog ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ * Real.log n := by
    rw [Real.negMulLog, Real.log_inv]; ring
  -- The LHS of Jensen is `(1/n) * H(p)`.
  have hlhs : (∑ i : ι, ((n : ℝ)⁻¹) • Real.negMulLog (p i))
      = (n : ℝ)⁻¹ * shannonEntropy p := by
    simp only [smul_eq_mul, shannonEntropy, Finset.mul_sum]
  rw [hlhs, hmean, hval] at hjensen
  -- Cancel the common positive factor `1/n`.
  exact le_of_mul_le_mul_left hjensen (by positivity)

/-- The uniform distribution attains the maximum-entropy bound: `H(uniform) = log n`. -/
theorem shannonEntropy_uniform [Nonempty ι] :
    shannonEntropy (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) = Real.log (Fintype.card ι) := by
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  simp only [shannonEntropy, Real.negMulLog, Real.log_inv, Finset.sum_const,
    Finset.card_univ, ← hn, nsmul_eq_mul]
  field_simp

end CauchySchwarzOQ01OQ03OQ02
