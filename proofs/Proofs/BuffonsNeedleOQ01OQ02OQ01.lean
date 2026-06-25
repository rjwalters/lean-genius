/-
# Buffon Constants: The Consecutive-Product Invariant

**Status**: Fully verified (0 axioms, 0 sorries)

This file extends `BuffonsNeedleOQ01OQ02.lean` (the higher-dimensional Buffon
constants `c_n`) in the Cauchy–Crofton direction.

Recall the Buffon dimensional constant
  c_n = E[|⟨u, e₁⟩|]   for uniform u ∈ S^{n-1}
      = 2·Γ(n/2) / ((n-1)·√π·Γ((n-1)/2)).

The parent file proved the *recurrence* c_{n+2} = (n/(n+1))·c_n. Here we prove a
sharper and more fundamental fact: a **dimension-independent invariant** carried
by *consecutive* constants.

## Main results

* `buffonConstant_consecutive_product`:  c_{n+1} · c_n = 2 / (n·π)   for n ≥ 2.
* `buffon_cauchy_invariant`:  n · c_n · c_{n+1} = 2/π,  independent of n.
  The conserved value 2/π is exactly the classical 2-dimensional Cauchy /
  Buffon–Barbier constant `c₂`, so every dimension carries a shadow of the
  planar Cauchy–Crofton formula.
* `buffonConstant_recurrence_from_invariant`:  the parent's recurrence
  c_{n+2} = (n/(n+1))·c_n is *derived* from the invariant — so the invariant is
  the more primitive statement.
* `buffonConstant_two_step_strictAnti`:  c_{n+2} < c_n, obtained directly from
  the invariant (concentration of measure), with no Gamma estimates.

The proof of the product identity is one application of the Gamma functional
equation Γ(z+1) = z·Γ(z): the two Gamma factors at argument n/2 cancel, and the
remaining Γ((n+1)/2) = ((n-1)/2)·Γ((n-1)/2) collapses the (n-1) factor.

This is the algebraic heart of the Cauchy–Crofton normalization: the kinematic
measure on lines is calibrated so that the planar constant 2/π reappears,
rescaled by 1/n, between every pair of neighbouring dimensions.
-/
import Mathlib

namespace BuffonConsecutiveProduct

open Real

-- ============================================================
-- The Buffon dimensional constant (self-contained re-declaration)
-- ============================================================

/-- The dimensional constant for Buffon's needle in ℝⁿ:
    c_n = E[|⟨u, e₁⟩|] for uniform u ∈ S^{n-1}, given by the Gamma ratio
    c_n = 2·Γ(n/2) / ((n-1)·√π·Γ((n-1)/2)).  For n ≤ 1 we set c_n = 0. -/
noncomputable def buffonConstant (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else 2 * Real.Gamma ((n : ℝ) / 2) /
    (((n : ℝ) - 1) * Real.sqrt π * Real.Gamma (((n : ℝ) - 1) / 2))

/-- The Buffon constant is positive for n ≥ 2. -/
theorem buffonConstant_pos (n : ℕ) (hn : 2 ≤ n) : 0 < buffonConstant n := by
  unfold buffonConstant
  simp only [show ¬(n ≤ 1) from by omega, ↓reduceIte]
  have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_n_half : (0 : ℝ) < (n : ℝ) / 2 := by linarith
  have h_nm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h_nm1_half : (0 : ℝ) < ((n : ℝ) - 1) / 2 := by linarith
  apply div_pos
  · exact mul_pos two_pos (Real.Gamma_pos_of_pos h_n_half)
  · exact mul_pos (mul_pos h_nm1 (Real.sqrt_pos.mpr pi_pos))
      (Real.Gamma_pos_of_pos h_nm1_half)

-- ============================================================
-- The consecutive-product invariant
-- ============================================================

/-- **Consecutive-product identity.** For every dimension n ≥ 2,
      c_{n+1} · c_n = 2 / (n·π).

    Both Gamma factors at argument n/2 cancel (one from the numerator of c_n,
    one from the denominator of c_{n+1}), and the surviving Γ((n+1)/2) reduces to
    ((n-1)/2)·Γ((n-1)/2) via the functional equation, cancelling the (n-1) factor
    and leaving 2/(n·π). -/
theorem buffonConstant_consecutive_product (n : ℕ) (hn : 2 ≤ n) :
    buffonConstant (n + 1) * buffonConstant n = 2 / ((n : ℝ) * π) := by
  unfold buffonConstant
  simp only [show ¬(n + 1 ≤ 1) from by omega, show ¬(n ≤ 1) from by omega,
    ↓reduceIte]
  have hn_ge : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- cast normalisations for the (n+1) arguments.  Note hB rewrites the inner
  -- `↑(n+1) - 1` of the `/2` argument too, sending it to `↑n / 2`.
  have hA : (↑(n + 1) : ℝ) / 2 = ((n : ℝ) - 1) / 2 + 1 := by push_cast; ring
  have hB : (↑(n + 1) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
  have hpos1 : (0 : ℝ) < (n : ℝ) / 2 := by linarith
  have hpos2 : (0 : ℝ) < ((n : ℝ) - 1) / 2 := by linarith
  -- the only Gamma fact used: Γ((n-1)/2 + 1) = ((n-1)/2)·Γ((n-1)/2)
  have hΓ : Real.Gamma (((n : ℝ) - 1) / 2 + 1)
      = (((n : ℝ) - 1) / 2) * Real.Gamma (((n : ℝ) - 1) / 2) :=
    Real.Gamma_add_one (ne_of_gt hpos2)
  rw [hA, hB, hΓ]
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) ≠ 0 := by linarith
  have h3 : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr pi_pos)
  have h4 : Real.Gamma ((n : ℝ) / 2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hpos1)
  have h5 : Real.Gamma (((n : ℝ) - 1) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hpos2)
  have h6 : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  field_simp
  ring_nf
  rw [Real.sq_sqrt pi_pos.le]

/-- **The Cauchy invariant.** The quantity n · c_n · c_{n+1} is independent of the
    dimension n and equals 2/π — exactly the classical planar Buffon/Cauchy
    constant c₂.  Higher dimensions therefore each carry a rescaled shadow of the
    2D Cauchy–Crofton formula. -/
theorem buffon_cauchy_invariant (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * buffonConstant n * buffonConstant (n + 1) = 2 / π := by
  have h := buffonConstant_consecutive_product n hn
  have h2 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hπ : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  -- n · c_n · c_{n+1} = n · (c_{n+1}·c_n) = n · (2/(nπ)) = 2/π
  have : (n : ℝ) * buffonConstant n * buffonConstant (n + 1)
      = (n : ℝ) * (buffonConstant (n + 1) * buffonConstant n) := by ring
  rw [this, h]
  field_simp

/-- The invariant takes the *same* value across all dimensions m, n ≥ 2. -/
theorem buffon_cauchy_invariant_const (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (m : ℝ) * buffonConstant m * buffonConstant (m + 1)
      = (n : ℝ) * buffonConstant n * buffonConstant (n + 1) := by
  rw [buffon_cauchy_invariant m hm, buffon_cauchy_invariant n hn]

-- ============================================================
-- Consequences: monotonicity and the parent recurrence, from the invariant
-- ============================================================

/-- **Two-step strict monotonicity** c_{n+2} < c_n, obtained purely from the
    invariant: c_{n+1}·c_n = 2/(nπ) > 2/((n+1)π) = c_{n+1}·c_{n+2}, and
    c_{n+1} > 0.  This is the concentration-of-measure decay, with no Gamma
    estimates. -/
theorem buffonConstant_two_step_strictAnti (n : ℕ) (hn : 2 ≤ n) :
    buffonConstant (n + 2) < buffonConstant n := by
  have e1 := buffonConstant_consecutive_product n hn
  have e2 := buffonConstant_consecutive_product (n + 1) (by omega)
  have hcpos : 0 < buffonConstant (n + 1) := buffonConstant_pos (n + 1) (by omega)
  have hn_ge : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hπ : (0 : ℝ) < π := pi_pos
  -- 2/((n+1)π) < 2/(nπ)
  have hlt : (2 : ℝ) / (((n : ℝ) + 1) * π) < 2 / ((n : ℝ) * π) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    have : (n : ℝ) * π < ((n : ℝ) + 1) * π := by nlinarith
    linarith
  -- rewrite e2's RHS with the cast (↑(n+1)) = ↑n + 1
  have e2' : buffonConstant (n + 2) * buffonConstant (n + 1)
      = 2 / (((n : ℝ) + 1) * π) := by
    have hcast : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [show n + 1 + 1 = n + 2 from rfl] at e2
    rw [e2, hcast]
  -- c_{n+2}·c_{n+1} < c_n·c_{n+1}, cancel c_{n+1} > 0
  have key : buffonConstant (n + 2) * buffonConstant (n + 1)
      < buffonConstant n * buffonConstant (n + 1) := by
    rw [e2', mul_comm (buffonConstant n) (buffonConstant (n + 1)), e1]
    exact hlt
  exact lt_of_mul_lt_mul_right key (le_of_lt hcpos)

/-- **The parent recurrence, derived.**  c_{n+2} = (n/(n+1))·c_n follows from the
    consecutive-product invariant (so the invariant is the more primitive fact).
    -/
theorem buffonConstant_recurrence_from_invariant (n : ℕ) (hn : 2 ≤ n) :
    buffonConstant (n + 2) = (n : ℝ) / ((n : ℝ) + 1) * buffonConstant n := by
  have e1 := buffonConstant_consecutive_product n hn
  have e2 := buffonConstant_consecutive_product (n + 1) (by omega)
  have hcpos : 0 < buffonConstant (n + 1) := buffonConstant_pos (n + 1) (by omega)
  have hn_ge : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : (n : ℝ) ≠ 0 := by linarith
  have h2' : (n : ℝ) + 1 ≠ 0 := by linarith
  have hπ : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  have e2' : buffonConstant (n + 2) * buffonConstant (n + 1)
      = 2 / (((n : ℝ) + 1) * π) := by
    have hcast : (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [show n + 1 + 1 = n + 2 from rfl] at e2
    rw [e2, hcast]
  -- cancel c_{n+1}: it suffices to prove the identity after ·c_{n+1}
  apply mul_right_cancel₀ (ne_of_gt hcpos)
  rw [e2']
  -- RHS·c_{n+1} = (n/(n+1)) · (c_n·c_{n+1}) = (n/(n+1)) · (2/(nπ)) = 2/((n+1)π)
  rw [mul_assoc, mul_comm (buffonConstant n) (buffonConstant (n + 1)), e1]
  field_simp

-- ============================================================
-- Numerical corollaries (consistency with known constants)
-- ============================================================

/-- c₃·c₂ = 1/π  (the invariant at n = 2 reproduces 2·c₂·c₃ = 2/π). -/
theorem product_three_two : buffonConstant 3 * buffonConstant 2 = 1 / π := by
  have h := buffonConstant_consecutive_product 2 (by norm_num)
  have hπ : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  rw [show (3 : ℕ) = 2 + 1 from rfl, h]
  push_cast; field_simp

/-- c₄·c₃ = 2/(3π). -/
theorem product_four_three : buffonConstant 4 * buffonConstant 3 = 2 / (3 * π) := by
  have h := buffonConstant_consecutive_product 3 (by norm_num)
  have hπ : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  rw [show (4 : ℕ) = 3 + 1 from rfl, h]
  push_cast; field_simp

/-- c₅·c₄ = 1/(2π). -/
theorem product_five_four : buffonConstant 5 * buffonConstant 4 = 1 / (2 * π) := by
  have h := buffonConstant_consecutive_product 4 (by norm_num)
  have hπ : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  rw [show (5 : ℕ) = 4 + 1 from rfl, h]
  push_cast; field_simp; ring

end BuffonConsecutiveProduct
