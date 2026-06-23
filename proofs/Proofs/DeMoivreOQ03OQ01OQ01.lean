/-
# De Moivre for irrational exponents: genuine single-valuedness (OQ-03-OQ-01-OQ-01)

The parent entry **de-moivre-oq-03-oq-01** ("De Moivre Extension to Irrational
Exponents") states `irrational_exponent_single_valued` as a placeholder
`theorem … : True := trivial` and asks, as its first open question:

  > Can `irrational_exponent_single_valued` be proved from `cpow_def_of_ne_zero`
  > and the single-valuedness of `Complex.log`? The claim is almost definitional.

This file replaces the `True` stub with the genuine mathematical content. For
`z = e^{iθ}` on the unit circle with `θ` in the principal branch `(-π, π]`, the
principal power `z^α = e^{iαθ}` is a *single* well-defined value (via
`cpow_def_of_ne_zero` and `Complex.log_exp`). What makes the irrational case
special is the *reason* it is single-valued: the would-be branch family
`k ↦ e^{2πi α k}` is **injective** — for irrational `α` the orbit never returns,
so there is no integer `q` producing a `q`-fold ambiguity, unlike the rational
`p/q` case (which has exactly `q` values). We prove:

  * `principal_value` — the single principal value `e^{iαθ} = (e^{iθ})^α`;
  * `exp_two_pi_ne_one_of_irrational` — `e^{2πiαn} ≠ 1` for `n ≠ 0`
    (the orbit never returns to `1`), the crux of single-valuedness;
  * `branch_injective` — `k ↦ e^{2πiαk}` is injective;
  * `irrational_exponent_single_valued` — the genuine statement: the principal
    value formula **together with** branch injectivity (no finite cyclic
    ambiguity), the honest replacement for the parent's `True` stub.

Zero axioms; imports only Mathlib.
-/
import Mathlib

namespace DeMoivreOQ03OQ01OQ01

open Complex Real

/- ## The single principal value -/

/-- **The principal value.** For `θ ∈ (-π, π]` and any real exponent `α`, the
principal power of `e^{iθ}` is the single value `e^{iαθ}` — exactly the De Moivre
formula, obtained from `cpow_def_of_ne_zero` and `Complex.log_exp`. -/
theorem principal_value (θ α : ℝ) (hθ_lo : -π < θ) (hθ_hi : θ ≤ π) :
    (Complex.exp (↑θ * Complex.I)) ^ (α : ℂ) = Complex.exp (↑(α * θ) * Complex.I) := by
  rw [cpow_def_of_ne_zero (exp_ne_zero _)]
  have him : (↑θ * Complex.I).im = θ := by simp
  rw [Complex.log_exp (by rw [him]; exact hθ_lo) (by rw [him]; exact hθ_hi)]
  congr 1; push_cast; ring

/- ## The orbit never returns: the source of single-valuedness -/

/-- **For irrational `α`, `e^{2πiαn} ≠ 1` whenever `n ≠ 0`.** The would-be branch
shift never collapses to the identity, so no integer `q` creates a `q`-fold
ambiguity. This is the precise content of "single-valuedness for irrational
exponents". -/
theorem exp_two_pi_ne_one_of_irrational {α : ℝ} (hα : Irrational α) {n : ℤ} (hn : n ≠ 0) :
    Complex.exp (↑(2 * π * α * n) * Complex.I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  rw [show (↑k : ℂ) * (2 * ↑π * Complex.I) = (↑k * (2 * ↑π)) * Complex.I from by ring] at hk
  have hk2 : (↑(2 * π * α * ↑n) : ℂ) = ↑k * (2 * ↑π) := mul_right_cancel₀ Complex.I_ne_zero hk
  have hk3 : 2 * π * α * ↑n = ↑k * (2 * π) := by exact_mod_cast hk2
  have hαn : (↑n : ℝ) * α = ↑k := by
    have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
    apply mul_left_cancel₀ h2pi
    linear_combination hk3
  have hirr : Irrational ((↑n : ℝ) * α) := hα.intCast_mul hn
  rw [hαn] at hirr
  exact Int.not_irrational k hirr

/-- **The branch family is injective.** For irrational `α`, the map
`k ↦ e^{2πiαk}` is injective on `ℤ`: distinct integers give distinct points, so
the "branches" never coincide — there is no finite cyclic structure as in the
rational case. -/
theorem branch_injective {α : ℝ} (hα : Irrational α) :
    Function.Injective (fun k : ℤ => Complex.exp (↑(2 * π * α * k) * Complex.I)) := by
  intro j k hjk
  simp only at hjk
  by_contra hne
  have hjkne : j - k ≠ 0 := sub_ne_zero.mpr hne
  refine exp_two_pi_ne_one_of_irrational hα hjkne ?_
  have hsub : Complex.exp (↑(2 * π * α * ↑j) * Complex.I - ↑(2 * π * α * ↑k) * Complex.I) = 1 :=
    Complex.exp_eq_exp_iff_exp_sub_eq_one.mp hjk
  have hdiff : (↑(2 * π * α * ↑j) : ℂ) * Complex.I - ↑(2 * π * α * ↑k) * Complex.I
      = ↑(2 * π * α * ↑(j - k)) * Complex.I := by push_cast; ring
  rwa [hdiff] at hsub

/- ## The genuine single-valuedness statement -/

/-- **`irrational_exponent_single_valued`, genuinely.** Replacing the parent's
`True := trivial` placeholder: for irrational `α` and `θ ∈ (-π, π]`, the principal
power `(e^{iθ})^α` equals the single value `e^{iαθ}`, **and** the branch family
`k ↦ e^{2πiαk}` is injective — so the value is genuinely single, with no finite
cyclic ambiguity (the defining contrast with the rational `p/q` case). -/
theorem irrational_exponent_single_valued {θ α : ℝ} (hα : Irrational α)
    (hθ_lo : -π < θ) (hθ_hi : θ ≤ π) :
    (Complex.exp (↑θ * Complex.I)) ^ (α : ℂ) = Complex.exp (↑(α * θ) * Complex.I) ∧
      Function.Injective (fun k : ℤ => Complex.exp (↑(2 * π * α * k) * Complex.I)) :=
  ⟨principal_value θ α hθ_lo hθ_hi, branch_injective hα⟩

/-- **The orbit never returns to its start.** A direct corollary: for irrational
`α`, `e^{2πiαn} = 1` only for `n = 0` — the multiplicative orbit `{e^{2πiαn}}` is a
free (infinite) family, the quantitative reason no `q`-th-root ambiguity arises. -/
theorem exp_two_pi_eq_one_iff {α : ℝ} (hα : Irrational α) (n : ℤ) :
    Complex.exp (↑(2 * π * α * n) * Complex.I) = 1 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    exact exp_two_pi_ne_one_of_irrational hα hn h
  · rintro rfl
    simp

end DeMoivreOQ03OQ01OQ01
