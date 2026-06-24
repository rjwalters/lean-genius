/-
# Gamma Reflection OQ-01-OQ-02: `1/Γ` as an entire function with zero set the non-positive integers

**Open Question (parent `GammaReflectionFormulaOQ01`).** The parent entry records Euler's
reflection formula and the non-vanishing corollary `sin(π s) ≠ 0 ⟹ Γ s ≠ 0`. Reflection
shows where `Γ` does *not* vanish; the dual object is the **reciprocal Gamma function**
`1/Γ`, which is the canonical *entire* completion of `Γ`: where `Γ` has its simple poles
(the non-positive integers), `1/Γ` has its zeros, and nowhere else.

This file packages `1/Γ` as that entire function and pins down its zero set exactly.

## What is new

Mathlib already has the two ingredients as *separate* facts:

* `Complex.differentiable_one_div_Gamma` — `s ↦ (Γ s)⁻¹` is differentiable on all of `ℂ`;
* `Complex.Gamma_eq_zero_iff` — `Γ s = 0 ↔ s` is a non-positive integer.

Neither Mathlib nor the parent entry combines them into the statement that `1/Γ` is an
**entire function whose zero set is *exactly* the non-positive integers**, and Mathlib does
not record the structural consequences derived here:

* the zero set `{z | (Γ z)⁻¹ = 0}` equals `{0, -1, -2, …}` as a set (`zeroSet_invGamma`);
* that zero set is **countable** (`countable_zeroSet`);
* `1/Γ` is **not identically zero** (`invGamma_one : (Γ 1)⁻¹ = 1`), hence by the analytic
  identity theorem **every zero is isolated** (`isolated_zeros`) — i.e. each pole of `Γ` is
  a genuine, isolated point of the zero locus of `1/Γ`.

## Method

`(Γ z)⁻¹ = 0 ↔ Γ z = 0` (`inv_eq_zero`) reduces the zero-set question to Mathlib's
`Gamma_eq_zero_iff`. Entirety is `differentiable_one_div_Gamma`, promoted to `AnalyticOnNhd`
via `Differentiable.analyticAt` (holomorphic ⟹ analytic on `ℂ`). Isolation of zeros uses the
principle of isolated zeros (`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`); the
"identically zero near a point" branch is killed by the identity theorem
(`eqOn_zero_of_preconnected_of_eventuallyEq_zero` on the preconnected set `univ`) together
with `(Γ 1)⁻¹ = 1 ≠ 0`.

## References

* Mathlib: `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`,
  `Mathlib/Analysis/Analytic/IsolatedZeros.lean`,
  `Mathlib/Analysis/Analytic/Uniqueness.lean`.
* Whittaker & Watson, *A Course of Modern Analysis*, §12.1 (the function `1/Γ`).
-/
import Mathlib

namespace GammaReflectionFormulaOQ01OQ02

open Complex
open scoped Topology

/-- The non-positive integers `{0, -1, -2, …}` as a subset of `ℂ`. -/
def nonposInt : Set ℂ := {z : ℂ | ∃ n : ℕ, z = -n}

/-! ## `1/Γ` is entire -/

/-- **`1/Γ` is entire.** The reciprocal Gamma function `s ↦ (Γ s)⁻¹` is differentiable on all
of `ℂ`, including the non-positive integers where `Γ` itself blows up. (Re-export of Mathlib's
`differentiable_one_div_Gamma` under a stable name.) -/
theorem differentiable_invGamma : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ :=
  Complex.differentiable_one_div_Gamma

/-- `1/Γ` is analytic at every point of `ℂ` (holomorphic on `ℂ` ⟹ analytic). -/
theorem analyticAt_invGamma (z : ℂ) : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) z :=
  differentiable_invGamma.analyticAt z

/-- `1/Γ` is analytic on all of `ℂ`: an entire function. -/
theorem analyticOnNhd_invGamma :
    AnalyticOnNhd ℂ (fun s : ℂ => (Gamma s)⁻¹) Set.univ :=
  fun z _ => analyticAt_invGamma z

/-! ## The zero set is exactly the non-positive integers -/

/-- **Zero criterion:** `(Γ z)⁻¹ = 0` iff `z` is a non-positive integer. The reciprocal
vanishes precisely at the poles of `Γ`. -/
theorem invGamma_eq_zero_iff (z : ℂ) :
    (Gamma z)⁻¹ = 0 ↔ ∃ n : ℕ, z = -n := by
  rw [inv_eq_zero, Complex.Gamma_eq_zero_iff]

/-- **Non-vanishing criterion:** `(Γ z)⁻¹ ≠ 0` iff `z` avoids every non-positive integer. -/
theorem invGamma_ne_zero_iff (z : ℂ) :
    (Gamma z)⁻¹ ≠ 0 ↔ ∀ n : ℕ, z ≠ -n := by
  simp only [ne_eq, invGamma_eq_zero_iff, not_exists]

/-- **The zero set of `1/Γ` is exactly `{0, -1, -2, …}`.** -/
theorem zeroSet_invGamma :
    {z : ℂ | (Gamma z)⁻¹ = 0} = nonposInt := by
  ext z; exact invGamma_eq_zero_iff z

/-- The non-positive integers are the range of `n ↦ -n`, hence a countable subset of `ℂ`. -/
theorem nonposInt_eq_range : nonposInt = Set.range (fun n : ℕ => -(n : ℂ)) := by
  ext z
  simp only [nonposInt, Set.mem_setOf_eq, Set.mem_range, eq_comm]

/-- **The zero set of `1/Γ` is countable.** -/
theorem countable_zeroSet : {z : ℂ | (Gamma z)⁻¹ = 0}.Countable := by
  rw [zeroSet_invGamma, nonposInt_eq_range]
  exact Set.countable_range _

/-! ## Concrete values and the recurrence -/

/-- `1/Γ` is **not** identically zero: `(Γ 1)⁻¹ = 1`. -/
theorem invGamma_one : (Gamma (1 : ℂ))⁻¹ = 1 := by
  rw [Complex.Gamma_one, inv_one]

/-- A sample zero: `(Γ 0)⁻¹ = 0` (the pole of `Γ` at the origin). -/
theorem invGamma_zero : (Gamma (0 : ℂ))⁻¹ = 0 := by
  rw [Complex.Gamma_zero, inv_zero]

/-- A sample zero away from the origin: `(Γ (-3))⁻¹ = 0`. -/
theorem invGamma_neg_three : (Gamma (-3 : ℂ))⁻¹ = 0 := by
  rw [invGamma_eq_zero_iff]
  exact ⟨3, by norm_num⟩

/-- **The functional equation of `1/Γ`** (valid everywhere, including at `s = 0`):
`(Γ s)⁻¹ = s · (Γ (s+1))⁻¹`. Reading off the factor `s` re-derives the zero at `s = 0`, and
iterating produces the full ladder of zeros at `0, -1, -2, …`. -/
theorem invGamma_recurrence (s : ℂ) :
    (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ :=
  Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s

/-! ## Every zero is isolated -/

/-- **The zeros of `1/Γ` are isolated.** At any zero `z` of `1/Γ`, the function is nonzero
throughout some punctured neighborhood of `z`. (So the poles of `Γ` are isolated points of the
zero locus of `1/Γ`, none of them an accumulation point of zeros.)

The proof applies the principle of isolated zeros to the entire function `1/Γ`; the alternative
"`1/Γ ≡ 0` near `z`" is impossible because, by the identity theorem on the preconnected set `ℂ`,
it would force `1/Γ ≡ 0` everywhere, contradicting `(Γ 1)⁻¹ = 1`. -/
theorem isolated_zeros {z : ℂ} (_hz : (Gamma z)⁻¹ = 0) :
    ∀ᶠ w in 𝓝[≠] z, (Gamma w)⁻¹ ≠ 0 := by
  rcases (analyticAt_invGamma z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · -- `1/Γ` identically zero near `z` ⟹ identically zero on `ℂ` ⟹ contradicts `(Γ 1)⁻¹ = 1`
    exfalso
    have h' : (fun s : ℂ => (Gamma s)⁻¹) =ᶠ[𝓝 z] 0 := by
      filter_upwards [h] with w hw using hw
    have hEq : Set.EqOn (fun s : ℂ => (Gamma s)⁻¹) 0 Set.univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        analyticOnNhd_invGamma isPreconnected_univ (Set.mem_univ z) h'
    have : (Gamma (1 : ℂ))⁻¹ = 0 := hEq (Set.mem_univ 1)
    rw [invGamma_one] at this
    exact one_ne_zero this
  · exact h

end GammaReflectionFormulaOQ01OQ02
