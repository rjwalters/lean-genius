/-
# De Moivre OQ-01-02-02: the single Laurent identity behind both sin and sinh ratios

The parent entry (`DeMoivreOQ01OQ02`) proved that **one** Chebyshev polynomial `Tₙ`
governs both the circular and hyperbolic *cosine* multiple-angle maps
(`cos (n z) = Tₙ(cos z)` and `cosh (n z) = Tₙ(cosh z)`), because `cos (i z) = cosh z`.

The open question asks: does the *same* unification extend to `Uₙ` — is there a single
polynomial identity that simultaneously yields the **sine ratio** `sin((n+1)z)/sin z`
and the **hyperbolic sine ratio** `sinh((n+1)z)/sinh z`?

**Answer: yes, and the common root is purely algebraic.** For any unit `w` in a field,

  `Uₙ((w + w⁻¹)/2) · (w − w⁻¹) = wⁿ⁺¹ − w⁻⁽ⁿ⁺¹⁾`.               (★)

This Laurent identity is not in Mathlib (Mathlib records the two analytic
specializations `U_complex_cos` / `U_complex_cosh` separately). Here we:

* prove (★) over `ℂ` from scratch by two-step induction on the Chebyshev recurrence
  (`U_resolvent`); it is a statement about the polynomial `Uₙ` alone, no transcendental
  functions;
* specialize `w = exp z` to recover the hyperbolic-sine ratio (`U_resolvent_sinh`);
* specialize `w = exp (i z)` to recover the circular-sine ratio (`U_resolvent_sin`).

Thus a single algebraic identity — evaluating the *same* `Uₙ` at `(w+w⁻¹)/2` — produces
both ratios, exactly mirroring the parent's `Tₙ` unification.

We also record the direct packaged mirror `U_eval_cos_and_cosh` of the parent's
`T_eval_cos_and_cosh`.
-/
import Mathlib

open Polynomial Polynomial.Chebyshev Complex

namespace DeMoivreOQ01OQ02OQ02

/-! ## Part 1: The unifying algebraic Laurent identity (★) -/

/-- Two-variable core of the Laurent identity: for `w, v` with `w · v = 1`,
`Uₙ((w+v)/2) · (w − v) = wⁿ⁺¹ − vⁿ⁺¹`. The constraint `w · v = 1` (i.e. `v = w⁻¹`) is
used only in the inductive step, via `linear_combination`. -/
theorem U_resolvent_aux (w v : ℂ) (hwv : w * v = 1) (n : ℕ) :
    (U ℂ (n : ℤ)).eval ((w + v) / 2) * (w - v) = w ^ (n + 1) - v ^ (n + 1) := by
  -- Prove the paired statement `P n ∧ P (n+1)` by ordinary induction; the Chebyshev
  -- recurrence relates index `n+2` to `n+1` and `n`.
  suffices h : ∀ m : ℕ,
      ((U ℂ (m : ℤ)).eval ((w + v) / 2) * (w - v) = w ^ (m + 1) - v ^ (m + 1)) ∧
      ((U ℂ ((m : ℤ) + 1)).eval ((w + v) / 2) * (w - v) = w ^ (m + 2) - v ^ (m + 2)) by
    have := (h n).1
    simpa using this
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [Int.natCast_zero, U_zero, eval_one, one_mul]; ring
    · simp only [Int.natCast_zero, zero_add, U_one, eval_mul, eval_ofNat, eval_X]
      ring
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨by simpa using ih1, ?_⟩
    -- `P (k+2)` from the recurrence `U (k+2) = 2 X · U (k+1) − U k`.
    push_cast
    have hrec : (U ℂ ((k : ℤ) + 2)) = 2 * X * (U ℂ ((k : ℤ) + 1)) - U ℂ (k : ℤ) :=
      U_add_two ℂ (k : ℤ)
    have hcast : ((k : ℤ) + 1) + 1 = ((k : ℤ) + 2) := by ring
    have heval :
        (U ℂ ((k : ℤ) + 1 + 1)).eval ((w + v) / 2)
          = 2 * ((w + v) / 2) * (U ℂ ((k : ℤ) + 1)).eval ((w + v) / 2)
            - (U ℂ (k : ℤ)).eval ((w + v) / 2) := by
      rw [hcast, hrec]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    have key :
        (U ℂ ((k : ℤ) + 1 + 1)).eval ((w + v) / 2) * (w - v)
          = (w + v) * ((U ℂ ((k : ℤ) + 1)).eval ((w + v) / 2) * (w - v))
            - (U ℂ (k : ℤ)).eval ((w + v) / 2) * (w - v) := by
      rw [heval]; ring
    rw [key, ih1, ih0]
    -- Residual is `(w·v − 1)·(wᵏ⁺¹ − vᵏ⁺¹) = 0`; supply the constraint to `ring`.
    linear_combination (w ^ (k + 1) - v ^ (k + 1)) * hwv

/-- **The single polynomial identity behind both ratios.**
For any nonzero `w : ℂ`, evaluating the `n`-th Chebyshev polynomial of the second kind
at `(w + w⁻¹)/2` gives the Laurent "resolvent"
`Uₙ((w+w⁻¹)/2) · (w − w⁻¹) = wⁿ⁺¹ − w⁻⁽ⁿ⁺¹⁾`.

This is proved directly from the Chebyshev recurrence `U_add_two`, with no reference to
trigonometric or hyperbolic functions. Both the circular and hyperbolic sine-ratio
formulas are specializations (see `U_resolvent_sin`, `U_resolvent_sinh`). -/
theorem U_resolvent (w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    (U ℂ (n : ℤ)).eval ((w + w⁻¹) / 2) * (w - w⁻¹)
      = w ^ (n + 1) - (w⁻¹) ^ (n + 1) :=
  U_resolvent_aux w w⁻¹ (mul_inv_cancel₀ hw) n

/-! ## Part 2: Both ratios as specializations of the single identity (★) -/

/-- **Hyperbolic-sine ratio from (★).** Setting `w = exp z` in `U_resolvent` turns
`(w+w⁻¹)/2` into `cosh z`, `w − w⁻¹` into `2 sinh z`, and `wⁿ⁺¹ − w⁻⁽ⁿ⁺¹⁾` into
`2 sinh((n+1)z)`, recovering `sinh((n+1)z) = Uₙ(cosh z)·sinh z`. -/
theorem U_resolvent_sinh (z : ℂ) (n : ℕ) :
    (U ℂ (n : ℤ)).eval (Complex.cosh z) * Complex.sinh z
      = Complex.sinh (((n : ℂ) + 1) * z) := by
  have h := U_resolvent (Complex.exp z) (Complex.exp_ne_zero z) n
  have hA : (Complex.exp z + (Complex.exp z)⁻¹) / 2 = Complex.cosh z := by
    rw [← Complex.exp_neg, ← Complex.two_cosh]; ring
  have hB : Complex.exp z - (Complex.exp z)⁻¹ = 2 * Complex.sinh z := by
    rw [← Complex.exp_neg]; exact (Complex.two_sinh z).symm
  have hC : (Complex.exp z) ^ (n + 1) - ((Complex.exp z)⁻¹) ^ (n + 1)
      = 2 * Complex.sinh (((n : ℂ) + 1) * z) := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.two_sinh]
    push_cast
    congr 2
    ring
  rw [hA, hB, hC] at h
  exact mul_left_cancel₀ (two_ne_zero) (by linear_combination h)

/-- **Circular-sine ratio from (★).** Substituting `z = x·i` into `U_resolvent_sinh`
(via `cosh (x i) = cos x`, `sinh (x i) = sin x · i`) recovers
`sin((n+1)x) = Uₙ(cos x)·sin x`. The *same* algebraic identity (★) therefore yields both
ratios. -/
theorem U_resolvent_sin (x : ℂ) (n : ℕ) :
    (U ℂ (n : ℤ)).eval (Complex.cos x) * Complex.sin x
      = Complex.sin (((n : ℂ) + 1) * x) := by
  have h := U_resolvent_sinh (x * Complex.I) n
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I,
      show ((n : ℂ) + 1) * (x * Complex.I) = (((n : ℂ) + 1) * x) * Complex.I from by ring,
      Complex.sinh_mul_I] at h
  exact mul_right_cancel₀ Complex.I_ne_zero (by linear_combination h)

/-! ## Part 3: The packaged "one polynomial `Uₙ`, both ratios" statement -/

/-- **Direct mirror of the parent's `T_eval_cos_and_cosh`.** A single statement records
that the *same* `Uₙ` produces both the circular sine ratio and the hyperbolic sine ratio.
(Packaged form of Mathlib's `U_complex_cos` / `U_complex_cosh`.) -/
theorem U_eval_cos_and_cosh (z : ℂ) (n : ℤ) :
    ((U ℂ n).eval (Complex.cos z) * Complex.sin z = Complex.sin (((n : ℂ) + 1) * z)) ∧
    ((U ℂ n).eval (Complex.cosh z) * Complex.sinh z = Complex.sinh (((n : ℂ) + 1) * z)) :=
  ⟨U_complex_cos z n, U_complex_cosh z n⟩

end DeMoivreOQ01OQ02OQ02
