/-
# Chebyshev–De Moivre over arbitrary rings: finite fields, ℂ and ℚ_p
  (de-moivre-oq-01-oq-03)

## Open Question (OQ-03 of de-moivre-oq-01)
"Is there a Lean formalization of the Chebyshev–De Moivre connection over finite
fields (relevant to cryptography)?"  And, more broadly (OQ-02), can the connection
be extended to complex or p-adic settings?

## Answer: YES — and uniformly, over *any* commutative ring.

The analytic De Moivre / Chebyshev identity
  `C n (2 cos θ) = 2 cos (n θ)`           (Mathlib: `Chebyshev.C_two_mul_complex_cos`)
is the shadow of a purely *algebraic* identity that needs no analysis, no `cos`, and
no division by 2.  Writing the substitution `x = z + z⁻¹` (so `z` plays the role of
`e^{iθ}`), the Chebyshev polynomial of the **third kind** `C` — normalized by
`C 0 = 2`, `C 1 = X`, `C (n+2) = X · C (n+1) − C n` — satisfies

      **(C R n).eval (z + w) = zⁿ + wⁿ      whenever  z · w = 1.**

This is the algebraic heart of De Moivre's theorem: on the "unit circle" `z·w = 1`
the power map `z ↦ zⁿ` is conjugate to evaluation of a fixed integer polynomial.

Because the statement lives over an arbitrary `CommRing R`, it specializes **for free**
to every setting the open question asks about:

* **Finite fields** `𝔽_q` (e.g. `ZMod p`): take any unit `z`, `w = z⁻¹`. This is the
  cryptographically relevant case (Lucas sequences / torus-based and Chebyshev-based
  key exchange live exactly here).
* **The p-adic numbers** `ℚ_[p]`: one line, since `ℚ_[p]` is a field.
* **The complex numbers** `ℂ`: with `z = e^{iθ}` we recover `C n (2cos θ) = 2cos(nθ)`,
  reproving Mathlib's analytic theorem from the algebraic one.

## Status
- All theorems proved (0 sorries, 0 axioms, no `native_decide`).
- Engine: a two-step induction on the Chebyshev recurrence.
- Builds on `Mathlib.RingTheory.Polynomial.Chebyshev`.
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

namespace DeMoivreChebyshevFiniteField

open Polynomial.Chebyshev

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE ALGEBRAIC ENGINE  (arbitrary commutative ring)
═══════════════════════════════════════════════════════════════════════════════ -/

variable {R : Type*} [CommRing R]

/-- **The algebraic De Moivre–Chebyshev identity.**
    For any commutative ring `R` and any `z w : R` with `z · w = 1`,
    the Chebyshev polynomial of the third kind `C` satisfies
      `(C R n).eval (z + w) = zⁿ + wⁿ`.
    This is De Moivre's theorem stripped of all analysis: on the "unit circle"
    `z·w = 1`, the power map is evaluation of a fixed integer polynomial. -/
theorem chebyshevC_eval_add (z w : R) (hzw : z * w = 1) (n : ℕ) :
    (C R (n : ℤ)).eval (z + w) = z ^ n + w ^ n := by
  -- Prove `P n ∧ P (n+1)` by ordinary induction; this is the two-step induction
  -- matching the order-2 recurrence `C (n+2) = (z+w)·C (n+1) − C n`.
  suffices h : ∀ m : ℕ, (C R (m : ℤ)).eval (z + w) = z ^ m + w ^ m ∧
      (C R ((m : ℤ) + 1)).eval (z + w) = z ^ (m + 1) + w ^ (m + 1) by
    exact (h n).1
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [Nat.cast_zero, C_zero, Polynomial.eval_ofNat, pow_zero]; norm_num
    · simp [C_one]
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨by exact_mod_cast ih1, ?_⟩
    -- Goal: (C R (↑(k+1) + 1)).eval (z+w) = z^(k+1+1) + w^(k+1+1)
    have hrec : C R ((k : ℤ) + 2)
        = Polynomial.X * C R ((k : ℤ) + 1) - C R (k : ℤ) :=
      C_add_two R (k : ℤ)
    have hidx : (((k + 1 : ℕ) : ℤ) + 1) = (k : ℤ) + 2 := by push_cast; ring
    rw [hidx, hrec]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
    rw [ih1, ih0]
    -- (z+w)·(z^(k+1)+w^(k+1)) − (z^k+w^k) = z^(k+2)+w^(k+2), using z·w = 1
    linear_combination (z ^ k + w ^ k) * hzw

/-- **Units version.** For a unit `z : Rˣ`,
      `(C R n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`. -/
theorem chebyshevC_eval_units (z : Rˣ) (n : ℕ) :
    (C R (n : ℤ)).eval ((z : R) + (↑z⁻¹ : R)) = (z : R) ^ n + (↑z⁻¹ : R) ^ n :=
  chebyshevC_eval_add (z : R) (↑z⁻¹ : R) z.mul_inv n

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: FIELDS — finite fields, ℚ_p, ℂ all at once
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Field version.** In any field `F`, for `z ≠ 0`,
      `(C F n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`.
    This single statement specializes to finite fields, the p-adics, ℝ and ℂ. -/
theorem chebyshevC_eval_field {F : Type*} [Field F] (z : F) (hz : z ≠ 0) (n : ℕ) :
    (C F (n : ℤ)).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n :=
  chebyshevC_eval_add z z⁻¹ (mul_inv_cancel₀ hz) n

/-- **Finite-field form.** For a prime `p` and a nonzero `z : ZMod p`,
      `(C (ZMod p) n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`.
    This is the cryptographically relevant case (e.g. Lucas/Chebyshev sequences
    over `𝔽_p`). -/
theorem chebyshevC_eval_zmod (p : ℕ) [Fact p.Prime] (z : ZMod p) (hz : z ≠ 0)
    (n : ℕ) :
    (C (ZMod p) (n : ℤ)).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n :=
  chebyshevC_eval_field z hz n

/-- **p-adic form.** Over `ℚ_[p]`, for `z ≠ 0`,
      `(C ℚ_[p] n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`.
    Answers the "p-adic setting" part of the open question. -/
theorem chebyshevC_eval_padic (p : ℕ) [Fact p.Prime] (z : ℚ_[p]) (hz : z ≠ 0)
    (n : ℕ) :
    (C ℚ_[p] (n : ℤ)).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n :=
  chebyshevC_eval_field z hz n

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE COMPLEX SHADOW — recovering `C n (2cos θ) = 2cos (n θ)`
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The algebraic identity over `ℂ` with `z = e^{iθ}` reproves the analytic
    De Moivre–Chebyshev theorem `C n (2 cos θ) = 2 cos (n θ)` (Mathlib's
    `Chebyshev.C_two_mul_complex_cos`) — now as a *corollary* of pure algebra. -/
theorem chebyshevC_complex_cos (θ : ℂ) (n : ℕ) :
    (C ℂ (n : ℤ)).eval (2 * Complex.cos θ) = 2 * Complex.cos ((n : ℂ) * θ) := by
  -- `2 cos x = e^{ix} + e^{-ix}` for every `x`.
  have two_cos : ∀ x : ℂ,
      2 * Complex.cos x
        = Complex.exp (x * Complex.I) + Complex.exp (-(x * Complex.I)) := by
    intro x; rw [Complex.cos, neg_mul]; ring
  have hz : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  -- Rewrite `2 cos θ` as `z + z⁻¹` with `z = e^{iθ}`.
  have e1 : (2 : ℂ) * Complex.cos θ
      = Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹ := by
    rw [two_cos, Complex.exp_neg]
  -- `zⁿ = e^{i n θ}` and `(z⁻¹)ⁿ = e^{-i n θ}`.
  have hzpow : Complex.exp (θ * Complex.I) ^ n
      = Complex.exp (((n : ℂ) * θ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; congr 1; ring
  have hwpow : ((Complex.exp (θ * Complex.I))⁻¹) ^ n
      = Complex.exp (-(((n : ℂ) * θ) * Complex.I)) := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; congr 1; ring
  rw [e1, chebyshevC_eval_field (Complex.exp (θ * Complex.I)) hz n, hzpow, hwpow,
    two_cos]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: CONCRETE FINITE-FIELD EXAMPLES (cryptographic flavour)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- In `ZMod 7`: `3` is a unit with `3⁻¹ = 5`, `3 + 3⁻¹ = 1`, and
    `C 2 (1) = 1² − 2 = −1 = 6`, matching `3² + (3⁻¹)² = 2 + 4 = 6`. -/
example : (C (ZMod 7) (2 : ℤ)).eval ((3 : ZMod 7) + (3 : ZMod 7)⁻¹)
    = (3 : ZMod 7) ^ 2 + ((3 : ZMod 7)⁻¹) ^ 2 := by
  have h3 : (3 : ZMod 7) ≠ 0 := by decide
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact chebyshevC_eval_zmod 7 3 h3 2

/-- Same data, both sides reduced to the explicit value `6 : ZMod 7`. -/
example : (3 : ZMod 7) ^ 2 + ((3 : ZMod 7)⁻¹) ^ 2 = 6 := by decide

/-- In `ZMod 11`: a degree-3 instance over a different finite field. -/
example : (C (ZMod 11) (3 : ℤ)).eval ((2 : ZMod 11) + (2 : ZMod 11)⁻¹)
    = (2 : ZMod 11) ^ 3 + ((2 : ZMod 11)⁻¹) ^ 3 := by
  have h2 : (2 : ZMod 11) ≠ 0 := by decide
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact chebyshevC_eval_zmod 11 2 h2 3

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @chebyshevC_eval_add
#check @chebyshevC_eval_units
#check @chebyshevC_eval_field
#check @chebyshevC_eval_zmod
#check @chebyshevC_eval_padic
#check @chebyshevC_complex_cos

end DeMoivreChebyshevFiniteField
