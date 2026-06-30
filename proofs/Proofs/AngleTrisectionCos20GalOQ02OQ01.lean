import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# angle-trisection-cos-20-gal OQ-02 → OQ-01: complex conjugation as the index-2 witness

The parent entry (`angle-trisection-cos-20-gal-oq-02`) proves the two algebraic facts behind
`[ℚ(cos 2π/n) : ℚ] = φ(n)/2`:

* `ζ = e^{iθ}` is a root of the **real** quadratic `X² − (2cos θ)X + 1`, so
  `[ℚ(ζ) : ℚ(cos θ)] ≤ 2`;
* `cos 2π/n` is a root of `Tₙ − 1` (Chebyshev witness).

It then lists as **open question OQ-1**:

> *Formalize `[ℚ(ζ_n) : ℚ(cos 2π/n)] = 2` by exhibiting complex conjugation as an order-2
> automorphism of `ℚ(ζ_n)` whose fixed field is the real subfield, then derive
> `[ℚ(cos 2π/n) : ℚ] = φ(n)/2`.*

The **abstract** Galois statement (conjugation's fixed field is the real subfield, and the
tower degree multiplies to `φ(n)/2`) needs the degree of the maximal real subfield of a
cyclotomic field, which Mathlib does not have — so it stays out of reach. What **is**
reachable, and is supplied here with `0` axioms, is the entire **element-level** content of
that witness — i.e. why the bound `≤ 2` is in fact an **equality** `= 2`:

1. **Conjugation maps `ζ` to the other root.** `conj(e^{iθ}) = e^{−iθ}` (`conj_zeta`), and the
   quadratic factors over its two roots `(z − ζ)(z − ζ⁻¹) = z² − (2cos θ)z + 1`
   (`quadratic_factor`). So the two roots are a complex-conjugate pair.
2. **Conjugation fixes the real coefficient.** `conj(2cos θ) = 2cos θ` (`conj_two_cos`): the
   quadratic lives over the real subfield, exactly as the tower `ℚ(cos θ) ⊆ ℚ(ζ)` requires.
3. **The two roots are genuinely distinct — the bound is sharp.** `ζ` is non-real iff
   `sin θ ≠ 0` (`zeta_im`, `conj_zeta_ne_self_iff`), and for every cyclotomic angle `θ = 2π/n`
   with `n ≥ 3` we have `sin(2π/n) > 0` (`sin_two_pi_div_pos`). Hence conjugation acts
   **nontrivially** on `ζ` (`cyclotomic_conj_ne_self`) and the two roots are distinct
   (`cyclotomic_roots_distinct`): the extension `ℚ(cos 2π/n) ⊆ ℚ(ζ_n)` is honestly degree `2`,
   not `1`, which is the source of the halving `φ(n)/2`.

This sharpens the parent's `≤ 2` to a verified degree-`2` dichotomy and provides the concrete
order-2 symmetry OQ-1 asks for, stopping precisely where Mathlib's missing real-subfield
degree begins. It does **not** prove the full field-degree formula.
-/

namespace AngleTrisectionCos20GalOQ02OQ01

open Complex

-- ============================================================
-- PART 1: Conjugation maps ζ to the other root ζ⁻¹
-- ============================================================

/-- **Complex conjugation sends `ζ = e^{iθ}` to the other root `e^{−iθ}`.** For real `θ`,
    `conj(θ·i) = −θ·i`, so `conj(e^{iθ}) = e^{−iθ}`. This is the concrete action of the
    order-2 automorphism OQ-1 refers to. -/
theorem conj_zeta (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * I)) = Complex.exp (-(θ : ℂ) * I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The product of the two roots is `1` (both lie on the unit circle, `e^{iθ}·e^{−iθ} = 1`). -/
theorem zeta_mul (x : ℂ) :
    Complex.exp (x * I) * Complex.exp (-x * I) = 1 := by
  rw [← Complex.exp_add, show x * I + -x * I = 0 by ring, Complex.exp_zero]

/-- The sum of the two roots is `2cos θ` (the real coefficient). -/
theorem zeta_add (x : ℂ) :
    Complex.exp (x * I) + Complex.exp (-x * I) = 2 * Complex.cos x :=
  (Complex.two_cos x).symm

/-- **The quadratic factors over its two roots.**
    `(z − e^{iθ})(z − e^{−iθ}) = z² − (2cos θ)z + 1`. The two roots `ζ, ζ⁻¹` are a
    conjugate pair (`conj_zeta`), so this is the minimal-type relation realizing the index-2
    step `ℚ(cos θ) ⊆ ℚ(ζ)`. -/
theorem quadratic_factor (x z : ℂ) :
    (z - Complex.exp (x * I)) * (z - Complex.exp (-x * I))
      = z ^ 2 - (2 * Complex.cos x) * z + 1 := by
  have hexpand : (z - Complex.exp (x * I)) * (z - Complex.exp (-x * I))
      = z ^ 2 - (Complex.exp (x * I) + Complex.exp (-x * I)) * z
        + Complex.exp (x * I) * Complex.exp (-x * I) := by ring
  rw [hexpand, zeta_add, zeta_mul]

-- ============================================================
-- PART 2: Conjugation fixes the real coefficient 2cos θ
-- ============================================================

/-- **Conjugation fixes `2cos θ`.** The quadratic's coefficient is real, so it is fixed by the
    order-2 automorphism — the quadratic genuinely lives over the real subfield `ℚ(cos θ)`. -/
theorem conj_two_cos (θ : ℝ) :
    (starRingEnd ℂ) (2 * (Real.cos θ : ℂ)) = 2 * (Real.cos θ : ℂ) := by
  rw [map_mul, map_ofNat, Complex.conj_ofReal]

-- ============================================================
-- PART 3: The two roots are genuinely distinct (the bound is sharp)
-- ============================================================

/-- The imaginary part of `ζ = e^{iθ}` is `sin θ`. -/
theorem zeta_im (θ : ℝ) : (Complex.exp ((θ : ℂ) * I)).im = Real.sin θ := by
  have hexp : Complex.exp ((θ : ℂ) * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

/-- **Conjugation acts nontrivially on `ζ` exactly when `sin θ ≠ 0`.** Since `conj z = z`
    iff `z` is real (`z.im = 0`), and `Im ζ = sin θ`, conjugation moves `ζ` precisely when
    `sin θ ≠ 0` — i.e. precisely when the two roots `ζ, ζ⁻¹` are distinct. -/
theorem conj_zeta_ne_self_iff (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * I)) ≠ Complex.exp ((θ : ℂ) * I)
      ↔ Real.sin θ ≠ 0 := by
  rw [Ne, Complex.conj_eq_iff_im, zeta_im]

/-- For `n ≥ 3`, the cyclotomic angle satisfies `sin(2π/n) > 0`, since `0 < 2π/n < π`. -/
theorem sin_two_pi_div_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < Real.sin (2 * Real.pi / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (by positivity) hn0
  · rw [div_lt_iff₀ hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]

/-- For `n ≥ 3`, `sin(2π/n) ≠ 0`. -/
theorem sin_two_pi_div_ne_zero (n : ℕ) (hn : 3 ≤ n) :
    Real.sin (2 * Real.pi / n) ≠ 0 :=
  ne_of_gt (sin_two_pi_div_pos n hn)

/-- **Conjugation moves the cyclotomic root `ζ_n` for every `n ≥ 3`.** This is the concrete
    nontrivial order-2 automorphism behind the index-2 step in `[ℚ(cos 2π/n):ℚ] = φ(n)/2`. -/
theorem cyclotomic_conj_ne_self (n : ℕ) (hn : 3 ≤ n) :
    (starRingEnd ℂ) (Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * I))
      ≠ Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * I) :=
  (conj_zeta_ne_self_iff _).mpr (sin_two_pi_div_ne_zero n hn)

/-- **The two roots of the quadratic are distinct for every cyclotomic angle `n ≥ 3`.**
    Hence the extension `ℚ(cos 2π/n) ⊆ ℚ(ζ_n)` is honestly degree `2` (not `1`): the source
    of the halving `φ(n)/2`. If the roots coincided, conjugation would fix `ζ_n`, contradicting
    `cyclotomic_conj_ne_self`. -/
theorem cyclotomic_roots_distinct (n : ℕ) (hn : 3 ≤ n) :
    Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * I)
      ≠ Complex.exp (-((2 * Real.pi / n : ℝ) : ℂ) * I) := by
  intro h
  apply cyclotomic_conj_ne_self n hn
  rw [conj_zeta]
  exact h.symm

-- ============================================================
-- PART 4: Consistency with φ(n)/2 (degree-2 witness ⇒ genuine halving)
-- ============================================================

/-- `cos 2π/9 = cos 40°` (the `cos 20°` trisection sibling): `φ(9)/2 = 3`, the cubic whose
    irreducibility forces the impossibility of trisecting `120°`. The degree-2 step proved
    above (conjugation, `n = 9 ≥ 3`) is the `÷2` taking `φ(9) = 6` to `3`. -/
theorem totient_div_two_nine : Nat.totient 9 / 2 = 3 := by decide

/-- `cos 2π/7` (regular heptagon): `φ(7)/2 = 3`. -/
theorem totient_div_two_seven : Nat.totient 7 / 2 = 3 := by decide

end AngleTrisectionCos20GalOQ02OQ01
