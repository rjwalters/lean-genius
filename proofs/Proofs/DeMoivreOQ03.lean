import Mathlib

/-
# De Moivre OQ-03: Fractional Exponents and Root Extraction

## Research Problem: de-moivre-oq-03
Extend De Moivre's theorem to fractional exponents z^(p/q).

## Mathematical Content

De Moivre's theorem for integer exponents states:
  (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)

This file extends the result to fractional exponents via root extraction.

Key Theorem (Root Enumeration via De Moivre):
The q-th roots of (e^{iθ})^p are precisely:
  ζ_k = exp(i(pθ + 2πk)/q)  for k = 0, 1, ..., q-1

Key Theorem (Fractional De Moivre — Principal Value):
For -π < θ ≤ π (principal argument range):
  cpow(e^{iθ}, p/q) = exp(ipθ/q) = cos(pθ/q) + i sin(pθ/q)

Key Theorem (Root Distinctness):
The q roots ζ_0, ..., ζ_{q-1} are all distinct.

## References
- De Moivre (1707): Original theorem for integer exponents
- Euler (1748): Extension via exponential form
- Needham (1997): "Visual Complex Analysis"
-/

open Complex Real

namespace DeMoivreOQ03

-- The k-th candidate q-th root of e^{ipθ}
noncomputable def qthRoot (θ : ℝ) (p : ℤ) (q : ℕ) (k : ℕ) : ℂ :=
  Complex.exp (↑((↑p * θ + 2 * π * ↑k) / ↑q) * I)

/-! ## Part I: Root Verification -/

/-- Each candidate root, raised to the q-th power, equals e^{ipθ} = (e^{iθ})^p.
    Proof: ζ_k^q = exp(iq(pθ + 2πk)/q) = exp(i(pθ + 2πk)) = exp(ipθ) · exp(2πik)
         = exp(ipθ) · 1 = (e^{iθ})^p. -/
theorem qthRoot_pow_eq (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (qthRoot θ p q k) ^ q = Complex.exp (↑θ * I) ^ p := by
  simp only [qthRoot]
  rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  have hq_ne_r : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Simplify the LHS exponent: q * ((pθ + 2πk)/q * I) = (pθ + 2πk) * I
  have h1 : (↑q : ℂ) * (↑((↑p * θ + 2 * π * ↑k) / ↑q) * I) =
      (↑(↑p * θ) + ↑(2 * π * ↑k)) * I := by
    rw [show (↑q : ℂ) * (↑((↑p * θ + 2 * π * ↑k) / ↑q) * I) =
        (↑q * ↑((↑p * θ + 2 * π * ↑k) / ↑q)) * I from by ring]
    congr 1
    rw [← ofReal_natCast, ← ofReal_mul, mul_div_cancel₀ _ hq_ne_r]
    push_cast; ring
  rw [h1]
  -- Split: exp((pθ + 2πk)i) = exp(pθi) · exp(2πki)
  have h2 : ((↑(↑p * θ) + ↑(2 * π * ↑k)) * I : ℂ) =
      ↑(↑p * θ) * I + ↑(2 * π * ↑k) * I := by ring
  rw [h2, Complex.exp_add]
  -- exp(2πki) = 1
  have h3 : Complex.exp (↑(2 * π * ↑k) * I) = 1 := by
    rw [show (↑(2 * π * ↑k) : ℂ) * I = ↑k * (2 * ↑π * I) from by push_cast; ring]
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  rw [h3, mul_one]
  congr 1; push_cast; ring

/-! ## Part II: Roots via Roots of Unity -/

-- The k-th q-th root of unity
noncomputable def rootOfUnity (q k : ℕ) : ℂ :=
  Complex.exp (2 * ↑π * I * ↑k / ↑q)

/-- Roots of unity are q-th roots of 1. -/
theorem rootOfUnity_pow (q : ℕ) (hq : 0 < q) (k : ℕ) :
    (rootOfUnity q k) ^ q = 1 := by
  simp only [rootOfUnity]
  rw [← Complex.exp_nat_mul]
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : (↑q : ℂ) * (2 * ↑π * I * ↑k / ↑q) = ↑k * (2 * ↑π * I) := by
    field_simp
  rw [h, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

/-- Root Factorization: ζ_k = ζ_0 · ω_k where ω_k = exp(2πik/q). -/
theorem qthRoot_eq_principal_mul_unity (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (k : ℕ) :
    qthRoot θ p q k = qthRoot θ p q 0 * rootOfUnity q k := by
  simp only [qthRoot, rootOfUnity, Nat.cast_zero, mul_zero, add_zero]
  rw [← Complex.exp_add]
  congr 1
  have hq_ne_r : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (↑p * θ + 2 * π * ↑k) / (↑q : ℝ) = ↑p * θ / ↑q + 2 * π * ↑k / ↑q := by
    rw [add_div]
  rw [h1]; push_cast; ring

/-! ## Part III: Root Distinctness -/

/-- Two different roots (with indices in [0, q)) are distinct. -/
theorem qthRoot_distinct (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (j k : ℕ) (hj : j < q) (hk : k < q) (hjk : j ≠ k) :
    qthRoot θ p q j ≠ qthRoot θ p q k := by
  simp only [qthRoot]
  intro h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨m, hm⟩ := h
  have hq_ne_r : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Cancel I from hm to get real equation
  have hI_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_cancel : (↑((↑p * θ + 2 * π * ↑j) / ↑q) : ℂ) =
      ↑((↑p * θ + 2 * π * ↑k) / ↑q) + (↑m : ℂ) * (2 * ↑π) := by
    apply mul_right_cancel₀ hI_ne
    convert hm using 1
    ring
  -- Extract real equation
  have hreal : (↑p * θ + 2 * π * ↑j) / (↑q : ℝ) =
      (↑p * θ + 2 * π * ↑k) / ↑q + 2 * π * ↑m := by
    apply Complex.ofReal_injective
    rw [h_cancel]; push_cast; ring
  -- Clear fractions: multiply hreal by q to get: pθ + 2πj = pθ + 2πk + 2πmq
  have hq_pos : (↑q : ℝ) > 0 := by positivity
  have h_cleared : ↑p * θ + 2 * π * (↑j : ℝ) = ↑p * θ + 2 * π * ↑k + 2 * π * ↑m * ↑q := by
    calc ↑p * θ + 2 * π * ↑j
        = ((↑p * θ + 2 * π * ↑j) / ↑q) * ↑q := by rw [div_mul_cancel₀ _ (ne_of_gt hq_pos)]
      _ = ((↑p * θ + 2 * π * ↑k) / ↑q + 2 * π * ↑m) * ↑q := by rw [hreal]
      _ = (↑p * θ + 2 * π * ↑k) / ↑q * ↑q + 2 * π * ↑m * ↑q := by ring
      _ = (↑p * θ + 2 * π * ↑k) + 2 * π * ↑m * ↑q := by rw [div_mul_cancel₀ _ (ne_of_gt hq_pos)]
  -- Cancel 2π: j = k + mq, then j - k = mq
  have h2pi_ne : (2 : ℝ) * π ≠ 0 := by positivity
  have h_jk : (↑j : ℝ) = ↑k + ↑m * ↑q := by
    have h1 : 2 * π * (↑j : ℝ) = 2 * π * (↑k + ↑m * ↑q) := by linarith
    exact mul_left_cancel₀ h2pi_ne h1
  have h_int : (j : ℤ) - k = m * q := by
    have : (↑j : ℝ) - ↑k = ↑m * ↑q := by linarith [h_jk]
    exact_mod_cast this
  -- |j - k| < q since j, k < q, so m = 0
  have hm0 : m = 0 := by
    by_contra hm_ne
    have h1 : 1 ≤ |m| := Int.one_le_abs hm_ne
    have h_abs_q : |(↑q : ℤ)| = (q : ℤ) := abs_of_nonneg (by omega)
    have h2 : (q : ℤ) ≤ |m * ↑q| := by
      rw [abs_mul, h_abs_q]; nlinarith
    have h3 : |((j : ℤ) - k)| < q := by rw [abs_lt]; constructor <;> omega
    rw [← h_int] at h2; omega
  rw [hm0] at h_int; simp at h_int
  exact hjk (by omega)

/-- **Cyclic periodicity of the root index.** Shifting the index `k` by `q`
returns the *same* root, because it rotates the argument by a full turn `2π`:
`ζ_{k+q} = exp(i(pθ + 2π(k+q))/q) = exp(i(pθ + 2πk)/q) · exp(2πi) = ζ_k`.
Together with `qthRoot_distinct` (the `q` indices in `[0, q)` give distinct
values) this pins the value set to *exactly* `q` roots, indexed cyclically
modulo `q`. This cyclic identification `k ∼ k + q` of the index is precisely
the combinatorial seed of the `q`-sheeted Riemann surface of `z ↦ z^{p/q}`:
the sheets are the residues `k mod q`, and crossing a branch cut advances `k`
by one, wrapping back to the start after `q` crossings. -/
theorem qthRoot_periodic (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (k : ℕ) :
    qthRoot θ p q (k + q) = qthRoot θ p q k := by
  simp only [qthRoot]
  have hq_ne_r : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- The two arguments differ by exactly 2π.
  have hexp : (↑p * θ + 2 * π * ↑(k + q)) / (q : ℝ) =
      (↑p * θ + 2 * π * ↑k) / ↑q + 2 * π := by
    rw [Nat.cast_add]; field_simp; ring
  rw [show (↑((↑p * θ + 2 * π * ↑(k + q)) / ↑q) : ℂ) * I =
        ↑((↑p * θ + 2 * π * ↑k) / ↑q + 2 * π) * I from by
      congr 1; exact_mod_cast hexp]
  rw [show (↑((↑p * θ + 2 * π * ↑k) / ↑q + 2 * π) : ℂ) * I =
        ↑((↑p * θ + 2 * π * ↑k) / ↑q) * I + 2 * ↑π * I from by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-! ## Part IV: Principal Value via cpow -/

/-- Fractional De Moivre (Principal Value): For θ in the principal range,
    cpow(e^{iθ}, p/q) = exp(ipθ/q). -/
theorem fractional_de_moivre (θ : ℝ) (p : ℤ) (q : ℕ) (_hq : 0 < q)
    (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) :
    Complex.exp (↑θ * I) ^ ((p : ℂ) / (q : ℂ)) =
    Complex.exp (↑(↑p * θ / ↑q) * I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  have hlog : Complex.log (Complex.exp (↑θ * I)) = ↑θ * I := by
    apply Complex.log_exp
    · show -π < (↑θ * I).im
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]
      exact hθ₁
    · show (↑θ * I).im ≤ π
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re]
      exact hθ₂
  rw [hlog]
  congr 1; push_cast; ring

/-- Fractional De Moivre (Trigonometric Form): For θ in the principal range,
    cpow(e^{iθ}, p/q) = cos(pθ/q) + i sin(pθ/q). -/
theorem fractional_de_moivre_trig (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) :
    Complex.exp (↑θ * I) ^ ((p : ℂ) / (q : ℂ)) =
    ↑(Real.cos (↑p * θ / ↑q)) + ↑(Real.sin (↑p * θ / ↑q)) * I := by
  rw [fractional_de_moivre θ p q hq hθ₁ hθ₂, Complex.exp_mul_I]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

/-- The principal cpow value equals the k=0 root. -/
theorem cpow_eq_principal_root (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) :
    Complex.exp (↑θ * I) ^ ((p : ℂ) / (q : ℂ)) = qthRoot θ p q 0 := by
  rw [fractional_de_moivre θ p q hq hθ₁ hθ₂]
  simp only [qthRoot, Nat.cast_zero, mul_zero, add_zero]

/-! ## Part V: Consistency with Integer De Moivre -/

/-- When q = 1, fractional De Moivre reduces to integer De Moivre. -/
theorem fractional_reduces_to_integer (θ : ℝ) (p : ℤ) :
    Complex.exp (↑θ * I) ^ ((p : ℂ) / (1 : ℂ)) =
    Complex.exp (↑θ * I) ^ p := by
  rw [div_one, Complex.cpow_intCast]

/-- Raising the principal p/q power to q gives z^p. -/
theorem fractional_power_consistency (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) :
    (Complex.exp (↑θ * I) ^ ((p : ℂ) / (q : ℂ))) ^ (q : ℕ) =
    Complex.exp (↑θ * I) ^ p := by
  rw [cpow_eq_principal_root θ p q hq hθ₁ hθ₂]
  exact qthRoot_pow_eq θ p q hq 0

/-! ## Part VI: Square Root Special Case -/

/-- The two square roots of e^{iθ} both satisfy ζ² = e^{iθ}. -/
theorem sqrt_roots (θ : ℝ) :
    (qthRoot θ 1 2 0) ^ 2 = Complex.exp (↑θ * I) ∧
    (qthRoot θ 1 2 1) ^ 2 = Complex.exp (↑θ * I) := by
  constructor
  · have := qthRoot_pow_eq θ 1 2 (by norm_num) 0; simpa using this
  · have := qthRoot_pow_eq θ 1 2 (by norm_num) 1; simpa using this

/-- The second square root is the negative of the first.
    ζ₁ = exp(i(θ + 2π)/2) = exp(iθ/2 + iπ) = exp(iθ/2) · exp(iπ) = -ζ₀. -/
theorem sqrt_root_neg (θ : ℝ) :
    qthRoot θ 1 2 1 = -qthRoot θ 1 2 0 := by
  simp only [qthRoot, Nat.cast_zero, mul_zero, add_zero, Int.cast_one, one_mul,
             Nat.cast_one, mul_one, Nat.cast_ofNat]
  -- Goal has (θ + 2 * π) / 2 on LHS and θ / 2 on RHS
  have h1 : (θ + 2 * π) / (2 : ℝ) = θ / 2 + π := by ring
  conv_lhs => rw [show (↑((θ + 2 * π) / 2) : ℂ) * I = ↑(θ / 2 + π) * I from by
    congr 1; exact_mod_cast h1]
  rw [show (↑(θ / 2 + π) : ℂ) * I = ↑(θ / 2) * I + ↑π * I from by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-! ## Part VII: Cube Root Special Case -/

/-- The three cube roots of e^{iθ} all satisfy ζ³ = e^{iθ}. -/
theorem cube_roots (θ : ℝ) (k : Fin 3) :
    (qthRoot θ 1 3 k) ^ 3 = Complex.exp (↑θ * I) := by
  have := qthRoot_pow_eq θ 1 3 (by norm_num) k
  simpa using this

/-- Cube roots factor via the primitive cube root of unity. -/
theorem cube_root_factored (θ : ℝ) (k : Fin 3) :
    qthRoot θ 1 3 k = qthRoot θ 1 3 0 * rootOfUnity 3 k :=
  qthRoot_eq_principal_mul_unity θ 1 3 (by norm_num) k

/-! ## Part VIII: Verified Examples -/

-- Square roots of 1 (θ = 0): ζ₀ = 1
example : qthRoot 0 1 2 0 = 1 := by
  simp [qthRoot, Complex.exp_zero]

-- Cube roots of 1: ζ₀ = 1
example : qthRoot 0 1 3 0 = 1 := by
  simp [qthRoot, Complex.exp_zero]

-- Fourth root of 1 (k=1): exp(iπ/2) = i
example : qthRoot 0 1 4 1 = I := by
  simp only [qthRoot, Int.cast_one, one_mul, zero_add, Nat.cast_ofNat, Nat.cast_one]
  conv_lhs => rw [show (↑((2 * π * 1) / (4 : ℝ)) : ℂ) * I = ↑(π / 2) * I from by
    congr 1; push_cast; ring]
  rw [Complex.exp_mul_I]
  simp

/-! ## Part IX: Summary -/

/-- De Moivre OQ-03 Summary: fractional exponents, root enumeration, principal value. -/
theorem demoivre_oq03_summary (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) (k : ℕ)
    (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) :
    -- (1) Each root satisfies ζ_k^q = z^p
    (qthRoot θ p q k) ^ q = Complex.exp (↑θ * I) ^ p ∧
    -- (2) Roots factor as principal × unity
    qthRoot θ p q k = qthRoot θ p q 0 * rootOfUnity q k ∧
    -- (3) Principal value equals k=0 root
    Complex.exp (↑θ * I) ^ ((p : ℂ) / (q : ℂ)) = qthRoot θ p q 0 ∧
    -- (4) Consistency: raising principal to q gives z^p
    (Complex.exp (↑θ * I) ^ ((p : ℂ) / (q : ℂ))) ^ (q : ℕ) =
      Complex.exp (↑θ * I) ^ p :=
  ⟨qthRoot_pow_eq θ p q hq k,
   qthRoot_eq_principal_mul_unity θ p q hq k,
   cpow_eq_principal_root θ p q hq hθ₁ hθ₂,
   fractional_power_consistency θ p q hq hθ₁ hθ₂⟩

end DeMoivreOQ03
