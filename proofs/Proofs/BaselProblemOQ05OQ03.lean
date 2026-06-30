import Mathlib

/-
# Basel Problem OQ-05-OQ-03: Direct proof of the sin(πx) product formula

## Open Question
The parent entry `BaselProblemOQ05` (Euler's proof via the Weierstrass product)
*axiomatized* the infinite product formula

  sin(πx)/(πx) = ∏'_{n=1}^∞ (1 - x²/n²),

because the Weierstrass factorization of sin was not available. This open
question asks for a direct proof of the product formula that avoids the
Weierstrass factorization theorem / complex contour integration.

## Result
We **eliminate that axiom**. Mathlib provides `Real.tendsto_euler_sin_prod`,
which establishes the Euler sine product as a *limit of partial products*

  π·x · ∏_{j<n} (1 - x²/(j+1)²)  →  sin(πx).

Mathlib's proof of this fact is the elementary one: it is obtained from the
recursion for the Wallis-type integrals ∫₀^{π/2} cos^{2n}(t)·cos(2zt) dt, and
does **not** use the Weierstrass factorization theorem or contour integration.
(It does pass through the complex sine internally, but only as a bookkeeping
device for the same real integral identity.)

What was missing — and what we supply here — is the bridge from the
*partial-product limit* form to the *infinite product* (`∏'`, `tprod`) form
that the parent axiom was stated in. This requires establishing
**multipliability** of the factors `(1 - x²/n²)`, which holds for every real
`x` because ∑ x²/n² converges. The two reformulations then agree by uniqueness
of limits and a first-term split of the `tprod`.

The headline theorem `weierstrass_sin_product` reproduces the parent's axiom
statement verbatim, now as a fully verified, 0-axiom theorem.

Results: 0 axioms, 0 sorries.
-/

set_option linter.unusedVariables false

namespace BaselOQ05OQ03

open Filter Real BigOperators Topology

-- ============================================================
-- SECTION I: Convergence of the product factors
-- ============================================================

/-- The shifted reciprocal squares `-x²/(n+1)²` are summable for every real `x`.
    This is the p-series with `p = 2`, scaled and index-shifted. -/
theorem summable_neg_sq_div (x : ℝ) :
    Summable (fun n : ℕ => -x ^ 2 / ((n : ℝ) + 1) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  -- shift the index by one to avoid the `n = 0` term
  have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr hbase
    simpa using this
  -- scale by the constant `-x²`
  have := hshift.mul_left (-x ^ 2)
  refine this.congr (fun n => ?_)
  field_simp

/-- **Multipliability of the Euler factors**: the family `n ↦ 1 - x²/(n+1)²`
    is multipliable for every real `x`. Since the reciprocal squares are
    summable, the partial products converge (Mathlib's
    `Real.multipliable_one_add_of_summable`). -/
theorem multipliable_euler_factors (x : ℝ) :
    Multipliable (fun n : ℕ => 1 - x ^ 2 / ((n : ℝ) + 1) ^ 2) := by
  have h := Real.multipliable_one_add_of_summable (summable_neg_sq_div x)
  refine h.congr (fun n => ?_)
  ring

-- ============================================================
-- SECTION II: From the partial-product limit to the tprod
-- ============================================================

/-- **Euler product, shifted form**: for `x ≠ 0`,

      sin(πx)/(πx) = ∏'_{n} (1 - x²/(n+1)²).

    Proof: Mathlib's `Real.tendsto_euler_sin_prod` gives convergence of the
    partial products `π·x·∏_{j<n}(1 - x²/(j+1)²)` to `sin(πx)`; multipliability
    gives convergence of the partial products to the `tprod`; uniqueness of
    limits ties the two together. -/
theorem euler_sin_tprod_shifted (x : ℝ) (hx : x ≠ 0) :
    sin (π * x) / (π * x) =
      ∏' (n : ℕ), (1 - x ^ 2 / ((n : ℝ) + 1) ^ 2) := by
  set g : ℕ → ℝ := fun n => 1 - x ^ 2 / ((n : ℝ) + 1) ^ 2 with hg
  -- partial products converge to the tprod
  have hmul : Multipliable g := multipliable_euler_factors x
  have htg : Tendsto (fun n => ∏ j ∈ Finset.range n, g j) atTop (𝓝 (∏' n, g n)) :=
    hmul.tendsto_prod_tprod_nat
  -- multiply by the constant π·x
  have htg' : Tendsto (fun n => π * x * ∏ j ∈ Finset.range n, g j) atTop
      (𝓝 (π * x * ∏' n, g n)) := htg.const_mul (π * x)
  -- Mathlib: the same partial products (times π·x) tend to sin(πx)
  have hsin : Tendsto (fun n => π * x * ∏ j ∈ Finset.range n, g j) atTop
      (𝓝 (sin (π * x))) := Real.tendsto_euler_sin_prod x
  -- uniqueness of limits
  have hpix : π * x * ∏' n, g n = sin (π * x) := tendsto_nhds_unique htg' hsin
  have hπ : π * x ≠ 0 := mul_ne_zero (ne_of_gt pi_pos) hx
  field_simp
  rw [mul_comm] at hpix
  linarith [hpix]

-- ============================================================
-- SECTION III: The parent's axiom, now a theorem
-- ============================================================

/-- **Weierstrass product for sin** (the parent OQ-05 axiom, discharged):

      sin(πx)/(πx) = ∏'_{n} (if n = 0 then 1 else 1 - x²/n²),  for x ≠ 0.

    This reproduces `BaselOQ05.weierstrass_sin_product` verbatim, but as a
    fully verified, axiom-free theorem. The `if n = 0 then 1` factor encodes
    the convention that the product runs over `n ≥ 1`; it is removed by a
    first-term split of the `tprod`. -/
theorem weierstrass_sin_product :
    ∀ x : ℝ, x ≠ 0 →
      sin (π * x) / (π * x) =
        ∏' (n : ℕ), if n = 0 then 1 else (1 - x ^ 2 / (n : ℝ) ^ 2) := by
  intro x hx
  set h : ℕ → ℝ := fun n => if n = 0 then 1 else (1 - x ^ 2 / (n : ℝ) ^ 2) with hh
  -- the shifted family `h (n+1)` equals the Euler factors `g n`
  have hshift_eq : (fun n : ℕ => h (n + 1)) =
      (fun n : ℕ => 1 - x ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    funext n
    simp only [hh, Nat.succ_ne_zero, if_false]
    push_cast
    ring_nf
  -- multipliability of the shifted family
  have hmul_shift : Multipliable (fun n : ℕ => h (n + 1)) := by
    rw [hshift_eq]; exact multipliable_euler_factors x
  -- first-term split: ∏' h = h 0 * ∏' (h ∘ (·+1)) = 1 * ∏' g
  have hsplit : ∏' n, h n = h 0 * ∏' n, h (n + 1) := tprod_eq_zero_mul' hmul_shift
  have h0 : h 0 = 1 := by simp [hh]
  have hgprod : ∏' n, h (n + 1) = ∏' (n : ℕ), (1 - x ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    rw [hshift_eq]
  rw [hsplit, h0, one_mul, hgprod]
  exact euler_sin_tprod_shifted x hx

-- ============================================================
-- SECTION IV: Basel corollary
-- ============================================================

/-- **Basel problem**: ∑ 1/n² = π²/6.

    With the product formula now a theorem, the classical Euler argument
    (compare the x² coefficients of the Taylor side and the product side)
    yields the Basel identity. We record the identity itself; the value is
    Mathlib's `hasSum_zeta_two`. -/
theorem basel_sum : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  hasSum_zeta_two

end BaselOQ05OQ03

#check @BaselOQ05OQ03.weierstrass_sin_product
#check @BaselOQ05OQ03.euler_sin_tprod_shifted
#check @BaselOQ05OQ03.multipliable_euler_factors
#check @BaselOQ05OQ03.basel_sum

#print axioms BaselOQ05OQ03.weierstrass_sin_product
#print axioms BaselOQ05OQ03.euler_sin_tprod_shifted
