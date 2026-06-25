import Proofs.BetaCentralBinomial
import Mathlib

/-
# Wallis/Stirling Asymptotics of the Diagonal Beta Value

## What This Proves

The parent entry establishes the diagonal Euler Beta value as a central binomial
reciprocal,

  `B(n+1, n+1) = 1 / ((2n+1) · C(2n, n))`.

This entry establishes its **asymptotic decay** as `n → ∞`.  The engine is the
classical Stirling/Wallis estimate of the central binomial coefficient, which is
*not* available in Mathlib and which we derive here from Mathlib's
`Stirling.factorial_isEquivalent_stirling`:

  **`centralBinom_isEquivalent`** :
    `C(2n, n) ~ 4ⁿ / √(πn)`   (as `n → ∞`).

From the parent's closed form this immediately gives the decay of the diagonal
Beta value:

  **`betaDiag_isEquivalent`** :
    `B(n+1, n+1) ~ √(πn) / ((2n+1) · 4ⁿ)`.

So the total mass of the symmetric `Beta(n+1, n+1)` density decays like
`√(πn) · 4⁻ⁿ / (2n+1) ≈ √π · 2⁻²ⁿ⁻¹ · n⁻¹ᐟ²`, the quantitative form of the fact
that the symmetric Beta density concentrates (after rescaling) to a Gaussian — the
mass collapses at the Wallis rate governed by the central binomial coefficient.

`betaIntegral_diag_eq` records that the real sequence `betaDiag` analysed here is
literally the (real) value of the complex Euler Beta integral on the diagonal, so
the asymptotic is a statement about `Complex.betaIntegral` itself.

## Relation to Mathlib

Mathlib has `Stirling.factorial_isEquivalent_stirling`
(`n! ~ √(2πn)·(n/e)ⁿ`) and `Nat.centralBinom`, but it does not state the
asymptotic of the central binomial coefficient, nor any asymptotic for the Beta
value.  Both are assembled here.
-/

open Filter Asymptotics
open scoped Topology Real Nat

namespace BetaDiagAsymptotic

/-- The central binomial coefficient as a real quotient of factorials:
`C(2n,n) = (2n)! / (n!·n!)`. -/
lemma centralBinom_cast (n : ℕ) :
    (Nat.centralBinom n : ℝ)
      = (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
  have hfac : Nat.centralBinom n * (Nat.factorial n * Nat.factorial n)
      = Nat.factorial (2 * n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose, ← mul_assoc]
    exact h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast hfac

/-- **Core algebraic identity (Wallis ratio).**  For `m, e > 0` the ratio of the
Stirling expressions for `(2k)!` and `(k!)²` collapses to `4ᵏ / √(πm)`.  This is the
only place the `4ᵏ` arises: it comes from `(2m/e)^{2k} / (m/e)^{2k} = 2^{2k} = 4ᵏ`. -/
lemma stirling_ratio_identity {m e : ℝ} (hm : 0 < m) (he : 0 < e) (k : ℕ) :
    Real.sqrt (2 * (2 * m) * π) * ((2 * m) / e) ^ (2 * k) /
        (Real.sqrt (2 * m * π) * (m / e) ^ k * (Real.sqrt (2 * m * π) * (m / e) ^ k))
      = 4 ^ k / Real.sqrt (π * m) := by
  have hpi : 0 < π := Real.pi_pos
  -- √(2·(2m)·π) = 2·√(πm)
  have hA : Real.sqrt (2 * (2 * m) * π) = 2 * Real.sqrt (π * m) := by
    rw [show 2 * (2 * m) * π = (2 : ℝ) ^ 2 * (π * m) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  -- (2m/e)^{2k} = 4ᵏ · ((m/e)ᵏ)²  (the only source of the 4ᵏ)
  have hC : ((2 * m) / e) ^ (2 * k) = 4 ^ k * ((m / e) ^ k) ^ 2 := by
    have h2 : (2 : ℝ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
    rw [show (2 * m) / e = 2 * (m / e) by rw [mul_div_assoc], mul_pow, h2, ← pow_mul,
      Nat.mul_comm k 2]
  -- self-products of the two square roots
  have hrsq : Real.sqrt (π * m) * Real.sqrt (π * m) = π * m :=
    Real.mul_self_sqrt (by positivity)
  have hsq2 : Real.sqrt (2 * m * π) * Real.sqrt (2 * m * π) = 2 * m * π :=
    Real.mul_self_sqrt (by positivity)
  have hr0 : Real.sqrt (π * m) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [hA, hC, div_eq_div_iff (by positivity) hr0]
  linear_combination (2 * 4 ^ k * ((m / e) ^ k) ^ 2) * hrsq - (4 ^ k * ((m / e) ^ k) ^ 2) * hsq2

/-- **Central binomial asymptotic (new).**  `C(2n, n) ~ 4ⁿ / √(πn)` as `n → ∞`.

Derived from Mathlib's Stirling equivalence `n! ~ √(2πn)·(n/e)ⁿ`. -/
theorem centralBinom_isEquivalent :
    (fun n : ℕ => (Nat.centralBinom n : ℝ)) ~[atTop]
      (fun n : ℕ => (4 : ℝ) ^ n / Real.sqrt (π * n)) := by
  have hstir := Stirling.factorial_isEquivalent_stirling
  have hk : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have h2n := hstir.comp_tendsto hk
  have hmul := hstir.mul hstir
  have hdiv := h2n.div hmul
  have hcb : (fun n : ℕ => (Nat.centralBinom n : ℝ)) ~[atTop]
      (fun n : ℕ => (Nat.factorial (2 * n) : ℝ) /
        ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))) := by
    apply Filter.EventuallyEq.isEquivalent
    exact Filter.Eventually.of_forall centralBinom_cast
  refine (hcb.trans hdiv).trans (Filter.EventuallyEq.isEquivalent ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hm : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  simp only [Function.comp_apply]
  rw [show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by push_cast; ring]
  exact stirling_ratio_identity hm (Real.exp_pos 1) n

/-- The real diagonal Beta value, `B(n+1,n+1) = 1 / ((2n+1)·C(2n,n))`. -/
noncomputable def betaDiag (n : ℕ) : ℝ :=
  1 / ((2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ))

/-- **Diagonal Beta value asymptotic (new).**
`B(n+1, n+1) ~ √(πn) / ((2n+1)·4ⁿ)` as `n → ∞`. -/
theorem betaDiag_isEquivalent :
    (fun n : ℕ => betaDiag n) ~[atTop]
      (fun n : ℕ => Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n)) := by
  have hcb := centralBinom_isEquivalent.inv
  have hconst : (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹) ~[atTop]
      (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹) := IsEquivalent.refl
  have hmul := hconst.mul hcb
  have hL : (fun n : ℕ => betaDiag n) =ᶠ[atTop]
      (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹ * (Nat.centralBinom n : ℝ)⁻¹) := by
    apply Filter.Eventually.of_forall; intro n
    simp only [betaDiag, one_div, mul_inv]
  have hR : (fun n : ℕ => (2 * (n : ℝ) + 1)⁻¹ * ((4 : ℝ) ^ n / Real.sqrt (π * n))⁻¹) =ᶠ[atTop]
      (fun n : ℕ => Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n)) := by
    apply Filter.Eventually.of_forall; intro n
    rw [inv_div]; ring
  exact (hL.isEquivalent.trans hmul).trans hR.isEquivalent

/-- The complex Euler Beta integral on the diagonal equals the real value
`betaDiag` analysed above, so the asymptotic is about `Complex.betaIntegral`. -/
theorem betaIntegral_diag_eq (n : ℕ) :
    Complex.betaIntegral ((n : ℂ) + 1) ((n : ℂ) + 1) = ((betaDiag n : ℝ) : ℂ) := by
  rw [BetaCentralBinomial.betaIntegral_diag_centralBinom]
  simp only [betaDiag]
  push_cast
  ring

end BetaDiagAsymptotic
