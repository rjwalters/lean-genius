/-
# The power-mean inequality `Mₚ ≤ M_q` for `0 < p ≤ q`

## Open Question (`amgm-inequality-oq-02-oq-03-oq-03-oq-03`)

The parent gallery entry *Full Maclaurin Chain* (`amgm-inequality-oq-02-oq-03-oq-03`)
records the open question:

> Can the Maclaurin chain be generalized to power means (Lᵖ norms), giving the
> power-mean inequality `M_p ≥ M_q` for `p ≤ q`?

### Answer and a clarification on direction

The power means

  `Mₚ(x) = ( (1/n) · Σᵢ xᵢᵖ )^{1/p}`

are **monotone increasing in the exponent**: for `0 < p ≤ q` one has
`Mₚ ≤ M_q`, *not* `Mₚ ≥ M_q` as the question literally states.  (For example
`M₁` is the arithmetic mean and `M₂` the quadratic mean / root-mean-square, and
`M₁ ≤ M₂` is the classical RMS–AM inequality.)  The decreasing ordering of the
question belongs to the *Maclaurin means* `Mₖ = (eₖ/C(n,k))^{1/k}`, which are
indexed by the **symmetric-function degree** `k` and decrease in `k`; that is a
genuinely different family from the power means, even though both interpolate the
AM–GM inequality.  So the honest answer to the question is: yes, there is a clean
power-mean generalization, and its correct form is `Mₚ ≤ M_q` for `p ≤ q`.

### Why this is not already in Mathlib

`Mathlib.Analysis.MeanInequalities` lists, verbatim in its `TODO` section,

  "- generalized mean inequality with any `p ≤ q`, including negative numbers;"

so the unweighted power-mean monotonicity is *not* presently available as a
theorem.  Mathlib does supply the convexity engine
`NNReal.rpow_arith_mean_le_arith_mean_rpow`
(Jensen for `t ↦ tʳ`, `r ≥ 1`, with arbitrary weights summing to `1`).  This file
specialises it to uniform weights `1/n` to obtain the power-mean inequality for
positive exponents `0 < p ≤ q`.

## Mechanism (all `0`-axiom, no `sorry`)

Put `r = q/p ≥ 1`, take uniform weights `wᵢ = 1/n`, and apply Jensen to
`zᵢ = xᵢᵖ`:

  `(Σ wᵢ xᵢᵖ)^{q/p} ≤ Σ wᵢ (xᵢᵖ)^{q/p} = Σ wᵢ xᵢ^q`,

then raise both sides to the power `1/q` (monotone, `q > 0`):

  `(Σ wᵢ xᵢᵖ)^{1/p} = ((Σ wᵢ xᵢᵖ)^{q/p})^{1/q} ≤ (Σ wᵢ xᵢ^q)^{1/q}`,

which is exactly `Mₚ ≤ M_q`.

The negative-exponent case (`p ≤ q` with `p < 0`, requiring `xᵢ > 0`) remains, as
in Mathlib, future work.
-/
import Mathlib

open Finset NNReal
open scoped BigOperators

namespace AmgmInequalityOQ02OQ03OQ03OQ03

noncomputable section

variable {ι : Type*}

/-- The (unweighted) **power mean** of order `p` of `x : ι → ℝ≥0` over a finite
set `s`:  `Mₚ = ( (1/|s|) · Σᵢ (x i)ᵖ )^{1/p}`, written with the uniform weight
`(|s|)⁻¹` distributed across the sum. -/
def powerMean (s : Finset ι) (x : ι → ℝ≥0) (p : ℝ) : ℝ≥0 :=
  (∑ i ∈ s, (s.card : ℝ≥0)⁻¹ * (x i) ^ p) ^ (1 / p)

/-- **Power-mean inequality.** For a nonempty finite index set and positive
exponents `0 < p ≤ q`, the power means are monotone in the exponent:
`Mₚ ≤ M_q`.

This is the unweighted "generalized mean inequality with `p ≤ q`" that
`Mathlib.Analysis.MeanInequalities` lists as a `TODO`.  The proof specialises
`NNReal.rpow_arith_mean_le_arith_mean_rpow` (Jensen for `t ↦ t^{q/p}`) to the
uniform weights `1/|s|`. -/
theorem powerMean_le_powerMean (s : Finset ι) (x : ι → ℝ≥0)
    (hs : s.Nonempty) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    powerMean s x p ≤ powerMean s x q := by
  unfold powerMean
  set n : ℝ≥0 := (s.card : ℝ≥0) with hn
  have hn0 : n ≠ 0 := by
    rw [hn]; exact_mod_cast (Finset.card_pos.mpr hs).ne'
  have hq : (0 : ℝ) < q := lt_of_lt_of_le hp hpq
  have hr : (1 : ℝ) ≤ q / p := (one_le_div hp).mpr hpq
  -- The uniform weights sum to one.
  have hw : ∑ _i ∈ s, n⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← hn, mul_inv_cancel₀ hn0]
  -- Jensen for `t ↦ t^{q/p}` with weights `1/n` applied to `zᵢ = (x i)^p`.
  have key := NNReal.rpow_arith_mean_le_arith_mean_rpow
    s (fun _ => n⁻¹) (fun i => (x i) ^ p) hw hr
  -- Simplify the right-hand exponent:  ((x i)^p)^{q/p} = (x i)^q.
  have hrhs : (∑ i ∈ s, n⁻¹ * ((x i) ^ p) ^ (q / p))
      = ∑ i ∈ s, n⁻¹ * (x i) ^ q := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← NNReal.rpow_mul]
    congr 2
    field_simp
  rw [hrhs] at key
  -- Raise both sides to the power `1/q ≥ 0`.
  have hmono := NNReal.rpow_le_rpow key (by positivity : (0 : ℝ) ≤ 1 / q)
  rw [← NNReal.rpow_mul] at hmono
  -- `(q/p) * (1/q) = 1/p`, so the left side becomes `Mₚ`.
  have hexp : q / p * (1 / q) = 1 / p := by field_simp
  rwa [hexp] at hmono

/-- **Root-mean-square ≥ arithmetic mean** (the quadratic mean dominates the
arithmetic mean), a special case of `powerMean_le_powerMean` with `p = 1`,
`q = 2`. -/
theorem arithMean_le_quadraticMean (s : Finset ι) (x : ι → ℝ≥0) (hs : s.Nonempty) :
    powerMean s x 1 ≤ powerMean s x 2 :=
  powerMean_le_powerMean s x hs (by norm_num) (by norm_num)

/-- The power mean is monotone across any positive exponent gap; restating
`powerMean_le_powerMean` with the hypotheses bundled for `0 < p` and `0 < q`. -/
theorem powerMean_mono (s : Finset ι) (x : ι → ℝ≥0) (hs : s.Nonempty)
    {p q : ℝ} (hp : 0 < p) (_hq : 0 < q) (hpq : p ≤ q) :
    powerMean s x p ≤ powerMean s x q :=
  powerMean_le_powerMean s x hs hp hpq

end

end AmgmInequalityOQ02OQ03OQ03OQ03
