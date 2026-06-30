/-
Pell's Equation OQ-06-OQ-04: The Chain Gives the Best Rational Approximations to √2

The parent entry (`pell-equation-oq-06`) builds the chain

    (1, 1) → (7, 5) → (41, 29) → (239, 169) → …

of solutions of the negative Pell equation x² − 2y² = −1, and the sibling
`-oq-01` classifies it. The siblings so far are *algebraic* (descent, powers of a
unit, a linear recurrence). This entry records the chain's **analytic** meaning:
the ratios xₙ/yₙ are exactly the best rational approximations to √2 coming from
this equation, and they converge to √2.

Because xₙ² − 2yₙ² = −1 < 0, every ratio underestimates √2:

    xₙ/yₙ  <  √2   for all n,

so the chain produces approximations *from below*. The defining identity factors
in ℝ as (xₙ − yₙ√2)(xₙ + yₙ√2) = xₙ² − 2yₙ² = −1, giving the exact error

    √2 − xₙ/yₙ  =  1 / (yₙ (xₙ + yₙ√2)),

a positive quantity bounded by the classical Diophantine-approximation estimate

    |xₙ/yₙ − √2|  <  1/yₙ².

Since yₙ → ∞ along the chain, the ratios converge: xₙ/yₙ → √2.

Main results:
  • `negPellSeq_snd_strictMono` — the y-coordinates strictly increase.
  • `negPellSeq_fst_lt_snd_mul_sqrt2` — xₙ < yₙ√2 (approximation strictly from below).
  • `negPellSeq_approx_bound` — |xₙ/yₙ − √2| < 1/yₙ² (Diophantine quality).
  • `negPellSeq_ratio_tendsto_sqrt2` — xₙ/yₙ → √2.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent entry: `pell-equation-oq-06` (the chain; infinitude).
- Sibling `pell-equation-oq-06-oq-01` (classification by descent).
- Sibling `pell-equation-oq-06-oq-02` (the chain as odd powers of 1 + √2).
- Sibling `pell-equation-oq-06-oq-03` (the order-2 recurrence uₙ₊₂ = 6uₙ₊₁ − uₙ).
- Classical: solutions of x² − 2y² = ±1 are the convergents of the continued
  fraction of √2; the negative-Pell solutions give the odd-indexed convergents,
  approximating √2 from below.
-/

import Mathlib
import Proofs.PellEquationOQ06

namespace PellEquationOQ06OQ04

open PellEquationOQ06
open Filter Topology

/-
## The y-coordinates grow without bound
-/

/-- **The second coordinates strictly increase along the chain.** Mirrors the
    parent's `negPellSeq_fst_strictMono`; `yₙ₊₁ = 2xₙ + 3yₙ > yₙ` since
    `xₙ, yₙ ≥ 1`. -/
theorem negPellSeq_snd_strictMono : StrictMono (fun n => (negPellSeq n).2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨hx, hy⟩ := negPellSeq_pos n
  rw [negPellSeq_succ]
  dsimp
  linarith

/-- A linear lower bound `n + 1 ≤ yₙ`, used to push `yₙ → ∞`. -/
theorem negPellSeq_snd_lower (n : ℕ) : (n : ℤ) + 1 ≤ (negPellSeq n).2 := by
  induction n with
  | zero => simp [negPellSeq_zero]
  | succ k ih =>
    have hstep : (negPellSeq k).2 < (negPellSeq (k + 1)).2 :=
      negPellSeq_snd_strictMono (Nat.lt_succ_self k)
    push_cast
    omega

/-
## The analytic core: error identity and bounds (per index `n`)
-/

/-- The engine for the analytic statements. For each `n`, writing `a = xₙ`,
    `b = yₙ`, `s = √2` over ℝ, the factorization `(a − bs)(a + bs) = a² − 2b² = −1`
    forces `a < bs`, and the ratio error `|a/b − s|` equals `1/(b(a + bs))`, which
    is `≤ b⁻¹` (for convergence) and `< 1/b²` (the Diophantine bound). -/
private theorem approx_core (n : ℕ) :
    ((negPellSeq n).1 : ℝ) < ((negPellSeq n).2 : ℝ) * Real.sqrt 2 ∧
      |((negPellSeq n).1 : ℝ) / ((negPellSeq n).2 : ℝ) - Real.sqrt 2|
        ≤ ((negPellSeq n).2 : ℝ)⁻¹ ∧
      |((negPellSeq n).1 : ℝ) / ((negPellSeq n).2 : ℝ) - Real.sqrt 2|
        < 1 / ((negPellSeq n).2 : ℝ) ^ 2 := by
  obtain ⟨hxZ, hyZ⟩ := negPellSeq_pos n
  set a : ℝ := ((negPellSeq n).1 : ℝ) with ha
  set b : ℝ := ((negPellSeq n).2 : ℝ) with hb
  set s : ℝ := Real.sqrt 2 with hsdef
  have ha1 : (1 : ℝ) ≤ a := by rw [ha]; exact_mod_cast hxZ
  have hb1 : (1 : ℝ) ≤ b := by rw [hb]; exact_mod_cast hyZ
  have hb0 : (0 : ℝ) < b := by linarith
  have hs0 : (0 : ℝ) < s := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : (1 : ℝ) < s := by
    have : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using this
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnorm : a ^ 2 - 2 * b ^ 2 = -1 := by
    rw [ha, hb]; exact_mod_cast negPellSeq_norm n
  -- factorization
  have hfac : (a + b * s) * (a - b * s) = -1 := by
    have hexp : (a + b * s) * (a - b * s) = a ^ 2 - b ^ 2 * s ^ 2 := by ring
    rw [hexp, hs2]; linarith [hnorm]
  have hsum_pos : (0 : ℝ) < a + b * s := by
    have : (0 : ℝ) < b * s := mul_pos hb0 hs0
    linarith
  have hne1 : a + b * s ≠ 0 := ne_of_gt hsum_pos
  have hdiff : a - b * s = (-1) / (a + b * s) := by
    rw [eq_div_iff hne1]; linear_combination hfac
  -- approximation from below
  have hlt : a < b * s := by
    have hneg : a - b * s < 0 := by
      rw [hdiff]; exact div_neg_of_neg_of_pos (by norm_num) hsum_pos
    linarith
  -- exact value of the ratio error
  have hratio_lt : a / b < s := by rw [div_lt_iff₀ hb0]; nlinarith [hlt]
  have hval : |a / b - s| = s - a / b := by rw [abs_of_neg (by linarith)]; ring
  have hbsa : b * s - a = 1 / (a + b * s) := by
    rw [eq_div_iff hne1]; linear_combination -hfac
  have hsab : s - a / b = (b * s - a) / b := by field_simp
  have hne2 : b ≠ 0 := ne_of_gt hb0
  have heq : |a / b - s| = 1 / (b * (a + b * s)) := by
    rw [hval, hsab, hbsa]
    field_simp
  -- the two reciprocal bounds
  have hbound1 : |a / b - s| ≤ b⁻¹ := by
    rw [heq, inv_eq_one_div]
    apply one_div_le_one_div_of_le hb0
    have h1 : (1 : ℝ) ≤ a + b * s := by nlinarith [mul_nonneg hb0.le hs0.le]
    nlinarith [mul_le_mul_of_nonneg_left h1 hb0.le]
  have hbound2 : |a / b - s| < 1 / b ^ 2 := by
    rw [heq]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [mul_pos hb0 (lt_of_lt_of_le one_pos ha1),
      mul_pos (mul_pos hb0 hb0) (sub_pos.mpr hs1)]
  exact ⟨hlt, hbound1, hbound2⟩

/-
## Public analytic theorems
-/

/-- **Every ratio underestimates √2.** Since `xₙ² − 2yₙ² = −1 < 0`, we have
    `xₙ < yₙ√2`, i.e. `xₙ/yₙ < √2` — the negative-Pell chain approximates √2
    strictly from below. -/
theorem negPellSeq_fst_lt_snd_mul_sqrt2 (n : ℕ) :
    ((negPellSeq n).1 : ℝ) < ((negPellSeq n).2 : ℝ) * Real.sqrt 2 :=
  (approx_core n).1

/-- **The ratio `xₙ/yₙ` underestimates √2.** Division form of the previous
    theorem. -/
theorem negPellSeq_ratio_lt_sqrt2 (n : ℕ) :
    ((negPellSeq n).1 : ℝ) / ((negPellSeq n).2 : ℝ) < Real.sqrt 2 := by
  have hyZ := (negPellSeq_pos n).2
  have hb0 : (0 : ℝ) < ((negPellSeq n).2 : ℝ) := by exact_mod_cast hyZ
  rw [div_lt_iff₀ hb0]
  have := negPellSeq_fst_lt_snd_mul_sqrt2 n
  nlinarith [this]

/-- **Diophantine quality bound.** The approximation error satisfies
    `|xₙ/yₙ − √2| < 1/yₙ²` — the hallmark of convergents of the continued
    fraction of √2. -/
theorem negPellSeq_approx_bound (n : ℕ) :
    |((negPellSeq n).1 : ℝ) / ((negPellSeq n).2 : ℝ) - Real.sqrt 2|
      < 1 / ((negPellSeq n).2 : ℝ) ^ 2 :=
  (approx_core n).2.2

/-
## Convergence
-/

/-- The y-coordinates tend to `+∞` (as reals). -/
theorem negPellSeq_snd_tendsto_atTop :
    Tendsto (fun n => ((negPellSeq n).2 : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono ?_ tendsto_natCast_atTop_atTop
  intro n
  have := negPellSeq_snd_lower n
  have hle : (n : ℤ) ≤ (negPellSeq n).2 := by omega
  exact_mod_cast hle

/-- **The ratios converge to √2.** `xₙ/yₙ → √2`: the negative-Pell chain is a
    sequence of rational approximations to √2 (from below), with error `< 1/yₙ²`
    and `yₙ → ∞`, so the limit is exactly √2. -/
theorem negPellSeq_ratio_tendsto_sqrt2 :
    Tendsto (fun n => ((negPellSeq n).1 : ℝ) / ((negPellSeq n).2 : ℝ))
      atTop (𝓝 (Real.sqrt 2)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (g := fun n => ((negPellSeq n).2 : ℝ)⁻¹)
    (fun n => ?_) ?_
  · rw [Real.dist_eq]
    exact (approx_core n).2.1
  · exact tendsto_inv_atTop_zero.comp negPellSeq_snd_tendsto_atTop

/-
## Sanity checks
-/

-- The first few ratios, all below √2: 1, 7/5 = 1.4, 41/29 ≈ 1.4138, → √2 ≈ 1.41421356…
example : ((negPellSeq 1).1 : ℝ) / ((negPellSeq 1).2 : ℝ) < Real.sqrt 2 :=
  negPellSeq_ratio_lt_sqrt2 1
example : ((negPellSeq 2).1 : ℝ) / ((negPellSeq 2).2 : ℝ) < Real.sqrt 2 :=
  negPellSeq_ratio_lt_sqrt2 2

#check @negPellSeq_snd_strictMono
#check @negPellSeq_fst_lt_snd_mul_sqrt2
#check @negPellSeq_approx_bound
#check @negPellSeq_ratio_tendsto_sqrt2

end PellEquationOQ06OQ04
