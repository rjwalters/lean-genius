/-
# Infinitely Many Good Rational Approximations (Dirichlet, infinitude form)

**Open question (oq-01)** for the gallery entry *Dirichlet's Approximation
Theorem*: upgrade the one-shot pigeonhole bound

  `∃ p q, 1 ≤ q ≤ Q ∧ |q·α − p| < 1/Q`

to the **infinitude** statement: every irrational `α` admits *infinitely many*
rationals `p/q` in lowest terms with `|α − p/q| < 1/q²`.

## What is proved here

`infinite_good_rational_approximations`:
  for irrational `α`, the set `{r : ℚ | |α − r| < 1/(r.den)²}` is infinite.

## Provenance / honesty

The infinitude statement is classical (Dirichlet, 1842) and is already available
in Mathlib as `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`.

The contribution of this file is *not* novelty: it is a **self-contained
derivation from the gallery's own base theorem**
`DirichletApproximation.dirichlet_approximation` (the from-scratch pigeonhole
one-shot bound), rather than a wrapper around Mathlib's infinitude theorem. We
re-run the classical bootstrap

  one-shot bound  ⟹  a strictly better good approximation exists  ⟹  infinitude

feeding it from our pigeonhole base. The only external inputs are elementary
glue (denominator-of-a-quotient divides the denominator, a `Finite` set has a
minimiser, the Archimedean property). We do **not** invoke
`exists_rat_abs_sub_le_and_den_le` / `exists_rat_abs_sub_lt_and_lt_of_irrational`
/ `infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` from Mathlib's
`NumberTheory.DiophantineApproximation`.

Note `|α − p/q| < 1/q²` (the standard "good approximation" form) is the same set
used by Mathlib, phrased on `ℚ` via the reduced denominator `r.den`: a one-shot
solution `p/q` with `q ≤ Q` gives `|α − p/q| < 1/(q·Q) ≤ 1/q²`, and reducing to
lowest terms only shrinks the denominator, so the bound `1/r.den²` still holds.
-/
import Proofs.DirichletApproximation

namespace DirichletApproximationOQ01

open Set

/-- **Rational form of the one-shot bound, fed from the gallery base theorem.**
For any real `α` and `n ≥ 1` there is a rational `r` with reduced denominator
`r.den ≤ n` and `|α − r| < 1/(n · r.den)`.

Proof: apply the pigeonhole base `dirichlet_approximation` with `Q = n` to get
`p, q` with `1 ≤ q ≤ n` and `|q·α − p| < 1/n`. Set `r = p/q`. Then
`|α − r| = |q·α − p|/q < 1/(n·q) ≤ 1/(n·r.den)` because the reduced denominator
`r.den` divides `q`, hence `r.den ≤ q`. -/
theorem exists_rat_lt (α : ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ r : ℚ, |α - (r : ℝ)| < 1 / ((n : ℝ) * (r.den : ℝ)) ∧ r.den ≤ n := by
  obtain ⟨p, q, hq1, hqn, hpq⟩ := DirichletApproximation.dirichlet_approximation α n hn
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- candidate rational `r = p/q` and its denominator facts (computed once)
  set r : ℚ := (p : ℚ) / (q : ℚ) with hr_def
  have hden_dvd : ((r.den : ℤ)) ∣ (q : ℤ) := by
    have hcast_q : ((q : ℚ)) = (((q : ℤ)) : ℚ) := by push_cast; ring
    rw [hr_def, hcast_q, Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd p (q : ℤ)
  have hden_le_q_nat : r.den ≤ q := by
    have : ((r.den : ℤ)) ≤ (q : ℤ) := Int.le_of_dvd (by exact_mod_cast hq1) hden_dvd
    exact_mod_cast this
  have hden_le_q : (r.den : ℝ) ≤ (q : ℝ) := by exact_mod_cast hden_le_q_nat
  have hden_pos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  refine ⟨r, ?_, le_trans hden_le_q_nat hqn⟩
  -- the distance bound: |α − p/q| = |q·α − p|/q < 1/(n·q) ≤ 1/(n·r.den)
  have hcast : ((r : ℝ)) = (p : ℝ) / (q : ℝ) := by rw [hr_def]; push_cast; ring
  rw [hcast]
  have hexpand : α - (p : ℝ) / (q : ℝ) = ((q : ℝ) * α - (p : ℝ)) / (q : ℝ) := by
    field_simp; ring
  rw [hexpand, abs_div, abs_of_pos hq_pos]
  calc |(q : ℝ) * α - (p : ℝ)| / (q : ℝ)
      < (1 / (n : ℝ)) / (q : ℝ) := by
        rw [div_lt_div_iff_of_pos_right hq_pos]; exact hpq
    _ = 1 / ((n : ℝ) * (q : ℝ)) := by rw [div_div]
    _ ≤ 1 / ((n : ℝ) * (r.den : ℝ)) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_left hden_le_q hn_pos.le

/-- **Bootstrap: a strictly better good approximation always exists.**
For irrational `α` and any rational `q`, there is a rational `q'` with
`|α − q'| < 1/(q'.den)²` and `|α − q'| < |α − q|`. -/
theorem exists_better (α : ℝ) (hα : Irrational α) (q : ℚ) :
    ∃ q' : ℚ, |α - (q' : ℝ)| < 1 / ((q'.den : ℝ)) ^ 2 ∧ |α - (q' : ℝ)| < |α - (q : ℝ)| := by
  have hpos : (0 : ℝ) < |α - (q : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hα.ne_rat q))
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |α - (q : ℝ)|)
  have hm_pos : (0 : ℝ) < (m : ℝ) := (one_div_pos.mpr hpos).trans hm
  have hm_nat : 0 < m := by exact_mod_cast hm_pos
  obtain ⟨q', hbd, hden⟩ := exists_rat_lt α m hm_nat
  have hden_pos : (0 : ℝ) < (q'.den : ℝ) := by exact_mod_cast q'.pos
  have hden_ge_one : (1 : ℝ) ≤ (q'.den : ℝ) := by exact_mod_cast q'.pos
  refine ⟨q', ?_, ?_⟩
  · -- |α − q'| < 1/(q'.den)²
    refine hbd.trans_le ?_
    rw [sq]
    apply one_div_le_one_div_of_le (by positivity)
    -- q'.den · q'.den ≤ m · q'.den  (since q'.den ≤ m)
    apply mul_le_mul_of_nonneg_right _ hden_pos.le
    exact_mod_cast hden
  · -- |α − q'| < |α − q|
    refine hbd.trans_lt ?_
    -- 1/(m·q'.den) ≤ 1/m < |α − q|
    have hstep1 : 1 / ((m : ℝ) * (q'.den : ℝ)) ≤ 1 / (m : ℝ) := by
      apply one_div_le_one_div_of_le hm_pos
      nlinarith [hm_pos, hden_ge_one]
    have hstep2 : 1 / (m : ℝ) < |α - (q : ℝ)| := by
      rw [div_lt_iff₀ hm_pos]
      have := (div_lt_iff₀ hpos).mp hm
      nlinarith [this]
    exact lt_of_le_of_lt hstep1 hstep2

/-- **Infinitely many good rational approximations.**
For irrational `α`, the set of rationals `r` with `|α − r| < 1/(r.den)²` is
infinite. This answers the gallery open question by bootstrapping the
from-scratch pigeonhole base theorem to its full Dirichlet infinitude form. -/
theorem infinite_good_rational_approximations (α : ℝ) (hα : Irrational α) :
    {r : ℚ | |α - (r : ℝ)| < 1 / ((r.den : ℝ)) ^ 2}.Infinite := by
  refine Or.resolve_left (Set.finite_or_infinite _) (fun h => ?_)
  -- nonempty witness: the integer floor ⌊α⌋ as a rational has denominator 1
  have hmem0 : (⌊α⌋ : ℚ) ∈ {r : ℚ | |α - (r : ℝ)| < 1 / ((r.den : ℝ)) ^ 2} := by
    have h1 : ((⌊α⌋ : ℤ) : ℝ) ≤ α := Int.floor_le α
    have h2 : α < (⌊α⌋ : ℝ) + 1 := Int.lt_floor_add_one α
    have hcast : (((⌊α⌋ : ℚ)) : ℝ) = (⌊α⌋ : ℝ) := by push_cast; ring
    simp only [Set.mem_setOf_eq, Rat.den_intCast, Nat.cast_one, one_pow, div_one, hcast]
    rw [abs_lt]
    constructor <;> linarith
  -- a finite nonempty set has a closest element; the bootstrap beats it
  obtain ⟨q, hq_mem, hq_min⟩ :=
    Set.exists_min_image _ (fun r : ℚ => |α - (r : ℝ)|) h ⟨(⌊α⌋ : ℚ), hmem0⟩
  obtain ⟨q', hq'_mem, hq'_better⟩ := exists_better α hα q
  exact absurd (hq_min q' hq'_mem) (not_le.mpr hq'_better)

end DirichletApproximationOQ01
