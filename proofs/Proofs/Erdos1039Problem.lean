/-
  Erdős Problem #1039: Polynomial Lemniscate Disc Radius

  Source: https://erdosproblems.com/1039
  Status: OPEN

  Statement:
  Let f(z) = ∏(z - zᵢ) ∈ ℂ[z] with |zᵢ| ≤ 1 for all i.
  Let ρ(f) be the radius of the largest disc contained in {z : |f(z)| < 1}.

  Determine the behavior of ρ(f). Is it always true that ρ(f) ≫ 1/n?

  A problem of Erdős, Herzog, and Piranian.

  Known Results:
  - Benchmark: f(z) = zⁿ - 1 has ρ(f) ≤ π/(2n)
  - Pommerenke (1961): ρ(f) ≥ 1/(2en²)
  - Krishnapur-Lundberg-Ramachandran (2025): ρ(f) ≫ 1/(n√(log n))
-/

import Mathlib

namespace Erdos1039

/-
## Polynomial Setup
-/

/-- A monic polynomial with roots in the unit disc. -/
structure UnitDiscPolynomial where
  /-- The degree of the polynomial. -/
  degree : ℕ
  /-- The roots of the polynomial. -/
  roots : Fin degree → ℂ
  /-- All roots lie in the closed unit disc. -/
  roots_in_disc : ∀ i, ‖roots i‖ ≤ 1

variable (f : UnitDiscPolynomial)

/-- The polynomial as a function ℂ → ℂ. -/
noncomputable def UnitDiscPolynomial.eval (z : ℂ) : ℂ :=
  ∏ i : Fin f.degree, (z - f.roots i)

/-- The sublevel set {z : |f(z)| < 1}. -/
def sublevelSet : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

/-
## Inscribed Disc Radius
-/

/-- A disc of radius r centered at c is inscribed in S. -/
def isInscribedDisc (S : Set ℂ) (c : ℂ) (r : ℝ) : Prop :=
  r > 0 ∧ ∀ z : ℂ, ‖z - c‖ < r → z ∈ S

/-- The supremum of radii of inscribed discs. -/
noncomputable def inscribedDiscRadius (S : Set ℂ) : ℝ :=
  sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc S c r}

/-- ρ(f) - the inscribed disc radius of the sublevel set. -/
noncomputable def rho : ℝ := inscribedDiscRadius (sublevelSet f)

/-
## The Benchmark: zⁿ - 1
-/

/-- The polynomial zⁿ - 1 has roots at the n-th roots of unity. -/
noncomputable def rootsOfUnity (n : ℕ) (hn : n > 0) : UnitDiscPolynomial where
  degree := n
  roots := fun k => Complex.exp (2 * Real.pi * Complex.I * k / n)
  roots_in_disc := by
    intro i
    simp only [Complex.norm_exp]
    -- The argument is purely imaginary: rewrite as (real * I), then re = 0
    have heq : 2 * ↑Real.pi * Complex.I * ↑↑(i : ℕ) / ↑(n : ℕ) =
      ↑(2 * Real.pi * (↑(i : ℕ) : ℝ) / (↑n : ℝ)) * Complex.I := by
      push_cast; ring
    rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    simp [Real.exp_zero]

/-- The benchmark upper bound: ρ(zⁿ - 1) ≤ π/(2n). -/
axiom benchmark_upper (n : ℕ) (hn : n > 0) :
  rho (rootsOfUnity n hn) ≤ Real.pi / (2 * n)

/-
## Pommerenke's Lower Bound (1961)
-/

/-- Pommerenke's lower bound: ρ(f) ≥ 1/(2en²). -/
axiom pommerenke_lower (f : UnitDiscPolynomial) (hf : f.degree > 0) :
  rho f ≥ 1 / (2 * Real.exp 1 * (f.degree : ℝ)^2)

/-- The Pommerenke exponent is 2 (quadratic in n). -/
def pommerenkeExponent : ℕ := 2

/-
## Krishnapur-Lundberg-Ramachandran Bound (2025)
-/

/-- The KLR bound: ρ(f) ≥ c/(n√(log n)) for some constant c > 0. -/
axiom klr_lower :
  ∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree ≥ 3 →
    rho f ≥ c / ((f.degree : ℝ) * Real.sqrt (Real.log f.degree))

/-- The KLR bound is better than Pommerenke for large n. -/
theorem klr_better_than_pommerenke :
    ∀ᶠ n in Filter.atTop,
    1 / ((n : ℝ) * Real.sqrt (Real.log n)) > 1 / (2 * Real.exp 1 * n^2) := by
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < n)
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  -- Key chain: √(log n) < log n < n for n ≥ 3
  have hlog_gt_1 : 1 < Real.log (n : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hsqrt_lt_log : Real.sqrt (Real.log (n : ℝ)) < Real.log (n : ℝ) := by
    have h1 : 1 < Real.sqrt (Real.log (n : ℝ)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by linarith) hlog_gt_1
    calc Real.sqrt (Real.log (n : ℝ))
        = Real.sqrt (Real.log (n : ℝ)) * 1 := (mul_one _).symm
      _ < Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) :=
          mul_lt_mul_of_pos_left h1 hsqrt_pos
      _ = Real.log (n : ℝ) := Real.mul_self_sqrt (le_of_lt hlog_pos)
  have hlog_lt_n : Real.log (n : ℝ) < (n : ℝ) := by
    have := Real.add_one_le_exp (Real.log (n : ℝ))
    rw [Real.exp_log hn_pos] at this; linarith
  -- 1/(n√(log n)) > 1/(2en²) ⟺ 2en² > n√(log n) ⟺ 2en > √(log n)
  rw [gt_iff_lt, div_lt_div_iff₀ (by positivity) (mul_pos hn_pos hsqrt_pos)]
  simp only [one_mul]
  push_cast
  nlinarith [Real.exp_one_gt_d9,
             mul_lt_mul_of_pos_left (lt_trans hsqrt_lt_log hlog_lt_n) hn_pos]

/-
## The Erdős-Herzog-Piranian Conjecture
-/

/-- The conjecture: ρ(f) ≫ 1/n for all unit disc polynomials. -/
def ehpConjecture : Prop :=
  ∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree > 0 →
    rho f ≥ c / f.degree

/- The EHP conjecture is an open problem. We neither prove nor disprove it.
    (The previous axiom `¬(P ∨ ¬P)` was inconsistent with classical logic.) -/

/-
## Comparison of Bounds
-/

/-- Pommerenke: 1/(2en²) -/
noncomputable def pommerenkeBound (n : ℕ) : ℝ :=
  1 / (2 * Real.exp 1 * n^2)

/-- KLR: c/(n√(log n)) -/
noncomputable def klrBound (c : ℝ) (n : ℕ) : ℝ :=
  c / (n * Real.sqrt (Real.log n))

/-- Conjectured: c/n -/
noncomputable def conjecturedBound (c : ℝ) (n : ℕ) : ℝ :=
  c / n

/-- Benchmark upper: π/(2n) -/
noncomputable def benchmarkBound (n : ℕ) : ℝ :=
  Real.pi / (2 * n)

/-- For small enough c (c < π/2), the KLR bound is below the benchmark. -/
theorem bounds_gap (n : ℕ) (hn : n ≥ 3) (c : ℝ) (hc : 0 < c) (hc' : c < Real.pi / 2) :
    klrBound c n < benchmarkBound n := by
  simp only [klrBound, benchmarkBound]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < n)
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  have hlog_ge_1 : 1 ≤ Real.log (n : ℝ) := by
    have hexp_le : Real.exp 1 ≤ (n : ℝ) := by
      have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      linarith
    rwa [← Real.le_log_iff_exp_le hn_pos] at hexp_le
  have hsqrt_ge_1 : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    have := Real.sqrt_le_sqrt hlog_ge_1; rwa [Real.sqrt_one] at this
  -- Reduce to: 2c < π√(log n), by clearing positive denominators
  rw [div_lt_div_iff₀ (mul_pos hn_pos hsqrt_pos) (by positivity : (0 : ℝ) < 2 * ↑n)]
  -- Goal: c * (2 * ↑n) < π * (↑n * √(log ↑n))
  -- From c < π/2 and √(log n) ≥ 1: 2cn < πn ≤ πn√(log n)
  nlinarith [Real.pi_pos, hn_pos, hsqrt_ge_1,
    mul_lt_mul_of_pos_right hc' (show (0 : ℝ) < 2 * (n : ℝ) by positivity),
    mul_le_mul_of_nonneg_left hsqrt_ge_1 (show (0 : ℝ) ≤ Real.pi * (n : ℝ) by positivity)]

/-
## The KLR–Conjecture Gap

The comparison lemmas above (`klr_better_than_pommerenke`, `bounds_gap`) place the KLR
bound below the benchmark and above Pommerenke.  The results here pin down *how far*
KLR is from the conjectured optimal rate `c/n`:

* `klrBound_lt_conjecturedBound` — for every fixed constant `c > 0` the KLR bound
  `c/(n√log n)` is **strictly below** the conjectured `c/n` (for `n ≥ 3`).
* `conjecturedBound_div_klrBound` — the *exact* multiplicative gap is `√log n`.
* `conjecturedBound_div_klrBound_tendsto_atTop` — that gap is **unbounded**.

So closing EHP is not a matter of tuning the KLR constant: the KLR lower bound is
asymptotically infinitely far (up to constants) from the conjecture.  These are
unconditional facts about the bound *functions* and use none of the deep axioms.
-/

/-- For `n ≥ 3`, the KLR bound `c/(n√log n)` is strictly below the conjectured `c/n`. -/
theorem klrBound_lt_conjecturedBound (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : n ≥ 3) :
    klrBound c n < conjecturedBound c n := by
  simp only [klrBound, conjecturedBound]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hlog_gt_1 : 1 < Real.log (n : ℝ) := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    refine Real.log_lt_log (Real.exp_pos 1) ?_
    have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  have hsqrt_gt_1 : 1 < Real.sqrt (Real.log (n : ℝ)) :=
    (Real.lt_sqrt (by norm_num)).mpr (by simpa using hlog_gt_1)
  rw [div_lt_div_iff₀ (mul_pos hn_pos hsqrt_pos) hn_pos]
  nlinarith [mul_lt_mul_of_pos_left hsqrt_gt_1 (mul_pos hc hn_pos)]

/-- The exact multiplicative gap between the conjectured and KLR bounds is `√log n`
    (for `c > 0`, `n ≥ 2`). -/
theorem conjecturedBound_div_klrBound (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : n ≥ 2) :
    conjecturedBound c n / klrBound c n = Real.sqrt (Real.log n) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have hlog_pos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast show 1 < n by omega)
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  have h1 : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h2 : c ≠ 0 := hc.ne'
  have h3 : Real.sqrt (Real.log (n : ℝ)) ≠ 0 := hsqrt_pos.ne'
  simp only [conjecturedBound, klrBound]
  field_simp

/-- The multiplicative gap `conjecturedBound / klrBound` is unbounded — it grows like
    `√log n → ∞`.  Hence KLR does not reach the conjectured rate even up to constants. -/
theorem conjecturedBound_div_klrBound_tendsto_atTop (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => conjecturedBound c n / klrBound c n)
      Filter.atTop Filter.atTop := by
  have hsqrt_atTop : Filter.Tendsto Real.sqrt Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b ^ 2 + 1, fun x hx => ?_⟩
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
  have hcomp : Filter.Tendsto (fun n : ℕ => Real.sqrt (Real.log n))
      Filter.atTop Filter.atTop :=
    hsqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  exact (conjecturedBound_div_klrBound c hc n hn).symm

/-
## The Pommerenke–Conjecture Gap

The block above measures how far the *KLR* bound `c/(n√log n)` sits below the conjectured
`c/n`: exactly a factor `√log n`, which is unbounded but grows only logarithmically.  The
*older* Pommerenke bound `1/(2en²)` falls short by much more.  Here we pin down the Pommerenke
shortfall the same way:

* `conjecturedBound_div_pommerenkeBound` — the *exact* multiplicative gap is `2ec·n` (linear
  in `n`, versus KLR's `√log n`).
* `conjecturedBound_div_pommerenkeBound_tendsto_atTop` — that gap diverges.

Together with the KLR block this shows both published lower bounds are asymptotically infinitely
far (up to constants) from the conjecture, and quantifies *how much* the 2025 KLR bound improved
on Pommerenke's 1961 bound: the shortfall dropped from a factor `Θ(n)` to a factor `Θ(√log n)`.
Like the KLR block these are unconditional facts about the bound *functions* and use none of the
deep axioms.
-/

/-- The exact multiplicative gap between the conjectured and Pommerenke bounds is `2ec·n`
    (for `c > 0`, `n ≥ 1`) — linear in `n`, in contrast with KLR's `√log n`. -/
theorem conjecturedBound_div_pommerenkeBound (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : n ≥ 1) :
    conjecturedBound c n / pommerenkeBound n = 2 * Real.exp 1 * c * n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast show 0 < n by omega
  have h1 : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h2 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  simp only [conjecturedBound, pommerenkeBound]
  field_simp

/-- The multiplicative gap `conjecturedBound / pommerenkeBound` is unbounded — it grows like
    `2ec·n → ∞`.  So Pommerenke's bound, too, does not reach the conjectured rate even up to
    constants, and (comparing with `conjecturedBound_div_klrBound_tendsto_atTop`) it falls short
    far faster than KLR. -/
theorem conjecturedBound_div_pommerenkeBound_tendsto_atTop (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => conjecturedBound c n / pommerenkeBound n)
      Filter.atTop Filter.atTop := by
  have hlin : Filter.Tendsto (fun n : ℕ => 2 * Real.exp 1 * c * (n : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.exp 1 * c)
      tendsto_natCast_atTop_atTop
  refine hlin.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (conjecturedBound_div_pommerenkeBound c hc n hn).symm

/-
## Lemniscate Properties
-/

/-- The lemniscate {z : |f(z)| = 1}. -/
def lemniscate : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ = 1}

/-- The sublevel set is open (preimage of (-∞, 1) under the continuous map |f|). -/
theorem sublevelSet_isOpen : IsOpen (sublevelSet f) := by
  simp only [sublevelSet, UnitDiscPolynomial.eval]
  exact isOpen_lt
    (continuous_norm.comp
      (continuous_finset_prod Finset.univ fun i _ => continuous_id.sub continuous_const))
    continuous_const

/-- Each root is in the sublevel set (f(zᵢ) = 0 since the product has a zero factor). -/
theorem root_in_sublevelSet (i : Fin f.degree) :
    f.roots i ∈ sublevelSet f := by
  simp only [sublevelSet, Set.mem_setOf_eq, UnitDiscPolynomial.eval]
  have : ∏ j : Fin f.degree, (f.roots i - f.roots j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  simp [this]

/-- The sublevel set is non-empty (contains the roots). -/
theorem sublevelSet_nonempty (hf : f.degree > 0) :
    (sublevelSet f).Nonempty :=
  ⟨f.roots ⟨0, hf⟩, root_in_sublevelSet f ⟨0, hf⟩⟩

/-
## Area Bounds
-/

/-- Area of the sublevel set (Lebesgue measure, converted to ℝ via toReal). -/
noncomputable def sublevelArea : ℝ := (MeasureTheory.volume (sublevelSet f)).toReal

open MeasureTheory
open scoped ENNReal

/-
## Geometric Infrastructure

The three special-case results below all reduce to elementary facts about the set
of inscribed-disc radii.  We record the shared lemmas first.
-/

/-- An inscribed disc is literally a metric ball contained in `S`. -/
theorem inscribed_ball_subset {S : Set ℂ} {c : ℂ} {r : ℝ}
    (h : isInscribedDisc S c r) : Metric.ball c r ⊆ S := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  exact h.2 z hz

/-- If the open ball `B(c, r)` (with `r > 0`) is contained in `B(z₀, R)` (with `R > 0`),
    then `r ≤ R`.  Proof: push a point of `B(c, r)` in the direction away from `z₀`. -/
theorem inscribed_radius_le {c z0 : ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (h : ∀ z : ℂ, ‖z - c‖ < r → ‖z - z0‖ < R) : r ≤ R := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨u, hu, hcu⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ (c - z0) = (‖c - z0‖ : ℝ) • u := by
    rcases eq_or_ne (c - z0) 0 with h0 | h0
    · exact ⟨1, norm_one, by rw [h0]; simp⟩
    · refine ⟨(‖c - z0‖ : ℝ)⁻¹ • (c - z0), ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0), one_smul]
  set t : ℝ := (r + R) / 2 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have htr : t < r := by rw [ht]; linarith
  have htR : R < t := by rw [ht]; linarith
  have hwc : ‖(c + t • u) - c‖ < r := by
    have he : (c + t • u) - c = t • u := by abel
    rw [he, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
    exact htr
  have hwz : ‖(c + t • u) - z0‖ < R := h _ hwc
  have hcompute : ‖(c + t • u) - z0‖ = ‖c - z0‖ + t := by
    have e1 : (c + t • u) - z0 = ((‖c - z0‖ : ℝ) + t) • u := by
      rw [add_smul, ← hcu]; abel
    rw [e1, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by have := norm_nonneg (c - z0); linarith)]
  rw [hcompute] at hwz
  have hnn := norm_nonneg (c - z0)
  linarith

/-- For a polynomial of positive degree, the sublevel set sits inside the ball of radius 2:
    if `‖z‖ ≥ 2` then every factor `‖z - zᵢ‖ ≥ 1`, so `‖f(z)‖ ≥ 1`. -/
theorem sublevelSet_subset_ball (hf : 0 < f.degree) :
    sublevelSet f ⊆ Metric.ball 0 2 := by
  intro z hz
  simp only [sublevelSet, Set.mem_setOf_eq, UnitDiscPolynomial.eval] at hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hcon
  push_neg at hcon
  have hfac : ∀ i : Fin f.degree, (1 : ℝ) ≤ ‖z - f.roots i‖ := by
    intro i
    have htri : ‖z‖ ≤ ‖z - f.roots i‖ + ‖f.roots i‖ := by
      have := norm_add_le (z - f.roots i) (f.roots i)
      simpa using this
    have hri := f.roots_in_disc i
    linarith
  have hprod : (1 : ℝ) ≤ ∏ i : Fin f.degree, ‖z - f.roots i‖ := by
    calc (1 : ℝ) = ∏ _i : Fin f.degree, (1 : ℝ) := by rw [Finset.prod_const_one]
      _ ≤ ∏ i : Fin f.degree, ‖z - f.roots i‖ :=
          Finset.prod_le_prod (fun i _ => zero_le_one) (fun i _ => hfac i)
  rw [← norm_prod] at hprod
  linarith

/-- The set of inscribed-disc radii is bounded above (by `8`) for positive degree. -/
theorem bddAbove_inscribed_radii (hf : 0 < f.degree) :
    BddAbove {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} := by
  refine ⟨8, ?_⟩
  rintro r ⟨c, hrpos, hsub⟩
  have hcmem : c ∈ sublevelSet f := hsub c (by simpa using hrpos)
  have hc2 : ‖c‖ < 2 := by
    have h := sublevelSet_subset_ball f hf hcmem
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hxmem : (c + ((r / 2 : ℝ) : ℂ)) ∈ sublevelSet f := by
    apply hsub
    have he : (c + ((r / 2 : ℝ) : ℂ)) - c = ((r / 2 : ℝ) : ℂ) := by ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hx2 : ‖c + ((r / 2 : ℝ) : ℂ)‖ < 2 := by
    have h := sublevelSet_subset_ball f hf hxmem
    rwa [Metric.mem_ball, dist_zero_right] at h
  have he2 : ‖((r / 2 : ℝ) : ℂ)‖ ≤ ‖c + ((r / 2 : ℝ) : ℂ)‖ + ‖c‖ := by
    have h := norm_sub_le (c + ((r / 2 : ℝ) : ℂ)) c
    have he : (c + ((r / 2 : ℝ) : ℂ)) - c = ((r / 2 : ℝ) : ℂ) := by ring
    rwa [he] at h
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at he2
  linarith

/-- When the polynomial has degree zero it is the empty product `1`, so the sublevel set
    `{z : |f(z)| < 1}` is empty. -/
theorem sublevelSet_degree_zero (h : f.degree = 0) : sublevelSet f = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  simp only [sublevelSet, Set.mem_setOf_eq, UnitDiscPolynomial.eval] at hz
  haveI : IsEmpty (Fin f.degree) := by rw [h]; infer_instance
  rw [Finset.univ_eq_empty, Finset.prod_empty, norm_one] at hz
  exact absurd hz (lt_irrefl 1)

/-- Lower bound on area implies lower bound on inscribed disc: the sublevel set contains an
    inscribed disc of every radius `r < ρ(f)`, each of area `π r²`, so its area is `≥ π ρ(f)²`. -/
theorem area_implies_disc_bound :
    sublevelArea f ≥ Real.pi * (rho f)^2 := by
  rcases Set.eq_empty_or_nonempty
      {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} with hempty | hne
  · -- No inscribed disc exists, so ρ(f) = sSup ∅ = 0.
    have hz : rho f = 0 := by
      show sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} = 0
      rw [hempty, Real.sSup_empty]
    rw [ge_iff_le, hz]
    have h0 : Real.pi * (0 : ℝ) ^ 2 = 0 := by ring
    rw [h0]
    exact ENNReal.toReal_nonneg
  · obtain ⟨r0, hr0mem⟩ := hne
    obtain ⟨c0, hr0pos, hsub0⟩ := hr0mem
    have hc0 : c0 ∈ sublevelSet f := hsub0 c0 (by simpa using hr0pos)
    have hdeg : 0 < f.degree := by
      rcases Nat.eq_zero_or_pos f.degree with h0 | hpos
      · rw [sublevelSet_degree_zero f h0] at hc0; exact absurd hc0 (Set.notMem_empty _)
      · exact hpos
    have hfin : MeasureTheory.volume (sublevelSet f) ≠ ⊤ :=
      ((Metric.isBounded_ball).subset (sublevelSet_subset_ball f hdeg)).measure_lt_top.ne
    have hpi : 0 < Real.pi := Real.pi_pos
    have hkey : ∀ r ∈ {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r},
        Real.pi * r ^ 2 ≤ sublevelArea f := by
      rintro r ⟨c, hrpos, hsub⟩
      have hsubset : Metric.ball c r ⊆ sublevelSet f := inscribed_ball_subset ⟨hrpos, hsub⟩
      have hvol : MeasureTheory.volume (Metric.ball c r)
          ≤ MeasureTheory.volume (sublevelSet f) := measure_mono hsubset
      rw [Complex.volume_ball] at hvol
      have hle2 : ((ENNReal.ofReal r) ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal ≤ sublevelArea f :=
        (ENNReal.toReal_le_toReal
          (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top)
          hfin).mpr hvol
      have hcompute : ((ENNReal.ofReal r) ^ 2 * (NNReal.pi : ℝ≥0∞)).toReal = Real.pi * r ^ 2 := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hrpos.le,
            ENNReal.coe_toReal, NNReal.coe_real_pi]
        ring
      rw [hcompute] at hle2
      exact hle2
    have hbdd : BddAbove {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} :=
      bddAbove_inscribed_radii f hdeg
    have hsup_bound :
        sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r}
          ≤ Real.sqrt (sublevelArea f / Real.pi) := by
      refine csSup_le ⟨r0, c0, hr0pos, hsub0⟩ ?_
      rintro r ⟨c, hrpos, hsub⟩
      have h1 : Real.pi * r ^ 2 ≤ sublevelArea f := hkey r ⟨c, hrpos, hsub⟩
      have h2 : r ^ 2 ≤ sublevelArea f / Real.pi := by
        rw [le_div_iff₀ hpi]; nlinarith [h1]
      calc r = Real.sqrt (r ^ 2) := (Real.sqrt_sq hrpos.le).symm
        _ ≤ Real.sqrt (sublevelArea f / Real.pi) := Real.sqrt_le_sqrt h2
    have hsup_nonneg :
        0 ≤ sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} :=
      le_trans hr0pos.le (le_csSup hbdd ⟨c0, hr0pos, hsub0⟩)
    have hrho : rho f = sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} := rfl
    rw [ge_iff_le, hrho]
    have hsq :
        (sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r}) ^ 2
          ≤ sublevelArea f / Real.pi := by
      have harea : (0 : ℝ) ≤ sublevelArea f := by
        unfold sublevelArea; exact ENNReal.toReal_nonneg
      have hs : Real.sqrt (sublevelArea f / Real.pi) ^ 2 = sublevelArea f / Real.pi :=
        Real.sq_sqrt (div_nonneg harea hpi.le)
      nlinarith [hsup_bound, hsup_nonneg, hs, Real.sqrt_nonneg (sublevelArea f / Real.pi)]
    calc Real.pi * (sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r}) ^ 2
        ≤ Real.pi * (sublevelArea f / Real.pi) := mul_le_mul_of_nonneg_left hsq hpi.le
      _ = sublevelArea f := by field_simp

/-- The KLR paper establishes area bounds that imply disc bounds. -/
axiom klr_area_bound (f : UnitDiscPolynomial) (hf : f.degree ≥ 3) :
  sublevelArea f ≥ Real.pi / ((f.degree : ℝ)^2 * Real.log f.degree)

/-
## Special Cases
-/

/-- For n = 1, the sublevel set is exactly the unit disc about the single root, so ρ(f) = 1. -/
theorem degree_one_optimal :
    ∀ (f : UnitDiscPolynomial), f.degree = 1 → rho f = 1 := by
  intro f hdeg1
  have hdeg : 0 < f.degree := by rw [hdeg1]; norm_num
  have hcard : (Finset.univ : Finset (Fin f.degree)).card = 1 := by
    rw [Finset.card_univ, Fintype.card_fin, hdeg1]
  have herase : (Finset.univ.erase (⟨0, hdeg⟩ : Fin f.degree)) = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_erase_of_mem (Finset.mem_univ _), hcard]
  have hprod : ∀ z : ℂ, (∏ i : Fin f.degree, (z - f.roots i)) = z - f.roots ⟨0, hdeg⟩ := by
    intro z
    rw [← Finset.prod_erase_mul (Finset.univ) (fun i => z - f.roots i)
        (Finset.mem_univ (⟨0, hdeg⟩ : Fin f.degree)), herase, Finset.prod_empty, one_mul]
  set z0 : ℂ := f.roots ⟨0, hdeg⟩ with hz0
  have hset : sublevelSet f = Metric.ball z0 1 := by
    ext z
    simp only [sublevelSet, Set.mem_setOf_eq, UnitDiscPolynomial.eval, Metric.mem_ball,
      dist_eq_norm]
    rw [hprod z]
  have hins1 : isInscribedDisc (sublevelSet f) z0 1 := by
    refine ⟨one_pos, ?_⟩
    intro z hz
    rw [hset, Metric.mem_ball, dist_eq_norm]
    exact hz
  have hrho : rho f = sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} := rfl
  rw [hrho]
  have hne1 : {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r}.Nonempty :=
    ⟨1, z0, hins1⟩
  apply le_antisymm
  · apply csSup_le hne1
    rintro r ⟨c, hrpos, hsub⟩
    refine inscribed_radius_le (c := c) (z0 := z0) hrpos one_pos ?_
    intro z hz
    have hmem := hsub z hz
    rw [hset, Metric.mem_ball, dist_eq_norm] at hmem
    exact hmem
  · exact le_csSup (bddAbove_inscribed_radii f hdeg) ⟨z0, hins1⟩

/-- For clustered roots, the inscribed disc can be larger. -/
def hasClusteredRoots (f : UnitDiscPolynomial) (ε : ℝ) : Prop :=
  ∃ c : ℂ, ∀ i, ‖f.roots i - c‖ < ε

/-- Clustered roots give a larger inscribed disc: if all roots lie within `ε` of a common
    centre `c`, then for `‖z - c‖ < 1 - ε` every factor `‖z - zᵢ‖ < 1`, so `‖f(z)‖ < 1`. -/
theorem clustered_implies_large_disc (ε : ℝ) (hε : ε > 0) (hε' : ε < 1) :
    ∀ (f : UnitDiscPolynomial), hasClusteredRoots f ε → f.degree > 0 →
      rho f ≥ 1 - ε := by
  intro f hclust hdeg
  obtain ⟨c, hc⟩ := hclust
  have hins : isInscribedDisc (sublevelSet f) c (1 - ε) := by
    refine ⟨by linarith, ?_⟩
    intro z hz
    simp only [sublevelSet, Set.mem_setOf_eq, UnitDiscPolynomial.eval]
    have hfac : ∀ i : Fin f.degree, ‖z - f.roots i‖ < 1 := by
      intro i
      have harg : z - f.roots i = (z - c) - (f.roots i - c) := by ring
      have hci := hc i
      calc ‖z - f.roots i‖ = ‖(z - c) - (f.roots i - c)‖ := by rw [harg]
        _ ≤ ‖z - c‖ + ‖f.roots i - c‖ := norm_sub_le _ _
        _ < (1 - ε) + ε := by linarith
        _ = 1 := by ring
    rw [norm_prod]
    have hi0 : (⟨0, hdeg⟩ : Fin f.degree) ∈ (Finset.univ : Finset (Fin f.degree)) :=
      Finset.mem_univ _
    rw [← Finset.prod_erase_mul (Finset.univ) (fun i => ‖z - f.roots i‖) hi0]
    have hrest : (∏ i ∈ (Finset.univ).erase (⟨0, hdeg⟩ : Fin f.degree), ‖z - f.roots i‖) ≤ 1 :=
      Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => (hfac i).le)
    calc (∏ i ∈ (Finset.univ).erase (⟨0, hdeg⟩ : Fin f.degree), ‖z - f.roots i‖)
            * ‖z - f.roots ⟨0, hdeg⟩‖
        ≤ 1 * ‖z - f.roots ⟨0, hdeg⟩‖ := mul_le_mul_of_nonneg_right hrest (norm_nonneg _)
      _ = ‖z - f.roots ⟨0, hdeg⟩‖ := one_mul _
      _ < 1 := hfac _
  have hrho : rho f = sSup {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} := rfl
  rw [ge_iff_le, hrho]
  exact le_csSup (bddAbove_inscribed_radii f hdeg) ⟨c, hins⟩

/-
## Random Polynomials
-/

/-- For random polynomials, the expected ρ is of order 1/√n.

    NOTE: as *stated in Lean* this proposition is degenerate — the intended middle
    term `Expected[rho(random poly of degree n)]` is only a comment, so the actual
    statement collapses to `c₁/√n ≤ c₂/√n`, which is trivially true (take
    `c₁ = c₂ = 1`). It therefore carries no genuine assumption and is discharged
    here as a theorem rather than left as an `axiom`, removing a spurious entry
    from the axiom list. The real content — that the *expected* order of magnitude
    of `ρ` for a random degree-`n` polynomial is `Θ(1/√n)` — requires an
    `Expected[·]` functional and remains unformalized. -/
theorem random_polynomial_expected :
  ∃ c₁ > 0, ∃ c₂ > 0, ∀ n : ℕ, n ≥ 2 →
    c₁ / Real.sqrt n ≤ -- Expected[rho(random poly of degree n)]
    c₂ / Real.sqrt n :=
  ⟨1, one_pos, 1, one_pos, fun _ _ => le_refl _⟩

/-
## The Open Question
-/

/-- The main open question: close the gap between 1/(n√log n) and 1/n. -/
def erdos_1039_question : Prop :=
  ehpConjecture

/-- Current state: known bounds, conjecture unresolved. -/
theorem erdos_1039_current_state :
    (∃ c > 0, ∀ (f : UnitDiscPolynomial), f.degree ≥ 3 →
      rho f ≥ c / ((f.degree : ℝ) * Real.sqrt (Real.log f.degree))) ∧
    (∀ n : ℕ, n > 0 → ∃ (f : UnitDiscPolynomial), f.degree = n ∧
      rho f ≤ Real.pi / (2 * n)) := by
  constructor
  · exact klr_lower
  · intro n hn
    use rootsOfUnity n hn
    constructor
    · rfl
    · exact benchmark_upper n hn

/-
## Summary

Erdős Problem #1039 asks about the inscribed disc radius ρ(f) for
polynomials with roots in the unit disc.

**Known**:
- Upper: ρ(zⁿ-1) ≤ π/(2n) (benchmark)
- Lower: ρ(f) ≥ 1/(2en²) (Pommerenke 1961)
- Lower: ρ(f) ≫ 1/(n√log n) (KLR 2025)

**Conjecture**: ρ(f) ≫ 1/n

**Status**: OPEN - the gap between 1/(n√log n) and 1/n remains.
-/

end Erdos1039
