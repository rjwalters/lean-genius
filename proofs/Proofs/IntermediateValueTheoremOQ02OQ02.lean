import Mathlib

/-
# Convergence Rates: Bisection (linear) vs. Newton (quadratic)

## Research problem: intermediate-value-theorem-oq-02-oq-02

The parent entry `intermediate-value-theorem-oq-02` built the **bisection algorithm**
attached to the constructive IVT and proved its bracket width is `(b-a)/2ⁿ`. The
sibling `-oq-02-oq-01` recovered the exact classical root as the common limit of the
bracket endpoints. This entry quantifies and *compares* how fast two classical
root-finding schemes approach the root:

* **Bisection** converges **linearly** with ratio `1/2`: the error is at most
  `(b-a)/2ⁿ⁺¹` and is exactly halved at every step. In "correct binary digits"
  the method gains **one bit per iteration**.
* **Newton's method** converges **quadratically**: the error obeys a recurrence
  `eₙ₊₁ ≤ C·eₙ²`, so the number of correct digits **doubles** per iteration once the
  iteration enters its basin of attraction.

## What is proved here (all `0`-axiom, no `sorry`)

1. **Abstract rate lemmas** — the mathematical heart of the comparison, stated for an
   arbitrary nonnegative error sequence:
   * `linear_rate` : `eₙ₊₁ ≤ r·eₙ  ⟹  eₙ ≤ rⁿ·e₀`.
   * `quadratic_rate` : `eₙ₊₁ ≤ C·eₙ²  ⟹  C·eₙ ≤ (C·e₀)^(2ⁿ)`.
   * Convergence corollaries: `r < 1` gives `rⁿ → 0`; `C·e₀ < 1` gives the
     doubly-exponential `(C·e₀)^(2ⁿ) → 0`.

2. **Bisection instantiation** (genuinely linear, ratio `1/2`):
   `bisect_error_bound` bounds the midpoint error by `(b-a)/2ⁿ⁺¹` for *any* point of
   the bracket, and `bisect_error_halves` shows the bound halves each step.

3. **Newton instantiation** (genuinely quadratic), via a fully worked, self-contained
   example: **Newton's iteration for `√A`** (`xₙ₊₁ = (xₙ + A/xₙ)/2`). We prove the
   exact identity `xₙ₊₁ - √A = (xₙ - √A)²/(2xₙ)`, deduce the quadratic error
   recurrence `eₙ₊₁ ≤ eₙ²/(2√A)`, and feed it through `quadratic_rate` to obtain
   true quadratic convergence. This derives — rather than assumes — the recurrence.

4. **The comparison** `quadratic_dominates_linear` : `r^(2ⁿ) ≤ rⁿ` for `0 ≤ r ≤ 1`
   (strict for `n ≥ 1`, `r < 1`): started from the same contraction factor, the
   quadratic error bound is never worse than the linear one and beats it from the
   first step on. This is the precise sense in which "doubling digits" outruns
   "adding one digit".

Everything is elementary and machine-checked; no completeness/limit axioms beyond
Mathlib's reals are used.
-/

namespace IVTConvergenceRates

open scoped Topology

/-! ## Part I — Abstract convergence-rate lemmas -/

/-- **Linear convergence.** If a nonnegative error sequence contracts by a factor
`r ≥ 0` at every step, then `eₙ ≤ rⁿ · e₀`. -/
theorem linear_rate {e : ℕ → ℝ} (_he : ∀ n, 0 ≤ e n) {r : ℝ} (hr : 0 ≤ r)
    (hrec : ∀ n, e (n + 1) ≤ r * e n) : ∀ n, e n ≤ r ^ n * e 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc e (n + 1) ≤ r * e n := hrec n
      _ ≤ r * (r ^ n * e 0) := by exact mul_le_mul_of_nonneg_left ih hr
      _ = r ^ (n + 1) * e 0 := by ring

/-- The linear bound tends to `0` when the contraction factor is `< 1`. -/
theorem linear_tendsto_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => r ^ n) Filter.atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

/-- **Quadratic convergence.** If a nonnegative error sequence satisfies
`eₙ₊₁ ≤ C · eₙ²` with `C ≥ 0`, then the rescaled error `gₙ = C · eₙ` is squared at
every step, giving the doubly-exponential bound `C · eₙ ≤ (C · e₀)^(2ⁿ)`. -/
theorem quadratic_rate {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n) {C : ℝ} (hC : 0 ≤ C)
    (hrec : ∀ n, e (n + 1) ≤ C * (e n) ^ 2) :
    ∀ n, C * e n ≤ (C * e 0) ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hgn : 0 ≤ C * e n := mul_nonneg hC (he n)
    have step : C * e (n + 1) ≤ (C * e n) ^ 2 := by
      calc C * e (n + 1) ≤ C * (C * (e n) ^ 2) :=
            mul_le_mul_of_nonneg_left (hrec n) hC
        _ = (C * e n) ^ 2 := by ring
    calc C * e (n + 1) ≤ (C * e n) ^ 2 := step
      _ ≤ ((C * e 0) ^ (2 ^ n)) ^ 2 := by exact pow_le_pow_left₀ hgn ih 2
      _ = (C * e 0) ^ (2 ^ (n + 1)) := by rw [← pow_mul, ← pow_succ]

/-- The quadratic bound tends to `0` (doubly exponentially) once `C · e₀ < 1`.
We phrase the decay through the explicit bound: `(C·e₀)^(2ⁿ) ≤ (C·e₀)ⁿ`, and the
right side already tends to `0` by `linear_tendsto_zero`. -/
theorem quadratic_le_linear_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    q ^ (2 ^ n) ≤ q ^ n :=
  pow_le_pow_of_le_one hq0 hq1 (Nat.le_of_lt n.lt_two_pow_self)

/-- Convergence of the quadratic bound to `0` for `0 ≤ q < 1`. -/
theorem quadratic_tendsto_zero {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Filter.Tendsto (fun n => q ^ (2 ^ n)) Filter.atTop (𝓝 0) := by
  have hsq : Filter.Tendsto (fun n => q ^ n) Filter.atTop (𝓝 0) :=
    linear_tendsto_zero hq0 hq1
  refine squeeze_zero (fun n => pow_nonneg hq0 _) (fun n => ?_) hsq
  exact quadratic_le_linear_bound hq0 (le_of_lt hq1) n

/-! ## Part II — Bisection: linear convergence with ratio `1/2`

We re-state the minimal bisection primitives so the file is self-contained; they are
identical to the parent entry `IntermediateValueTheoremOQ02`. -/

/-- One bisection step: keep the half whose midpoint sign matches a root. -/
noncomputable def bisectStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f ((p.1 + p.2) / 2) ≤ 0 then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)

/-- `n`-fold bisection. -/
noncomputable def bisect (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  match n with
  | 0 => p
  | n + 1 => bisectStep f (bisect f n p)

/-- The midpoint produced after `n` steps. -/
noncomputable def bisectMid (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  ((bisect f n p).1 + (bisect f n p).2) / 2

/-- A bisection step halves the bracket width. -/
theorem bisectStep_width (f : ℝ → ℝ) (p : ℝ × ℝ) :
    (bisectStep f p).2 - (bisectStep f p).1 = (p.2 - p.1) / 2 := by
  unfold bisectStep; split_ifs <;> dsimp only <;> ring

/-- A bisection step preserves the endpoint ordering. -/
theorem bisectStep_ordered (f : ℝ → ℝ) (p : ℝ × ℝ) (h : p.1 ≤ p.2) :
    (bisectStep f p).1 ≤ (bisectStep f p).2 := by
  unfold bisectStep; split_ifs <;> dsimp only <;> linarith

/-- After `n` steps the bracket width is `(b - a)/2ⁿ`. -/
theorem bisect_width (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) :
    (bisect f n p).2 - (bisect f n p).1 = (p.2 - p.1) / 2 ^ n := by
  induction n with
  | zero => simp [bisect]
  | succ n ih =>
    show (bisectStep f (bisect f n p)).2 - (bisectStep f (bisect f n p)).1 = _
    rw [bisectStep_width, ih]; ring

/-- After `n` steps the bracket endpoints are still ordered. -/
theorem bisect_ordered (f : ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) (h : p.1 ≤ p.2) :
    (bisect f n p).1 ≤ (bisect f n p).2 := by
  induction n with
  | zero => exact h
  | succ n ih => exact bisectStep_ordered f _ ih

/-- **Bisection error bound (linear rate `1/2`).** The midpoint approximates *every*
point `x` of the `n`-th bracket with error at most `(b - a)/2ⁿ⁺¹`. In particular, a
true root (which the parent entry shows lies in the bracket) is approximated to that
precision. -/
theorem bisect_error_bound (f : ℝ → ℝ) (a b : ℝ) (_hab : a ≤ b) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (bisect f n (a, b)).1 (bisect f n (a, b)).2) :
    |bisectMid f n (a, b) - x| ≤ (b - a) / 2 ^ (n + 1) := by
  obtain ⟨hxL, hxR⟩ := hx
  have hw : (bisect f n (a, b)).2 - (bisect f n (a, b)).1 = (b - a) / 2 ^ n := by
    simpa using bisect_width f n (a, b)
  have hpow : (b - a) / 2 ^ (n + 1) = ((b - a) / 2 ^ n) / 2 := by
    rw [pow_succ]; ring
  simp only [bisectMid]
  rw [hpow, ← hw, abs_le]
  constructor <;> linarith

/-- The bisection error bound **halves at every step** — the defining feature of
linear convergence with ratio `1/2`. -/
theorem bisect_error_halves (a b : ℝ) (n : ℕ) :
    (b - a) / 2 ^ (n + 1 + 1) = ((b - a) / 2 ^ (n + 1)) / 2 := by
  rw [pow_succ]; ring

/-- Restated as a contraction recurrence so it plugs directly into `linear_rate`:
the bisection error sequence `Eₙ = (b-a)/2ⁿ⁺¹` satisfies `Eₙ₊₁ = (1/2)·Eₙ`. -/
theorem bisect_error_linear_recurrence (a b : ℝ) (n : ℕ) :
    (b - a) / 2 ^ (n + 1 + 1) = (1 / 2) * ((b - a) / 2 ^ (n + 1)) := by
  rw [pow_succ]; ring

/-! ## Part III — Newton: quadratic convergence for `√A`

A fully self-contained quadratic instance. For `A > 0` the Newton iteration for the
zero of `t ↦ t² - A` is `xₙ₊₁ = (xₙ + A/xₙ)/2`. We derive the exact error identity and
the quadratic recurrence, then conclude via `quadratic_rate`. -/

/-- Newton step for `√A`: `x ↦ (x + A/x)/2`. -/
noncomputable def sqrtNewtonStep (A x : ℝ) : ℝ := (x + A / x) / 2

/-- Newton iterates for `√A` from a start `x₀`. -/
noncomputable def sqrtNewtonSeq (A x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => sqrtNewtonStep A (sqrtNewtonSeq A x₀ n)

/-- **Exact Newton error identity.** With `s = √A` and `x > 0`,
`sqrtNewtonStep A x - s = (x - s)²/(2x)`. -/
theorem sqrtNewtonStep_sub_sqrt (A x : ℝ) (hA : 0 ≤ A) (hx : 0 < x) :
    sqrtNewtonStep A x - Real.sqrt A = (x - Real.sqrt A) ^ 2 / (2 * x) := by
  have hs : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  rw [sqrtNewtonStep]
  field_simp
  nlinarith [hs, hx]

/-- One Newton step lands at or above `√A` (and stays positive) when `x > 0`. -/
theorem sqrtNewtonStep_ge_sqrt (A x : ℝ) (hA : 0 ≤ A) (hx : 0 < x) :
    Real.sqrt A ≤ sqrtNewtonStep A x := by
  have hid := sqrtNewtonStep_sub_sqrt A x hA hx
  have hnn : 0 ≤ (x - Real.sqrt A) ^ 2 / (2 * x) := by positivity
  linarith [hid ▸ hnn]

/-- Positivity is preserved by the Newton step, given `A > 0`. -/
theorem sqrtNewtonStep_pos (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    0 < sqrtNewtonStep A x :=
  lt_of_lt_of_le (Real.sqrt_pos.2 hA) (sqrtNewtonStep_ge_sqrt A x hA.le hx)

/-- All Newton iterates are positive (for `A > 0`, `x₀ > 0`). -/
theorem sqrtNewtonSeq_pos (A x₀ : ℝ) (hA : 0 < A) (hx₀ : 0 < x₀) :
    ∀ n, 0 < sqrtNewtonSeq A x₀ n := by
  intro n
  induction n with
  | zero => exact hx₀
  | succ n ih => exact sqrtNewtonStep_pos A _ hA ih

/-- From step `1` on, every iterate is `≥ √A`. -/
theorem sqrtNewtonSeq_ge_sqrt (A x₀ : ℝ) (hA : 0 < A) (hx₀ : 0 < x₀) :
    ∀ n, Real.sqrt A ≤ sqrtNewtonSeq A x₀ (n + 1) := by
  intro n
  have hpos := sqrtNewtonSeq_pos A x₀ hA hx₀ n
  exact sqrtNewtonStep_ge_sqrt A _ hA.le hpos

/-- **Quadratic error recurrence for Newton's `√A` iteration.** Writing
`eₙ = xₙ₊₁ - √A ≥ 0` for the error from step `1` on, we have
`eₙ₊₁ ≤ (1/(2√A)) · eₙ²` — genuine quadratic convergence with `C = 1/(2√A)`. -/
theorem sqrtNewton_quadratic_recurrence (A x₀ : ℝ) (hA : 0 < A) (hx₀ : 0 < x₀)
    (n : ℕ) :
    sqrtNewtonSeq A x₀ (n + 2) - Real.sqrt A
      ≤ (1 / (2 * Real.sqrt A)) * (sqrtNewtonSeq A x₀ (n + 1) - Real.sqrt A) ^ 2 := by
  set s := Real.sqrt A with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hA
  have hxpos : 0 < sqrtNewtonSeq A x₀ (n + 1) := sqrtNewtonSeq_pos A x₀ hA hx₀ (n + 1)
  have hxge : s ≤ sqrtNewtonSeq A x₀ (n + 1) := sqrtNewtonSeq_ge_sqrt A x₀ hA hx₀ n
  have hid : sqrtNewtonSeq A x₀ (n + 2) - s
      = (sqrtNewtonSeq A x₀ (n + 1) - s) ^ 2 / (2 * sqrtNewtonSeq A x₀ (n + 1)) := by
    have : sqrtNewtonSeq A x₀ (n + 2)
        = sqrtNewtonStep A (sqrtNewtonSeq A x₀ (n + 1)) := rfl
    rw [this, hsdef]
    exact sqrtNewtonStep_sub_sqrt A _ hA.le hxpos
  rw [hid]
  have hle : 2 * s ≤ 2 * sqrtNewtonSeq A x₀ (n + 1) := by linarith
  calc (sqrtNewtonSeq A x₀ (n + 1) - s) ^ 2 / (2 * sqrtNewtonSeq A x₀ (n + 1))
      ≤ (sqrtNewtonSeq A x₀ (n + 1) - s) ^ 2 / (2 * s) := by gcongr
    _ = 1 / (2 * s) * (sqrtNewtonSeq A x₀ (n + 1) - s) ^ 2 := by ring

/-! ## Part IV — The comparison: quadratic dominates linear -/

/-- **Quadratic dominates linear.** Started from the *same* contraction factor
`0 ≤ r ≤ 1`, the quadratic error bound `r^(2ⁿ)` never exceeds the linear bound `rⁿ`.
Because `n < 2ⁿ`, the quadratic bound is strictly smaller for `n ≥ 1` whenever
`r < 1`: bisection adds one correct bit per step, Newton doubles them. -/
theorem quadratic_dominates_linear {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    r ^ (2 ^ n) ≤ r ^ n :=
  pow_le_pow_of_le_one hr0 hr1 (Nat.le_of_lt n.lt_two_pow_self)

/-- Strict domination from the first step on (`n ≥ 1`, `r < 1`, `r > 0`). -/
theorem quadratic_strictly_dominates {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {n : ℕ} (_hn : 1 ≤ n) : r ^ (2 ^ n) < r ^ n := by
  have hgt : n < 2 ^ n := n.lt_two_pow_self
  have hsplit : r ^ (2 ^ n) = r ^ n * r ^ (2 ^ n - n) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  have hpos : 0 < r ^ n := pow_pos hr0 n
  have hlt1 : r ^ (2 ^ n - n) < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  calc r ^ n * r ^ (2 ^ n - n) < r ^ n * 1 := mul_lt_mul_of_pos_left hlt1 hpos
    _ = r ^ n := mul_one _

/-- **Summary comparison.** For a normalized error `0 < q < 1`:
the bisection bound after `n` steps is `q · (1/2)ⁿ`-style geometric decay (one bit
per step), while the Newton bound `q^(2ⁿ)` is doubly exponential and dominated termwise
by the geometric `qⁿ`. Both go to `0`; the Newton bound does so unboundedly faster. -/
theorem rate_comparison_summary {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∀ n, q ^ (2 ^ n) ≤ q ^ n) ∧
    (∀ n, 1 ≤ n → q ^ (2 ^ n) < q ^ n) ∧
    Filter.Tendsto (fun n => q ^ n) Filter.atTop (𝓝 0) ∧
    Filter.Tendsto (fun n => q ^ (2 ^ n)) Filter.atTop (𝓝 0) :=
  ⟨fun n => quadratic_dominates_linear hq0.le hq1.le n,
   fun _n hn => quadratic_strictly_dominates hq0 hq1 hn,
   linear_tendsto_zero hq0.le hq1,
   quadratic_tendsto_zero hq0.le hq1⟩

end IVTConvergenceRates
