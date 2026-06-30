/-
# The quintic Bernoulli endpoint: `a₅* ∈ (−3, −2)` and the monotone creep toward `−2`

**Open question (bernoulli-inequality-oq-01-oq-01-oq-01).** The parent entry
`bernoulli-inequality-oq-01-oq-01-oq-01` (`BernoulliInequalityOQ01OQ01OQ01.lean`)
proved that `−2` is the sharp *uniform* (`n`-independent) left endpoint of the
strict Bernoulli inequality `1 + n·a < (1 + a)ⁿ`, while for each *individual* odd
exponent the true endpoint `aₙ*` lies strictly **below** `−2`.  It pinned the cubic
case exactly — `cubic_iff` shows the `n = 3` endpoint is `a₃* = −3` — and left open
the behaviour of the higher odd endpoints, observing only that the sequence
`a₃* < a₅* < a₇* < ⋯` is expected to *creep up toward `−2`*.

This file resolves the **next odd case `n = 5`** and thereby exhibits the first
step of that creep.  The mechanism mirrors the parent's cubic factorisation: where
`(1+a)³ − (1+3a) = a²(a + 3)` had the rational root `−3`, here

  `(1+a)⁵ − (1+5a) = a² · (a³ + 5a² + 10a + 10)`

and the residual cubic `g(a) = a³ + 5a² + 10a + 10` has **no rational root**.  We
show `g` is strictly increasing (its derivative `3a² + 10a + 12` — equivalently the
divided-difference bracket — is a positive-definite quadratic), so it has a *unique*
real root `a₅*`, and locate it by the sign change `g(−3) = −2 < 0 < 2 = g(−2)`.

## Main results

* `quintic_factor` — the residual factorisation `(1+a)⁵ − (1+5a) = a²·g(a)`.
* `residualCubic_strictMono` — `g` is strictly monotone, hence injective: the
  endpoint is unique.
* `quintic_iff_residual_pos` — `1 + 5a < (1+a)⁵ ↔ a ≠ 0 ∧ 0 < g(a)`.
* `quintic_endpoint` — **the headline.** There is an endpoint `a₅* ∈ (−3, −2)` with
  `1 + 5a < (1+a)⁵ ↔ a ≠ 0 ∧ a₅* < a`, the exact analogue of the parent's
  `cubic_iff` with the irrational endpoint in place of `−3`.  Since `−3 < a₅* < −2`,
  this is the first instalment of the creep `a₃* = −3 < a₅* < −2`.
* `strict_at_neg_five_halves` / `quintic_fails_at_neg_29` / `cubic_holds_at_neg_29`
  — concrete witnesses bracketing `a₅*`: the `n = 5` inequality holds at `−5/2` but
  fails at `−29/10`, while the `n = 3` inequality still holds at `−29/10`.  The
  failure of `n = 5` where `n = 3` succeeds is the creep made concrete.
* `strict_at_neg_two_odd` — the structural reason every odd endpoint is below `−2`:
  for *every* odd `n ≥ 2` the strict inequality already holds at `a = −2` (there
  `(1+a)ⁿ = (−1)ⁿ = −1` beats the line `1 − 2n`), so `−2` is interior and `aₙ* < −2`
  universally, with `−2 = sup_n aₙ*` approached from below.

All results are `0`-axiom and machine-checked.
-/
import Mathlib

namespace BernoulliInequalityOQ01OQ01OQ01OQ01

open Real

/-- The residual cubic `g(a) = a³ + 5a² + 10a + 10` left after dividing the
quintic Bernoulli gap `(1+a)⁵ − (1+5a)` by the trivial double factor `a²`. -/
def residualCubic (a : ℝ) : ℝ := a ^ 3 + 5 * a ^ 2 + 10 * a + 10

/-- **Residual factorisation.** `(1 + a)⁵ − (1 + 5a) = a²·g(a)`, the quintic
analogue of the parent's `(1 + a)³ − (1 + 3a) = a²(a + 3)`.  The double factor `a²`
is why `a = 0` is always an equality point; the strict inequality is governed
entirely by the sign of `g`. -/
theorem quintic_factor (a : ℝ) :
    (1 + a) ^ 5 - (1 + 5 * a) = a ^ 2 * residualCubic a := by
  simp only [residualCubic]; ring

/-- **The residual cubic is strictly increasing.** The divided difference
`g(b) − g(a) = (b − a)·(a² + ab + b² + 5a + 5b + 10)` has a positive-definite
bracket — `12·bracket = (3a + 3b + 10)² + 3(a − b)² + 20 > 0` — so `g` is strictly
monotone.  Consequently `g` is injective and has at most one real root: the quintic
endpoint, once located, is unique. -/
theorem residualCubic_strictMono : StrictMono residualCubic := by
  intro a b hab
  have hbr : 0 < a ^ 2 + a * b + b ^ 2 + 5 * a + 5 * b + 10 := by
    nlinarith [sq_nonneg (3 * a + 3 * b + 10), sq_nonneg (a - b)]
  have hid : residualCubic b - residualCubic a
      = (b - a) * (a ^ 2 + a * b + b ^ 2 + 5 * a + 5 * b + 10) := by
    simp only [residualCubic]; ring
  have hp := mul_pos (sub_pos.mpr hab) hbr
  linarith [hid, hp]

/-- `g` is continuous (a polynomial), needed for the intermediate value argument. -/
theorem continuous_residualCubic : Continuous residualCubic := by
  unfold residualCubic; fun_prop

/-- **Sign-governed form of the strict inequality.** Dividing out the double factor
`a²`, the strict quintic Bernoulli inequality reduces to the sign of the residual
cubic: `1 + 5a < (1 + a)⁵ ↔ a ≠ 0 ∧ 0 < g(a)`. -/
theorem quintic_iff_residual_pos (a : ℝ) :
    1 + 5 * a < (1 + a) ^ 5 ↔ a ≠ 0 ∧ 0 < residualCubic a := by
  have hfac : (1 + a) ^ 5 - (1 + 5 * a) = a ^ 2 * residualCubic a := quintic_factor a
  constructor
  · intro h
    have hpos : 0 < a ^ 2 * residualCubic a := by linarith [hfac]
    refine ⟨?_, ?_⟩
    · rintro rfl; norm_num [residualCubic] at hpos
    · by_contra hg
      push_neg at hg
      nlinarith [hpos, mul_nonneg (sq_nonneg a) (neg_nonneg.mpr hg)]
  · rintro ⟨ha0, hg⟩
    have ha2 : 0 < a ^ 2 := by positivity
    have : 0 < a ^ 2 * residualCubic a := mul_pos ha2 hg
    linarith [hfac]

/-- **The quintic endpoint (headline).** There is a left endpoint `a₅* ∈ (−3, −2)`
such that the strict quintic Bernoulli inequality holds **iff** `a ≠ 0` and
`a₅* < a`:

  `1 + 5a < (1 + a)⁵ ↔ a ≠ 0 ∧ a₅* < a`.

This is the exact analogue of the parent's `cubic_iff` (`a₃* = −3`), now with an
irrational endpoint.  Because `−3 < a₅* < −2`, it realises the first step of the
predicted creep `a₃* = −3 < a₅* < −2` of the odd endpoints up toward the sharp
uniform bound `−2`. -/
theorem quintic_endpoint :
    ∃ a₅ : ℝ, (-3 < a₅ ∧ a₅ < -2) ∧
      ∀ a : ℝ, (1 + 5 * a < (1 + a) ^ 5 ↔ a ≠ 0 ∧ a₅ < a) := by
  -- Locate the unique root of `g` in `(−3, −2)` via the intermediate value theorem.
  have hg3 : residualCubic (-3) < 0 := by norm_num [residualCubic]
  have hg2 : 0 < residualCubic (-2) := by norm_num [residualCubic]
  have hmem : (0 : ℝ) ∈ Set.Ioo (residualCubic (-3)) (residualCubic (-2)) := ⟨hg3, hg2⟩
  obtain ⟨a₅, ha₅mem, ha₅⟩ :=
    intermediate_value_Ioo (by norm_num : (-3 : ℝ) ≤ -2)
      continuous_residualCubic.continuousOn hmem
  refine ⟨a₅, ⟨ha₅mem.1, ha₅mem.2⟩, ?_⟩
  intro a
  rw [quintic_iff_residual_pos a]
  -- `0 < g(a) ↔ a₅* < a` because `g` is strictly monotone and `g(a₅*) = 0`.
  have key : (0 < residualCubic a ↔ a₅ < a) := by
    rw [← ha₅]; exact residualCubic_strictMono.lt_iff_lt
  exact and_congr_right (fun _ => key)

/-- **Concrete witness below `−2`.** The `n = 5` strict inequality holds at
`a = −5/2 ∈ (a₅*, −2)`, since `g(−5/2) = 5/8 > 0`.  In particular `a₅* < −5/2`,
tightening the bracket on the endpoint. -/
theorem strict_at_neg_five_halves :
    1 + 5 * (-5 / 2 : ℝ) < (1 + (-5 / 2)) ^ 5 := by norm_num

/-- **The creep, made concrete (`n = 5` fails).** At `a = −29/10` the residual cubic
is negative (`g(−29/10) < 0`), so the `n = 5` strict inequality **fails**:
`a₅* > −29/10`. -/
theorem quintic_fails_at_neg_29 :
    ¬ (1 + 5 * (-29 / 10 : ℝ) < (1 + (-29 / 10)) ^ 5) := by norm_num

/-- **The creep, made concrete (`n = 3` still holds).** At the very same point
`a = −29/10` the *cubic* inequality holds, because `−29/10 > a₃* = −3`.  Contrasting
with `quintic_fails_at_neg_29`, this exhibits a point where `n = 3` succeeds yet
`n = 5` fails — the endpoint has strictly moved up from `−3`, the creep in action. -/
theorem cubic_holds_at_neg_29 :
    1 + 3 * (-29 / 10 : ℝ) < (1 + (-29 / 10)) ^ 3 := by norm_num

/-- **Why every odd endpoint sits below `−2`.** For *every* odd `n ≥ 2` the strict
Bernoulli inequality already holds at `a = −2`: there `(1 + a)ⁿ = (−1)ⁿ = −1`, which
beats the line value `1 + n·(−2) = 1 − 2n ≤ −3`.  Hence `−2` is interior to the
strict domain for each odd `n`, forcing `aₙ* < −2` universally; the endpoints
approach the sharp uniform bound `−2` from below, never reaching it. -/
theorem strict_at_neg_two_odd {n : ℕ} (hn : Odd n) (hn2 : 2 ≤ n) :
    1 + (n : ℝ) * (-2) < (1 + (-2 : ℝ)) ^ n := by
  have hpow : (1 + (-2 : ℝ)) ^ n = -1 := by
    rw [show (1 + (-2 : ℝ)) = -1 by norm_num, hn.neg_one_pow]
  rw [hpow]
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  nlinarith [hnr]

end BernoulliInequalityOQ01OQ01OQ01OQ01
