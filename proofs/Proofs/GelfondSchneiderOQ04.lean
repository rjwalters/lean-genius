import Mathlib

/-
# Gelfond–Schneider — OQ-04: The Logarithm Dichotomy and the Transcendence of log₂ 3

## Research Problem: gelfond-schneider-oq-04

The gallery parent (`gelfond-schneider`) records the Gelfond–Schneider theorem (Hilbert's 7th
problem) as a stated assumption and derives the classic transcendental *constants* `2^√2`,
`e^π`, `√2^√2`, `2^∛2`, together with the fact that `log a` is transcendental for algebraic
`a ∉ {0, 1}`.

This file proves the other principal number-theoretic consequence of Gelfond–Schneider — the
one about *logarithms of one algebraic number to another algebraic base* — which the parent
does not contain.

## Main result — the logarithm dichotomy

For positive algebraic reals `a, b` with `a ≠ 1`, the base-`a` logarithm of `b`,

      log_a b  =  log b / log a,

is **either rational or transcendental — never an irrational algebraic number.**

Proof.  Suppose `β := log b / log a` were algebraic *and* irrational.  Since `a > 0`,

      a ^ β  =  exp(β · log a)  =  exp(log b)  =  b      (using log a ≠ 0 and b > 0),

so `a ^ β = b`.  But Gelfond–Schneider says `a ^ β` is transcendental (algebraic base
`a ≠ 0, 1`, irrational algebraic exponent `β`), contradicting that `b` is algebraic.  Hence
`β` cannot be both algebraic and irrational: it is rational or transcendental.  ∎

## A concrete instance — log₂ 3 is transcendental

The dichotomy upgrades *irrationality* of a logarithm to *transcendence* for free.  We supply
the irrationality input in the cleanest classical case:

* `irrational_log_three_div_log_two` — `log 3 / log 2 ∉ ℚ`.  A rational value `p/d` would give
  `2^p = 3^d` for positive integers `p, d` (exponentiate `p · log 2 = d · log 3`), impossible
  by parity: the left side is even and the right side is odd.
* `transcendental_log_three_div_log_two` — feeding this into the dichotomy at the algebraic
  bases `2, 3`, the non-rational ratio `log₂ 3` must be transcendental.

## Assumption

`gelfond_schneider_real` is re-declared here as an `axiom`, exactly as in the parent entry — the
full Gelfond–Schneider proof (Siegel's lemma, auxiliary functions, zero estimates) is not
formalized.  Every theorem below is otherwise fully machine-checked; `#print axioms` shows the
only non-foundational dependency is this single Gelfond–Schneider assumption.

Tags: transcendental-number-theory, gelfond-schneider, hilbert-7, logarithm, irrationality
-/

namespace GelfondSchneiderOQ04

open Real

/-- **Gelfond–Schneider theorem** (real form, Hilbert's 7th problem), stated as an assumption
    exactly as in the gallery parent `gelfond-schneider`.  If `a` is a positive algebraic real
    with `a ≠ 1`, and `b` is an irrational algebraic real, then `a ^ b` is transcendental
    (not algebraic over `ℚ`). -/
axiom gelfond_schneider_real (a b : ℝ) (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
    (ha_alg : IsAlgebraic ℚ a) (hb_alg : IsAlgebraic ℚ b) (hb_irr : Irrational b) :
    ¬ IsAlgebraic ℚ (a ^ b)

/-- `log a ≠ 0` for a positive `a ≠ 1`. -/
private lemma log_ne_zero_of_pos_ne_one {a : ℝ} (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) :
    Real.log a ≠ 0 := by
  rw [ne_eq, Real.log_eq_zero]
  push_neg
  exact ⟨ne_of_gt ha_pos, ha_ne_one, by linarith⟩

/-- `a ^ (log b / log a) = b` for positive `a ≠ 1` and positive `b` — the identity that turns a
    logarithm into an exponent for the dichotomy. -/
private lemma rpow_logb_eq {a b : ℝ} (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) (hb_pos : 0 < b) :
    a ^ (Real.log b / Real.log a) = b := by
  have hla : Real.log a ≠ 0 := log_ne_zero_of_pos_ne_one ha_pos ha_ne_one
  rw [Real.rpow_def_of_pos ha_pos]
  have : Real.log a * (Real.log b / Real.log a) = Real.log b := by field_simp
  rw [this, Real.exp_log hb_pos]

/-- **The Gelfond–Schneider logarithm dichotomy.**

    For positive algebraic reals `a, b` with `a ≠ 1`, the ratio `log b / log a` (the base-`a`
    logarithm of `b`) is *either rational or transcendental* — it is never an irrational
    algebraic number.

    If it were algebraic and irrational, then `a ^ (log b / log a) = b` would be transcendental
    by Gelfond–Schneider, contradicting that `b` is algebraic. -/
theorem gelfond_schneider_logb_dichotomy
    (a b : ℝ) (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) (hb_pos : 0 < b)
    (ha_alg : IsAlgebraic ℚ a) (hb_alg : IsAlgebraic ℚ b) :
    (∃ q : ℚ, (q : ℝ) = Real.log b / Real.log a) ∨
      ¬ IsAlgebraic ℚ (Real.log b / Real.log a) := by
  by_cases hrat : ∃ q : ℚ, (q : ℝ) = Real.log b / Real.log a
  · exact Or.inl hrat
  · right
    intro hβ_alg
    have hβ_irr : Irrational (Real.log b / Real.log a) := hrat
    have hab : a ^ (Real.log b / Real.log a) = b := rpow_logb_eq ha_pos ha_ne_one hb_pos
    have htr := gelfond_schneider_real a (Real.log b / Real.log a) ha_pos ha_ne_one ha_alg
      hβ_alg hβ_irr
    rw [hab] at htr
    exact htr hb_alg

/-- **`log 3 / log 2` is irrational.**  A rational value would force `2^p = 3^d` for positive
    integers `p, d`, impossible by parity (an even number equal to an odd number). -/
theorem irrational_log_three_div_log_two : Irrational (Real.log 3 / Real.log 2) := by
  rw [Irrational]
  rintro ⟨q, hq⟩
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : (0 : ℝ) < (q : ℝ) := by rw [hq]; positivity
  have hqnum_pos : 0 < q.num := by
    rwa [Rat.num_pos, ← Rat.cast_pos (K := ℝ)]
  have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  -- cross-multiplied real relation:  q.num · log 2 = q.den · log 3
  have hcross : (q.num : ℝ) * Real.log 2 = (q.den : ℝ) * Real.log 3 := by
    have hqeq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
    rw [hqeq] at hq
    field_simp at hq
    nlinarith [hq, hl2, hl3]
  -- pass to natural-number exponents
  set N : ℕ := q.num.toNat with hN
  have hNcast : (N : ℝ) = (q.num : ℝ) := by
    rw [hN]; exact_mod_cast Int.toNat_of_nonneg (le_of_lt hqnum_pos)
  have hNpos : 0 < N := by rw [hN]; omega
  have hlog : Real.log ((2 : ℝ) ^ N) = Real.log ((3 : ℝ) ^ q.den) := by
    rw [Real.log_pow, Real.log_pow]
    rw [hNcast]
    linarith [hcross]
  have hpow : (2 : ℝ) ^ N = (3 : ℝ) ^ q.den := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h3 : (0 : ℝ) < (3 : ℝ) ^ q.den := by positivity
    have := congrArg Real.exp hlog
    rwa [Real.exp_log h2, Real.exp_log h3] at this
  have hnat : (2 : ℕ) ^ N = (3 : ℕ) ^ q.den := by
    have : ((2 ^ N : ℕ) : ℝ) = ((3 ^ q.den : ℕ) : ℝ) := by push_cast; exact hpow
    exact_mod_cast this
  -- parity contradiction:  2 ∣ 2^N = 3^d  ⟹  2 ∣ 3
  have hdvd : (2 : ℕ) ∣ 3 ^ q.den := by
    rw [← hnat]; exact dvd_pow_self 2 hNpos.ne'
  have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  norm_num at this

/-- **`log₂ 3` is transcendental.**  Combining the irrationality of `log 3 / log 2` with the
    Gelfond–Schneider logarithm dichotomy (applied to the algebraic bases `2, 3`): since the
    ratio is not rational, it must be transcendental. -/
theorem transcendental_log_three_div_log_two :
    ¬ IsAlgebraic ℚ (Real.log 3 / Real.log 2) := by
  have halg2 : IsAlgebraic ℚ (2 : ℝ) := by
    have := isAlgebraic_int (R := ℚ) (A := ℝ) 2; simpa using this
  have halg3 : IsAlgebraic ℚ (3 : ℝ) := by
    have := isAlgebraic_int (R := ℚ) (A := ℝ) 3; simpa using this
  rcases gelfond_schneider_logb_dichotomy 2 3 (by norm_num) (by norm_num) (by norm_num)
      halg2 halg3 with hrat | htr
  · exfalso
    obtain ⟨q, hq⟩ := hrat
    exact irrational_log_three_div_log_two ⟨q, hq⟩
  · exact htr

#check @gelfond_schneider_logb_dichotomy
#check @irrational_log_three_div_log_two
#check @transcendental_log_three_div_log_two

/-
## Summary

Proved (0 sorries; the single non-foundational assumption is the Gelfond–Schneider theorem
`gelfond_schneider_real`, re-declared as an axiom exactly as in the parent entry; imports only
Mathlib):

* `gelfond_schneider_logb_dichotomy` — for positive algebraic `a, b` with `a ≠ 1`, the ratio
  `log b / log a` is rational or transcendental, never an irrational algebraic number.
* `irrational_log_three_div_log_two` — `log 3 / log 2 ∉ ℚ` (parity of `2^p = 3^d`).
* `transcendental_log_three_div_log_two` — hence `log₂ 3` is transcendental.

The dichotomy is the structural heart: Gelfond–Schneider, usually invoked to produce
transcendental *constants*, here forbids an *irrational algebraic logarithm*, converting any
irrationality fact about `log_a b` (for algebraic `a, b`) into transcendence.  `log₂ 3` is the
cleanest concrete witness.
-/

end GelfondSchneiderOQ04

#print axioms GelfondSchneiderOQ04.gelfond_schneider_logb_dichotomy
#print axioms GelfondSchneiderOQ04.transcendental_log_three_div_log_two
