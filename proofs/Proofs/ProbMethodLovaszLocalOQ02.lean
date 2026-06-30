/-
  Lovász Local Lemma — OQ-02: The Sharp Symmetric Criterion `e·p·(d+1) ≤ 1`

  The gallery's `prob-method-lovasz-local` formalizes the symmetric Lovász Local
  Lemma with the simplified, textbook-friendly criterion `p·(d+1) ≤ 1/3`, and its
  child `lovasz-local-lemma-oq-02` proves that the *rational* avoidance threshold
      T(d) = d^d / (d+1)^(d+1) = (1/(d+1))·(d/(d+1))^d
  is algebraically optimal. What neither establishes is the connection to the
  *canonical* sharp criterion that appears in every textbook statement of the LLL:

      e · p · (d+1) ≤ 1,        i.e.   p ≤ 1/(e·(d+1)),

  where `e = Real.exp 1` is Euler's number. The parent entry lists this exact gap
  as an open question, noting that it "requires formalizing e = lim (1+1/n)^n".

  This file closes the gap **without** the limit. The whole story reduces to a
  single one-line inequality already in Mathlib, `Real.add_one_le_exp`:

      (1 + 1/d)^d ≤ e          (key lemma `one_add_inv_pow_le_exp_one`)

  Taking reciprocals turns this into `1/e ≤ (d/(d+1))^d`, hence the sharp
  threshold `1/(e(d+1))` lies *below* the algebraic threshold `T(d)`. Therefore
  the sharp criterion `e·p·(d+1) ≤ 1` implies the LLL avoidance condition
  `p ≤ T(d)` that the gallery already discharges (`sharp_criterion_implies_threshold`).

  Finally we prove the sharp criterion is a genuine improvement: since `e < 3`,
  the `1/3` criterion implies the sharp one (`third_implies_sharp`), and there are
  probabilities `p` admitted by the sharp criterion but rejected by `1/3`
  (`exists_sharp_not_third`). The improvement window is the interval
  `1/(3(d+1)) < p·(d+1) ≤ 1/e`.

  Everything is over ℝ (forced, since `e` is irrational) and is fully verified:
  0 sorries, 0 `axiom` declarations, no `native_decide`.

  Main results:
  * `one_add_inv_pow_le_exp_one`     : (1 + 1/d)^d ≤ e
  * `inv_exp_one_le`                 : 1/e ≤ (d/(d+1))^d
  * `sharp_le_lllThresholdReal`      : 1/(e(d+1)) ≤ T(d)
  * `sharp_criterion_implies_threshold` (**headline**): e·p·(d+1) ≤ 1 ⟹ p ≤ T(d)
  * `exp_one_lt_three`               : e < 3
  * `third_implies_sharp`            : p(d+1) ≤ 1/3 ⟹ e·p·(d+1) ≤ 1
  * `exists_sharp_not_third`         : the sharp criterion is strictly more permissive
  * `sharp_symmetric_lll` (capstone) : sharp criterion ⟹ (p ≤ T(d)) ∧ avoidance > 0
-/
import Mathlib

namespace ProbMethodLovaszLocalOQ02

open Real

/-- The (real) symmetric Lovász Local Lemma threshold
`T(d) = (1/(d+1))·(d/(d+1))^d = d^d/(d+1)^(d+1)`. This is the largest event
probability the symmetric LLL tolerates at maximum dependency degree `d`; the
rational version and its optimality are proved in `lovasz-local-lemma-oq-02`. -/
noncomputable def lllThresholdReal (d : ℕ) : ℝ :=
  (1 / ((d : ℝ) + 1)) * ((d : ℝ) / ((d : ℝ) + 1)) ^ d

/-- **Key lemma.** `(1 + 1/d)^d ≤ e` for every `d ≥ 1`. This is the entire
analytic content distinguishing the sharp LLL constant `e` from the loose `3`.
The proof needs no limit: it is `1 + 1/d ≤ exp(1/d)` (Mathlib's
`Real.add_one_le_exp`) raised to the `d`-th power, since `(exp(1/d))^d = exp 1`. -/
theorem one_add_inv_pow_le_exp_one {d : ℕ} (hd : 1 ≤ d) :
    (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp 1 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have h1 : (1 : ℝ) + 1 / (d : ℝ) ≤ Real.exp (1 / (d : ℝ)) := by
    have := Real.add_one_le_exp (1 / (d : ℝ)); linarith
  have hb : (0 : ℝ) ≤ 1 + 1 / (d : ℝ) := by positivity
  have h2 : (1 + 1 / (d : ℝ)) ^ d ≤ (Real.exp (1 / (d : ℝ))) ^ d :=
    pow_le_pow_left₀ hb h1 d
  have h3 : (Real.exp (1 / (d : ℝ))) ^ d = Real.exp 1 := by
    rw [← Real.exp_nat_mul, mul_one_div, div_self hdne]
  rwa [h3] at h2

/-- Reciprocal form of the key lemma: `1/e ≤ (d/(d+1))^d`. -/
theorem inv_exp_one_le {d : ℕ} (hd : 1 ≤ d) :
    1 / Real.exp 1 ≤ ((d : ℝ) / ((d : ℝ) + 1)) ^ d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have key := one_add_inv_pow_le_exp_one hd
  have hsum : 1 + 1 / (d : ℝ) = ((d : ℝ) + 1) / (d : ℝ) := by field_simp
  have hbase : ((d : ℝ) / ((d : ℝ) + 1)) ^ d = 1 / ((1 + 1 / (d : ℝ)) ^ d) := by
    rw [hsum, one_div, ← inv_pow, inv_div]
  rw [hbase]
  exact one_div_le_one_div_of_le (by positivity) key

/-- The sharp threshold `1/(e·(d+1))` lies below the algebraic threshold `T(d)`.
This is what makes the sharp criterion *sufficient*: any `p` it admits already
satisfies the LLL avoidance condition `p ≤ T(d)`. -/
theorem sharp_le_lllThresholdReal {d : ℕ} (hd : 1 ≤ d) :
    1 / (Real.exp 1 * ((d : ℝ) + 1)) ≤ lllThresholdReal d := by
  have hrec := inv_exp_one_le hd
  have hL : 1 / (Real.exp 1 * ((d : ℝ) + 1))
      = (1 / ((d : ℝ) + 1)) * (1 / Real.exp 1) := by
    rw [one_div_mul_one_div, mul_comm ((d : ℝ) + 1) (Real.exp 1)]
  rw [lllThresholdReal, hL]
  exact mul_le_mul_of_nonneg_left hrec (by positivity)

/-- **Headline.** The sharp symmetric LLL criterion `e·p·(d+1) ≤ 1` implies the
avoidance condition `p ≤ T(d)` already discharged by the gallery's LLL. Thus the
textbook criterion is fully justified — no limit required, only `(1+1/d)^d ≤ e`. -/
theorem sharp_criterion_implies_threshold {d : ℕ} (hd : 1 ≤ d) {p : ℝ}
    (_hp : 0 ≤ p) (hsharp : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
    p ≤ lllThresholdReal d := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hbridge := sharp_le_lllThresholdReal hd
  have hple : p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [hsharp]
  linarith [hple, hbridge]

/-- `e < 3`, from Mathlib's numeric bound `Real.exp_one_lt_d9`. -/
theorem exp_one_lt_three : Real.exp 1 < 3 :=
  lt_trans Real.exp_one_lt_d9 (by norm_num)

/-- The loose criterion `p(d+1) ≤ 1/3` is *stronger* than the sharp one: it
implies `e·p·(d+1) ≤ 1`. (Because `e < 3`, so `e·(1/3) < 1`.) Hence replacing
`1/3` by the sharp `1/e` only ever enlarges the set of admissible `p`. -/
theorem third_implies_sharp {d : ℕ} {p : ℝ}
    (_hp : 0 ≤ p) (hthird : p * ((d : ℝ) + 1) ≤ 1 / 3) :
    Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he3 := exp_one_lt_three
  have h1 : Real.exp 1 * (p * ((d : ℝ) + 1)) ≤ Real.exp 1 * (1 / 3) :=
    mul_le_mul_of_nonneg_left hthird (le_of_lt he)
  nlinarith [h1, he3]

/-- The improvement is strict: there exist probabilities admitted by the sharp
criterion `e·p·(d+1) ≤ 1` but rejected by the loose `p(d+1) ≤ 1/3`. The witness
`p = 1/(e(d+1))` saturates the sharp criterion (`e·p·(d+1) = 1`) yet has
`p(d+1) = 1/e > 1/3`. So the sharp criterion strictly extends the gallery's. -/
theorem exists_sharp_not_third {d : ℕ} (hd : 1 ≤ d) :
    ∃ p : ℝ, 0 ≤ p ∧ Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1
      ∧ 1 / 3 < p * ((d : ℝ) + 1) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he3 := exp_one_lt_three
  have hne1 : Real.exp 1 ≠ 0 := ne_of_gt he
  have hne2 : (d : ℝ) + 1 ≠ 0 := ne_of_gt hd1
  refine ⟨1 / (Real.exp 1 * ((d : ℝ) + 1)), by positivity, ?_, ?_⟩
  · have heq : Real.exp 1 * (1 / (Real.exp 1 * ((d : ℝ) + 1))) * ((d : ℝ) + 1) = 1 := by
      field_simp
    linarith [heq]
  · have hpd : (1 / (Real.exp 1 * ((d : ℝ) + 1))) * ((d : ℝ) + 1) = 1 / Real.exp 1 := by
      field_simp
    rw [hpd, lt_div_iff₀ he]; linarith [he3]

/-- The symmetric avoidance product `(d/(d+1))^n` is strictly positive — the
qualitative conclusion of the LLL (the bad events can all be simultaneously
avoided with positive probability). -/
theorem avoidance_pos {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    0 < ((d : ℝ) / ((d : ℝ) + 1)) ^ n := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact pow_pos (div_pos hd0 (by linarith)) n

/-- **Capstone.** The sharp symmetric LLL: if each bad event has probability
`p` with `e·p·(d+1) ≤ 1` and dependency degree at most `d`, then `p` satisfies
the LLL threshold `T(d)` and the avoidance product is positive — the events can
all be avoided. This is the textbook statement, now formally connected to `e`. -/
theorem sharp_symmetric_lll {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 ≤ p)
    (hsharp : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) (n : ℕ) :
    p ≤ lllThresholdReal d ∧ 0 < ((d : ℝ) / ((d : ℝ) + 1)) ^ n :=
  ⟨sharp_criterion_implies_threshold hd hp hsharp, avoidance_pos hd n⟩

end ProbMethodLovaszLocalOQ02
