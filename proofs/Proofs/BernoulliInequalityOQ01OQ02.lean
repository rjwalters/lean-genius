import Mathlib
import Proofs.BernoulliInequalityOQ01OQ01

/-
# Second-order Bernoulli and its equality characterization

**Open question (bernoulli-inequality-oq-01-oq-02).** Characterize equality in
Bernoulli's inequality `(1 + a)ⁿ ≥ 1 + n·a`.

The *first-order* equality characterization is already settled by the parent and
sibling entries: `BernoulliInequalityOQ01.one_add_mul_eq_pow_iff` gives it for
`-1 < a`, and `BernoulliInequalityOQ01OQ01.one_add_mul_eq_pow_full_iff`
sharpens it to Mathlib's full weak domain `-2 ≤ a`: equality `1 + n·a = (1+a)ⁿ`
holds iff `a = 0 ∨ n ≤ 1`.  We record that result as a one-line corollary
(`one_add_mul_eq_pow_iff_ge`) for the slug's literal `a ≥ -1` target.

The new content of this entry is the **second-order** refinement.  For `a ≥ 0`,
truncating the binomial expansion after the quadratic term gives the sharper
lower bound

  `(1 + a)ⁿ  ≥  1 + n·a + C(n,2)·a²`,   where `C(n,2) = n(n-1)/2`,

and this inequality has its *own* sharp equality characterization, one step
shifted from the first-order case:

* `sq_bernoulli`        : `0 ≤ a → 1 + n·a + (n(n-1)/2)·a² ≤ (1+a)ⁿ`.
* `sq_bernoulli_strict` : `0 < a → 3 ≤ n → 1 + n·a + (n(n-1)/2)·a² < (1+a)ⁿ`.
* `sq_bernoulli_eq_iff` : for `0 ≤ a`, equality holds **iff** `a = 0 ∨ n ≤ 2`.

The threshold moves from `n ≤ 1` (first order) to `n ≤ 2` (second order): the
quadratic truncation is *exact* through `n = 2` — indeed `(1+a)² = 1 + 2a + a²`
is the full expansion — and becomes strict precisely once the cubic term `a³`
can appear, i.e. for `n ≥ 3` and `a > 0`.

**Mechanism.** The inequality is a one-line induction: multiplying the inductive
bound by `1 + a ≥ 0` and using `C(n,2) + n = C(n+1,2)` (Pascal) reproduces the
next bound up to the discarded nonnegative tail `C(n,2)·a³ ≥ 0`.  Strictness for
`n ≥ 3` comes from that tail being *strictly* positive once `n ≥ 3` and `a > 0`.

**Relation to Mathlib.** Mathlib has the first-order weak form
`one_add_mul_le_pow` (domain `-2 ≤ a`) and `rpow` Bernoulli forms, but no
second-order integer-power Bernoulli with an equality characterization.  The
restriction to `a ≥ 0` is sharp: for `-1 < a < 0` the quadratic truncation
*overshoots* (e.g. `n = 3, a = -1/2`: the bound `1/4` exceeds `(1/2)³ = 1/8`),
so the second-order inequality genuinely requires nonnegativity, unlike the
first-order inequality which holds down to `a = -2`.
-/

namespace BernoulliInequalityOQ01OQ02

variable {a : ℝ}

/-- **Second-order Bernoulli inequality.** For `a ≥ 0` and every `n`, the binomial
power dominates its quadratic Taylor truncation:
`1 + n·a + (n(n-1)/2)·a² ≤ (1 + a)ⁿ`.

This sharpens the first-order Bernoulli bound `1 + n·a ≤ (1+a)ⁿ` by the next
binomial term `C(n,2)·a² = (n(n-1)/2)·a²`. -/
theorem sq_bernoulli (ha : 0 ≤ a) (n : ℕ) :
    1 + n * a + ((n : ℝ) * ((n : ℝ) - 1) / 2) * a ^ 2 ≤ (1 + a) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h1a : (0 : ℝ) ≤ 1 + a := by linarith
      -- `m·(m-1) ≥ 0` for a natural `m` (so the discarded cubic tail is `≥ 0`).
      have hm2 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp
        · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
          nlinarith
      have ha3 : 0 ≤ a ^ 3 := by positivity
      -- Multiply the inductive bound by the nonnegative factor `1 + a`.
      have hstep := mul_le_mul_of_nonneg_right ih h1a
      rw [pow_succ]
      push_cast
      nlinarith [hstep, mul_nonneg hm2 ha3]

/-- **Strict second-order Bernoulli.** For `a > 0` and `n ≥ 3`, the quadratic
truncation is a *strict* lower bound: `1 + n·a + (n(n-1)/2)·a² < (1 + a)ⁿ`.

The discarded cubic tail `C(n,2)·a³` is strictly positive once `n ≥ 3`. -/
theorem sq_bernoulli_strict (ha : 0 < a) :
    ∀ {n : ℕ}, 3 ≤ n → 1 + n * a + ((n : ℝ) * ((n : ℝ) - 1) / 2) * a ^ 2 < (1 + a) ^ n := by
  have ha' : 0 ≤ a := le_of_lt ha
  have h1a : (0 : ℝ) < 1 + a := by linarith
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hexp : (1 + a) ^ 3 = 1 + 3 * a + 3 * a ^ 2 + a ^ 3 := by ring
      have ha3 : (0 : ℝ) < a ^ 3 := by positivity
      push_cast
      nlinarith [hexp, ha3]
  | succ m hm ih =>
      have hm2 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        nlinarith
      have ha3 : 0 ≤ a ^ 3 := by positivity
      have hstep := mul_lt_mul_of_pos_right ih h1a
      rw [pow_succ]
      push_cast
      nlinarith [hstep, mul_nonneg hm2 ha3]

/-- **Equality characterization for second-order Bernoulli.** For `a ≥ 0`,
equality `1 + n·a + (n(n-1)/2)·a² = (1 + a)ⁿ` holds **iff** `a = 0 ∨ n ≤ 2`.

The threshold `n ≤ 2` (versus `n ≤ 1` for the first-order inequality) reflects
that the quadratic truncation is exact through degree two. -/
theorem sq_bernoulli_eq_iff (ha : 0 ≤ a) {n : ℕ} :
    1 + n * a + ((n : ℝ) * ((n : ℝ) - 1) / 2) * a ^ 2 = (1 + a) ^ n ↔ a = 0 ∨ n ≤ 2 := by
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hn⟩ := hcon
    have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hlt := sq_bernoulli_strict hpos (by omega : 3 ≤ n)
    linarith
  · rintro (rfl | hn)
    · simp
    · interval_cases n <;> push_cast <;> ring

/-- **Sharp strictness for second-order Bernoulli.** For `a ≥ 0`, the quadratic
truncation is a strict lower bound exactly when `a ≠ 0` and `n ≥ 3`. -/
theorem sq_bernoulli_strict_iff (ha : 0 ≤ a) {n : ℕ} :
    1 + n * a + ((n : ℝ) * ((n : ℝ) - 1) / 2) * a ^ 2 < (1 + a) ^ n ↔ a ≠ 0 ∧ 3 ≤ n := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; simp at h
    · by_contra hn
      push_neg at hn
      interval_cases n <;> push_cast at h <;> nlinarith [h]
  · rintro ⟨ha0, hn⟩
    exact sq_bernoulli_strict (lt_of_le_of_ne ha (Ne.symm ha0)) hn

/-- The second-order lower bound expressed with the binomial coefficient
`C(n,2) = n.choose 2` it represents. -/
theorem sq_bernoulli_choose (ha : 0 ≤ a) (n : ℕ) :
    1 + n * a + (n.choose 2 : ℝ) * a ^ 2 ≤ (1 + a) ^ n := by
  have hcast : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [Nat.choose_two_right]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : 1 ≤ n := h
      push_cast [Nat.cast_sub this]
      ring
  rw [hcast]; exact sq_bernoulli ha n

/-- **First-order equality characterization on `a ≥ -1`** (the slug's literal
target), a one-line corollary of the sibling's full-domain version. -/
theorem one_add_mul_eq_pow_iff_ge (ha : -1 ≤ a) {n : ℕ} :
    1 + n * a = (1 + a) ^ n ↔ a = 0 ∨ n ≤ 1 :=
  BernoulliInequalityOQ01OQ01.one_add_mul_eq_pow_full_iff (by linarith)

/-- The exactness at `n = 2`: the quadratic truncation is the *full* expansion,
so equality holds for every `a`. -/
example : ∀ a : ℝ, 1 + 2 * a + ((2 : ℝ) * ((2 : ℝ) - 1) / 2) * a ^ 2 = (1 + a) ^ 2 := by
  intro a; ring

/-- Concrete strict instance: `a = 1, n = 4`. `1 + 4 + 6 = 11 < 16 = 2⁴`. -/
example : (1 : ℝ) + 4 * 1 + ((4 : ℝ) * ((4 : ℝ) - 1) / 2) * 1 ^ 2 < (1 + 1) ^ 4 := by
  norm_num

/-- Sharpness of `a ≥ 0`: for `-1 < a < 0` the quadratic truncation *overshoots*.
At `a = -1/2, n = 3` the bound `1/4` exceeds `(1/2)³ = 1/8`, so the second-order
inequality genuinely fails outside `a ≥ 0`. -/
example : ¬ (1 : ℝ) + 3 * (-1 / 2) + ((3 : ℝ) * ((3 : ℝ) - 1) / 2) * (-1 / 2) ^ 2
    ≤ (1 + (-1 / 2)) ^ 3 := by norm_num

end BernoulliInequalityOQ01OQ02
