import Mathlib

/-
# Boole Summation over a Normed Vector Space

## What This Proves

The parent `alternating-series-boole-summation` establishes the finite **Boole summation
identity** and its total-variation remainder bound for *real* sequences. This child ports
both to sequences valued in an arbitrary normed real vector space `E` (so `E = ℂ`, an
operator algebra, or any Banach space).

Writing the alternating partial sum and the forward difference as

  `altSum a n m = ∑_{j ∈ [n, m)} (-1)^j • a j`,   `fdiff a j = a (j+1) - a j`,

the **first-order Boole identity** is

  `altSum a n m = ½ • ((-1)^n • a n - (-1)^m • a m) - ½ • altSum (fdiff a) n m`,

and the associated **remainder bound** is

  `‖altSum a n m - ½ • ((-1)^n • a n - (-1)^m • a m)‖ ≤ ½ · ∑_{j ∈ [n, m)} ‖fdiff a j‖`.

## Honest Scope

The algebraic identity and the norm bound are domain-agnostic: they need only that `E` is a
normed ℝ-module, and they are proved here in that generality. What does **not** port is the
antitone/telescoping *monotonicity* refinement of the real parent — it uses the order on ℝ,
which a general normed space lacks. This entry therefore delivers exactly the order-free core.

## Method

The identity is a one-step induction (`Nat.le_induction`) peeling the top index with
`Finset.sum_Ico_succ_top`; the algebraic step closes with the `module` tactic after
`pow_succ`. The remainder bound rewrites the difference via the identity (`abel`) and then
applies `norm_smul` and `norm_sum_le`, using `‖(-1)^j‖ = 1`.

0 sorries, 0 axioms (only `propext` / `Classical.choice` / `Quot.sound`).
-/

namespace AlternatingSeriesBooleSummationOQ02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The alternating partial sum `∑_{j ∈ [n, m)} (-1)^j • a j` of an `E`-valued sequence. -/
def altSum (a : ℕ → E) (n m : ℕ) : E := ∑ j ∈ Finset.Ico n m, (-1 : ℝ) ^ j • a j

/-- The forward difference `a (j+1) - a j`. -/
def fdiff (a : ℕ → E) (j : ℕ) : E := a (j + 1) - a j

@[simp] theorem altSum_self (a : ℕ → E) (n : ℕ) : altSum a n n = 0 := by
  simp [altSum]

/-- Peeling the top index of an `altSum`. -/
theorem altSum_succ_top (a : ℕ → E) {n m : ℕ} (h : n ≤ m) :
    altSum a n (m + 1) = altSum a n m + (-1 : ℝ) ^ m • a m := by
  simp only [altSum]; rw [Finset.sum_Ico_succ_top h]

/-- **First-order Boole summation identity over a normed ℝ-vector space.**
`altSum a n m = ½·((-1)^n•a n - (-1)^m•a m) - ½·altSum(Δa) n m`, valid for any `n ≤ m`
and any sequence into a normed real vector space. -/
theorem boole_first_normed (a : ℕ → E) {n m : ℕ} (h : n ≤ m) :
    altSum a n m
      = (1 / 2 : ℝ) • ((-1 : ℝ) ^ n • a n - (-1 : ℝ) ^ m • a m)
        - (1 / 2 : ℝ) • altSum (fdiff a) n m := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      rw [altSum_succ_top a hm, altSum_succ_top (fdiff a) hm, ih, fdiff, pow_succ]
      module

/-- **Boole remainder bound over a normed ℝ-vector space.**
The alternating sum differs from its two-point model `½·((-1)^n•a n - (-1)^m•a m)` by at
most half the total variation `∑ ‖Δa j‖`. This is the order-free norm form of the parent's
total-variation bound. -/
theorem altSum_sub_model_norm_le (a : ℕ → E) {n m : ℕ} (h : n ≤ m) :
    ‖altSum a n m - (1 / 2 : ℝ) • ((-1 : ℝ) ^ n • a n - (-1 : ℝ) ^ m • a m)‖
      ≤ (1 / 2 : ℝ) * ∑ j ∈ Finset.Ico n m, ‖fdiff a j‖ := by
  have key := boole_first_normed a h
  have hrw : altSum a n m - (1 / 2 : ℝ) • ((-1 : ℝ) ^ n • a n - (-1 : ℝ) ^ m • a m)
      = -((1 / 2 : ℝ) • altSum (fdiff a) n m) := by rw [key]; abel
  have hhalf : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by rw [Real.norm_eq_abs]; norm_num
  rw [hrw, norm_neg, norm_smul, hhalf]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc ‖altSum (fdiff a) n m‖
      = ‖∑ j ∈ Finset.Ico n m, (-1 : ℝ) ^ j • fdiff a j‖ := by rw [altSum]
    _ ≤ ∑ j ∈ Finset.Ico n m, ‖(-1 : ℝ) ^ j • fdiff a j‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.Ico n m, ‖fdiff a j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [norm_smul]

/-- Instantiation at `E = ℂ`: the identity and remainder bound cover complex-valued
alternating sums (Fourier / Dirichlet partial sums) with no extra work. -/
example (a : ℕ → ℂ) {n m : ℕ} (h : n ≤ m) :
    ‖altSum a n m - (1 / 2 : ℝ) • ((-1 : ℝ) ^ n • a n - (-1 : ℝ) ^ m • a m)‖
      ≤ (1 / 2 : ℝ) * ∑ j ∈ Finset.Ico n m, ‖fdiff a j‖ :=
  altSum_sub_model_norm_le a h

end AlternatingSeriesBooleSummationOQ02
