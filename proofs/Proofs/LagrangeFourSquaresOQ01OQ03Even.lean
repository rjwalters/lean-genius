import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-
# Jacobi four-square RHS: the even-case closed form  (OQ-01 → OQ-03, continued)

`LagrangeFourSquaresOQ01OQ03.lean` defines the right-hand side of Jacobi's
four-square formula, `jacobiCount n = 8·Σ_{d|n, 4∤d} d`, and proves the **odd**
collapse `jacobiCount n = 8·σ(n)` (the `4∤d` filter is vacuous for odd `n`).

This file completes the elementary **closed-form characterization of the Jacobi
RHS** for *all* `n`, 0-axiom, without depending on the `native_decide` oracle of
the base file (so it is genuinely axiom-free) and without touching the
Mathlib-blocked general `r4 = jacobiCount` equality. `jacobiCount` is restated here
verbatim (a two-line divisor-sum definition) to keep this file self-contained.

1. `jacobiCount_of_not_four_dvd` — the `4∤d` filter is vacuous **whenever `4 ∤ n`**
   (covering `n` odd and `n ≡ 2 (mod 4)`), so `jacobiCount n = 8·σ(n)`.
2. `sum_four_dvd_divisors` — the genuinely new "even" content: for `4 ∣ n`,
   `Σ_{d | n, 4 | d} d = 4·σ(n/4)` (via the divisor bijection `e ↦ 4e`).
3. `jacobiCount_four_dvd_add` — from the divisor partition by `4 | d`: for `4 ∣ n`,
   `jacobiCount n + 32·σ(n/4) = 8·σ(n)`, pinning `jacobiCount n = 8σ(n) − 32σ(n/4)`.

Together (1)+(3) give the full closed form of `jacobiCount` on every `n` from
ordinary divisor sums — the elementary half of Jacobi that is *not* Mathlib-blocked.
-/

namespace LagrangeFourSquaresOQ01OQ03Even

open Finset

/-- The right-hand side of Jacobi's four-square formula:
`jacobiCount n = 8 · Σ_{d ∣ n, 4 ∤ d} d` (restated from the base file). -/
def jacobiCount (n : ℕ) : ℕ :=
  8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d

/-- **Generalized odd collapse.** Whenever `4 ∤ n`, no divisor of `n` is divisible
by `4`, so the Jacobi filter is vacuous and `jacobiCount n = 8·σ(n)`. Subsumes the
base file's `jacobiCount_odd` and additionally covers `n ≡ 2 (mod 4)`. -/
theorem jacobiCount_of_not_four_dvd {n : ℕ} (hn : ¬ (4 ∣ n)) :
    jacobiCount n = 8 * ∑ d ∈ n.divisors, d := by
  unfold jacobiCount
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_true_of_mem
  intro d hd
  rw [Nat.mem_divisors] at hd
  intro hdvd
  exact hn (hdvd.trans hd.1)

/-- The divisors of `n` that **are** divisible by `4` are exactly `4·e` for `e` a
divisor of `n/4` (when `4 ∣ n`). -/
theorem filter_four_dvd_divisors {n : ℕ} (hn : 4 ∣ n) :
    n.divisors.filter (fun d => 4 ∣ d) = (n / 4).divisors.image (fun e => 4 * e) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
  constructor
  · rintro ⟨⟨hdn, -⟩, ⟨e, rfl⟩⟩
    refine ⟨e, ⟨?_, ?_⟩, rfl⟩
    · have hdvd : 4 * e ∣ 4 * (n / 4) := by rwa [Nat.mul_div_cancel' hn]
      exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp hdvd
    · have h4 : n / 4 ≠ 0 := by
        rw [Ne, Nat.div_eq_zero_iff]
        push_neg
        exact ⟨by norm_num, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hn⟩
      exact h4
  · rintro ⟨e, ⟨hen, -⟩, rfl⟩
    refine ⟨⟨?_, hn0⟩, ⟨e, rfl⟩⟩
    calc 4 * e ∣ 4 * (n / 4) := mul_dvd_mul_left 4 hen
      _ = n := Nat.mul_div_cancel' hn

/-- **The even content.** For `4 ∣ n`, the sum of divisors of `n` divisible by `4`
is `4·σ(n/4)`, via the bijection `e ↦ 4e` from `(n/4).divisors`. -/
theorem sum_four_dvd_divisors {n : ℕ} (hn : 4 ∣ n) :
    ∑ d ∈ n.divisors.filter (fun d => 4 ∣ d), d = 4 * ∑ e ∈ (n / 4).divisors, e := by
  rw [filter_four_dvd_divisors hn, Finset.sum_image, Finset.mul_sum]
  intro a _ b _ hab
  exact (mul_right_inj' (by norm_num : (4 : ℕ) ≠ 0)).mp hab

/-- **Even closed form (partition identity).** For `4 ∣ n`,
`jacobiCount n + 32·σ(n/4) = 8·σ(n)`, i.e. `jacobiCount n = 8σ(n) − 32σ(n/4)`.
Combined with `jacobiCount_of_not_four_dvd` this determines `jacobiCount` on all
`n` from ordinary divisor sums. Example `n = 4`: `24 + 32·1 = 8·7 = 56`. -/
theorem jacobiCount_four_dvd_add {n : ℕ} (hn : 4 ∣ n) :
    jacobiCount n + 32 * ∑ e ∈ (n / 4).divisors, e = 8 * ∑ d ∈ n.divisors, d := by
  unfold jacobiCount
  have hpart : (∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d)
      + (∑ d ∈ n.divisors.filter (fun d => 4 ∣ d), d)
      = ∑ d ∈ n.divisors, d := by
    rw [add_comm, Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 4 ∣ d)]
  rw [sum_four_dvd_divisors hn] at hpart
  omega

/-- Sanity check of the even closed form at `n = 4`: `jacobiCount 4 = 24`. -/
example : jacobiCount 4 = 24 := by decide

/-- **Unified closed form of the Jacobi right-hand side.**  Packaging
`jacobiCount_of_not_four_dvd` and `jacobiCount_four_dvd_add` into a single
determination valid for *every* `n`: off the `4 ∣ n` locus the Jacobi count is the
plain scaled divisor sum `8·σ(n)`, and on it the same value is corrected by exactly
`32·σ(n/4)` (equivalently `jacobiCount n = 8σ(n) − 32σ(n/4)`).  This is the entry
point the docstring's "(1)+(3) determine `jacobiCount` on all `n`" claim refers to:
the Jacobi RHS is pinned on every `n` purely from ordinary divisor sums, with no
`native_decide` and no axioms (`propext`/`Classical.choice`/`Quot.sound` only). -/
theorem jacobiCount_closed_form (n : ℕ) :
    (¬ 4 ∣ n → jacobiCount n = 8 * ∑ d ∈ n.divisors, d) ∧
    (4 ∣ n → jacobiCount n + 32 * ∑ e ∈ (n / 4).divisors, e
        = 8 * ∑ d ∈ n.divisors, d) :=
  ⟨jacobiCount_of_not_four_dvd, jacobiCount_four_dvd_add⟩

end LagrangeFourSquaresOQ01OQ03Even
