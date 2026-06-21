/-
  Cantelli's One-Sided Chebyshev Inequality (Finite Form)

  Open question OQ-04 (parent: prob-method-second-moment).

  In the discrete Finset-ℚ setting of `ProbMethodSecondMoment.lean` /
  `ProbMethodSecondMomentOQ02.lean` — a finite "sample space" `s : Finset α`
  with the uniform counting measure and a "random variable" `f : α → ℚ` —
  Cantelli's inequality (the sharp one-sided form of Chebyshev) states

      P(f − μ ≥ a)  ≤  σ² / (σ² + a²)        (a > 0),

  where `μ = mean s f` and `σ² = variance s f`. Here the upper-tail
  "probability" is the fraction of sample points whose deviation reaches `a`:

      tailProb s f a  =  #{ i ∈ s : f i − μ ≥ a } / #s.

  The constant `σ²/(σ² + a²)` is strictly sharper than the one-sided
  Chebyshev bound `σ²/a²` (recovered as a corollary), with equality for a
  two-point distribution — so this is the best possible bound depending only
  on the first two moments.

  ## Proof (division-free, fully elementary)

  The textbook proof minimises `(σ² + t²)/(a + t)²` over the shift `t ≥ 0`,
  the optimum being `t = σ²/a`. To stay polynomial we use the *scaled* shift
  `g i = a·(f i − μ) + σ²` (which is `a·(d_i + σ²/a)`), avoiding fractions:

  * `∑_{i∈s} g i² = #s · σ² · (a² + σ²)`  — expand and use `∑ d_i = 0`,
    `∑ d_i² = #s · σ²` (the two defining moment identities).
  * On the tail event `d_i ≥ a > 0` we have `g i ≥ a² + σ² ≥ 0`, hence
    `g i² ≥ (a² + σ²)²`; summing over the (sub)set of tail points gives
    `#tail · (a² + σ²)² ≤ ∑_{i∈s} g i²`.
  * Combining and cancelling the positive factor `a² + σ²` yields the cleared
    inequality `#tail · (σ² + a²) ≤ #s · σ²`, which is exactly
    `tailProb ≤ σ²/(σ² + a²)` after clearing the (positive) denominators.

  Everything lives over ℚ with Finset sums — no measure theory, no real
  analysis, no `axiom`/`sorry`.
-/
import Mathlib
import Proofs.ProbMethodSecondMomentOQ02

set_option linter.unusedVariables false

namespace ProbMethod.SecondMoment

variable {α : Type*}

/-! ## Centering identity -/

/-- The deviations from the mean sum to zero: `∑_{i∈s} (f i − mean s f) = 0`. -/
theorem sum_sub_mean_eq_zero (s : Finset α) (f : α → ℚ) (hs : s.Nonempty) :
    s.sum (fun i => f i - mean s f) = 0 := by
  have hcard : (s.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
  have hsplit : s.sum (fun i => f i - mean s f) = s.sum f - (s.card : ℚ) * mean s f := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit, mean]
  first
    | (field_simp; ring)
    | field_simp

/-! ## The cleared key inequality -/

/-- **Cantelli, cleared form.** With `μ = mean s f`, `V = variance s f`, and
the tail event `{ i ∈ s : f i − μ ≥ a }`, for every `a > 0`:

    #tail · (V + a²)  ≤  #s · V.

This is the division-free heart of Cantelli's inequality; dividing through by
the positive quantities recovers the probability statement. -/
theorem cantelli_key (s : Finset α) (f : α → ℚ) (a : ℚ) (hs : s.Nonempty)
    (ha : 0 < a) :
    ((s.filter (fun i => a ≤ f i - mean s f)).card : ℚ) * (variance s f + a ^ 2)
      ≤ (s.card : ℚ) * variance s f := by
  have hvar_nonneg : 0 ≤ variance s f := by
    rw [variance]
    exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
  -- Second-moment identity for the scaled shift `g i = a·(f i − μ) + V`.
  have sumId :
      s.sum (fun i => (a * (f i - mean s f) + variance s f) ^ 2)
        = (s.card : ℚ) * variance s f * (a ^ 2 + variance s f) := by
    have hcard : (s.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
    have hsumsq :
        s.sum (fun i => (f i - mean s f) ^ 2) = variance s f * (s.card : ℚ) := by
      rw [variance]
      first
        | (field_simp; ring)
        | field_simp
    have expand :
        s.sum (fun i => (a * (f i - mean s f) + variance s f) ^ 2)
          = s.sum (fun i => a ^ 2 * (f i - mean s f) ^ 2
              + 2 * a * variance s f * (f i - mean s f) + (variance s f) ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [expand, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
        sum_sub_mean_eq_zero s f hs, hsumsq]
    ring
  -- Lower bound: the tail points alone force `g i² ≥ (a² + V)²`.
  have hlow :
      ((s.filter (fun i => a ≤ f i - mean s f)).card : ℚ) * (a ^ 2 + variance s f) ^ 2
        ≤ s.sum (fun i => (a * (f i - mean s f) + variance s f) ^ 2) := by
    have hsub : s.filter (fun i => a ≤ f i - mean s f) ⊆ s := Finset.filter_subset _ _
    have hSsum :
        (s.filter (fun i => a ≤ f i - mean s f)).sum
            (fun i => (a * (f i - mean s f) + variance s f) ^ 2)
          ≤ s.sum (fun i => (a * (f i - mean s f) + variance s f) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have hconst :
        (s.filter (fun i => a ≤ f i - mean s f)).sum
            (fun _ : α => (a ^ 2 + variance s f) ^ 2)
          ≤ (s.filter (fun i => a ≤ f i - mean s f)).sum
            (fun i => (a * (f i - mean s f) + variance s f) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hfi : a ≤ f i - mean s f := (Finset.mem_filter.mp hi).2
      have h0 : 0 ≤ a ^ 2 + variance s f := add_nonneg (sq_nonneg a) hvar_nonneg
      have hstep : a ^ 2 + variance s f ≤ a * (f i - mean s f) + variance s f := by
        nlinarith [mul_le_mul_of_nonneg_left hfi ha.le]
      nlinarith [hstep, h0]
    rw [Finset.sum_const, nsmul_eq_mul] at hconst
    exact le_trans hconst hSsum
  rw [sumId] at hlow
  have hVa2 : (0 : ℚ) < a ^ 2 + variance s f :=
    add_pos_of_pos_of_nonneg (pow_pos ha 2) hvar_nonneg
  rw [sq, ← mul_assoc] at hlow
  have key := le_of_mul_le_mul_right hlow hVa2
  rw [add_comm (variance s f) (a ^ 2)]
  exact key

/-! ## The probability statement -/

/-- Upper-tail "probability" under the uniform counting measure on `s`:
the fraction of sample points where `f` exceeds its mean by at least `a`. -/
def tailProb (s : Finset α) (f : α → ℚ) (a : ℚ) : ℚ :=
  (s.filter (fun i => a ≤ f i - mean s f)).card / s.card

/-- **Cantelli's one-sided Chebyshev inequality (finite form).**
For `a > 0` on a nonempty finite sample space,

    P(f − μ ≥ a)  ≤  σ² / (σ² + a²). -/
theorem cantelli (s : Finset α) (f : α → ℚ) (a : ℚ) (hs : s.Nonempty)
    (ha : 0 < a) :
    tailProb s f a ≤ variance s f / (variance s f + a ^ 2) := by
  have hvar_nonneg : 0 ≤ variance s f := by
    rw [variance]
    exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
  have hN : (0 : ℚ) < s.card := by exact_mod_cast hs.card_pos
  have hden : (0 : ℚ) < variance s f + a ^ 2 :=
    add_pos_of_nonneg_of_pos hvar_nonneg (pow_pos ha 2)
  rw [tailProb]
  first
    | rw [div_le_div_iff₀ hN hden]
    | rw [div_le_div_iff_of_pos hN hden]
    | rw [div_le_div_iff hN hden]
  rw [mul_comm (variance s f) (s.card : ℚ)]
  exact cantelli_key s f a hs ha

/-- **Cantelli is sharper than one-sided Chebyshev.** The Cantelli bound
implies the classical one-sided Chebyshev tail bound `σ²/a²`, since
`σ²/(σ² + a²) ≤ σ²/a²`. -/
theorem tailProb_le_chebyshev (s : Finset α) (f : α → ℚ) (a : ℚ) (hs : s.Nonempty)
    (ha : 0 < a) :
    tailProb s f a ≤ variance s f / a ^ 2 := by
  have hvar_nonneg : 0 ≤ variance s f := by
    rw [variance]
    exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
  have ha2 : (0 : ℚ) < a ^ 2 := pow_pos ha 2
  have hden : (0 : ℚ) < variance s f + a ^ 2 :=
    add_pos_of_nonneg_of_pos hvar_nonneg ha2
  have hcomp : variance s f / (variance s f + a ^ 2) ≤ variance s f / a ^ 2 := by
    first
      | rw [div_le_div_iff₀ hden ha2]
      | rw [div_le_div_iff_of_pos hden ha2]
      | rw [div_le_div_iff hden ha2]
    nlinarith [mul_self_nonneg (variance s f)]
  exact le_trans (cantelli s f a hs ha) hcomp

end ProbMethod.SecondMoment
