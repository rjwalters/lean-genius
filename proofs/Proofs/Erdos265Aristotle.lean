/-
  Aristotle targets for Erdos Problem #265
  Routine supporting lemmas for automated proof search.
  See Erdos265Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (limsup a_n^{1/2^n} > 1)
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axiom declarations
-/
import Mathlib

namespace Erdos265Aristotle

open Filter

variable (a : ℕ → ℕ)

/-- A sequence of positive integers -/
def IsPositiveIntSeq : Prop := ∀ n, a n ≥ 1

noncomputable def singleExpGrowth (n : ℕ) : ℝ :=
  (a n : ℝ) ^ (1 / n : ℝ)

noncomputable def genExpGrowth (β : ℝ) (n : ℕ) : ℝ :=
  (a n : ℝ) ^ (1 / β ^ n)

/-
PROBLEM
TARGET 1: If a_n^{1/β^n} → ∞ for β > 1, then a_n^{1/n} → ∞
Strategy: For β > 1 and large n, β^n ≥ n, so 1/n ≥ 1/β^n.
Since a_n ≥ 1, rpow is monotone: (a_n)^{1/n} ≥ (a_n)^{1/β^n}.
By comparison, singleExpGrowth → ∞.
Key tools: Real.rpow_le_rpow_of_exponent_le, tendsto_pow_atTop_atTop_of_one_lt

PROVIDED SOLUTION
For β > 1 and large n, β^n ≥ n (use eventually_pow_ge_id), so 1/n ≥ 1/β^n. Since a_n ≥ 1 (from hpos), we have (a_n : ℝ) ≥ 1, so by rpow_mono_exponent (i.e. Real.rpow_le_rpow_of_exponent_le), (a_n)^{1/β^n} ≤ (a_n)^{1/n}. Since genExpGrowth a β → ∞, by comparison (Filter.Tendsto.atTop_mono or similar), singleExpGrowth a → ∞.
-/
theorem singleExp_of_genExp (β : ℝ) (hβ : β > 1)
    (hpos : IsPositiveIntSeq a)
    (htend : Tendsto (genExpGrowth a β) atTop atTop) :
    Tendsto (singleExpGrowth a) atTop atTop := by
      rw [ Filter.tendsto_atTop_atTop ] at *;
      -- For β > 1 and large n, β^n ≥ n (use eventually_pow_ge_id), so 1/n ≥ 1/β^n.
      have h_exp_ge : ∀ᶠ n in atTop, (n : ℝ) ≤ β ^ n := by
        -- We'll use that β^n grows faster than n for β > 1.
        have h_exp_growth : Filter.Tendsto (fun n : ℝ => β ^ n / n) Filter.atTop Filter.atTop := by
          have h_exp_growth : Filter.Tendsto (fun n : ℝ => Real.exp (n * Real.log β) / n) Filter.atTop Filter.atTop := by
            have := Real.tendsto_exp_div_pow_atTop 1;
            have := this.comp ( Filter.tendsto_id.atTop_mul_const ( Real.log_pos hβ ) );
            convert this.const_mul_atTop ( Real.log_pos hβ ) using 2 ; norm_num ; ring;
            norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos hβ ];
          simpa only [ Real.rpow_def_of_pos ( zero_lt_one.trans hβ ), mul_comm ] using h_exp_growth;
        filter_upwards [ h_exp_growth.eventually_gt_atTop 1, Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ lt_div_iff₀ hn' ] at hn; linarith;
      -- Since $a_n \geq 1$, we have $(a_n)^{1/n} \geq (a_n)^{1/β^n}$.
      have h_ge : ∀ᶠ n in atTop, ((a n) : ℝ) ^ (1 / (n : ℝ)) ≥ ((a n) : ℝ) ^ (1 / (β ^ n : ℝ)) := by
        filter_upwards [ h_exp_ge.natCast_atTop, Filter.eventually_gt_atTop 0 ] with n hn hn' ; gcongr ; aesop;
        exact_mod_cast hn;
      exact fun b => by rcases htend b with ⟨ i, hi ⟩ ; rcases Filter.eventually_atTop.mp h_ge with ⟨ j, hj ⟩ ; exact ⟨ Max.max i j, fun n hn => le_trans ( hi n ( le_trans ( le_max_left _ _ ) hn ) ) ( hj n ( le_trans ( le_max_right _ _ ) hn ) ) ⟩ ;

/-
PROBLEM
TARGET 2: For β > 1, eventually β^n ≥ n
Strategy: tendsto_pow_atTop_atTop_of_one_lt gives β^n → ∞,
so eventually β^n ≥ n
Key tools: tendsto_pow_atTop_atTop_of_one_lt, Filter.Tendsto.eventually_ge_atTop

PROVIDED SOLUTION
Use Filter.Tendsto.eventually_ge_atTop (or eventually_atTop) applied to the fact that β^n → ∞ (from tendsto_pow_atTop_atTop_of_one_lt or similar). Since β > 1, the sequence n ↦ β^n tends to atTop, so eventually β^n ≥ n.
-/
theorem eventually_pow_ge_id (β : ℝ) (hβ : β > 1) :
    ∀ᶠ n in atTop, (n : ℝ) ≤ β ^ n := by
      -- Since $\beta > 1$, we have $\beta^n \to \infty$ as $n \to \infty$.
      have h_beta_n_inf : Filter.Tendsto (fun n => β^n / (n : ℝ)) Filter.atTop Filter.atTop := by
        -- We can use the change of variables $u = n \ln \beta$ to transform the limit expression.
        suffices h_log : Filter.Tendsto (fun u => Real.exp u / (u / Real.log β)) Filter.atTop Filter.atTop by
          convert h_log.comp ( show Filter.Tendsto ( fun n => n * Real.log β ) Filter.atTop Filter.atTop from Filter.tendsto_id.atTop_mul_const <| Real.log_pos hβ ) using 2 ; norm_num [ Real.rpow_def_of_pos <| zero_lt_one.trans hβ, mul_div_cancel₀ _ <| ne_of_gt <| Real.log_pos hβ ] ; ring_nf;
          norm_num [ ne_of_gt, Real.log_pos hβ ];
        simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos hβ ] using Filter.Tendsto.const_mul_atTop ( Real.log_pos hβ ) ( Real.tendsto_exp_div_pow_atTop 1 );
      filter_upwards [ h_beta_n_inf.eventually_gt_atTop 1, Filter.eventually_gt_atTop 0 ] with n hn hn' using by rw [ div_eq_mul_inv ] at hn; nlinarith [ inv_mul_cancel₀ hn'.ne' ] ;

/-
PROBLEM
TARGET 3: rpow monotonicity for base ≥ 1
Strategy: This should be in Mathlib as Real.rpow_le_rpow_of_exponent_le
Key tools: Real.rpow_le_rpow_of_exponent_le

PROVIDED SOLUTION
This is exactly Real.rpow_le_rpow_of_exponent_le applied to hx and hpq.
-/
theorem rpow_mono_exponent (x : ℝ) (hx : 1 ≤ x) (p q : ℝ) (hpq : p ≤ q) :
    x ^ p ≤ x ^ q := by
      exact?

end Erdos265Aristotle