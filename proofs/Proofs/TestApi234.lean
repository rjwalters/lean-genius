import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

open Real

-- Test 1: piecewise continuous with if-then-else
noncomputable def testPiecewise (c : ℝ) : ℝ :=
  if c < 0 then 0 else 1 - Real.exp (-c)

-- Test 2: Continuous.if_le for piecewise
theorem test_piecewise_continuous : Continuous testPiecewise := by
  unfold testPiecewise
  apply Continuous.if_lt continuous_id continuous_const
  · exact continuous_const
  · exact continuous_const.sub (continuous_exp.comp continuous_neg)
  · intro x hx
    simp at hx
    rw [hx]
    simp

-- Test 3: exp bounds
theorem test_exp_nonneg (c : ℝ) (hc : c ≥ 0) : Real.exp (-c) ≤ 1 := by
  calc Real.exp (-c) ≤ Real.exp 0 := by
        apply exp_le_exp.mpr; linarith
    _ = 1 := exp_zero

-- Test 4: Finset.card_le_card for monotone filter
theorem test_filter_mono {N : ℕ} {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    ((Finset.range N).filter (fun n => decide (n < 3) = true)).card ≤
    ((Finset.range N).filter (fun n => decide (n < 5) = true)).card := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x
  simp
  omega

-- Test 5: Finset.filter_subset_filter with general Prop
-- This is what we need for density_monotone
example {N : ℕ} {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q x) :
    ((Finset.range N).filter P).card ≤ ((Finset.range N).filter Q).card := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact fun _ => h _
