/-!
# AC → BV: Absolutely Continuous ⟹ Bounded Variation

**Open Question OQ-01** from `fundamental-theorem-calculus-oq-01`
(Lebesgue FTC entry: "Can AC → BV be proved directly from the ε-δ definition?")

## Answer: Yes.

Every F : ℝ → ℝ absolutely continuous on [a,b] (ε-δ definition in
`FundamentalTheoremCalculusLebesgue`) has bounded variation on [a,b].
No extra Mathlib infrastructure is needed beyond `Mathlib.Analysis.BoundedVariation`.

## Proof sketch

1. AC with ε=1 gives δ>0.
2. Let n = ⌈(b-a)/δ⌉+1, step = (b-a)/n < δ.
3. **Key**: eVariationOn F (Icc c d) ≤ 1 when d-c < δ (via AC + partition sum bound).
4. By Icc_add_Icc applied n-1 times: eVariationOn F (Icc a b) ≤ n < ⊤.

## Status: 0 sorries, 0 axioms
-/

import Proofs.FundamentalTheoremCalculusLebesgue
import Mathlib.Analysis.BoundedVariation
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

open FTCLebesgue Set ENNReal Finset

set_option maxHeartbeats 800000

namespace FTCLebesgueACImpliesBV

/-! ## Lemma 1: edist on ℝ equals ENNReal.ofReal |x - y| -/

private lemma edist_real_ofReal {x y : ℝ} :
    edist x y = ENNReal.ofReal |x - y| := by
  rw [edist_dist, Real.dist_eq]

/-! ## Lemma 2: Upper-bound criterion for eVariationOn -/

private lemma eVariationOn_le_of_forall {f : ℝ → ℝ} {s : Set ℝ} {C : ℝ≥0∞}
    (h : ∀ (n : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ s) →
      ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤ C) :
    eVariationOn f s ≤ C := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  exact h n u hu hus

/-! ## Lemma 3: Telescoping sum for Fin n -/

private lemma fin_telescoping {n : ℕ} (u : ℕ → ℝ) :
    ∑ k : Fin n, (u (k.val + 1) - u k.val) = u n - u 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    linarith

/-! ## Lemma 4: Short subintervals have bounded variation ≤ 1 -/

private lemma eVariationOn_le_one_of_short {F : ℝ → ℝ} {a b c d : ℝ}
    (hca : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    {δ : ℝ} (hδ : 0 < δ) (hlen : d - c < δ)
    (hac : ∀ (n : ℕ) (as bs : Fin n → ℝ),
      (∀ k, a ≤ as k ∧ as k ≤ bs k ∧ bs k ≤ b) →
      (∀ j k : Fin n, j ≠ k → bs j ≤ as k ∨ bs k ≤ as j) →
      (∑ k, (bs k - as k)) < δ →
      (∑ k, |F (bs k) - F (as k)|) < 1) :
    eVariationOn F (Set.Icc c d) ≤ 1 := by
  apply eVariationOn_le_of_forall
  intro n u hu_mono hu_mem
  simp_rw [edist_real_ofReal]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _), ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_lt
  -- AC gives ∑ k : Fin n, |F(u(k+1)) - F(u(k))| < 1
  have key := hac n (fun k => u k.val) (fun k => u (k.val + 1))
    (fun k => ⟨le_trans hca (hu_mem k.val).1,
               hu_mono (Nat.le_succ k.val),
               le_trans (hu_mem (k.val + 1)).2 hdb⟩)
    (fun j k hjk => by
      rcases lt_or_gt_of_ne hjk with h | h
      · left;  exact hu_mono (Nat.succ_le_of_lt h)
      · right; exact hu_mono (Nat.succ_le_of_lt h))
    (by rw [fin_telescoping u]; linarith [(hu_mem 0).1, (hu_mem n).2])
  -- Convert Fin sum in key to range sum matching goal
  rw [← Fin.sum_univ_eq_sum_range (fun i => |F (u (i + 1)) - F (u i)|) n]
  exact key

/-! ## Lemma 5: Inductive variation bound via Icc_add_Icc -/

private lemma eVariationOn_le_n {F : ℝ → ℝ} (a step : ℝ) (hstep : 0 < step) (n : ℕ)
    (hpieces : ∀ k : Fin n,
        eVariationOn F (Set.Icc (a + k.val * step) (a + (k.val + 1) * step)) ≤ 1) :
    eVariationOn F (Set.Icc a (a + n * step)) ≤ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [le_zero_iff]
    apply eVariationOn.eq_zero_iff.mpr
    intro x hx y hy
    have hxa : x = a := le_antisymm (Set.mem_Icc.mp hx).2 (Set.mem_Icc.mp hx).1
    have hya : y = a := le_antisymm (Set.mem_Icc.mp hy).2 (Set.mem_Icc.mp hy).1
    rw [hxa, hya]; exact edist_self _
  | succ m ih =>
    have hm_le : a ≤ a + ↑m * step := by
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep.le)
    have hmid : a + ↑m * step ≤ a + (↑m + 1) * step := by linarith
    -- Split at midpoint using Icc_add_Icc
    have heq := eVariationOn.Icc_add_Icc F hm_le hmid (Set.mem_univ _)
    simp only [Set.univ_inter] at heq
    -- heq : eVar(a, a+m*step) + eVar(a+m*step, a+(m+1)*step) = eVar(a, a+(m+1)*step)
    rw [show a + (↑(m + 1) : ℝ) * step = a + (↑m + 1) * step by push_cast; ring, ← heq]
    have hih  : eVariationOn F (Set.Icc a (a + ↑m * step)) ≤ m :=
      ih (fun k => hpieces ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
    have hlast : eVariationOn F (Set.Icc (a + ↑m * step) (a + (↑m + 1) * step)) ≤ 1 :=
      hpieces ⟨m, Nat.lt_succ_self m⟩
    calc eVariationOn F (Set.Icc a (a + ↑m * step)) +
         eVariationOn F (Set.Icc (a + ↑m * step) (a + (↑m + 1) * step))
        ≤ (m : ℝ≥0∞) + 1 := add_le_add hih hlast
      _ = ↑(m + 1)       := by push_cast; ring

/-! ## Main Theorem: AC → BV -/

/-- **AC → BV**: Every absolutely continuous function on [a,b] has bounded variation.

This answers OQ-01 from the Lebesgue FTC entry: AC → BV holds directly from the ε-δ
definition without additional infrastructure.

Key step toward the full Lebesgue FTC:
  AC → **BV** → Jordan decomposition → a.e. differentiable → Lebesgue FTC. -/
theorem ac_implies_bv {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    BoundedVariationOn F (Set.Icc a b) := by
  -- Case a = b: [a,a] is a point, variation = 0 ≠ ⊤
  rcases eq_or_lt_of_le hab with rfl | hab'
  · show eVariationOn F (Set.Icc a a) ≠ ⊤
    have : eVariationOn F (Set.Icc a a) = 0 :=
      eVariationOn.eq_zero_iff.mpr fun x hx y hy => by
        have hxa : x = a := le_antisymm (Set.mem_Icc.mp hx).2 (Set.mem_Icc.mp hx).1
        have hya : y = a := le_antisymm (Set.mem_Icc.mp hy).2 (Set.mem_Icc.mp hy).1
        rw [hxa, hya]; exact edist_self _
    rw [this]; exact ENNReal.zero_ne_top
  -- General case: choose n pieces of length step = (b-a)/n < δ
  obtain ⟨δ, hδ, hac⟩ := hF 1 one_pos
  have hba : 0 < b - a := sub_pos.mpr hab'
  -- n = ⌈(b-a)/δ⌉ + 1 ensures step = (b-a)/n < δ
  set n : ℕ := ⌈(b - a) / δ⌉₊ + 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  set step : ℝ := (b - a) / n
  have hstep_pos : 0 < step := div_pos hba hn_pos
  -- Each piece has length step < δ
  have hstep_lt : step < δ := by
    rw [div_lt_iff hn_pos]
    have h_ceil : (b - a) / δ ≤ (⌈(b - a) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hn_eq : (n : ℝ) = ⌈(b - a) / δ⌉₊ + 1 := by push_cast; ring
    rw [hn_eq]
    nlinarith [mul_le_mul_of_nonneg_right h_ceil hδ.le, Nat.cast_nonneg (⌈(b - a) / δ⌉₊)]
  -- a + n * step = b
  have hab_step : a + n * step = b := by
    have : n * step = b - a := mul_div_cancel₀ _ hn_pos.ne'
    linarith
  -- Each of the n pieces [a+k*step, a+(k+1)*step] has variation ≤ 1
  have hpieces : ∀ k : Fin n,
      eVariationOn F (Set.Icc (a + k.val * step) (a + (k.val + 1) * step)) ≤ 1 := by
    intro k
    apply eVariationOn_le_one_of_short
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep_pos.le)
    · linarith [hstep_pos]
    · have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.isLt
      have : a + (k.val + 1) * step ≤ a + n * step := by nlinarith [hstep_pos.le]
      linarith [hab_step]
    · exact hδ
    · ring_nf; exact hstep_lt
    · exact hac
  -- Total variation ≤ n < ⊤
  show eVariationOn F (Set.Icc a b) ≠ ⊤
  rw [← hab_step]
  exact ne_top_of_le_ne_top ENNReal.natCast_ne_top
    (eVariationOn_le_n a step hstep_pos n hpieces)

end FTCLebesgueACImpliesBV
