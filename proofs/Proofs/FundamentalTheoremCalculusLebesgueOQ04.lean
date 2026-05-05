/-!
# AbsolutelyContinuousOn for Normed Space-Valued Functions (OQ-04)

**Open Question OQ-04** from `fundamental-theorem-calculus-oq-01`
(Lebesgue FTC entry: "Should AbsolutelyContinuousOn be generalized to
functions between normed spaces?")

## Answer: Yes.

For any `NormedAddCommGroup E`, the definition of absolute continuity extends
naturally from `F : ℝ → ℝ` to `f : ℝ → E` by replacing `|·|` with `‖·‖`.

This generalization encompasses:
- Curves in ℝⁿ (coordinate motion, mechanics)
- Matrix-valued processes (control theory)
- Banach space-valued paths (abstract evolution equations)

**Main theorem**: Every normed-AC function has bounded variation (AC → BV).

The proof follows the same partition argument as the real-valued case
(see `FundamentalTheoremCalculusLebesgueOQ01`), using:
- `edist x y = ENNReal.ofReal ‖x - y‖` (the normed-space analogue)
- `eVariationOn.Icc_add_Icc` (additive splitting, works for any metric space)

## Status: 0 sorries, 0 axioms

## Theorems (7):
1. `const_normed_ac` — constant functions are normed-AC
2. `lipschitz_implies_normed_ac` — Lipschitz → normed-AC
3. `normed_ac_implies_real_ac` — normed-AC at E = ℝ recovers real-valued AC
4. `normed_ac_mono_subinterval` — restriction to subintervals preserves normed-AC
5. `normed_ac_implies_bv` — main theorem: normed-AC → bounded variation
6. `normed_bv_ne_top` — eVariationOn is finite (equivalent formulation)
7. `real_ac_iff_normed_ac` — real-valued AC is a special case of normed-AC
-/

import Proofs.FundamentalTheoremCalculusLebesgue
import Mathlib.Analysis.BoundedVariation
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Tactic

open Set ENNReal Finset FTCLebesgue

set_option maxHeartbeats 800000

namespace FTCNormedAC

variable {E : Type*} [NormedAddCommGroup E]

-- ═══════════════════════════════════════════════════════════════
-- PART I: Definition
-- ═══════════════════════════════════════════════════════════════

/-- A function `f : ℝ → E` (where `E` is a normed group) is **absolutely continuous**
    on `[a, b]` if for every `ε > 0` there exists `δ > 0` such that for any finite
    collection of pairwise disjoint subintervals `[aₖ, bₖ] ⊂ [a, b]` with total length
    `∑ (bₖ - aₖ) < δ`, we have `∑ ‖f(bₖ) - f(aₖ)‖ < ε`.

    This is the natural vector-valued analogue of `AbsolutelyContinuousOn` from
    `FundamentalTheoremCalculusLebesgue`, replacing `|·|` with `‖·‖`. -/
def AbsolutelyContinuousOnNormed (f : ℝ → E) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
    ∀ (n : ℕ) (as bs : Fin n → ℝ),
      (∀ k, a ≤ as k ∧ as k ≤ bs k ∧ bs k ≤ b) →
      (∀ j k : Fin n, j ≠ k → bs j ≤ as k ∨ bs k ≤ as j) →
      (∑ k, (bs k - as k)) < δ →
      (∑ k, ‖f (bs k) - f (as k)‖) < ε

-- ═══════════════════════════════════════════════════════════════
-- PART II: Basic Examples
-- ═══════════════════════════════════════════════════════════════

/-- Constant functions are normed-AC: `‖c - c‖ = 0 < ε` for any collection of intervals. -/
theorem const_normed_ac (c : E) (a b : ℝ) : AbsolutelyContinuousOnNormed (fun _ => c) a b := by
  intro ε hε
  exact ⟨1, one_pos, fun n as bs _ _ _ => by simp [hε]⟩

/-- Lipschitz functions are normed-AC.
    If `‖f(x) - f(y)‖ ≤ K · |x - y|` for all `x, y ∈ [a, b]`, then `f` is normed-AC
    with `δ = ε / (K + 1)`. -/
theorem lipschitz_implies_normed_ac {f : ℝ → E} {K : ℝ} (hK : K ≥ 0)
    {a b : ℝ} (hab : a ≤ b)
    (hLip : ∀ x y : ℝ, x ∈ Icc a b → y ∈ Icc a b → ‖f x - f y‖ ≤ K * |x - y|) :
    AbsolutelyContinuousOnNormed f a b := by
  intro ε hε
  have hKp : (0 : ℝ) < K + 1 := by linarith
  refine ⟨ε / (K + 1), div_pos hε hKp, ?_⟩
  intro n as bs hsub _ htotal
  have hsum_nn : (0 : ℝ) ≤ ∑ k, (bs k - as k) :=
    Finset.sum_nonneg fun k _ => by linarith [(hsub k).2.1, (hsub k).1]
  have hstep : ∀ k : Fin n, ‖f (bs k) - f (as k)‖ ≤ K * (bs k - as k) := fun k => by
    have ⟨hak, hle, hbk⟩ := hsub k
    calc ‖f (bs k) - f (as k)‖
        = ‖f (as k) - f (bs k)‖ := norm_sub_rev _ _
      _ ≤ K * |as k - bs k| := hLip (as k) (bs k) ⟨hak, hle.trans hbk⟩ ⟨hak.trans hle, hbk⟩
      _ = K * (bs k - as k) := by rw [abs_of_nonpos (by linarith), neg_sub]
  calc ∑ k, ‖f (bs k) - f (as k)‖
      ≤ ∑ k, K * (bs k - as k) := Finset.sum_le_sum fun k _ => hstep k
    _ = K * ∑ k, (bs k - as k) := by rw [Finset.mul_sum]
    _ < K * (ε / (K + 1)) + ε / (K + 1) := by
        nlinarith [mul_le_mul_of_nonneg_left htotal.le hK, div_pos hε hKp]
    _ = ε := by field_simp; ring

-- ═══════════════════════════════════════════════════════════════
-- PART III: Connection to Real-Valued AC
-- ═══════════════════════════════════════════════════════════════

/-- For `E = ℝ`, normed-AC implies the original `AbsolutelyContinuousOn`. -/
theorem normed_ac_implies_real_ac {F : ℝ → ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnNormed F a b) :
    AbsolutelyContinuousOn F a b := by
  intro ε hε
  obtain ⟨δ, hδ, hac⟩ := hF ε hε
  refine ⟨δ, hδ, fun n as bs hsub hdisj htot => ?_⟩
  have key := hac n as bs hsub hdisj htot
  simp_rw [Real.norm_eq_abs] at key
  exact key

/-- For `E = ℝ`, `AbsolutelyContinuousOn` implies normed-AC. -/
theorem real_ac_implies_normed_ac {F : ℝ → ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOn F a b) :
    AbsolutelyContinuousOnNormed F a b := by
  intro ε hε
  obtain ⟨δ, hδ, hac⟩ := hF ε hε
  refine ⟨δ, hδ, fun n as bs hsub hdisj htot => ?_⟩
  have key := hac n as bs hsub hdisj htot
  simp_rw [Real.norm_eq_abs]
  exact key

/-- For `E = ℝ`, normed-AC is equivalent to `AbsolutelyContinuousOn`. -/
theorem real_ac_iff_normed_ac {F : ℝ → ℝ} {a b : ℝ} :
    AbsolutelyContinuousOnNormed F a b ↔ AbsolutelyContinuousOn F a b :=
  ⟨normed_ac_implies_real_ac, real_ac_implies_normed_ac⟩

-- ═══════════════════════════════════════════════════════════════
-- PART IV: Subinterval Restriction
-- ═══════════════════════════════════════════════════════════════

/-- Normed-AC on `[a, b]` implies normed-AC on any subinterval `[c, d] ⊆ [a, b]`. -/
theorem normed_ac_mono_subinterval {f : ℝ → E} {a b c d : ℝ}
    (hca : a ≤ c) (hdb : d ≤ b)
    (hf : AbsolutelyContinuousOnNormed f a b) :
    AbsolutelyContinuousOnNormed f c d := by
  intro ε hε
  obtain ⟨δ, hδ, hac⟩ := hf ε hε
  refine ⟨δ, hδ, fun n as bs hsub hdisj htot => ?_⟩
  exact hac n as bs
    (fun k => let ⟨hck, hle, hdk⟩ := hsub k; ⟨hca.trans hck, hle, hdk.trans hdb⟩)
    hdisj htot

-- ═══════════════════════════════════════════════════════════════
-- PART V: Private Helpers for the Main Theorem
-- ═══════════════════════════════════════════════════════════════

private lemma edist_norm_ofReal (x y : E) :
    edist x y = ENNReal.ofReal ‖x - y‖ := by
  rw [edist_dist, dist_norm]

private lemma eVariationOn_le_of_forall_normed {f : ℝ → E} {s : Set ℝ} {C : ℝ≥0∞}
    (h : ∀ (n : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ s) →
      ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤ C) :
    eVariationOn f s ≤ C := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  exact h n u hu hus

private lemma fin_telescoping_normed {n : ℕ} (u : ℕ → ℝ) :
    ∑ k : Fin n, (u (k.val + 1) - u k.val) = u n - u 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    linarith

private lemma eVariationOn_le_one_normed {f : ℝ → E} {a b c d : ℝ}
    (hca : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    {δ : ℝ} (hδ : 0 < δ) (hlen : d - c < δ)
    (hac : ∀ (n : ℕ) (as bs : Fin n → ℝ),
      (∀ k, a ≤ as k ∧ as k ≤ bs k ∧ bs k ≤ b) →
      (∀ j k : Fin n, j ≠ k → bs j ≤ as k ∨ bs k ≤ as j) →
      (∑ k, (bs k - as k)) < δ →
      (∑ k, ‖f (bs k) - f (as k)‖) < 1) :
    eVariationOn f (Set.Icc c d) ≤ 1 := by
  apply eVariationOn_le_of_forall_normed
  intro n u hu_mono hu_mem
  simp_rw [edist_norm_ofReal]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _), ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_lt
  -- Apply AC to the partition u(0)≤u(1)≤...≤u(n) with as k = u k, bs k = u (k+1)
  have key := hac n (fun k => u k.val) (fun k => u (k.val + 1))
    -- Subintervals are within [a, b]
    (fun k => ⟨hca.trans (hu_mem k.val).1,
               hu_mono (Nat.le_succ k.val),
               (hu_mem (k.val + 1)).2.trans hdb⟩)
    -- Disjointness: u (j+1) ≤ u k or u (k+1) ≤ u j
    (fun j k hjk => by
      have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hjk' with h | h
      · left; exact hu_mono (Nat.succ_le_of_lt h)
      · right; exact hu_mono (Nat.succ_le_of_lt h))
    -- Total length < δ
    (by
      rw [← Fin.sum_univ_eq_sum_range (fun i => u (i + 1) - u i) n,
          fin_telescoping_normed]
      have hc := (hu_mem 0).1
      have hd := (hu_mem n).2
      linarith)
  -- Connect the Fin sum to the range sum
  rw [← Fin.sum_univ_eq_sum_range (fun i => ‖f (u (i + 1)) - f (u i)‖) n]
  exact key

private lemma eVariationOn_le_n_normed {f : ℝ → E} (a step : ℝ) (hstep : 0 < step) (n : ℕ)
    (hpieces : ∀ k : Fin n,
        eVariationOn f (Set.Icc (a + k.val * step) (a + (k.val + 1) * step)) ≤ 1) :
    eVariationOn f (Set.Icc a (a + n * step)) ≤ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [le_zero_iff]
    exact eVariationOn.eq_zero_iff.mpr fun x hx y hy => by
      have hxa : x = a := le_antisymm (Set.mem_Icc.mp hx).2 (Set.mem_Icc.mp hx).1
      have hya : y = a := le_antisymm (Set.mem_Icc.mp hy).2 (Set.mem_Icc.mp hy).1
      rw [hxa, hya]; exact edist_self _
  | succ m ih =>
    have hm_le : a ≤ a + ↑m * step :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep.le)
    have hmid : a + ↑m * step ≤ a + (↑m + 1) * step := by linarith
    have heq := eVariationOn.Icc_add_Icc f hm_le hmid (Set.mem_univ _)
    simp only [Set.univ_inter] at heq
    rw [show a + (↑(m + 1) : ℝ) * step = a + (↑m + 1) * step by push_cast; ring, ← heq]
    have hih : eVariationOn f (Set.Icc a (a + ↑m * step)) ≤ m :=
      ih (fun k => hpieces ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
    have hlast : eVariationOn f (Set.Icc (a + ↑m * step) (a + (↑m + 1) * step)) ≤ 1 :=
      hpieces ⟨m, Nat.lt_succ_self m⟩
    calc eVariationOn f (Set.Icc a (a + ↑m * step)) +
         eVariationOn f (Set.Icc (a + ↑m * step) (a + (↑m + 1) * step))
        ≤ (m : ℝ≥0∞) + 1 := add_le_add hih hlast
      _ = ↑(m + 1)       := by push_cast; ring

-- ═══════════════════════════════════════════════════════════════
-- PART VI: Main Theorem — Normed-AC implies BV
-- ═══════════════════════════════════════════════════════════════

/-- **Normed AC → BV**: Every normed-absolutely-continuous function has bounded variation.

    This extends `ac_implies_bv` (from `FundamentalTheoremCalculusLebesgueOQ01`) to
    functions `f : ℝ → E` where `E` is any `NormedAddCommGroup`.

    **Proof strategy** (identical to the real-valued case):
    1. AC with `ε = 1` gives `δ > 0`.
    2. Partition `[a, b]` into `n = ⌈(b-a)/δ⌉ + 1` equal subintervals of length `< δ`.
    3. Each subinterval has `eVariationOn f ≤ 1` (normed-AC + `edist = ENNReal.ofReal ‖·‖`).
    4. By `eVariationOn.Icc_add_Icc` induction: total `eVariationOn f [a,b] ≤ n < ⊤`. -/
theorem normed_ac_implies_bv {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnNormed f a b) :
    BoundedVariationOn f (Set.Icc a b) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · -- Degenerate case: [a, a] has variation 0 ≠ ⊤
    have : eVariationOn f (Set.Icc a a) = 0 :=
      eVariationOn.eq_zero_iff.mpr fun x hx y hy => by
        have hxa : x = a := le_antisymm (Set.mem_Icc.mp hx).2 (Set.mem_Icc.mp hx).1
        have hya : y = a := le_antisymm (Set.mem_Icc.mp hy).2 (Set.mem_Icc.mp hy).1
        rw [hxa, hya]; exact edist_self _
    exact this ▸ ENNReal.zero_ne_top
  -- General case: a < b
  obtain ⟨δ, hδ, hac⟩ := hf 1 one_pos
  have hba : 0 < b - a := sub_pos.mpr hab'
  -- Choose n so that each piece has length < δ
  set n : ℕ := ⌈(b - a) / δ⌉₊ + 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  set step : ℝ := (b - a) / n
  have hstep_pos : 0 < step := div_pos hba hn_pos
  have hstep_lt : step < δ := by
    rw [div_lt_iff hn_pos]
    have h_ceil : (b - a) / δ ≤ (⌈(b - a) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hn_eq : (n : ℝ) = ⌈(b - a) / δ⌉₊ + 1 := by push_cast; ring
    rw [hn_eq]
    nlinarith [mul_le_mul_of_nonneg_right h_ceil hδ.le, Nat.cast_nonneg (⌈(b - a) / δ⌉₊)]
  have hab_step : a + n * step = b := by
    have : n * step = b - a := mul_div_cancel₀ _ hn_pos.ne'
    linarith
  -- Each piece has eVariationOn ≤ 1
  have hpieces : ∀ k : Fin n,
      eVariationOn f (Set.Icc (a + k.val * step) (a + (k.val + 1) * step)) ≤ 1 := by
    intro k
    apply eVariationOn_le_one_normed
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep_pos.le)
    · linarith [hstep_pos]
    · have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.isLt
      have : a + (k.val + 1) * step ≤ a + n * step := by nlinarith [hstep_pos.le]
      linarith [hab_step]
    · exact hδ
    · ring_nf; exact hstep_lt
    · exact hac
  -- Total variation ≤ n < ⊤
  show eVariationOn f (Set.Icc a b) ≠ ⊤
  rw [← hab_step]
  exact ne_top_of_le_ne_top ENNReal.natCast_ne_top
    (eVariationOn_le_n_normed a step hstep_pos n hpieces)

/-- Bounded variation (non-top eVariation) from normed-AC: explicit formulation. -/
theorem normed_bv_ne_top {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnNormed f a b) :
    eVariationOn f (Set.Icc a b) ≠ ⊤ :=
  normed_ac_implies_bv hab hf

end FTCNormedAC
