import Mathlib

/-
# Equality Condition for Strong Subadditivity of Shannon Entropy

## What This Proves

Strong subadditivity (SSA) of Shannon entropy states

  H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z).

This file pins down exactly *when equality holds*. The SSA deficit equals the
conditional mutual information

  I(X;Z|Y) = H(X,Y) + H(Y,Z) − H(X,Y,Z) − H(Y) ≥ 0,

and `I(X;Z|Y) = 0` precisely when `X` and `Z` are conditionally independent
given `Y` — i.e. `X – Y – Z` is a Markov chain:

  p(x,y,z) · p_Y(y) = p_{XY}(x,y) · p_{YZ}(y,z)   for all x, y, z.

This is the sharp boundary of SSA: the inequality is an equality iff the joint
distribution factors through `Y`.

## Proof Strategy

1. `ssa_deficit_eq_cmi`: an entropy-algebra identity rewriting the SSA deficit
   as the relative-entropy sum
     cmiSum = Σ_{x,y,z} p(x,y,z) · log( p(x,y,z) · p_Y(y)
                                        / (p_{XY}(x,y) · p_{YZ}(y,z)) ).
2. `ssa_cmi_eq_zero_iff`: `cmiSum = 0 ↔ factorization`. With
   q(x,y,z) = p_{XY}(x,y)·p_{YZ}(y,z)/p_Y(y) the summand is `p·log(p/q)`, a
   relative entropy whose nonnegativity is strict unless `p = q` (the strict KL
   bound). Equality forces `p = q` everywhere — the Markov factorization.
3. `strong_subadditivity_eq_iff`: combine the two.

## Mathlib Dependencies

Self-contained: imports only Mathlib. The Shannon entropy, three-variable
marginals, marginal telescoping helper, and the strict/non-strict pointwise KL
bounds are all reproduced here.
-/

namespace InformationTheory

open Finset

-- ═══════════════════════════════════════════════════════════════
-- Shannon entropy and three-variable marginals (self-contained)
-- ═══════════════════════════════════════════════════════════════

/-- Shannon entropy `H(p) = -∑ p(x) log p(x)`, with `0 log 0 = 0`. -/
noncomputable def shannonEntropy' {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

/-- Marginal on `(X,Y)`: `p_{XY}(x,y) = ∑_z p(x,y,z)`. -/
noncomputable def marginalXY {α β γ : Type*} [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : α × β → ℝ :=
  fun ⟨x, y⟩ => ∑ z : γ, pXYZ (x, y, z)

/-- Marginal on `(Y,Z)`: `p_{YZ}(y,z) = ∑_x p(x,y,z)`. -/
noncomputable def marginalYZ {α β γ : Type*} [Fintype α]
    (pXYZ : α × β × γ → ℝ) : β × γ → ℝ :=
  fun ⟨y, z⟩ => ∑ x : α, pXYZ (x, y, z)

/-- Marginal on `Y`: `p_Y(y) = ∑_x ∑_z p(x,y,z)`. -/
noncomputable def marginalY_3 {α β γ : Type*} [Fintype α] [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : β → ℝ :=
  fun y => ∑ x : α, ∑ z : γ, pXYZ (x, y, z)

-- ═══════════════════════════════════════════════════════════════
-- Marginal telescoping and pointwise KL bounds (helpers)
-- ═══════════════════════════════════════════════════════════════

/-- `S log S = Σ_i a_i · log S` over the support, where `S = ∑ a_i`. -/
private lemma marginal_telescope {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (if (∑ i, a i) = 0 then (0 : ℝ) else (∑ i, a i) * Real.log (∑ i, a i)) =
    ∑ i, (if a i = 0 then 0 else a i * Real.log (∑ j, a j)) := by
  by_cases hs : (∑ i, a i) = 0
  · have h0 : ∀ i, a i = 0 := fun i =>
      le_antisymm (by linarith [Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)]) (ha i)
    simp [h0]
  · simp only [hs, ↓reduceIte]; symm
    rw [show ∑ i, (if a i = 0 then (0 : ℝ) else a i * Real.log (∑ j, a j)) =
        ∑ i, a i * Real.log (∑ j, a j) from
      Finset.sum_congr rfl fun i _ => by by_cases h : a i = 0 <;> simp [h]]
    rw [← Finset.sum_mul]

private lemma rlog_lt_sub_one {y : ℝ} (hy : 0 < y) (hne : y ≠ 1) :
    Real.log y < y - 1 := by
  have hlog_ne : Real.log y ≠ 0 := by
    intro h; apply hne; rw [← Real.exp_log hy, h, Real.exp_zero]
  have hexp := Real.add_one_lt_exp hlog_ne
  rw [Real.exp_log hy] at hexp
  linarith

private lemma kl_lb {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have hlog : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq), Real.log_div (ne_of_gt hq) (ne_of_gt hp)]; ring
  have hmul : p * Real.log (q / p) ≤ p * (q / p - 1) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
  have heq : p * (q / p - 1) = q - p := by field_simp
  rw [hlog, mul_neg]; linarith [hmul, heq]

private lemma kl_lb_strict {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) :
    p - q < p * Real.log (p / q) := by
  have hqp_ne_one : q / p ≠ 1 := by
    intro h; field_simp at h; exact hne h.symm
  have h1 : Real.log (q / p) < q / p - 1 := rlog_lt_sub_one (div_pos hq hp) hqp_ne_one
  have hlog : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq), Real.log_div (ne_of_gt hq) (ne_of_gt hp)]; ring
  have hmul : p * Real.log (q / p) < p * (q / p - 1) := mul_lt_mul_of_pos_left h1 hp
  have heq : p * (q / p - 1) = q - p := by field_simp
  rw [hlog, mul_neg]; linarith [hmul, heq]

-- ═══════════════════════════════════════════════════════════════
-- The conditional mutual information sum
-- ═══════════════════════════════════════════════════════════════

/-- The conditional mutual information `I(X;Z|Y)` written as a relative-entropy
    sum, with the convention that a zero-probability term contributes `0`. -/
noncomputable def cmiSum {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : ℝ :=
  ∑ x : α, ∑ y : β, ∑ z : γ,
    (if pXYZ (x, y, z) = 0 then (0 : ℝ)
     else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) *
       (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) /
       ((∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z)))))

-- ═══════════════════════════════════════════════════════════════
-- PART I: The SSA deficit equals the conditional mutual information
-- ═══════════════════════════════════════════════════════════════

/-- **Deficit = conditional mutual information.** -/
theorem ssa_deficit_eq_cmi {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz) :
    shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ)
      - shannonEntropy' pXYZ - shannonEntropy' (marginalY_3 pXYZ)
    = cmiSum pXYZ := by
  have hXY : ∀ x y, (if (∑ z : γ, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ z, pXYZ (x, y, z)) * Real.log (∑ z, pXYZ (x, y, z))) =
      ∑ z : γ, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ z' : γ, pXYZ (x, y, z'))) := by
    intro x y; exact marginal_telescope (fun z => pXYZ (x, y, z)) (fun z => hp (x, y, z))
  have hYZ : ∀ y z, (if (∑ x : α, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ x, pXYZ (x, y, z)) * Real.log (∑ x, pXYZ (x, y, z))) =
      ∑ x : α, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) := by
    intro y z; exact marginal_telescope (fun x => pXYZ (x, y, z)) (fun x => hp (x, y, z))
  have hY : ∀ y, (if (∑ x : α, ∑ z : γ, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ x, ∑ z, pXYZ (x, y, z)) * Real.log (∑ x, ∑ z, pXYZ (x, y, z))) =
      ∑ x : α, ∑ z : γ, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z'))) := by
    intro y
    have h := marginal_telescope (fun (xz : α × γ) => pXYZ (xz.1, y, xz.2))
      (fun (xz : α × γ) => hp (xz.1, y, xz.2))
    simp_rw [Fintype.sum_prod_type] at h; exact h
  have hterm : ∀ x y z,
      (if pXYZ (x, y, z) = 0 then (0 : ℝ) else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z))) =
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) *
         (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) /
         ((∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))))) +
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (∑ z' : γ, pXYZ (x, y, z'))) +
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) -
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z'))) := by
    intro x y z
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · simp [hpxyz]
    · simp only [hpxyz, ↓reduceIte]
      have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
      have hpXY : 0 < ∑ z', pXYZ (x, y, z') :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z))
      have hpYZ : 0 < ∑ x', pXYZ (x', y, z) :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp (x', y, z)) (Finset.mem_univ x))
      have hpY : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
        lt_of_lt_of_le hpXY (Finset.single_le_sum
          (fun x' _ => Finset.sum_nonneg fun z' _ => hp (x', y, z')) (Finset.mem_univ x))
      have hlog : Real.log (pXYZ (x, y, z)) =
          Real.log (pXYZ (x, y, z) * (∑ x', ∑ z', pXYZ (x', y, z')) /
            ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z)))) +
          Real.log (∑ z', pXYZ (x, y, z')) +
          Real.log (∑ x', pXYZ (x', y, z)) -
          Real.log (∑ x', ∑ z', pXYZ (x', y, z')) := by
        rw [Real.log_div (ne_of_gt (mul_pos hpos hpY)) (ne_of_gt (mul_pos hpXY hpYZ)),
            Real.log_mul (ne_of_gt hpos) (ne_of_gt hpY),
            Real.log_mul (ne_of_gt hpXY) (ne_of_gt hpYZ)]
        ring
      rw [hlog]; ring
  have hHXY : shannonEntropy' (marginalXY pXYZ) =
      -∑ x : α, ∑ y : β, ∑ z : γ, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
        else pXYZ (x, y, z) * Real.log (∑ z' : γ, pXYZ (x, y, z'))) := by
    unfold shannonEntropy' marginalXY
    congr 1
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hXY x y))
  have hHYZ : shannonEntropy' (marginalYZ pXYZ) =
      -∑ x : α, ∑ y : β, ∑ z : γ, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
        else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) := by
    unfold shannonEntropy' marginalYZ
    congr 1
    rw [Fintype.sum_prod_type]
    rw [show (∑ y : β, ∑ z : γ, (if (∑ x : α, pXYZ (x, y, z)) = 0 then (0 : ℝ)
          else (∑ x, pXYZ (x, y, z)) * Real.log (∑ x, pXYZ (x, y, z))))
        = ∑ y : β, ∑ z : γ, ∑ x : α, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
          else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) from
      Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => hYZ y z))]
    rw [show (∑ y : β, ∑ z : γ, ∑ x : α, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
          else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))))
        = ∑ y : β, ∑ x : α, ∑ z : γ, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
          else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) from
      Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
  have hHXYZ : shannonEntropy' pXYZ =
      -∑ x : α, ∑ y : β, ∑ z : γ, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
        else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z))) := by
    unfold shannonEntropy'
    congr 1
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
  have hHY : shannonEntropy' (marginalY_3 pXYZ) =
      -∑ x : α, ∑ y : β, ∑ z : γ, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
        else pXYZ (x, y, z) * Real.log (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z'))) := by
    unfold shannonEntropy' marginalY_3
    congr 1
    rw [show (∑ y : β, (if (∑ x : α, ∑ z : γ, pXYZ (x, y, z)) = 0 then (0 : ℝ)
          else (∑ x, ∑ z, pXYZ (x, y, z)) * Real.log (∑ x, ∑ z, pXYZ (x, y, z))))
        = ∑ y : β, ∑ x : α, ∑ z : γ, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
          else pXYZ (x, y, z) * Real.log (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z'))) from
      Finset.sum_congr rfl (fun y _ => hY y)]
    rw [Finset.sum_comm]
  rw [hHXY, hHYZ, hHXYZ, hHY]
  unfold cmiSum
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

-- ═══════════════════════════════════════════════════════════════
-- PART II: CMI vanishes iff the Markov factorization holds
-- ═══════════════════════════════════════════════════════════════

/-- **Vanishing of conditional mutual information.**
    `I(X;Z|Y) = 0` iff `X – Y – Z` is a Markov chain, in division-free form. -/
theorem ssa_cmi_eq_zero_iff {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    cmiSum pXYZ = 0 ↔
    ∀ x y z, pXYZ (x, y, z) * marginalY_3 pXYZ y
      = marginalXY pXYZ (x, y) * marginalYZ pXYZ (y, z) := by
  have hsum_n : ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) = 1 := by
    have h := hsum; rw [Fintype.sum_prod_type] at h; simp_rw [Fintype.sum_prod_type] at h; exact h
  set q := fun x y z => (∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z)) /
    (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) with hq_def
  have hq_nn : ∀ x y z, 0 ≤ q x y z := fun x y z => by
    simp only [hq_def]
    exact div_nonneg
      (mul_nonneg (Finset.sum_nonneg fun z' _ => hp _) (Finset.sum_nonneg fun x' _ => hp _))
      (Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun z' _ => hp _)
  -- positivity of marginals at a support point
  have hmarg_pos : ∀ x y z, pXYZ (x, y, z) ≠ 0 →
      0 < (∑ z' : γ, pXYZ (x, y, z')) ∧ 0 < (∑ x' : α, pXYZ (x', y, z)) ∧
      0 < (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) := by
    intro x y z hne
    have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hne)
    have hpXY : 0 < ∑ z', pXYZ (x, y, z') :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z))
    have hpYZ : 0 < ∑ x', pXYZ (x', y, z) :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp (x', y, z)) (Finset.mem_univ x))
    have hpY : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
      lt_of_lt_of_le hpXY (Finset.single_le_sum
        (fun x' _ => Finset.sum_nonneg fun z' _ => hp (x', y, z')) (Finset.mem_univ x))
    exact ⟨hpXY, hpYZ, hpY⟩
  have hq_pos_of : ∀ x y z, pXYZ (x, y, z) ≠ 0 → 0 < q x y z := by
    intro x y z hne
    obtain ⟨hpXY, hpYZ, hpY⟩ := hmarg_pos x y z hne
    simp only [hq_def]; exact div_pos (mul_pos hpXY hpYZ) hpY
  have hq_sum_y : ∀ y, ∑ x : α, ∑ z : γ, q x y z = ∑ x, ∑ z, pXYZ (x, y, z) := by
    intro y
    simp only [hq_def]
    by_cases hpy : (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) = 0
    · have hall : ∀ x z, pXYZ (x, y, z) = 0 := by
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x _ => Finset.sum_nonneg fun z _ => hp (x, y, z))).mp hpy
        intro x z
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun z _ => hp (x, y, z))).mp (h2 x (Finset.mem_univ x)) z (Finset.mem_univ z)
      simp [hall]
    · have hD : (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) ≠ 0 := hpy
      have step1 : ∀ x : α, (∑ z : γ,
            (∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))
              / (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')))
          = (∑ z' : γ, pXYZ (x, y, z')) * (∑ z : γ, ∑ x' : α, pXYZ (x', y, z))
              / (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) := by
        intro x
        rw [← Finset.sum_div, ← Finset.mul_sum]
      simp_rw [step1]
      rw [← Finset.sum_div, ← Finset.sum_mul]
      rw [show (∑ z : γ, ∑ x' : α, pXYZ (x', y, z)) = ∑ x' : α, ∑ z : γ, pXYZ (x', y, z) from
        Finset.sum_comm]
      rw [mul_div_assoc, div_self hD, mul_one]
  have hq_sum : ∑ x : α, ∑ y : β, ∑ z : γ, q x y z = 1 := by
    conv_lhs => rw [Finset.sum_comm]
    simp_rw [hq_sum_y]
    rw [Finset.sum_comm]; exact hsum_n
  -- Rewrite cmiSum's summand into relative-entropy `p · log(p / q)` form.
  have hcmi_q : cmiSum pXYZ = ∑ x : α, ∑ y : β, ∑ z : γ,
      (if pXYZ (x, y, z) = 0 then (0 : ℝ)
       else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z)) := by
    unfold cmiSum
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
      (fun y _ => Finset.sum_congr rfl (fun z _ => ?_)))
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · simp [hpxyz]
    · rw [if_neg hpxyz, if_neg hpxyz]
      obtain ⟨hpXY, hpYZ, hpY⟩ := hmarg_pos x y z hpxyz
      have hlog_eq : pXYZ (x, y, z) * (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) /
          ((∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))) =
          pXYZ (x, y, z) / q x y z := by
        simp only [hq_def]
        field_simp
      rw [hlog_eq]
  rw [hcmi_q]
  constructor
  · -- Forward: cmiSum = 0 → factorization.
    intro hS
    have hbound : ∀ x y z, pXYZ (x, y, z) - q x y z ≤
        (if pXYZ (x, y, z) = 0 then (0 : ℝ)
         else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z)) := by
      intro x y z
      by_cases hpxyz : pXYZ (x, y, z) = 0
      · rw [if_pos hpxyz]; have := hq_nn x y z; linarith
      · rw [if_neg hpxyz]
        have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
        exact kl_lb hpos (hq_pos_of x y z hpxyz)
    have hFge : ∀ x y z, 0 ≤
        (if pXYZ (x, y, z) = 0 then (0 : ℝ)
         else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z))
        - (pXYZ (x, y, z) - q x y z) := fun x y z => by linarith [hbound x y z]
    have hsumFge : ∑ x : α, ∑ y : β, ∑ z : γ,
        ((if pXYZ (x, y, z) = 0 then (0 : ℝ)
          else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z))
         - (pXYZ (x, y, z) - q x y z)) = 0 := by
      simp only [Finset.sum_sub_distrib]
      rw [hS, hsum_n, hq_sum]; ring
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun z _ =>
        hFge x y z)).mp hsumFge
    have hFeq : ∀ x y z,
        (if pXYZ (x, y, z) = 0 then (0 : ℝ)
         else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z))
        - (pXYZ (x, y, z) - q x y z) = 0 := by
      intro x y z
      have hx := h1 x (Finset.mem_univ x)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => Finset.sum_nonneg fun z _ => hFge x y z)).mp hx
      have hy := h2 y (Finset.mem_univ y)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => hFge x y z)).mp hy
      exact h3 z (Finset.mem_univ z)
    have hpeqq : ∀ x y z, pXYZ (x, y, z) = q x y z := by
      intro x y z
      have hf := hFeq x y z
      by_cases hpxyz : pXYZ (x, y, z) = 0
      · rw [if_pos hpxyz] at hf; linarith
      · rw [if_neg hpxyz] at hf
        have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
        have hqpos := hq_pos_of x y z hpxyz
        by_contra hne
        have := kl_lb_strict hpos hqpos hne
        linarith
    intro x y z
    simp only [marginalY_3, marginalXY, marginalYZ]
    by_cases hpy : (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) = 0
    · have hp0 : pXYZ (x, y, z) = 0 := by
        have hle : pXYZ (x, y, z) ≤ ∑ x', ∑ z', pXYZ (x', y, z') :=
          le_trans (Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z))
            (Finset.single_le_sum (fun x' _ => Finset.sum_nonneg fun z' _ => hp (x', y, z'))
              (Finset.mem_univ x))
        linarith [hp (x, y, z)]
      have hpXY0 : (∑ z' : γ, pXYZ (x, y, z')) = 0 := by
        apply Finset.sum_eq_zero; intro z' _
        have hle : pXYZ (x, y, z') ≤ ∑ x', ∑ z', pXYZ (x', y, z') :=
          le_trans (Finset.single_le_sum (fun z'' _ => hp (x, y, z'')) (Finset.mem_univ z'))
            (Finset.single_le_sum (fun x' _ => Finset.sum_nonneg fun z'' _ => hp (x', y, z''))
              (Finset.mem_univ x))
        linarith [hp (x, y, z')]
      rw [hpy, hp0, hpXY0]; ring
    · have hpY_pos : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
        lt_of_le_of_ne
          (Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun z' _ => hp (x', y, z'))
          (Ne.symm hpy)
      rw [hpeqq x y z]
      simp only [hq_def]
      field_simp
  · -- Backward: factorization → cmiSum = 0.
    intro hfac
    apply Finset.sum_eq_zero; intro x _
    apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro z _
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · rw [if_pos hpxyz]
    · rw [if_neg hpxyz]
      have hqpos := hq_pos_of x y z hpxyz
      obtain ⟨_, _, hpY_pos⟩ := hmarg_pos x y z hpxyz
      have hpq : pXYZ (x, y, z) = q x y z := by
        have hf := hfac x y z
        simp only [marginalY_3, marginalXY, marginalYZ] at hf
        simp only [hq_def]
        rw [eq_div_iff hpY_pos.ne']
        linarith [hf]
      rw [hpq, div_self hqpos.ne', Real.log_one, mul_zero]

-- ═══════════════════════════════════════════════════════════════
-- PART III: Equality condition for strong subadditivity
-- ═══════════════════════════════════════════════════════════════

/-- **Equality condition for strong subadditivity.**
    `H(X,Y,Z) + H(Y) = H(X,Y) + H(Y,Z)` holds iff `X – Y – Z` is a Markov chain
    (conditional independence of `X` and `Z` given `Y`):
      p(x,y,z) · p_Y(y) = p_{XY}(x,y) · p_{YZ}(y,z)   for all x, y, z. -/
theorem strong_subadditivity_eq_iff {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    (shannonEntropy' pXYZ + shannonEntropy' (marginalY_3 pXYZ)
      = shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ))
    ↔ (∀ x y z, pXYZ (x, y, z) * marginalY_3 pXYZ y
        = marginalXY pXYZ (x, y) * marginalYZ pXYZ (y, z)) := by
  rw [← ssa_cmi_eq_zero_iff hp hsum]
  have hdef := ssa_deficit_eq_cmi (pXYZ := pXYZ) hp
  constructor
  · intro heq; linear_combination -hdef - heq
  · intro hcmi; linear_combination -hdef - hcmi

-- ═══════════════════════════════════════════════════════════════
-- PART IV: Strong subadditivity itself (the inequality), self-contained
-- ═══════════════════════════════════════════════════════════════

/-- **The conditional mutual information is nonnegative: `0 ≤ cmiSum pXYZ`.**
    Equivalently `I(X;Z|Y) ≥ 0`.  This is the SSA *inequality* in relative-entropy
    form, and it needs only `pXYZ ≥ 0` — no normalization `∑ p = 1`.  The proof is the
    Gibbs/KL bound termwise (`p log(p/q) ≥ p − q`) summed against the reference
    kernel `q = p_{XY} p_{YZ} / p_Y`, whose per-`y` mass matches that of `p`
    (`∑_{x,z} q = ∑_{x,z} p`), so the linear lower bound telescopes to `0`. -/
theorem cmiSum_nonneg {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz) :
    0 ≤ cmiSum pXYZ := by
  set q := fun x y z => (∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z)) /
    (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) with hq_def
  have hq_nn : ∀ x y z, 0 ≤ q x y z := fun x y z => by
    simp only [hq_def]
    exact div_nonneg
      (mul_nonneg (Finset.sum_nonneg fun z' _ => hp _) (Finset.sum_nonneg fun x' _ => hp _))
      (Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun z' _ => hp _)
  have hmarg_pos : ∀ x y z, pXYZ (x, y, z) ≠ 0 →
      0 < (∑ z' : γ, pXYZ (x, y, z')) ∧ 0 < (∑ x' : α, pXYZ (x', y, z)) ∧
      0 < (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) := by
    intro x y z hne
    have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hne)
    have hpXY : 0 < ∑ z', pXYZ (x, y, z') :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z))
    have hpYZ : 0 < ∑ x', pXYZ (x', y, z) :=
      lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp (x', y, z)) (Finset.mem_univ x))
    have hpY : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
      lt_of_lt_of_le hpXY (Finset.single_le_sum
        (fun x' _ => Finset.sum_nonneg fun z' _ => hp (x', y, z')) (Finset.mem_univ x))
    exact ⟨hpXY, hpYZ, hpY⟩
  have hq_pos_of : ∀ x y z, pXYZ (x, y, z) ≠ 0 → 0 < q x y z := by
    intro x y z hne
    obtain ⟨hpXY, hpYZ, hpY⟩ := hmarg_pos x y z hne
    simp only [hq_def]; exact div_pos (mul_pos hpXY hpYZ) hpY
  have hq_sum_y : ∀ y, ∑ x : α, ∑ z : γ, q x y z = ∑ x, ∑ z, pXYZ (x, y, z) := by
    intro y
    simp only [hq_def]
    by_cases hpy : (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) = 0
    · have hall : ∀ x z, pXYZ (x, y, z) = 0 := by
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x _ => Finset.sum_nonneg fun z _ => hp (x, y, z))).mp hpy
        intro x z
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun z _ => hp (x, y, z))).mp (h2 x (Finset.mem_univ x)) z (Finset.mem_univ z)
      simp [hall]
    · have hD : (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) ≠ 0 := hpy
      have step1 : ∀ x : α, (∑ z : γ,
            (∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))
              / (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')))
          = (∑ z' : γ, pXYZ (x, y, z')) * (∑ z : γ, ∑ x' : α, pXYZ (x', y, z))
              / (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) := by
        intro x
        rw [← Finset.sum_div, ← Finset.mul_sum]
      simp_rw [step1]
      rw [← Finset.sum_div, ← Finset.sum_mul]
      rw [show (∑ z : γ, ∑ x' : α, pXYZ (x', y, z)) = ∑ x' : α, ∑ z : γ, pXYZ (x', y, z) from
        Finset.sum_comm]
      rw [mul_div_assoc, div_self hD, mul_one]
  -- Rewrite cmiSum's summand into relative-entropy `p · log(p / q)` form.
  have hcmi_q : cmiSum pXYZ = ∑ x : α, ∑ y : β, ∑ z : γ,
      (if pXYZ (x, y, z) = 0 then (0 : ℝ)
       else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z)) := by
    unfold cmiSum
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
      (fun y _ => Finset.sum_congr rfl (fun z _ => ?_)))
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · simp [hpxyz]
    · rw [if_neg hpxyz, if_neg hpxyz]
      obtain ⟨hpXY, hpYZ, hpY⟩ := hmarg_pos x y z hpxyz
      have hlog_eq : pXYZ (x, y, z) * (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) /
          ((∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))) =
          pXYZ (x, y, z) / q x y z := by
        simp only [hq_def]
        field_simp
      rw [hlog_eq]
  rw [hcmi_q]
  -- Termwise Gibbs bound `p − q ≤ p log(p/q)` (with the zero convention).
  have hbound : ∀ x y z, pXYZ (x, y, z) - q x y z ≤
      (if pXYZ (x, y, z) = 0 then (0 : ℝ)
       else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z)) := by
    intro x y z
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · rw [if_pos hpxyz]; have := hq_nn x y z; linarith
    · rw [if_neg hpxyz]
      have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
      exact kl_lb hpos (hq_pos_of x y z hpxyz)
  -- The reference kernel has the same total mass as `p`, so `∑ (p − q) = 0`.
  have hq_eq_p : ∑ x : α, ∑ y : β, ∑ z : γ, q x y z
      = ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => hq_sum_y y
  have hsum_pq : ∑ x : α, ∑ y : β, ∑ z : γ, (pXYZ (x, y, z) - q x y z) = 0 := by
    simp only [Finset.sum_sub_distrib]
    linarith [hq_eq_p]
  calc (0 : ℝ) = ∑ x : α, ∑ y : β, ∑ z : γ, (pXYZ (x, y, z) - q x y z) := hsum_pq.symm
    _ ≤ ∑ x : α, ∑ y : β, ∑ z : γ,
          (if pXYZ (x, y, z) = 0 then (0 : ℝ)
           else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q x y z)) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        Finset.sum_le_sum fun z _ => hbound x y z

/-- **Strong subadditivity of Shannon entropy (the inequality), self-contained.**
    `H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)` for any nonnegative weight `pXYZ`.
    Combines `ssa_deficit_eq_cmi` (deficit = `I(X;Z|Y)`) with `cmiSum_nonneg`.  Unlike
    the version in the parent `ShannonEntropy.lean`, this needs no normalization and
    lives in the same self-contained file as the equality characterization. -/
theorem ssa_inequality {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz) :
    shannonEntropy' pXYZ + shannonEntropy' (marginalY_3 pXYZ)
      ≤ shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ) := by
  have hdef := ssa_deficit_eq_cmi (pXYZ := pXYZ) hp
  have hnn := cmiSum_nonneg (pXYZ := pXYZ) hp
  linarith

end InformationTheory
