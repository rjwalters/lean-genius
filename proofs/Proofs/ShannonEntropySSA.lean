import Mathlib
import Proofs.ShannonEntropy

/-
# Strong Subadditivity of Shannon Entropy

## What This Proves

Strong subadditivity (SSA) is the deepest inequality in Shannon information theory:

  H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)

This says: the total information in three variables, plus the information
in the "shared" variable Y, is at most the sum of the informations in the
two pairs (X,Y) and (Y,Z) that overlap in Y.

Equivalently: conditioning on more variables can only reduce entropy:
  H(X|Y,Z) ≤ H(X|Y)

Or: conditional mutual information is non-negative:
  I(X;Z|Y) = H(X|Y) - H(X|Y,Z) ≥ 0

## Proof Strategy

For each value y with p(y) > 0, the conditional distribution
p(x,z|y) = p(x,y,z)/p(y) is a valid joint distribution on α × γ.
Its mutual information I_y(X;Z) ≥ 0 by the already-proved
mutual_info_nonneg. The conditional MI is the weighted average:
  I(X;Z|Y) = Σ_y p(y) I_y(X;Z) ≥ 0

## Historical Note

SSA was conjectured by Lanford and Robinson (1968) and proved by
Lieb and Ruskai (1973) for quantum entropy. The classical (Shannon)
case is simpler and follows from properties of KL divergence.

## Mathlib Dependencies

Uses only the Shannon entropy infrastructure from ShannonEntropy.lean.
-/

namespace InformationTheory

open Finset

-- ═══════════════════════════════════════════════════════════════
-- PART I: Three-Variable Marginal Distributions
-- ═══════════════════════════════════════════════════════════════

-- Reproduce definitions for self-containment (same as ShannonEntropy.lean)
noncomputable def shannonEntropy' {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

/-- Marginal distribution on (X,Y) from a joint on (X,Y,Z):
    p_{XY}(x,y) = Σ_z p(x,y,z) -/
noncomputable def marginalXY {α β γ : Type*} [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : α × β → ℝ :=
  fun ⟨x, y⟩ => ∑ z : γ, pXYZ (x, y, z)

/-- Marginal distribution on (Y,Z) from a joint on (X,Y,Z):
    p_{YZ}(y,z) = Σ_x p(x,y,z) -/
noncomputable def marginalYZ {α β γ : Type*} [Fintype α]
    (pXYZ : α × β × γ → ℝ) : β × γ → ℝ :=
  fun ⟨y, z⟩ => ∑ x : α, pXYZ (x, y, z)

/-- Marginal distribution on Y from a joint on (X,Y,Z):
    p_Y(y) = Σ_x Σ_z p(x,y,z) -/
noncomputable def marginalY_3 {α β γ : Type*} [Fintype α] [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : β → ℝ :=
  fun y => ∑ x : α, ∑ z : γ, pXYZ (x, y, z)

-- ═══════════════════════════════════════════════════════════════
-- PART II: Marginal Properties
-- ═══════════════════════════════════════════════════════════════

/-- The XY-marginal preserves non-negativity. -/
theorem marginalXY_nonneg {α β γ : Type*} [Fintype γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz) :
    ∀ xy : α × β, 0 ≤ marginalXY pXYZ xy := by
  intro ⟨x, y⟩
  exact Finset.sum_nonneg fun z _ => hp (x, y, z)

/-- The YZ-marginal preserves non-negativity. -/
theorem marginalYZ_nonneg {α β γ : Type*} [Fintype α]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz) :
    ∀ yz : β × γ, 0 ≤ marginalYZ pXYZ yz := by
  intro ⟨y, z⟩
  exact Finset.sum_nonneg fun x _ => hp (x, y, z)

/-- The Y-marginal preserves non-negativity. -/
theorem marginalY_3_nonneg {α β γ : Type*} [Fintype α] [Fintype γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz) :
    ∀ y : β, 0 ≤ marginalY_3 pXYZ y := by
  intro y
  exact Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun z _ => hp (x, y, z)

/-- The XY-marginal sums to 1. -/
theorem marginalXY_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {pXYZ : α × β × γ → ℝ}
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    ∑ xy : α × β, marginalXY pXYZ xy = 1 := by
  unfold marginalXY
  simp only
  rw [show ∑ xy : α × β, ∑ z : γ, pXYZ (xy.1, xy.2, z) =
      ∑ xyz : α × β × γ, pXYZ xyz from by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 1; ext x; congr 1; ext y; rfl]
  exact hsum

/-- The YZ-marginal sums to 1. -/
theorem marginalYZ_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {pXYZ : α × β × γ → ℝ}
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    ∑ yz : β × γ, marginalYZ pXYZ yz = 1 := by
  unfold marginalYZ
  simp only
  rw [show ∑ yz : β × γ, ∑ x : α, pXYZ (x, yz.1, yz.2) =
      ∑ xyz : α × β × γ, pXYZ xyz from by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    congr 1; ext x
    rw [Fintype.sum_prod_type]]
  exact hsum

/-- The Y-marginal sums to 1. -/
theorem marginalY_3_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {pXYZ : α × β × γ → ℝ}
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    ∑ y : β, marginalY_3 pXYZ y = 1 := by
  unfold marginalY_3
  rw [show ∑ y : β, ∑ x : α, ∑ z : γ, pXYZ (x, y, z) =
      ∑ xyz : α × β × γ, pXYZ xyz from by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    congr 1; ext x; rfl]
  exact hsum

-- ═══════════════════════════════════════════════════════════════
-- PART III: Entropy Chain Rule for Pairs
-- ═══════════════════════════════════════════════════════════════

/-- The Y-marginal of a joint distribution on α × β. -/
noncomputable def marginalSnd {α β : Type*} [Fintype α]
    (pXY : α × β → ℝ) : β → ℝ :=
  fun y => ∑ x : α, pXY (x, y)

/-- Conditional entropy H(X|Y) from ShannonEntropy.lean, reproduced. -/
noncomputable def condEntropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) : ℝ :=
  -(∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y))))

/-- **Entropy Chain Rule**: H(X,Y) = H(Y) + H(X|Y)

    The joint entropy decomposes into the marginal entropy of Y
    plus the conditional entropy of X given Y.

    Proof: H(X,Y) = -Σ p(x,y) log p(x,y)
    H(Y) + H(X|Y) = -Σ p(y) log p(y) - Σ p(x,y) log(p(x,y)/p(y))

    Split the conditional term: p(x,y) log(p(x,y)/p(y))
    = p(x,y) [log p(x,y) - log p(y)]
    = p(x,y) log p(x,y) - p(x,y) log p(y)

    Summing over x: Σ_x p(x,y) log p(x,y) - p(y) log p(y)
    So -Σ_x Σ_y p(x,y) log(p(x,y)/p(y)) = H(X,Y) - H(Y)
    Thus H(Y) + H(X|Y) = H(Y) + H(X,Y) - H(Y) = H(X,Y). -/
theorem entropy_chain_rule {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    shannonEntropy' pXY =
    shannonEntropy' (marginalSnd pXY) + condEntropy pXY := by
  -- H(X,Y) = H(Y) + H(X|Y) by splitting log p(x,y) = log(p(x,y)/p_Y(y)) + log p_Y(y)
  -- Step 1: Term-by-term identity
  have hterm : ∀ x y,
      (if pXY (x, y) = 0 then (0 : ℝ) else pXY (x, y) * Real.log (pXY (x, y))) =
      (if pXY (x, y) = 0 then 0
       else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y)))) +
      (if pXY (x, y) = 0 then 0
       else pXY (x, y) * Real.log (∑ x' : α, pXY (x', y))) := by
    intro x y
    by_cases hpxy : pXY (x, y) = 0
    · simp [hpxy]
    · simp only [hpxy, ↓reduceIte]
      have hpxy_pos : 0 < pXY (x, y) := lt_of_le_of_ne (hp (x, y)) (Ne.symm hpxy)
      have hpy_pos : 0 < ∑ x' : α, pXY (x', y) :=
        lt_of_lt_of_le hpxy_pos
          (Finset.single_le_sum (fun x' _ => hp (x', y)) (Finset.mem_univ x))
      rw [show pXY (x, y) * Real.log (pXY (x, y) / (∑ x', pXY (x', y))) +
          pXY (x, y) * Real.log (∑ x', pXY (x', y)) =
          pXY (x, y) * (Real.log (pXY (x, y) / (∑ x', pXY (x', y))) +
          Real.log (∑ x', pXY (x', y))) from by ring]
      congr 1
      rw [Real.log_div (ne_of_gt hpxy_pos) (ne_of_gt hpy_pos)]
      ring
  -- Step 2: Marginal telescoping
  have hmarg : ∀ y,
      ∑ x : α, (if pXY (x, y) = 0 then (0 : ℝ)
        else pXY (x, y) * Real.log (∑ x' : α, pXY (x', y))) =
      (if (∑ x : α, pXY (x, y)) = 0 then 0
       else (∑ x : α, pXY (x, y)) * Real.log (∑ x : α, pXY (x, y))) := by
    intro y
    by_cases hpy : (∑ x : α, pXY (x, y)) = 0
    · have hall : ∀ x, pXY (x, y) = 0 := by
        intro x; have h1 := hp (x, y)
        have h2 : pXY (x, y) ≤ ∑ x', pXY (x', y) :=
          Finset.single_le_sum (fun x' _ => hp (x', y)) (Finset.mem_univ x)
        linarith
      simp [hpy, hall]
    · simp only [hpy, ↓reduceIte]
      have : ∑ x : α, (if pXY (x, y) = 0 then (0 : ℝ)
          else pXY (x, y) * Real.log (∑ x' : α, pXY (x', y))) =
          ∑ x : α, pXY (x, y) * Real.log (∑ x' : α, pXY (x', y)) := by
        apply Finset.sum_congr rfl; intro x _
        by_cases hpxy : pXY (x, y) = 0
        · simp [hpxy]
        · simp [hpxy]
      rw [this, ← Finset.sum_mul]
  -- Step 3: Assembly
  unfold shannonEntropy' condEntropy marginalSnd
  dsimp only
  -- Convert product-type sum to nested sum
  conv_lhs =>
    rw [show ∑ xy : α × β, (if pXY xy = 0 then (0 : ℝ)
        else pXY xy * Real.log (pXY xy)) =
        ∑ x : α, ∑ y : β, (if pXY (x, y) = 0 then 0
        else pXY (x, y) * Real.log (pXY (x, y))) from Fintype.sum_prod_type _]
  -- Apply the term splitting and distribute sums
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  -- Swap sum order and apply marginal telescoping
  rw [show ∑ x : α, ∑ y : β, (if pXY (x, y) = 0 then (0 : ℝ) else
      pXY (x, y) * Real.log (∑ x', pXY (x', y))) =
      ∑ y : β, (if (∑ x, pXY (x, y)) = 0 then 0 else
      (∑ x, pXY (x, y)) * Real.log (∑ x, pXY (x, y))) from by
    rw [Finset.sum_comm]; congr 1; ext y; exact hmarg y]
  ring

-- ═══════════════════════════════════════════════════════════════
-- PART IV: Subadditivity from Chain Rule
-- ═══════════════════════════════════════════════════════════════

/-- **Subadditivity**: H(X,Y) ≤ H(X) + H(Y)

    Proof: H(X,Y) = H(Y) + H(X|Y) ≤ H(Y) + H(X)
    since conditioning reduces entropy: H(X|Y) ≤ H(X). -/
theorem subadditivity {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    shannonEntropy' pXY ≤
    shannonEntropy' (fun x => ∑ y : β, pXY (x, y)) +
    shannonEntropy' (marginalSnd pXY) := by
  -- From chain rule: H(X,Y) = H(Y) + H(X|Y)
  -- From conditioning reduces entropy: H(X|Y) ≤ H(X)
  -- Combined: H(X,Y) ≤ H(Y) + H(X) = H(X) + H(Y)
  rw [entropy_chain_rule hp hsum]
  -- Goal: H(Y) + H(X|Y) ≤ H(X) + H(Y)
  -- shannonEntropy' = shannonEntropy and condEntropy = conditionalEntropy by def
  -- Use conditioning_reduces_entropy from ShannonEntropy.lean
  have hcond : condEntropy pXY ≤ shannonEntropy' (fun x => ∑ y : β, pXY (x, y)) := by
    -- condEntropy and conditionalEntropy are definitionally equal, as are shannonEntropy' and shannonEntropy
    exact conditioning_reduces_entropy hp hsum
  linarith

-- ═══════════════════════════════════════════════════════════════
-- PART V: Strong Subadditivity
-- ═══════════════════════════════════════════════════════════════

/-- **Strong Subadditivity** (Lieb-Ruskai 1973):
    H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)

    Equivalent formulations:
    - I(X;Z|Y) ≥ 0 (conditional MI non-negative)
    - H(X|Y,Z) ≤ H(X|Y) (conditioning on more reduces entropy)
    - H(X|Y) + H(Z|Y) ≥ H(X,Z|Y) (subadditivity conditioned on Y)

    Proof: The deficit H(X,Y) + H(Y,Z) - H(X,Y,Z) - H(Y)
    equals the conditional mutual information I(X;Z|Y),
    which is a weighted average of MI values:
      I(X;Z|Y) = Σ_y p(y) D(p(x,z|y) || p(x|y)p(z|y))
    Each term is ≥ 0 by non-negativity of KL divergence.

    This is the deepest inequality in classical information theory.
    The quantum version (von Neumann entropy) was proved by Lieb
    and Ruskai using the concavity of the trace function. -/
theorem strong_subadditivity {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy' pXYZ + shannonEntropy' (marginalY_3 pXYZ) ≤
    shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ) := by
  -- Proof: I(X;Z|Y) = H(XY)+H(YZ)-H(XYZ)-H(Y) ≥ 0.
  -- Define q(x,y,z)=pXY(x,y)*pYZ(y,z)/pY(y). Apply kl_term_bound' pointwise,
  -- sum to get Σ(pXYZ-q)=0, then connect KL sum to entropy deficit via lifting.
  suffices h : shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ) -
      shannonEntropy' pXYZ - shannonEntropy' (marginalY_3 pXYZ) ≥ 0 by linarith
  -- Abbreviate marginals
  set pXY' : α × β → ℝ := marginalXY pXYZ
  set pYZ' : β × γ → ℝ := marginalYZ pXYZ
  set pY' : β → ℝ := marginalY_3 pXYZ
  -- Nested-sum form of hsum
  have hsum_n : ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) = 1 := by
    have h := hsum; rw [Fintype.sum_prod_type] at h; simp_rw [Fintype.sum_prod_type] at h; exact h
  -- Non-negativity and sum-to-1 for marginals (already proved as theorems above)
  have hpXY_nn : ∀ xy, 0 ≤ pXY' xy := marginalXY_nonneg hp
  have hpYZ_nn : ∀ yz, 0 ≤ pYZ' yz := marginalYZ_nonneg hp
  have hpY_nn : ∀ y, 0 ≤ pY' y := marginalY_3_nonneg hp
  -- (if p=0 then 0 else p*log p) = p*log p (since Real.log 0 = 0)
  have hite : ∀ p : ℝ, (if p = 0 then (0 : ℝ) else p * Real.log p) = p * Real.log p := by
    intro p; by_cases hp0 : p = 0 <;> simp [hp0]
  -- Simplified entropy: shannonEntropy' f = -Σ f * log f
  have hent : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ),
      shannonEntropy' f = -∑ i, f i * Real.log (f i) := by
    intros; unfold shannonEntropy'; congr 1; apply Finset.sum_congr rfl
    intro i _; exact hite (f i)
  -- Reference distribution q(x,y,z) = pXY(x,y)*pYZ(y,z)/pY(y)
  set q : α × β × γ → ℝ := fun ⟨x, y, z⟩ =>
    pXY' (x, y) * pYZ' (y, z) / pY' y
  have hq_nn : ∀ xyz, 0 ≤ q xyz := fun ⟨x, y, z⟩ =>
    div_nonneg (mul_nonneg (hpXY_nn (x, y)) (hpYZ_nn (y, z))) (hpY_nn y)
  -- Σ_xyz q = 1
  have hq_sum : ∑ xyz : α × β × γ, q xyz = 1 := by
    -- Each inner sum Σ_x Σ_z q(x,y,z) = pY'(y), then Σ_y pY'(y) = 1
    suffices h_inner : ∀ y : β, ∑ x : α, ∑ z : γ, q (x, y, z) = pY' y by
      rw [show ∑ xyz : α × β × γ, q xyz = ∑ y : β, ∑ x : α, ∑ z : γ, q (x, y, z) from by
        rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rw [Finset.sum_comm]]
      simp_rw [h_inner]; exact marginalY_3_sum hsum
    intro y
    simp only [q]
    by_cases hpy : pY' y = 0
    · -- pY'(y) = 0: denominator is 0, so all terms are a/0 = 0
      simp [hpy]
    · -- pY'(y) > 0: factor (Σ_x pXY)*(Σ_z pYZ)/pY = pY*pY/pY = pY
      have hpY_pos : 0 < pY' y := lt_of_le_of_ne (hpY_nn y) (Ne.symm hpy)
      have hfactor : ∑ x : α, ∑ z : γ, pXY' (x, y) * pYZ' (y, z) / pY' y =
          (∑ x : α, pXY' (x, y)) * (∑ z : γ, pYZ' (y, z)) / pY' y := by
        simp_rw [mul_div_assoc, ← Finset.mul_sum, Finset.sum_div]
        rw [← Finset.sum_mul, ← mul_div_assoc]
      rw [hfactor]
      have hXY_y : ∑ x : α, pXY' (x, y) = pY' y := by
        simp only [pXY', pY', marginalXY, marginalY_3]
      have hYZ_y : ∑ z : γ, pYZ' (y, z) = pY' y := by
        simp only [pYZ', pY', marginalYZ, marginalY_3]
        exact Finset.sum_comm
      rw [hXY_y, hYZ_y, mul_div_cancel₀ _ hpY_pos.ne']
  -- KL sum ≥ 0 via kl_term_bound'
  have h_kl : 0 ≤ ∑ xyz : α × β × γ,
      (if pXYZ xyz = 0 then (0 : ℝ) else pXYZ xyz * Real.log (pXYZ xyz / q xyz)) := by
    suffices h_lb : ∑ xyz, (pXYZ xyz - q xyz) ≤
        ∑ xyz, if pXYZ xyz = 0 then 0 else pXYZ xyz * Real.log (pXYZ xyz / q xyz) by
      have hzero : ∑ xyz : α × β × γ, (pXYZ xyz - q xyz) = 0 := by
        rw [Finset.sum_sub_distrib, hsum, hq_sum, sub_self]
      linarith
    apply Finset.sum_le_sum; intro ⟨x, y, z⟩ _
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · simp [hpxyz]; exact hq_nn _
    · simp only [hpxyz, ↓reduceIte]
      have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
      have hpXY_pos : 0 < pXY' (x, y) := by
        apply lt_of_lt_of_le hpos
        exact Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z)
      have hpYZ_pos : 0 < pYZ' (y, z) := by
        apply lt_of_lt_of_le hpos
        exact Finset.single_le_sum (fun x' _ => hp (x', y, z)) (Finset.mem_univ x)
      have hpY_pos : 0 < pY' y := by
        apply lt_of_lt_of_le hpXY_pos
        apply Finset.single_le_sum (fun x' _ => Finset.sum_nonneg fun z' _ => hp (x', y, z'))
        exact Finset.mem_univ x
      have hq_pos : 0 < q (x, y, z) := div_pos (mul_pos hpXY_pos hpYZ_pos) hpY_pos
      linarith [kl_term_bound' hpos hq_pos]
  -- Algebraic identity: KL sum = H(XY)+H(YZ)-H(XYZ)-H(Y)
  -- Expand KL term: pXYZ*log(pXYZ/q) = pXYZ*log(pXYZ) + pXYZ*log(pY) - pXYZ*log(pXY) - pXYZ*log(pYZ)
  -- when pXYZ > 0; when pXYZ = 0 all terms are 0.
  -- Sum, then use lifting: Σ_{x,y,z} pXYZ*log(f(x,y)) = Σ_{x,y} pXY*log(pXY) etc.
  -- This connects to the entropies.
  have h_identity : ∑ xyz : α × β × γ,
      (if pXYZ xyz = 0 then (0 : ℝ) else pXYZ xyz * Real.log (pXYZ xyz / q xyz)) =
      shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ) -
      shannonEntropy' pXYZ - shannonEntropy' (marginalY_3 pXYZ) := by
    -- Simplify using hite (drop if-then-else in entropy sums)
    simp_rw [hent]
    -- Rewrite the KL terms: for pXYZ = 0, term = 0; for pXYZ > 0, expand log
    have hkl_term : ∀ x y z,
        (if pXYZ (x, y, z) = 0 then (0 : ℝ)
         else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) / q (x, y, z))) =
        pXYZ (x, y, z) * Real.log (pXYZ (x, y, z)) +
        pXYZ (x, y, z) * Real.log (pY' y) -
        pXYZ (x, y, z) * Real.log (pXY' (x, y)) -
        pXYZ (x, y, z) * Real.log (pYZ' (y, z)) := by
      intro x y z
      by_cases hpxyz : pXYZ (x, y, z) = 0
      · simp [hpxyz]
      · simp only [hpxyz, ↓reduceIte]
        have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
        have hpXY_pos : 0 < pXY' (x, y) :=
          lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z))
        have hpYZ_pos : 0 < pYZ' (y, z) :=
          lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp (x', y, z)) (Finset.mem_univ x))
        have hpY_pos : 0 < pY' y :=
          lt_of_lt_of_le hpXY_pos (Finset.single_le_sum
            (fun x' _ => Finset.sum_nonneg fun z' _ => hp (x', y, z')) (Finset.mem_univ x))
        have hq_pos : 0 < q (x, y, z) := div_pos (mul_pos hpXY_pos hpYZ_pos) hpY_pos
        rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hq_pos)]
        simp only [q, pXY', pYZ', pY', marginalXY, marginalYZ, marginalY_3]
        rw [Real.log_div (mul_pos hpXY_pos hpYZ_pos).ne' hpY_pos.ne',
            Real.log_mul hpXY_pos.ne' hpYZ_pos.ne']
        ring
    -- Convert product sum to nested, apply kl_term expansion
    rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type, hkl_term]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- Lifting: Σ_{x,y,z} pXYZ*log(pXY(x,y)) = Σ_{x,y} pXY*log(pXY)
    have hlift_XY :
        ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) * Real.log (pXY' (x, y)) =
        ∑ xy : α × β, pXY' xy * Real.log (pXY' xy) := by
      rw [← Fintype.sum_prod_type]
      congr 1; ext ⟨x, y⟩
      simp only [pXY', marginalXY]
      rw [← Finset.sum_mul]
    -- Lifting: Σ_{x,y,z} pXYZ*log(pYZ(y,z)) = Σ_{y,z} pYZ*log(pYZ)
    have hlift_YZ :
        ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) * Real.log (pYZ' (y, z)) =
        ∑ yz : β × γ, pYZ' yz * Real.log (pYZ' yz) := by
      rw [show ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) * Real.log (pYZ' (y, z)) =
          ∑ yz : β × γ, ∑ x : α, pXYZ (x, yz.1, yz.2) * Real.log (pYZ' yz) from by
        conv_lhs => rw [show ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) * Real.log (pYZ' (y, z)) =
          ∑ y : β, ∑ z : γ, ∑ x : α, pXYZ (x, y, z) * Real.log (pYZ' (y, z)) from by
          rw [Finset.sum_comm]; congr 1; ext y; exact Finset.sum_comm]
        rw [← Fintype.sum_prod_type]]
      congr 1; ext ⟨y, z⟩
      simp only [pYZ', marginalYZ]
      rw [← Finset.sum_mul]
    -- Lifting: Σ_{x,y,z} pXYZ*log(pY(y)) = Σ_y pY*log(pY)
    have hlift_Y :
        ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) * Real.log (pY' y) =
        ∑ y : β, pY' y * Real.log (pY' y) := by
      rw [Finset.sum_comm]; congr 1; ext y
      simp only [pY', marginalY_3]
      simp_rw [← Finset.sum_mul]
    rw [hlift_XY, hlift_YZ, hlift_Y]
    -- Σ_{x,y,z} pXYZ*log(pXYZ) = Σ_{xyz} pXYZ*log(pXYZ)
    rw [show ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) * Real.log (pXYZ (x, y, z)) =
        ∑ xyz : α × β × γ, pXYZ xyz * Real.log (pXYZ xyz) by
      rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]]
    ring
  linarith [h_kl, h_identity.le]

-- ═══════════════════════════════════════════════════════════════
-- PART VI: Consequences of SSA
-- ═══════════════════════════════════════════════════════════════

/-- **Conditioning reduces entropy** (general form):
    H(X|Y,Z) ≤ H(X|Y)

    Extra conditioning can only reduce uncertainty.
    This follows directly from SSA. -/
theorem conditioning_reduces_entropy_general {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    -- H(X|Y,Z) ≤ H(X|Y)
    -- where H(X|Y,Z) = H(X,Y,Z) - H(Y,Z) and H(X|Y) = H(X,Y) - H(Y)
    shannonEntropy' pXYZ - shannonEntropy' (marginalYZ pXYZ) ≤
    shannonEntropy' (marginalXY pXYZ) - shannonEntropy' (marginalY_3 pXYZ) := by
  -- This is a direct rearrangement of SSA:
  -- H(XYZ) + H(Y) ≤ H(XY) + H(YZ)
  -- ⟺ H(XYZ) - H(YZ) ≤ H(XY) - H(Y)
  linarith [strong_subadditivity hp hsum]

/-- **Data processing for conditional entropy**:
    Processing Z cannot increase the information X provides about Z conditioned on Y.
    This is a direct corollary of SSA. -/
theorem conditional_mi_nonneg {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    -- I(X;Z|Y) = H(X,Y) + H(Y,Z) - H(X,Y,Z) - H(Y) ≥ 0
    shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ) -
    shannonEntropy' pXYZ - shannonEntropy' (marginalY_3 pXYZ) ≥ 0 := by
  linarith [strong_subadditivity hp hsum]

end InformationTheory
