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
  -- kl_term_bound (private in ShannonEntropy.lean — copied here)
  have kl_tb : ∀ {p q : ℝ}, 0 < p → 0 < q → p * Real.log (p / q) ≥ p - q := by
    intro p q hp hq
    have h1 : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp)
    have h2 : p * Real.log (q / p) ≤ q - p :=
      calc p * Real.log (q / p) ≤ p * (q / p - 1) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
            _ = q - p := by field_simp; ring
    linarith [show p * Real.log (p / q) = -(p * Real.log (q / p)) by
      rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),
          Real.log_div (ne_of_gt hq) (ne_of_gt hp)]; ring]

  -- Nested sum = 1
  have hsum_n : ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) = 1 := by
    have h := hsum; rw [Fintype.sum_prod_type] at h; simp_rw [Fintype.sum_prod_type] at h; exact h

  -- Marginal telescoping: if S=0 then 0 else S·log S = Σ (if aᵢ=0 then 0 else aᵢ·log S)
  have htele : ∀ {ι : Type*} [Fintype ι] (a : ι → ℝ) (_ : ∀ i, 0 ≤ a i),
      (if (∑ i, a i) = 0 then (0 : ℝ) else (∑ i, a i) * Real.log (∑ i, a i)) =
      ∑ i, (if a i = 0 then 0 else a i * Real.log (∑ j, a j)) := by
    intro ι _ a ha
    by_cases hs : (∑ i, a i) = 0
    · have : ∀ i, a i = 0 := fun i =>
        le_antisymm (by linarith [Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)]) (ha i)
      simp [hs, this]
    · simp only [hs, ↓reduceIte]; symm
      rw [show ∑ i, (if a i = 0 then (0 : ℝ) else a i * Real.log (∑ j, a j)) =
          ∑ i, a i * Real.log (∑ j, a j) from
        Finset.sum_congr rfl fun i _ => by by_cases h : a i = 0 <;> simp [h]]
      rw [← Finset.sum_mul]

  -- XY marginal telescoping
  have hXY : ∀ x y, (if (∑ z : γ, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ z, pXYZ (x, y, z)) * Real.log (∑ z, pXYZ (x, y, z))) =
      ∑ z : γ, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ z' : γ, pXYZ (x, y, z'))) := by
    intro x y; exact htele (fun z => pXYZ (x, y, z)) (fun z => hp (x, y, z))

  -- YZ marginal telescoping
  have hYZ : ∀ y z, (if (∑ x : α, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ x, pXYZ (x, y, z)) * Real.log (∑ x, pXYZ (x, y, z))) =
      ∑ x : α, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) := by
    intro y z; exact htele (fun x => pXYZ (x, y, z)) (fun x => hp (x, y, z))

  -- Y marginal telescoping
  have hY : ∀ y, (if (∑ x : α, ∑ z : γ, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ x, ∑ z, pXYZ (x, y, z)) * Real.log (∑ x, ∑ z, pXYZ (x, y, z))) =
      ∑ x : α, ∑ z : γ, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z'))) := by
    intro y
    have h := htele (fun (xz : α × γ) => pXYZ (xz.1, y, xz.2)) (fun xz => hp (xz.1, y, xz.2))
    simp_rw [Fintype.sum_prod_type] at h; exact h

  -- Term splitting: p·log(p) = CMI_term + p·log(pXY) + p·log(pYZ) - p·log(pY)
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
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp _) (Finset.mem_univ z))
      have hpYZ : 0 < ∑ x', pXYZ (x', y, z) :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp _) (Finset.mem_univ x))
      have hpY : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
        lt_of_lt_of_le hpXY (Finset.single_le_sum
          (fun x' _ => Finset.sum_nonneg fun z' _ => hp _) (Finset.mem_univ x))
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
      calc pXYZ (x, y, z) * Real.log (pXYZ (x, y, z))
          = pXYZ (x, y, z) * (
            Real.log (pXYZ (x, y, z) * (∑ x', ∑ z', pXYZ (x', y, z')) /
              ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z)))) +
            Real.log (∑ z', pXYZ (x, y, z')) +
            Real.log (∑ x', pXYZ (x', y, z)) -
            Real.log (∑ x', ∑ z', pXYZ (x', y, z'))) := by congr 1; exact hlog
        _ = _ := by ring

  -- === PART 1: Show the conditional MI ≥ 0 ===
  set q := fun x y z => (∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z)) /
    (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) with hq_def
  have hq_nn : ∀ x y z, 0 ≤ q x y z := fun x y z => div_nonneg
    (mul_nonneg (Finset.sum_nonneg fun z' _ => hp _) (Finset.sum_nonneg fun x' _ => hp _))
    (Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun z' _ => hp _)
  have hq_sum_y : ∀ y, ∑ x : α, ∑ z : γ, q x y z = ∑ x, ∑ z, pXYZ (x, y, z) := by
    intro y
    simp only [hq_def]
    by_cases hpy : (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) = 0
    · have hall : ∀ x z, pXYZ (x, y, z) = 0 := by
        intro x z; linarith [hp (x, y, z),
          Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z),
          Finset.single_le_sum (fun x' _ =>
            Finset.sum_nonneg fun z' _ => hp (x', y, z')) (Finset.mem_univ x)]
      simp [hall, hpy]
    · have hpy_ne : (∑ x', ∑ z', pXYZ (x', y, z')) ≠ 0 := hpy
      simp_rw [mul_div_assoc]
      simp_rw [← Finset.sum_div, ← Finset.mul_sum]
      rw [← Finset.sum_div, ← Finset.sum_mul]
      rw [show ∑ z : γ, ∑ x' : α, pXYZ (x', y, z) = ∑ x' : α, ∑ z : γ, pXYZ (x', y, z) from
        Finset.sum_comm]
      rw [mul_div_cancel₀ _ hpy_ne]
  have hq_sum : ∑ x : α, ∑ y : β, ∑ z : γ, q x y z = 1 := by
    conv_lhs => rw [Finset.sum_comm]
    simp_rw [hq_sum_y]
    rw [Finset.sum_comm]; exact hsum_n
  have h_cmi : 0 ≤ ∑ x : α, ∑ y : β, ∑ z : γ,
      (if pXYZ (x, y, z) = 0 then (0 : ℝ)
       else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) *
         (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) /
         ((∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))))) := by
    suffices h_lb : ∑ x, ∑ y, ∑ z, (pXYZ (x, y, z) - q x y z) ≤
        ∑ x, ∑ y, ∑ z, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
         else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) *
           (∑ x', ∑ z', pXYZ (x', y, z')) /
           ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z))))) by
      have hzero : ∑ x, ∑ y, ∑ z, (pXYZ (x, y, z) - q x y z) = 0 := by
        simp only [Finset.sum_sub_distrib]; rw [hsum_n, hq_sum, sub_self]
      linarith
    apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
    apply Finset.sum_le_sum; intro z _
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · simp [hpxyz]; exact hq_nn x y z
    · simp only [hpxyz, ↓reduceIte]
      have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
      have hpXY : 0 < ∑ z', pXYZ (x, y, z') :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp _) (Finset.mem_univ z))
      have hpYZ : 0 < ∑ x', pXYZ (x', y, z) :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp _) (Finset.mem_univ x))
      have hpY : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
        lt_of_lt_of_le hpXY (Finset.single_le_sum
          (fun x' _ => Finset.sum_nonneg fun z' _ => hp _) (Finset.mem_univ x))
      have hq_pos : 0 < q x y z := by
        simp only [hq_def]; exact div_pos (mul_pos hpXY hpYZ) hpY
      have hlog_eq : pXYZ (x, y, z) * (∑ x', ∑ z', pXYZ (x', y, z')) /
          ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z))) =
          pXYZ (x, y, z) / q x y z := by
        simp only [hq_def]; field_simp; ring
      rw [hlog_eq]
      exact kl_tb hpos hq_pos

  -- === PART 2: Entropy algebra — connect CMI to SSA deficit ===
  unfold shannonEntropy' marginalXY marginalYZ marginalY_3
  dsimp only
  conv_lhs => arg 1; arg 1; rw [show ∑ xyz : α × β × γ,
    (if pXYZ xyz = 0 then (0 : ℝ) else pXYZ xyz * Real.log (pXYZ xyz)) =
    ∑ x : α, ∑ y : β, ∑ z : γ,
    (if pXYZ (x, y, z) = 0 then 0 else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z))) from by
      rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]]
  conv_rhs => arg 1; arg 1; rw [show ∑ xy : α × β,
    (if (fun xy => ∑ z : γ, pXYZ (xy.1, xy.2, z)) xy = 0 then (0 : ℝ)
     else (fun xy => ∑ z, pXYZ (xy.1, xy.2, z)) xy *
       Real.log ((fun xy => ∑ z, pXYZ (xy.1, xy.2, z)) xy)) =
    ∑ x : α, ∑ y : β,
    (if (∑ z : γ, pXYZ (x, y, z)) = 0 then 0
     else (∑ z, pXYZ (x, y, z)) * Real.log (∑ z, pXYZ (x, y, z))) from by
      rw [Fintype.sum_prod_type]]
  conv_rhs => arg 2; arg 1; rw [show ∑ yz : β × γ,
    (if (fun yz => ∑ x : α, pXYZ (x, yz.1, yz.2)) yz = 0 then (0 : ℝ)
     else (fun yz => ∑ x, pXYZ (x, yz.1, yz.2)) yz *
       Real.log ((fun yz => ∑ x, pXYZ (x, yz.1, yz.2)) yz)) =
    ∑ y : β, ∑ z : γ,
    (if (∑ x : α, pXYZ (x, y, z)) = 0 then 0
     else (∑ x, pXYZ (x, y, z)) * Real.log (∑ x, pXYZ (x, y, z))) from by
      rw [Fintype.sum_prod_type]]
  simp_rw [hXY]
  simp_rw [hYZ]
  simp_rw [hY]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith [h_cmi]

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
