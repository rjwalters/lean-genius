/-
  Strong Subadditivity of Shannon Entropy

  H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)

  Equivalently: I(X;Z|Y) ≥ 0, i.e., conditional mutual information is non-negative.

  This is one of the deepest inequalities in classical information theory,
  proved by Lieb and Ruskai (1973) for quantum entropy and following from
  conditional KL divergence non-negativity for classical entropy.

  Proof approach: SSA ⟺ H(X|Y,Z) ≤ H(X|Y) (conditioning on more reduces entropy).
  This follows from the non-negativity of mutual information applied to the
  conditional distribution of X and Z given Y.
-/
import Mathlib
import Proofs.ShannonEntropy

namespace InformationTheory

-- ============================================================
-- Part 1: Three-Variable Marginal Distributions
-- ============================================================

/-- Marginal distribution of (X,Y) from joint (X,Y,Z). -/
noncomputable def marginalXY {α β γ : Type*} [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : α × β → ℝ :=
  fun (x, y) => ∑ z : γ, pXYZ (x, y, z)

/-- Marginal distribution of (Y,Z) from joint (X,Y,Z). -/
noncomputable def marginalYZ {α β γ : Type*} [Fintype α]
    (pXYZ : α × β × γ → ℝ) : β × γ → ℝ :=
  fun (y, z) => ∑ x : α, pXYZ (x, y, z)

/-- Marginal distribution of Y from joint (X,Y,Z). -/
noncomputable def marginalY {α β γ : Type*} [Fintype α] [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : β → ℝ :=
  fun y => ∑ x : α, ∑ z : γ, pXYZ (x, y, z)

-- ============================================================
-- Part 2: Properties of Marginals
-- ============================================================

theorem marginalXY_nonneg {α β γ : Type*} [Fintype γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (x : α) (y : β) : 0 ≤ marginalXY pXYZ (x, y) := by
  unfold marginalXY
  exact Finset.sum_nonneg fun z _ => hp (x, y, z)

theorem marginalYZ_nonneg {α β γ : Type*} [Fintype α]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (y : β) (z : γ) : 0 ≤ marginalYZ pXYZ (y, z) := by
  unfold marginalYZ
  exact Finset.sum_nonneg fun x _ => hp (x, y, z)

theorem marginalY_nonneg {α β γ : Type*} [Fintype α] [Fintype γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (y : β) : 0 ≤ marginalY pXYZ y := by
  unfold marginalY
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun z _ => hp (x, y, z)

theorem marginalXY_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {pXYZ : α × β × γ → ℝ} (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    ∑ xy : α × β, marginalXY pXYZ xy = 1 := by
  unfold marginalXY
  simp only [Finset.sum_product']
  rw [← Finset.sum_product']
  convert hsum using 1
  rw [Finset.sum_product']
  congr 1; ext x; rw [Finset.sum_product']; congr 1; ext y
  rfl

theorem marginalYZ_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {pXYZ : α × β × γ → ℝ} (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    ∑ yz : β × γ, marginalYZ pXYZ yz = 1 := by
  unfold marginalYZ
  -- ∑_{y,z} ∑_x p(x,y,z) = ∑_{x,y,z} p(x,y,z) = 1
  simp only [Finset.sum_product']
  rw [Finset.sum_comm]
  convert hsum using 1
  rw [Finset.sum_product']
  congr 1; ext x; rw [Finset.sum_product']

theorem marginalY_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {pXYZ : α × β × γ → ℝ} (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    ∑ y : β, marginalY pXYZ y = 1 := by
  unfold marginalY
  -- ∑_y ∑_x ∑_z p(x,y,z) = ∑_{x,y,z} p(x,y,z) = 1
  rw [Finset.sum_comm]
  convert hsum using 1
  rw [Finset.sum_product']
  congr 1; ext x; rw [Finset.sum_comm]; rw [Finset.sum_product']

-- ============================================================
-- Part 3: Strong Subadditivity
-- ============================================================

/-- **Strong Subadditivity of Shannon Entropy (Lieb-Ruskai 1973)**

    H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)

    Equivalent forms:
    - I(X;Z|Y) ≥ 0 (conditional mutual information non-negative)
    - H(X|Y,Z) ≤ H(X|Y) (conditioning on more reduces entropy)

    This is the fundamental inequality of classical information theory.
    The proof uses the non-negativity of KL divergence (already proved
    as kl_divergence_nonneg). -/
theorem strong_subadditivity {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [DecidableEq (α × β)] [DecidableEq (β × γ)] [DecidableEq (α × β × γ)]
    {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy pXYZ + shannonEntropy (marginalY pXYZ) ≤
      shannonEntropy (marginalXY pXYZ) + shannonEntropy (marginalYZ pXYZ) := by
  -- SSA is equivalent to I(X;Z|Y) ≥ 0.
  -- I(X;Z|Y) = Σ_{x,y,z} p(x,y,z) log(p(x,y,z) p(y) / (p(x,y) p(y,z)))
  -- This is the KL divergence D(p(x,y,z) || p(x,y)p(y,z)/p(y)) ≥ 0.
  -- Equivalently, it's the sum over y of p(y) · D(p(x,z|y) || p(x|y)p(z|y)) ≥ 0.
  sorry

/-- Corollary: Subadditivity for three variables.
    H(X,Y,Z) ≤ H(X) + H(Y) + H(Z) -/
theorem subadditivity_three {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [DecidableEq (α × β)] [DecidableEq (β × γ)] [DecidableEq (α × β × γ)]
    {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy pXYZ ≤
      shannonEntropy (fun x => ∑ y : β, ∑ z : γ, pXYZ (x, y, z)) +
      shannonEntropy (marginalY pXYZ) +
      shannonEntropy (fun z => ∑ x : α, ∑ y : β, pXYZ (x, y, z)) := by
  sorry

end InformationTheory
