/-
Erdős Problem #2 OQ-01: Exact Maximum Minimum Modulus for Covering Systems

What is the exact maximum possible minimum modulus M?
Currently known: 42 ≤ M ≤ 616,000.

This file formalizes structural theorems about the gap:
1. Achievability is downward-monotone
2. The exact maximum M exists (well-ordering + Owens + Balister)
3. M is unique
4. M lies in [42, 616000]
5. Complete characterization of the achievable set as an initial segment

All structural theorems proved with 0 sorries.
Axioms inherited from parent file: hough_bound, balister_bound,
  owens_construction, reciprocal_sum_ge_one.

References:
- Hough, "Solution of the minimum modulus problem for covering systems" (2015)
- Balister et al., "Covering systems with restricted divisibility" (2022)
- Owens, "A covering system with minimum modulus 42" (2014)
- Erdős Problem #2: https://erdosproblems.com/2
-/

import Proofs.Erdos2Problem

open Set Finset Erdos2

namespace Erdos2OQ01

-- ══════════════════════════════════════════════════════════════════
-- § 1. Achievability
-- ══════════════════════════════════════════════════════════════════

/-- A minimum modulus value m is **achievable** if some covering system
    has all moduli ≥ m. -/
def Achievable (m : ℕ) : Prop :=
  ∃ cs : CoveringSystem, cs.hasMinModulusAtLeast m

/-- Achievability is downward-monotone: if minimum modulus m is achievable,
    then so is any smaller value m'. A covering system with all moduli ≥ m
    automatically has all moduli ≥ m' when m' ≤ m. -/
theorem achievable_mono {m m' : ℕ} (h : m' ≤ m) (hm : Achievable m) : Achievable m' := by
  obtain ⟨cs, hcs⟩ := hm
  exact ⟨cs, fun c hc => le_trans h (hcs c hc)⟩

/-- 42 is achievable (Owens 2014). -/
theorem achievable_42 : Achievable 42 := owens_construction

/-- Every value ≤ 42 is achievable (by monotonicity from Owens). -/
theorem achievable_le_42 (m : ℕ) (hm : m ≤ 42) : Achievable m :=
  achievable_mono hm achievable_42

/-- No value > 616000 is achievable. If a covering system had all moduli
    > 616000, Balister's bound would be violated. -/
theorem not_achievable_gt_616000 (m : ℕ) (hm : m > 616000) : ¬Achievable m := by
  intro ⟨cs, hcs⟩
  obtain ⟨c, hc, hle⟩ := balister_bound cs
  have := hcs c hc
  omega

-- ══════════════════════════════════════════════════════════════════
-- § 2. The Exact Maximum Minimum Modulus
-- ══════════════════════════════════════════════════════════════════

/-- The exact maximum minimum modulus M is the largest achievable value:
    (a) some covering system achieves minimum modulus M, and
    (b) no covering system has ALL moduli > M (i.e., some modulus ≤ M). -/
def IsExactMaxMinModulus (M : ℕ) : Prop :=
  Achievable M ∧ ¬Achievable (M + 1)

/-- Equivalent characterization: M is exact max iff it's achievable and
    every covering system has at least one modulus ≤ M. -/
theorem isExactMax_iff (M : ℕ) :
    IsExactMaxMinModulus M ↔
    (∃ cs : CoveringSystem, cs.hasMinModulusAtLeast M) ∧
    (∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ M) := by
  constructor
  · intro ⟨hach, hnext⟩
    exact ⟨hach, fun cs => by
      by_contra h
      push_neg at h
      exact hnext ⟨cs, fun c hc => by have := h c hc; omega⟩⟩
  · intro ⟨hach, hbound⟩
    exact ⟨hach, fun ⟨cs, hcs⟩ => by
      obtain ⟨c, hc, hle⟩ := hbound cs
      have := hcs c hc
      omega⟩

-- ══════════════════════════════════════════════════════════════════
-- § 3. Existence and Uniqueness
-- ══════════════════════════════════════════════════════════════════

/-- The exact maximum minimum modulus is unique: if M₁ and M₂ are both
    exact maxima, they must be equal. -/
theorem exact_max_unique (M₁ M₂ : ℕ) (h₁ : IsExactMaxMinModulus M₁)
    (h₂ : IsExactMaxMinModulus M₂) : M₁ = M₂ := by
  obtain ⟨hach₁, hnext₁⟩ := h₁
  obtain ⟨hach₂, hnext₂⟩ := h₂
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- M₁ < M₂ means M₁ + 1 ≤ M₂, so Achievable (M₁ + 1) by monotonicity
    exact hnext₁ (achievable_mono (by omega) hach₂)
  · -- M₂ < M₁ means M₂ + 1 ≤ M₁, so Achievable (M₂ + 1) by monotonicity
    exact hnext₂ (achievable_mono (by omega) hach₁)

/-- The exact maximum minimum modulus exists.

    Proof by well-ordering: The set of non-achievable naturals is nonempty
    (616001 is not achievable by Balister's bound). Its minimum n₀ satisfies
    n₀ - 1 being achievable (by minimality) and n₀ being not achievable.
    So M = n₀ - 1 is the exact maximum. -/
theorem exists_exact_max : ∃ M : ℕ, IsExactMaxMinModulus M := by
  classical
  -- 616001 is not achievable
  have hnotach : ∃ n, ¬Achievable n :=
    ⟨616001, not_achievable_gt_616000 616001 (by omega)⟩
  -- n₀ = smallest non-achievable value
  set n₀ := Nat.find hnotach with hn₀_def
  have hn₀_not : ¬Achievable n₀ := Nat.find_spec hnotach
  have hn₀_min : ∀ m, m < n₀ → ¬¬Achievable m :=
    fun m hm => Nat.find_min hnotach hm
  -- n₀ ≥ 1 since Achievable 0 (any covering system has all moduli ≥ 0)
  have hn₀_pos : n₀ ≥ 1 := by
    by_contra h
    push_neg at h
    interval_cases n₀
    exact hn₀_not (achievable_le_42 0 (by omega))
  -- M = n₀ - 1 is the exact maximum
  refine ⟨n₀ - 1, ?_, ?_⟩
  · -- Achievable (n₀ - 1): since n₀ - 1 < n₀ and n₀ is the smallest non-achievable
    exact not_not.mp (hn₀_min (n₀ - 1) (by omega))
  · -- ¬Achievable n₀: by definition
    have : n₀ - 1 + 1 = n₀ := by omega
    rw [this]
    exact hn₀_not

-- ══════════════════════════════════════════════════════════════════
-- § 4. The Gap [42, 616000]
-- ══════════════════════════════════════════════════════════════════

/-- The exact maximum minimum modulus is at least 42.
    Proof: Owens' construction shows 42 is achievable, so M ≥ 42
    since M is the largest achievable value. -/
theorem exact_max_ge_42 (M : ℕ) (hM : IsExactMaxMinModulus M) : M ≥ 42 := by
  obtain ⟨_, hnext⟩ := hM
  by_contra h
  push_neg at h
  -- M < 42 means M + 1 ≤ 42, so Achievable (M + 1) by monotonicity from 42
  exact hnext (achievable_le_42 (M + 1) (by omega))

/-- The exact maximum minimum modulus is at most 616000.
    Proof: If M > 616000 then M is not achievable (Balister), contradicting
    the definition of IsExactMaxMinModulus. -/
theorem exact_max_le_616000 (M : ℕ) (hM : IsExactMaxMinModulus M) : M ≤ 616000 := by
  obtain ⟨hach, _⟩ := hM
  by_contra h
  push_neg at h
  exact not_achievable_gt_616000 M (by omega) hach

/-- The gap theorem: any exact maximum minimum modulus lies in [42, 616000]. -/
theorem gap_bounds (M : ℕ) (hM : IsExactMaxMinModulus M) : 42 ≤ M ∧ M ≤ 616000 :=
  ⟨exact_max_ge_42 M hM, exact_max_le_616000 M hM⟩

/-- There exists a unique M in [42, 616000] that is the exact maximum. -/
theorem exact_max_in_interval :
    ∃ M : ℕ, 42 ≤ M ∧ M ≤ 616000 ∧ IsExactMaxMinModulus M := by
  obtain ⟨M, hM⟩ := exists_exact_max
  exact ⟨M, exact_max_ge_42 M hM, exact_max_le_616000 M hM, hM⟩

-- ══════════════════════════════════════════════════════════════════
-- § 5. Complete Characterization of the Achievable Set
-- ══════════════════════════════════════════════════════════════════

/-- Below the exact maximum, every value is achievable. -/
theorem achievable_le_max (M m : ℕ) (hM : IsExactMaxMinModulus M) (hm : m ≤ M) :
    Achievable m :=
  achievable_mono hm hM.1

/-- Above the exact maximum, no value is achievable. -/
theorem not_achievable_gt_max (M m : ℕ) (hM : IsExactMaxMinModulus M) (hm : m > M) :
    ¬Achievable m := by
  intro hach
  obtain ⟨_, hnext⟩ := hM
  exact hnext (achievable_mono (by omega) hach)

/-- The achievable set is exactly {0, 1, ..., M}. -/
theorem achievable_iff_le_max (M m : ℕ) (hM : IsExactMaxMinModulus M) :
    Achievable m ↔ m ≤ M := by
  constructor
  · intro hach
    by_contra h
    push_neg at h
    exact not_achievable_gt_max M m hM h hach
  · exact achievable_le_max M m hM

-- ══════════════════════════════════════════════════════════════════
-- § 6. Derived Results
-- ══════════════════════════════════════════════════════════════════

/-- Balister's bound implies Hough's bound (616,000 < 10^16). -/
theorem balister_implies_hough :
    ∀ cs : CoveringSystem, ∃ c ∈ cs.classes, c.modulus ≤ 10^16 := by
  intro cs
  obtain ⟨c, hc, hle⟩ := balister_bound cs
  exact ⟨c, hc, by omega⟩

/-- If M is the exact maximum, then M+1 is the smallest non-achievable value. -/
theorem succ_is_smallest_non_achievable (M : ℕ) (hM : IsExactMaxMinModulus M)
    (n : ℕ) (hn : ¬Achievable n) : M + 1 ≤ n := by
  by_contra h
  push_neg at h
  exact hn (achievable_le_max M n hM (by omega))

/-- The gap has width at most 615,958 (= 616000 - 42). -/
theorem gap_width : ∀ M : ℕ, IsExactMaxMinModulus M → M - 42 ≤ 615958 := by
  intro M hM
  have := exact_max_le_616000 M hM
  omega

/-- Narrowing the gap: any improvement to the lower bound L > 42 or
    upper bound U < 616000 reduces the search space for M. -/
theorem gap_narrowing (L U : ℕ) (hL : Achievable L) (hU : ¬Achievable (U + 1))
    (M : ℕ) (hM : IsExactMaxMinModulus M) : L ≤ M ∧ M ≤ U := by
  constructor
  · rw [← achievable_iff_le_max M L hM]
    exact hL
  · by_contra h
    push_neg at h
    exact hU (achievable_le_max M (U + 1) hM (by omega))

end Erdos2OQ01
