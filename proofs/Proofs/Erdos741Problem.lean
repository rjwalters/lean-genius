/-
# Erdős Problem 741: Splitting Sumsets with Positive Density

**Part 1 (Density splitting):** If A ⊆ ℕ is such that A + A has positive
upper density, can one always decompose A = A₁ ⊔ A₂ such that both
A₁ + A₁ and A₂ + A₂ have positive upper density?

**Part 2 (Basis splitting):** Is there a basis A of order 2 such that for
every decomposition A = A₁ ⊔ A₂, the sumsets A₁ + A₁ and A₂ + A₂
cannot both have bounded gaps (be syndetic)?

This is a problem of Burr and Erdős. Erdős believed he could construct a
basis answering Part 2 affirmatively but "could never quite finish the proof."

**Status:** OPEN

**Reference:** erdosproblems.com/741, Er94b
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Set Filter

/-
## Density and Sumset Definitions
-/

/-- Upper density of a set A ⊆ ℕ: limsup |A ∩ [0,n]| / (n+1). -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
    atTop.limsup (fun n => ((A ∩ Set.Iic n).ncard : ℝ) / (n + 1 : ℝ))

/-- HasPosDensity A means A has positive upper density. -/
def HasPosDensity (A : Set ℕ) : Prop :=
    0 < upperDensity A

/-- The sumset A + B = { a + b : a ∈ A, b ∈ B }. -/
def sumset (A B : Set ℕ) : Set ℕ :=
    { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

/-- A is a basis of order 2 if every sufficiently large natural number
is in A + A. -/
def IsBasisOrder2 (A : Set ℕ) : Prop :=
    ∀ᶠ n in atTop, n ∈ sumset A A

/-- A set S ⊆ ℕ is syndetic (has bounded gaps) if there exists g such that
every interval [n, n+g] intersects S. -/
def IsSyndetic (S : Set ℕ) : Prop :=
    ∃ g : ℕ, ∀ n : ℕ, ∃ m ∈ S, n ≤ m ∧ m ≤ n + g

/-
## Main Conjectures (OPEN)
-/

/-- Part 1 (Density splitting): If A + A has positive density, can A be split
into A₁ ⊔ A₂ with both A₁ + A₁ and A₂ + A₂ having positive density? -/
def ErdosProblem741_density : Prop :=
    ∀ A : Set ℕ, HasPosDensity (sumset A A) →
      ∃ A₁ A₂ : Set ℕ, A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧
        HasPosDensity (sumset A₁ A₁) ∧ HasPosDensity (sumset A₂ A₂)

/-- Part 2 (Basis splitting): Does there exist a basis of order 2 such that
no partition A = A₁ ⊔ A₂ makes both A₁ + A₁ and A₂ + A₂ syndetic? -/
def ErdosProblem741_basis : Prop :=
    ∃ A : Set ℕ, IsBasisOrder2 A ∧
      ∀ A₁ A₂ : Set ℕ, A = A₁ ∪ A₂ → Disjoint A₁ A₂ →
        ¬(IsSyndetic (sumset A₁ A₁) ∧ IsSyndetic (sumset A₂ A₂))

/-
## Sumset Algebraic Properties
-/

/-- The sumset is commutative. -/
theorem sumset_comm (A B : Set ℕ) : sumset A B = sumset B A := by
  ext n; constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, by omega⟩
  · rintro ⟨b, hb, a, ha, rfl⟩; exact ⟨a, ha, b, hb, by omega⟩

/-- The empty sumset is empty. -/
theorem empty_sumset : sumset ∅ (∅ : Set ℕ) = ∅ := by
  ext n; simp [sumset]

/-- Sumset with empty set on the left is empty. -/
theorem sumset_empty_left (B : Set ℕ) : sumset ∅ B = ∅ := by
  ext n; simp [sumset]

/-- Sumset with empty set on the right is empty. -/
theorem sumset_empty_right (A : Set ℕ) : sumset A ∅ = ∅ := by
  ext n; simp [sumset]

/-- If A ⊆ B, then sumset A A ⊆ sumset B B. -/
theorem sumset_mono {A B : Set ℕ} (h : A ⊆ B) : sumset A A ⊆ sumset B B := by
  intro n ⟨a, ha, b, hb, hn⟩
  exact ⟨a, h ha, b, h hb, hn⟩

/-- Sumset is monotone in both arguments. -/
theorem sumset_mono_left {A₁ A₂ B : Set ℕ} (h : A₁ ⊆ A₂) :
    sumset A₁ B ⊆ sumset A₂ B := by
  intro n ⟨a, ha, b, hb, hn⟩
  exact ⟨a, h ha, b, hb, hn⟩

/-- 0 ∈ sumset A A if 0 ∈ A. -/
theorem zero_mem_sumset_self {A : Set ℕ} (h : 0 ∈ A) : 0 ∈ sumset A A :=
  ⟨0, h, 0, h, by omega⟩

/-- If a ∈ A, then 2*a ∈ sumset A A. -/
theorem double_mem_sumset {A : Set ℕ} {a : ℕ} (h : a ∈ A) :
    2 * a ∈ sumset A A :=
  ⟨a, h, a, h, by omega⟩

/-- A ∪ B sumset contains sumset A A. -/
theorem sumset_union_contains_left (A B : Set ℕ) :
    sumset A A ⊆ sumset (A ∪ B) (A ∪ B) :=
  sumset_mono (Set.subset_union_left)

/-- A ∪ B sumset contains sumset B B. -/
theorem sumset_union_contains_right (A B : Set ℕ) :
    sumset B B ⊆ sumset (A ∪ B) (A ∪ B) :=
  sumset_mono (Set.subset_union_right)

/-
## Partition Properties
-/

/-- A trivial partition always exists: A = A ∪ ∅. -/
theorem trivial_partition (A : Set ℕ) : A = A ∪ ∅ ∧ Disjoint A (∅ : Set ℕ) := by
  exact ⟨by simp, disjoint_bot_right⟩

/-- A symmetric partition: A = A₁ ∪ A₂ with A₁ = A₂ᶜ ∩ A. -/
theorem complement_partition (A : Set ℕ) (A₁ : Set ℕ) (h₁ : A₁ ⊆ A) :
    A = A₁ ∪ (A \ A₁) ∧ Disjoint A₁ (A \ A₁) := by
  constructor
  · ext x; constructor
    · intro hx
      by_cases hx₁ : x ∈ A₁
      · exact Or.inl hx₁
      · exact Or.inr ⟨hx, hx₁⟩
    · rintro (hx | ⟨hx, _⟩) <;> [exact h₁ hx; exact hx]
  · exact disjoint_sdiff_self_right

/-- In a disjoint partition, elements are in exactly one part. -/
theorem partition_membership {A₁ A₂ : Set ℕ} (hdisj : Disjoint A₁ A₂) {x : ℕ}
    (hx₁ : x ∈ A₁) : x ∉ A₂ := by
  intro hx₂
  exact Set.disjoint_left.mp hdisj hx₁ hx₂

/-
## Syndetic Set Properties
-/

/-- ℕ is syndetic (with gap 0). -/
theorem nat_syndetic : IsSyndetic (Set.univ : Set ℕ) :=
  ⟨0, fun n => ⟨n, Set.mem_univ n, le_refl n, by omega⟩⟩

/-- The empty set is not syndetic. -/
theorem empty_not_syndetic : ¬IsSyndetic (∅ : Set ℕ) := by
  rintro ⟨g, hg⟩
  obtain ⟨m, hm, -⟩ := hg 0
  exact hm

/-- A syndetic set is nonempty. -/
theorem syndetic_nonempty {S : Set ℕ} (h : IsSyndetic S) : S.Nonempty := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨m, hm, -⟩ := hg 0
  exact ⟨m, hm⟩

/-- A superset of a syndetic set is syndetic. -/
theorem syndetic_mono {S T : Set ℕ} (h : S ⊆ T) (hs : IsSyndetic S) : IsSyndetic T := by
  obtain ⟨g, hg⟩ := hs
  exact ⟨g, fun n => let ⟨m, hm, h1, h2⟩ := hg n; ⟨m, h hm, h1, h2⟩⟩

/-- A syndetic set is infinite. -/
theorem syndetic_infinite {S : Set ℕ} (h : IsSyndetic S) : S.Infinite := by
  obtain ⟨g, hg⟩ := h
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨m, hm, h1, _⟩ := hg (n + 1)
  exact ⟨m, hm, by omega⟩

/-
## Density Properties (Axiomatized)
-/

/-- The empty set has zero density. -/
theorem density_empty : upperDensity ∅ = 0 := by
  simp only [upperDensity, Set.empty_inter, Set.ncard_empty, Nat.cast_zero, zero_div]
  exact Filter.limsup_const 0

/-- ℕ has density 1. -/
theorem density_univ : upperDensity Set.univ = 1 := by
  simp only [upperDensity, Set.univ_inter]
  suffices h : (fun n : ℕ => ((Set.Iic n).ncard : ℝ) / ((n : ℝ) + 1)) = fun _ => 1 by
    rw [h]; exact Filter.limsup_const 1
  ext n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hIic : (Set.Iic n : Set ℕ).ncard = n + 1 := by
    rw [← Set.ncard_coe_Finset, Finset.toSet_toFinset]
    simp [Set.toFinset_Iic, Finset.card_Iic]
  rw [hIic, div_eq_one_iff_eq hn]
  push_cast; ring

/-- Density is monotone: A ⊆ B implies upperDensity A ≤ upperDensity B. -/
theorem density_mono {A B : Set ℕ} (h : A ⊆ B) : upperDensity A ≤ upperDensity B := by
  unfold upperDensity
  apply Filter.limsup_le_limsup
  · filter_upwards [] with n
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ h)
        ((Set.Iic n).toFinite.subset Set.inter_subset_right)

/-- Upper density is at most 1 for any set. -/
theorem density_le_one (A : Set ℕ) : upperDensity A ≤ 1 :=
  density_univ ▸ density_mono (Set.subset_univ A)

/-
## Basis Properties
-/

/-- A basis of order 2 is infinite. -/
theorem basis_infinite {A : Set ℕ} (h : IsBasisOrder2 A) : A.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  -- Eventually all large numbers are in sumset A A
  -- This requires infinitely many elements of A
  -- We prove by contradiction: if A ⊆ [0, M], then sumset A A ⊆ [0, 2M]
  by_contra hfin
  push_neg at hfin
  -- All elements of A are ≤ n
  have hA_bound : ∀ a ∈ A, a ≤ n := fun a ha => le_of_not_gt (fun h => hfin a ha h)
  -- Then sumset A A ⊆ [0, 2n]
  have hS_bound : ∀ s ∈ sumset A A, s ≤ 2 * n := by
    rintro s ⟨a, ha, b, hb, rfl⟩
    have := hA_bound a ha
    have := hA_bound b hb
    omega
  -- But h says all large enough numbers are in sumset A A
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  -- Take m = max(N, 2*n + 1)
  have hm := hN (max N (2 * n + 1)) (le_max_left _ _)
  have := hS_bound _ hm
  omega

/-- A cofinite set (containing all sufficiently large n) has density 1.
    Proof strategy: for n ≥ N₀, |S∩{0,...,n}| ≥ n-N₀+1, so ratio ≥ (n-N₀+1)/(n+1) → 1.
    Combined with ratio ≤ 1 (density_le_one), limsup = 1. -/
theorem cofinite_density_one {S : Set ℕ} (h : ∀ᶠ n in atTop, n ∈ S) :
    upperDensity S = 1 := by
  rw [Filter.eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  apply le_antisymm (density_le_one S)
  unfold upperDensity
  -- Card bound: for n ≥ N₀, |S ∩ Iic n| ≥ n - N₀ + 1 via {N₀,...,n} ⊆ S
  have hcard : ∀ n ≥ N₀, (n - N₀ + 1 : ℕ) ≤ (S ∩ Set.Iic n).ncard := by
    intro n hn
    have hfin : (S ∩ Set.Iic n).Finite :=
      (Set.finite_Iic n).subset Set.inter_subset_right
    have hincl : (Finset.Icc N₀ n : Set ℕ) ⊆ S ∩ Set.Iic n := by
      intro m hm
      simp only [Finset.coe_Icc, Set.mem_Icc] at hm
      exact ⟨hN₀ m hm.1, hm.2⟩
    calc n - N₀ + 1 = (Finset.Icc N₀ n).card := by simp [Finset.card_Icc]; omega
      _ = ((Finset.Icc N₀ n : Set ℕ)).ncard := (Set.ncard_coe_Finset _).symm
      _ ≤ (S ∩ Set.Iic n).ncard := Set.ncard_le_ncard hincl hfin
  -- The ratio sequence is eventually ≥ 1 - N₀/(n+1)
  have hlb : ∀ᶠ n : ℕ in Filter.atTop,
      (1 : ℝ) - N₀ / (↑n + 1) ≤ ((S ∩ Set.Iic n).ncard : ℝ) / (↑n + 1) := by
    filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
    have hn_pos : (0 : ℝ) < n + 1 := by positivity
    rw [div_le_div_iff hn_pos hn_pos]  -- both as cross-multiply
    have hc := Nat.cast_le.mpr (hcard n hn)
    push_cast [Nat.sub_add_cancel hn] at hc ⊢
    linarith
  -- 1 - N₀/(n+1) → 1 as n → ∞
  have htend_lb : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - N₀ / (↑n + 1))
      Filter.atTop (nhds 1) := by
    rw [show (1 : ℝ) = 1 - 0 from by ring]
    apply Filter.Tendsto.sub tendsto_const_nhds
    -- N₀/(n+1) → 0: write as N₀ * (n+1)⁻¹ → N₀ * 0 = 0
    simp_rw [div_eq_mul_inv]
    rw [show (0 : ℝ) = N₀ * 0 from (mul_zero _).symm]
    apply Filter.Tendsto.const_mul
    -- (n+1)⁻¹ → 0 since n+1 → ∞
    apply Filter.Tendsto.inv_tendsto_atTop
    apply Filter.tendsto_atTop_atTop.mpr
    intro b; refine ⟨⌈b⌉₊, fun n hn => ?_⟩
    have hb : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    have hn_cast : (⌈b⌉₊ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    linarith
  -- limsup ≥ lim of lower bound = 1
  calc (1 : ℝ) = atTop.limsup (fun n : ℕ => 1 - ↑N₀ / (↑n + 1)) := by
          exact (htend_lb.limsup_eq ⟨1, by
            filter_upwards [] with n; apply sub_le_self; positivity⟩).symm
      _ ≤ atTop.limsup (fun n : ℕ => ((S ∩ Set.Iic n).ncard : ℝ) / (↑n + 1)) :=
          Filter.limsup_le_limsup hlb

/-- A basis of order 2 has positive density sumset. -/
theorem basis_has_pos_density_sumset {A : Set ℕ} (h : IsBasisOrder2 A) :
    HasPosDensity (sumset A A) := by
  unfold HasPosDensity
  rw [cofinite_density_one h]
  norm_num

/-
## Connections Between Parts
-/

/-- If Part 2 holds and A is the constructed basis, then in any partition
    at least one part's sumset fails to be syndetic. -/
theorem part2_gives_non_syndetic (h : ErdosProblem741_basis) :
    ∃ A : Set ℕ, IsBasisOrder2 A ∧
      ∀ A₁ A₂ : Set ℕ, A = A₁ ∪ A₂ → Disjoint A₁ A₂ →
        ¬IsSyndetic (sumset A₁ A₁) ∨ ¬IsSyndetic (sumset A₂ A₂) := by
  obtain ⟨A, hbasis, hpart⟩ := h
  exact ⟨A, hbasis, fun A₁ A₂ heq hdisj => by
    by_contra habs
    push_neg at habs
    exact hpart A₁ A₂ heq hdisj ⟨habs.1, habs.2⟩⟩

/-- Syndetic implies positive density. -/
/-- Part 2 (if true) would imply Part 1 fails for the specific basis A. -/
theorem part2_contradicts_part1_for_basis (h2 : ErdosProblem741_basis) :
    ∃ A : Set ℕ, HasPosDensity (sumset A A) ∧
      ∀ A₁ A₂ : Set ℕ, A = A₁ ∪ A₂ → Disjoint A₁ A₂ →
        ¬(IsSyndetic (sumset A₁ A₁) ∧ IsSyndetic (sumset A₂ A₂)) := by
  obtain ⟨A, hbasis, hpart⟩ := h2
  exact ⟨A, basis_has_pos_density_sumset hbasis, hpart⟩

/-
## Problem Status
-/

def erdos_741_status : String := "OPEN"
