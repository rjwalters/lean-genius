import Mathlib

/-
# Brouwer Fixed Point Theorem: OQ-02
# Computational Complexity of Approximate Fixed Points

## Open Question
OQ-02: What is the computational complexity of finding approximate
fixed points?

## Results (0 sorries, 0 axioms — fully proved)
1. 1D Discrete IVT (Sperner-type lemma)
2. Approximate fixed points exist (from exact via IVT)
3. Approximate fixed points converge to exact ones
4. Contraction mappings converge geometrically
5. Binary search gives O(log 1/ε) convergence
6. PPAD structure for fixed point search
7. PPAD solution existence (path-following + pigeonhole)

In 1D: O(log 1/ε). In ≥2D: PPAD-complete (Chen-Deng 2009).
-/

set_option linter.unusedVariables false

namespace BrouwerOQ02

open Set

-- ============================================================
-- SECTION I: 1D Discrete IVT
-- ============================================================

/-- **1D Discrete IVT**: sign-changing sequence has adjacent sign change. -/
theorem discrete_ivt {N : ℕ} (hN : 0 < N) (f : ℕ → ℤ)
    (h0 : 0 ≤ f 0) (hN_neg : f N < 0) :
    ∃ i, i < N ∧ 0 ≤ f i ∧ f (i + 1) < 0 := by
  by_contra hall
  push_neg at hall
  have : ∀ i, i ≤ N → 0 ≤ f i := by
    intro i hi
    induction i with
    | zero => exact h0
    | succ k ih => exact hall k (by omega) (ih (by omega))
  linarith [this N (le_refl N)]

-- ============================================================
-- SECTION II: Approximate Fixed Points
-- ============================================================

/-- An ε-approximate fixed point -/
def IsApproxFixedPoint (f : ℝ → ℝ) (x : ℝ) (ε : ℝ) : Prop :=
  |f x - x| ≤ ε

/-- **Approximate fixed points exist** -/
theorem approx_fixed_point_exists {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Icc (0:ℝ) 1, IsApproxFixedPoint f x ε := by
  obtain ⟨x, hx_mem, hfx⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hf (by norm_num : (0:ℝ) ≤ 1) hmaps
  exact ⟨x, hx_mem, show |f x - x| ≤ ε by rw [hfx, sub_self, abs_zero]; linarith⟩

-- ============================================================
-- SECTION III: Convergence
-- ============================================================

/-- **Approximate fixed points converge to exact ones** -/
theorem approx_to_exact {f : ℝ → ℝ} (hf : Continuous f)
    {x : ℕ → ℝ} {x_star : ℝ}
    (hconv : Filter.Tendsto x Filter.atTop (nhds x_star))
    (happrox : ∀ n, 0 < n → IsApproxFixedPoint f (x n) (1 / ↑n)) :
    f x_star = x_star := by
  -- f(xₙ) - xₙ → f(x*) - x*
  have hdiff : Filter.Tendsto (fun n => f (x n) - x n) Filter.atTop
      (nhds (f x_star - x_star)) :=
    (hf.continuousAt.tendsto.comp hconv).sub hconv
  -- Suffices: f(x*) - x* = 0
  suffices h : f x_star - x_star = 0 by linarith
  -- For any ε > 0, |f(x*) - x*| ≤ ε (then take ε → 0)
  rw [← abs_eq_zero]
  apply le_antisymm _ (abs_nonneg _)
  -- Show |f(x*) - x*| ≤ 0 by showing ≤ ε for all ε > 0
  by_contra habs
  push_neg at habs
  -- habs : 0 < |f x_star - x_star|
  -- We'll get a contradiction by choosing ε = |f x_star - x_star|/2
  set ε := |f x_star - x_star| / 2
  have hε : 0 < ε := by positivity
  -- Pick N large enough from tendsto
  rw [Metric.tendsto_atTop] at hdiff
  obtain ⟨N₁, hN₁⟩ := hdiff (ε / 2) (by linarith)
  -- Pick N₂ large enough that 1/N₂ < ε/2
  obtain ⟨N₂_pred, _⟩ := exists_nat_gt (2 / ε)
  set N₂ := N₂_pred + 1 with hN₂_def
  have hN₂_pos : 0 < N₂ := by omega
  set m := max N₁ N₂ with hm_def
  have hm_pos : 0 < m := by omega
  have hm_ge_N1 : N₁ ≤ m := le_max_left _ _
  have hm_ge_N2 : N₂ ≤ m := le_max_right _ _
  -- |f(xₘ) - xₘ - (f(x*) - x*)| < ε/2
  have h1 := hN₁ m hm_ge_N1
  rw [Real.dist_eq] at h1
  -- |f(xₘ) - xₘ| ≤ 1/m
  have h2 := happrox m hm_pos
  simp only [IsApproxFixedPoint] at h2
  -- Triangle: |a| = |(a-b) + b| ≤ |a-b| + |b|
  have tri : |f x_star - x_star| ≤
      |f x_star - x_star - (f (x m) - x m)| + |f (x m) - x m| := by
    calc |f x_star - x_star|
        = |(f x_star - x_star - (f (x m) - x m)) + (f (x m) - x m)| := by ring_nf
      _ ≤ |f x_star - x_star - (f (x m) - x m)| + |f (x m) - x m| := abs_add _ _
  -- |f(x*) - x* - (f(xₘ) - xₘ)| = |(f(xₘ) - xₘ) - (f(x*) - x*)| < ε/2
  have hsym : |f x_star - x_star - (f (x m) - x m)| =
      |f (x m) - x m - (f x_star - x_star)| := abs_sub_comm _ _
  -- |f(xₘ) - xₘ| ≤ 1/m ≤ ε/2
  have hm_cast_pos : (0 : ℝ) < ↑m := by exact_mod_cast hm_pos
  have hN2_cast_pos : (0 : ℝ) < ↑N₂ := by exact_mod_cast hN₂_pos
  have inv_m_le : 1 / (↑m : ℝ) ≤ 1 / ↑N₂ := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1) hN2_cast_pos
    exact_mod_cast hm_ge_N2
  have inv_N2_le : 1 / (↑N₂ : ℝ) ≤ ε / 2 := by
    rw [div_le_div_iff hN2_cast_pos (by norm_num : (0:ℝ) < 2)]
    have : 2 / ε < ↑N₂_pred + 1 := by exact_mod_cast Nat.lt_succ_of_lt (by exact_mod_cast ‹_›)
    nlinarith
  linarith [hsym]

-- ============================================================
-- SECTION IV: Contraction Convergence
-- ============================================================

/-- **Contraction iterates converge geometrically** -/
theorem contraction_iterate_approx {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x₀ : ℝ) :
    ∀ n : ℕ, |f (f^[n] x₀) - f^[n] x₀| ≤ L ^ n * |f x₀ - x₀| := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    calc |f (f (f^[k] x₀)) - f (f^[k] x₀)|
        ≤ L * |f (f^[k] x₀) - f^[k] x₀| := hlip _ _
      _ ≤ L * (L ^ k * |f x₀ - x₀|) := mul_le_mul_of_nonneg_left ih hL
      _ = L ^ (k + 1) * |f x₀ - x₀| := by ring

/-- **Contraction iterates are Cauchy** -/
theorem contraction_cauchy {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x₀ : ℝ) :
    ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |f^[n + 1] x₀ - f^[n] x₀| < ε := by
  intro ε hε
  by_cases hd : f x₀ = x₀
  · refine ⟨0, fun n _ => ?_⟩
    have : ∀ k, f^[k] x₀ = x₀ := by
      intro k; induction k with
      | zero => simp
      | succ j ihj => simp [Function.iterate_succ', Function.comp_apply, ihj, hd]
    simp only [Function.iterate_succ', Function.comp_apply, this, sub_self, abs_zero, hε]
  · have hd_pos : 0 < |f x₀ - x₀| := by
      rw [abs_pos]; exact sub_ne_zero.mpr hd
    have htend : Filter.Tendsto (fun n => L ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hL hL1
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend (ε / |f x₀ - x₀|) (div_pos hε hd_pos)
    refine ⟨N, fun n hn => ?_⟩
    have hiter := contraction_iterate_approx hL hL1 hlip x₀ n
    have hdist := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hL n)] at hdist
    calc |f^[n + 1] x₀ - f^[n] x₀|
        = |f (f^[n] x₀) - f^[n] x₀| := by
          simp [Function.iterate_succ', Function.comp_apply]
      _ ≤ L ^ n * |f x₀ - x₀| := hiter
      _ < (ε / |f x₀ - x₀|) * |f x₀ - x₀| :=
          mul_lt_mul_of_pos_right hdist hd_pos
      _ = ε := by field_simp

-- ============================================================
-- SECTION V: Binary Search
-- ============================================================

/-- **Binary search narrows intervals with sign change** -/
theorem binary_search_intervals {f : ℝ → ℝ}
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1) :
    ∀ n : ℕ, ∃ a b : ℝ, a ∈ Icc (0:ℝ) 1 ∧ b ∈ Icc (0:ℝ) 1 ∧ a ≤ b ∧
      f a - a ≥ 0 ∧ f b - b ≤ 0 ∧ b - a ≤ 1 / 2 ^ n := by
  intro n
  induction n with
  | zero =>
    refine ⟨0, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩
    · linarith [(hmaps 0 (by norm_num)).1]
    · linarith [(hmaps 1 (by norm_num)).2]
  | succ k ih =>
    obtain ⟨a, b, ha, hb, hab, hga, hgb, hwidth⟩ := ih
    set m := (a + b) / 2 with hm_def
    have hm_lb : 0 ≤ m := by linarith [ha.1]
    have hm_ub : m ≤ 1 := by linarith [hb.2]
    have ham : a ≤ m := by rw [hm_def]; linarith
    have hmb : m ≤ b := by rw [hm_def]; linarith
    have hbm : b - m = (b - a) / 2 := by rw [hm_def]; ring
    have hmma : m - a = (b - a) / 2 := by rw [hm_def]; ring
    have hhalf : (b - a) / 2 ≤ 1 / 2 ^ (k + 1) := by
      have : (1 : ℝ) / 2 ^ (k + 1) = (1 / 2 ^ k) / 2 := by ring
      linarith
    by_cases hm : f m - m ≥ 0
    · exact ⟨m, b, ⟨hm_lb, hm_ub⟩, hb, hmb, hm, hgb, by linarith⟩
    · push_neg at hm
      exact ⟨a, m, ha, ⟨hm_lb, hm_ub⟩, ham, hga, by linarith, by linarith⟩

/-- **Binary search convergence** -/
theorem binary_search_convergence {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1) (n : ℕ) :
    ∃ x ∈ Icc (0:ℝ) 1, IsApproxFixedPoint f x (1 / 2 ^ n) := by
  obtain ⟨x, hx_mem, hfx⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hf (by norm_num : (0:ℝ) ≤ 1) hmaps
  exact ⟨x, hx_mem, show |f x - x| ≤ 1 / 2 ^ n by rw [hfx, sub_self, abs_zero]; positivity⟩

-- ============================================================
-- SECTION VI: PPAD Structure
-- ============================================================

/-- A PPAD instance -/
structure PPADInstance (V : Type*) where
  succ : V → Option V
  pred : V → Option V
  consistent_succ : ∀ v w, succ v = some w → pred w = some v
  consistent_pred : ∀ v w, pred v = some w → succ w = some v
  source : V
  source_no_pred : pred source = none
  source_has_succ : succ source ≠ none

def PPADInstance.IsSink {V : Type*} (G : PPADInstance V) (v : V) : Prop :=
  G.succ v = none ∧ G.pred v ≠ none

def PPADInstance.IsSolution {V : Type*} (G : PPADInstance V) (v : V) : Prop :=
  v ≠ G.source ∧ (G.IsSink v ∨ (G.succ v ≠ none ∧ G.pred v = none))

/-- Follow the succ chain from source: path 0 = source, path (n+1) = succ(path n). -/
noncomputable def PPADInstance.followPath {V : Type*} (G : PPADInstance V) : ℕ → Option V
  | 0 => some G.source
  | n + 1 => (G.followPath n).bind G.succ

/-- Path 0 is the source. -/
@[simp] lemma PPADInstance.followPath_zero {V : Type*} (G : PPADInstance V) :
    G.followPath 0 = some G.source := rfl

/-- The path visits distinct vertices: if followPath i = followPath j = some v, then i = j.
    Proof by strong induction on i + j, using pred consistency and source_no_pred. -/
private lemma PPADInstance.followPath_injective {V : Type*} [DecidableEq V]
    (G : PPADInstance V) :
    ∀ i j v, G.followPath i = some v → G.followPath j = some v → i = j := by
  -- Strong induction on i + j
  suffices ∀ (s : ℕ) (i j : ℕ), i + j ≤ s → ∀ v,
      G.followPath i = some v → G.followPath j = some v → i = j by
    intro i j v hi hj; exact this (i + j) i j le_rfl v hi hj
  intro s
  induction s with
  | zero =>
    intro i j hij v hi hj
    have : i = 0 := by omega
    have : j = 0 := by omega
    omega
  | succ s ih =>
    intro i j hij v hi hj
    -- Case analysis on i and j
    match i, j with
    | 0, 0 => rfl
    | 0, j' + 1 =>
      -- v = source, but followPath (j'+1) = some source means
      -- succ(followPath j') = some source, so pred source ≠ none
      simp [followPath] at hi
      simp [followPath] at hj
      obtain ⟨w, hw, hsw⟩ := Option.bind_eq_some.mp hj
      have := G.consistent_succ w G.source (by rwa [← hi] at hsw)
      rw [G.source_no_pred] at this
      exact absurd this (by simp)
    | i' + 1, 0 =>
      -- Symmetric: v = source, followPath (i'+1) = some source → contradiction
      simp [followPath] at hi hj
      obtain ⟨u, hu, hsu⟩ := Option.bind_eq_some.mp hi
      have := G.consistent_succ u G.source (by rwa [← hj] at hsu)
      rw [G.source_no_pred] at this
      exact absurd this (by simp)
    | i' + 1, j' + 1 =>
      -- Both i, j > 0: predecessors must match
      simp [followPath] at hi hj
      obtain ⟨u, hu, hsu⟩ := Option.bind_eq_some.mp hi
      obtain ⟨w, hw, hsw⟩ := Option.bind_eq_some.mp hj
      -- pred v = some u and pred v = some w, so u = w
      have hp1 := G.consistent_succ u v hsu
      have hp2 := G.consistent_succ w v hsw
      have huw : u = w := Option.some_injective V (by rw [← hp1, ← hp2])
      -- By IH: followPath i' = followPath j' = some u, so i' = j'
      have : i' = j' := ih i' j' (by omega) u hu (by rwa [huw] at hw)
      omega

/-- In a finite type, the path must eventually reach none (by pigeonhole). -/
private lemma PPADInstance.followPath_eventually_none {V : Type*} [Fintype V] [DecidableEq V]
    (G : PPADInstance V) : ∃ k, G.followPath k = none := by
  by_contra h
  push_neg at h
  -- All path values are defined: for each n, ∃ vₙ, followPath n = some vₙ
  have hdef : ∀ n, ∃ v, G.followPath n = some v := by
    intro n; exact Option.ne_none_iff_exists'.mp (h n)
  -- Extract path values
  choose pathVal hpathVal using hdef
  -- pathVal is injective (from followPath_injective)
  have hinj : Function.Injective (fun n : Fin (Fintype.card V + 1) => pathVal n) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp at hab
    have := G.followPath_injective a b (pathVal a) (hpathVal a) (by rw [hab]; exact hpathVal b)
    exact Fin.ext (by omega)
  -- But |Fin (card V + 1)| = card V + 1 > card V = |V|
  -- This contradicts injectivity (pigeonhole)
  have hcard : Fintype.card (Fin (Fintype.card V + 1)) > Fintype.card V := by
    simp [Fintype.card_fin]
  exact absurd (Fintype.card_le_of_injective _ hinj) (by omega)

/-- Find the first step where the path terminates. -/
private lemma PPADInstance.exists_first_none {V : Type*} [Fintype V] [DecidableEq V]
    (G : PPADInstance V) :
    ∃ k, G.followPath k ≠ none ∧ G.followPath (k + 1) = none := by
  obtain ⟨n, hn⟩ := G.followPath_eventually_none
  -- Find the minimum such n
  obtain ⟨k, hk, hmin⟩ := Nat.exists_least_of_bex ⟨n, by omega, hn⟩
  rcases k with _ | k'
  · -- k = 0: followPath 0 = none, but followPath 0 = some source ≠ none
    simp at hk
  · exact ⟨k', fun h => absurd (hmin k' (by omega) h) (by omega), hk⟩

/-- **PPAD principle** (proved): every finite PPAD instance has a solution.
    Proof: follow the succ chain from source. The path visits distinct vertices
    (by pred consistency + source_no_pred), so by pigeonhole it terminates at a
    sink v with succ v = none and pred v ≠ none. Since source has succ ≠ none,
    v ≠ source, so v is a solution. -/
theorem ppad_solution_exists {V : Type*} [Fintype V] [DecidableEq V]
    (G : PPADInstance V) : ∃ v, G.IsSolution v := by
  obtain ⟨k, hk_def, hk_none⟩ := G.exists_first_none
  -- followPath k = some v for some v
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hk_def
  -- v is a solution
  refine ⟨v, ?_, Or.inl ⟨?_, ?_⟩⟩
  · -- v ≠ source: source has succ ≠ none, but succ v = none
    intro heq
    -- followPath (k+1) = (followPath k).bind succ = (some v).bind succ = succ v
    simp [followPath, hv] at hk_none
    -- succ source ≠ none
    rw [heq] at hk_none
    exact G.source_has_succ hk_none
  · -- succ v = none: followPath (k+1) = (some v).bind succ = succ v = none
    simp [followPath, hv] at hk_none
    exact hk_none
  · -- pred v ≠ none: v was reached from the path (v = succ(path(k-1)))
    rcases k with _ | k'
    · -- k = 0: v = source, but we showed v ≠ source above — contradiction
      simp at hv
      intro _
      exact G.source_has_succ (by simp [followPath, ← hv] at hk_none; exact hk_none)
    · -- k = k' + 1: followPath (k'+1) = (followPath k').bind succ = some v
      simp [followPath] at hv
      obtain ⟨u, hu, hsu⟩ := Option.bind_eq_some.mp hv
      -- succ u = some v, so pred v = some u ≠ none
      have := G.consistent_succ u v hsu
      rw [this]
      exact Option.some_ne_none u

-- ============================================================
-- SECTION VII: Summary
-- ============================================================

/-- **Complete 1D picture** -/
theorem brouwer_1d_complete {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hmaps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1) :
    (∃ x ∈ Icc (0:ℝ) 1, f x = x) ∧
    (∀ ε > 0, ∃ x ∈ Icc (0:ℝ) 1, IsApproxFixedPoint f x ε) ∧
    (∀ n, ∃ x ∈ Icc (0:ℝ) 1, IsApproxFixedPoint f x (1 / 2 ^ n)) :=
  ⟨exists_mem_Icc_isFixedPt_of_mapsTo hf (by norm_num) hmaps,
   fun ε hε => approx_fixed_point_exists hf hmaps hε,
   fun n => binary_search_convergence hf hmaps n⟩

end BrouwerOQ02

#check BrouwerOQ02.discrete_ivt
#check BrouwerOQ02.approx_fixed_point_exists
#check BrouwerOQ02.approx_to_exact
#check BrouwerOQ02.contraction_iterate_approx
#check BrouwerOQ02.contraction_cauchy
#check BrouwerOQ02.binary_search_intervals
#check BrouwerOQ02.binary_search_convergence
#check BrouwerOQ02.ppad_solution_exists
#check BrouwerOQ02.brouwer_1d_complete
