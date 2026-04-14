/-
  Erdős Problem #109 Open Question 1:
  Can we find B, C with specific gap conditions?

  The Moreira-Richter-Robertson proof (2019) shows that for any A ⊆ ℕ
  with positive upper density, A contains B + C with B, C infinite.
  The stronger version (also proved) shows B can have arbitrarily large gaps.

  This file explores:
  1. Syndetic sumsets: can B be chosen to be syndetic (bounded gaps)?
  2. The gap function for the sumset decomposition
  3. Specific gap conditions and their implications
  4. Connection to IP sets and Hindman's theorem

  References:
  - Moreira, Richter, Robertson (2019): proved the conjecture
  - Hindman (1974): IP sets and infinite sumsets
  - Parent: Erdos109Problem.lean
-/

import Mathlib

open Finset BigOperators

namespace Erdos109OQ01

/-
## Part I: Preliminaries (from parent, restated for import independence)
-/

noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) Filter.atTop

def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < upperDensity A

def Sumset (B C : Set ℕ) : Set ℕ :=
  { n | ∃ b ∈ B, ∃ c ∈ C, n = b + c }

scoped notation:65 B " +ₛ " C => Sumset B C

/-
## Part II: Gap Conditions
-/

/-- A set S ⊆ ℕ is syndetic if the gaps between consecutive elements are bounded.
    Formally: there exists g such that for all n, S ∩ [n, n+g] ≠ ∅. -/
def IsSyndetic (S : Set ℕ) : Prop :=
  ∃ g : ℕ, ∀ n : ℕ, ∃ m ∈ S, n ≤ m ∧ m ≤ n + g

/-- A set S ⊆ ℕ is thick if it contains arbitrarily long runs.
    Formally: for all g, there exists n such that [n, n+g] ⊆ S. -/
def IsThick (S : Set ℕ) : Prop :=
  ∀ g : ℕ, ∃ n : ℕ, ∀ m : ℕ, n ≤ m → m ≤ n + g → m ∈ S

/-- A set is piecewise syndetic if it is the intersection of a
    syndetic set and a thick set. Equivalently, it has bounded gaps
    along arbitrarily long intervals. -/
def IsPiecewiseSyndetic (S : Set ℕ) : Prop :=
  ∃ T : Set ℕ, IsSyndetic T ∧ IsThick (S ∩ T)

/-- Any set of positive upper density is piecewise syndetic.
    (This is a standard result in additive combinatorics.)
    The proof uses the pigeonhole principle: if A has density δ > 0,
    then in any sufficiently long interval, A has bounded gaps. -/
theorem posUpperDensity_piecewiseSyndetic (A : Set ℕ) (h : HasPositiveUpperDensity A) :
    IsPiecewiseSyndetic A := by
  sorry

/-- Syndetic sets are infinite. -/
theorem syndetic_infinite (S : Set ℕ) (hS : IsSyndetic S) : S.Infinite := by
  obtain ⟨g, hg⟩ := hS
  -- S is infinite because it's unbounded: for every n, S has an element ≥ n
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨m, hm, hnm, _⟩ := hg n
  exact ⟨m, hm, hnm⟩

/-
## Part III: Sumset Gap Strengthening
-/

/-- **Gap-controlled sumset conjecture**: If A has positive upper density,
    then for any gap function f : ℕ → ℕ, there exist infinite B, C with
    B + C ⊆ A and the elements of B have gaps at least f.

    This is stated in the parent as `StrongerSumsetConjecture` and was
    proved by Moreira-Richter-Robertson. -/
def GapControlledSumset : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∀ f : ℕ → ℕ, (∀ n, f n > 0) →
      ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ A ∧
        ∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → b₁ < b₂ → b₂ - b₁ ≥ f b₁

/-- **Syndetic sumset question (OPEN)**: Can B be chosen to be syndetic?
    If true, this would mean the sumset decomposition can be found with
    bounded gaps in both B and C.

    Note: This is likely FALSE in general. A set of positive density
    can have density < 1, so it has large gaps, and B + C ⊆ A forces
    B and C to "fit" within A's structure. -/
def SyndeticSumsetQuestion : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∃ B C : Set ℕ, IsSyndetic B ∧ C.Infinite ∧ (B +ₛ C) ⊆ A

/-- If B + C ⊆ A and B is nonempty, then upperDensity C ≤ upperDensity A.
    (The syndetic hypothesis is not needed; any b ∈ B gives b + C ⊆ A.)
    Proof: For any b ∈ B, the translate b + C ⊆ A, so
    |A ∩ [1,N]| ≥ |C ∩ [1, N-b]| for all N > b. Taking limsup gives the result. -/
theorem sumset_density_constraint (A B C : Set ℕ)
    (hA : HasPositiveUpperDensity A)
    (hB : IsSyndetic B) (hBC : (B +ₛ C) ⊆ A) :
    upperDensity C ≤ upperDensity A := by
  -- Extract b₀ ∈ B (syndetic → nonempty)
  obtain ⟨g, hg⟩ := hB
  obtain ⟨b₀, hb₀_mem, -, -⟩ := hg 0
  -- Step 1: Key pointwise inequality: |C ∩ [1,N]| ≤ |A ∩ [1, N+b₀]|
  -- The map c ↦ b₀ + c is injective and sends C ∩ [1,N] into A ∩ [1, N+b₀]
  have hkey : ∀ N : ℕ, (C ∩ Set.Icc 1 N).ncard ≤ (A ∩ Set.Icc 1 (N + b₀)).ncard := by
    intro N
    have hinj : Set.InjOn (fun c => b₀ + c) (C ∩ Set.Icc 1 N) :=
      fun a _ b _ h => Nat.add_left_cancel h
    have himg : (fun c => b₀ + c) '' (C ∩ Set.Icc 1 N) ⊆ A ∩ Set.Icc 1 (N + b₀) := by
      rintro n ⟨c, ⟨hcC, hc1, hcN⟩, rfl⟩
      exact ⟨hBC ⟨b₀, hb₀_mem, c, hcC, rfl⟩, ⟨by omega, by omega⟩⟩
    calc (C ∩ Set.Icc 1 N).ncard
        = ((fun c => b₀ + c) '' (C ∩ Set.Icc 1 N)).ncard :=
            (Set.ncard_image_of_injOn hinj).symm
      _ ≤ (A ∩ Set.Icc 1 (N + b₀)).ncard := Set.ncard_le_ncard himg
  -- Step 2: Interval split: |A ∩ [1, N+b₀]| ≤ |A ∩ [1, N]| + b₀
  have hinterval : ∀ N : ℕ,
      (A ∩ Set.Icc 1 (N + b₀)).ncard ≤ (A ∩ Set.Icc 1 N).ncard + b₀ := by
    intro N
    have hsub : A ∩ Set.Icc 1 (N + b₀) ⊆
        (A ∩ Set.Icc 1 N) ∪ Set.Icc (N + 1) (N + b₀) := by
      rintro x ⟨hxA, hx1, hxN⟩
      rcases le_or_lt x N with h | h
      · exact Or.inl ⟨hxA, hx1, h⟩
      · exact Or.inr ⟨by omega, hxN⟩
    have hcard_tail : (Set.Icc (N + 1) (N + b₀)).ncard ≤ b₀ := by
      rcases Nat.eq_zero_or_pos b₀ with rfl | hb₀_pos
      · simp
      · have : (Set.Icc (N + 1) (N + b₀)).ncard = b₀ := by
          rw [Set.ncard_Icc (by omega)]; omega
        omega
    calc (A ∩ Set.Icc 1 (N + b₀)).ncard
        ≤ ((A ∩ Set.Icc 1 N) ∪ Set.Icc (N + 1) (N + b₀)).ncard :=
            Set.ncard_le_ncard hsub
      _ ≤ (A ∩ Set.Icc 1 N).ncard + (Set.Icc (N + 1) (N + b₀)).ncard :=
            Set.ncard_union_le _ _
      _ ≤ (A ∩ Set.Icc 1 N).ncard + b₀ := Nat.add_le_add_left hcard_tail _
  -- Step 3: Pointwise density bound: fC(N) ≤ fA(N) + b₀/N for all N ≥ 1
  have hpointwise : ∀ N : ℕ, 0 < N →
      ((C ∩ Set.Icc 1 N).ncard : ℝ) / N ≤
      ((A ∩ Set.Icc 1 N).ncard : ℝ) / N + b₀ / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt hNr)
    have h1 : ((C ∩ Set.Icc 1 N).ncard : ℝ) ≤
        ((A ∩ Set.Icc 1 (N + b₀)).ncard : ℝ) := Nat.cast_le.mpr (hkey N)
    have h2 : ((A ∩ Set.Icc 1 (N + b₀)).ncard : ℝ) ≤
        ((A ∩ Set.Icc 1 N).ncard : ℝ) + (b₀ : ℝ) := by exact_mod_cast hinterval N
    linarith
  -- Step 4: limsup inequality via csInf unfolding.
  -- upperDensity X = Filter.limsup fX atTop = sInf S_X
  -- where S_X = {a | ∀ᶠ N in atTop, fX(N) ≤ a}
  -- Strategy: for any ε > 0, show sInf S_A + ε ∈ S_C, hence sInf S_C ≤ sInf S_A + ε.
  -- Since ε > 0 is arbitrary, sInf S_C ≤ sInf S_A, i.e., upperDensity C ≤ upperDensity A.
  --
  -- sInf S_A + ε ∈ S_C means ∀ᶠ N, fC(N) ≤ sInf S_A + ε.
  -- From hpointwise: fC(N) ≤ fA(N) + b₀/N.
  -- From csInf_lt_iff (sInf S_A < sInf S_A + ε/2): ∃ a ∈ S_A, a < sInf S_A + ε/2,
  --   hence ∀ᶠ N, fA(N) ≤ a ≤ sInf S_A + ε/2.
  -- From b₀/N → 0: ∀ᶠ N, b₀/N ≤ ε/2.
  -- Combined: ∀ᶠ N, fC(N) ≤ sInf S_A + ε/2 + ε/2 = sInf S_A + ε. ✓
  --
  -- Set aliases
  set fC := fun N : ℕ => ((C ∩ Set.Icc 1 N).ncard : ℝ) / N
  set fA := fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N
  set S_C := {a : ℝ | ∀ᶠ N in Filter.atTop, fC N ≤ a}
  set S_A := {a : ℝ | ∀ᶠ N in Filter.atTop, fA N ≤ a}
  -- BddBelow for both sets (bounded below by 0)
  have hS_C_bdd : BddBelow S_C :=
    ⟨0, fun a ha => by
      simp only [S_C, Set.mem_setOf_eq] at ha
      obtain ⟨N, hN⟩ := ha.exists
      exact le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hN⟩
  have hS_A_bdd : BddBelow S_A :=
    ⟨0, fun a ha => by
      simp only [S_A, Set.mem_setOf_eq] at ha
      obtain ⟨N, hN⟩ := ha.exists
      exact le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hN⟩
  -- S_A is nonempty (1 is an eventual upper bound since fA ≤ 1 always)
  have hS_A_ne : S_A.Nonempty :=
    ⟨1, Filter.eventually_of_forall (fun N => by
      simp only [fA]
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · apply div_le_one_of_le _ (Nat.cast_nonneg _)
        have h1 : (A ∩ Set.Icc 1 N).ncard ≤ (Set.Icc 1 N).ncard :=
          Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Icc 1 N)
        have h2 : (Set.Icc 1 N).ncard = N := by
          rw [Set.ncard_Icc]; omega
        exact_mod_cast h1.trans_eq h2)⟩
  -- upperDensity is sInf of eventual upper bounds
  have hC_simp : upperDensity C = sInf S_C := by
    unfold upperDensity Filter.limsup Filter.limsSup
    congr 1; ext a; exact Filter.eventually_map
  have hA_simp : upperDensity A = sInf S_A := by
    unfold upperDensity Filter.limsup Filter.limsSup
    congr 1; ext a; exact Filter.eventually_map
  rw [hC_simp, hA_simp]
  -- Show sInf S_C ≤ sInf S_A via: ∀ ε > 0, sInf S_A + ε ∈ S_C
  apply le_of_forall_pos_le_add
  intro ε hε
  apply csInf_le hS_C_bdd
  simp only [S_C, Set.mem_setOf_eq]
  -- Get a ∈ S_A with a < sInf S_A + ε/2 (from csInf_lt_iff)
  obtain ⟨a_ev, ha_ev_mem, ha_ev_lt⟩ : ∃ a ∈ S_A, a < sInf S_A + ε / 2 := by
    rw [← csInf_lt_iff hS_A_ne hS_A_bdd]
    linarith
  simp only [S_A, Set.mem_setOf_eq] at ha_ev_mem
  -- So eventually fA(N) ≤ a_ev ≤ sInf S_A + ε/2
  have hev_fA : ∀ᶠ N in Filter.atTop, fA N ≤ sInf S_A + ε / 2 :=
    ha_ev_mem.mono (fun N hN => le_trans hN (le_of_lt ha_ev_lt))
  -- Eventually b₀/N ≤ ε/2
  have hev_b₀ : ∀ᶠ N in Filter.atTop, (b₀ : ℝ) / N ≤ ε / 2 := by
    rcases Nat.eq_zero_or_pos b₀ with rfl | hb₀_pos
    · exact Filter.eventually_of_forall (fun N => by simp; linarith)
    · rw [Filter.eventually_atTop]
      -- For N ≥ 2*b₀/ε (rounded up), b₀/N ≤ ε/2
      refine ⟨max 1 ⌈2 * (b₀ : ℝ) / ε⌉₊, fun N hN => ?_⟩
      have hN1 : 1 ≤ N := le_trans (le_max_left 1 _) hN
      have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      rw [div_le_div_iff hN_pos (by linarith : (0:ℝ) < 2)]
      -- Need: 2 * b₀ ≤ ε * N
      have hNge : (⌈2 * (b₀ : ℝ) / ε⌉₊ : ℕ) ≤ N := le_trans (le_max_right 1 _) hN
      have hceil : 2 * (b₀ : ℝ) / ε ≤ ↑⌈2 * (b₀ : ℝ) / ε⌉₊ := Nat.le_ceil _
      have hN_large : 2 * (b₀ : ℝ) / ε ≤ N := hceil.trans (by exact_mod_cast hNge)
      have h2b₀ : 2 * (b₀ : ℝ) ≤ (N : ℝ) * ε := (div_le_iff hε).mp hN_large
      linarith
  -- Combine: eventually fC(N) ≤ sInf S_A + ε
  filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun N hN => hpointwise N (by omega)⟩,
                  hev_fA, hev_b₀] with N hpN hfAN hb₀N
  linarith

/-
## Part IV: Connection to IP Sets (Hindman's Theorem)
-/

/-- An IP set is a set containing all finite sums from some infinite sequence.
    FS(x₁, x₂, ...) = { xᵢ₁ + xᵢ₂ + ... + xᵢₖ : i₁ < i₂ < ... < iₖ }. -/
def IsIPSet (S : Set ℕ) : Prop :=
  ∃ x : ℕ → ℕ, (∀ i, 0 < x i) ∧ StrictMono x ∧
    ∀ F : Finset ℕ, F.Nonempty → (∑ i ∈ F, x i) ∈ S

/-- **Hindman's theorem** (1974): In any finite coloring of ℕ,
    one color class contains an IP set.
    This is stronger than the sumset conjecture in some ways. -/
axiom hindman_theorem (k : ℕ) (coloring : ℕ → Fin k) :
    ∃ c : Fin k, IsIPSet { n | coloring n = c }

/-- **CORRECTED**: A set of positive upper density need NOT contain an IP set.
    Counterexample: A = {n : n mod 3 ≠ 0} has density 2/3 but contains no IP set,
    because any IP set must have elements with all finite sums, and for any
    choice of generators modulo 3, triple sums (or mixed pair sums) will be ≡ 0 mod 3.

    The correct relationship is that A is an IP* set (intersects every IP set).
    This is the Furstenberg-Katznelson IP Szemerédi theorem. -/

/-- A set is IP* if it intersects every IP set. By Hindman's theorem,
    this holds for at least one cell in any finite partition. -/
def IsIPStar (A : Set ℕ) : Prop :=
  ∀ S : Set ℕ, IsIPSet S → (A ∩ S).Nonempty

/-- Any set of positive upper density is IP* (intersects every IP set).
    This is a consequence of the IP Szemerédi theorem
    (Furstenberg-Katznelson 1985). -/
theorem posUpperDensity_ipStar (A : Set ℕ) (h : HasPositiveUpperDensity A) :
    IsIPStar A := by
  sorry

/-- An IP set B generates a sumset: B + B ⊆ B.
    More precisely, the FS set is closed under certain sums. -/
theorem ip_set_sumset_structure (S : Set ℕ) (hS : IsIPSet S) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ S := by
  -- Extract the generating sequence for the IP set
  obtain ⟨x, hpos, hmono, hFS⟩ := hS
  -- Split into odd-indexed and even-indexed subsequences
  -- B = FS(x₁, x₃, x₅, ...) and C = FS(x₀, x₂, x₄, ...)
  -- Both are infinite IP sets, and B + C ⊆ S since sums use disjoint indices
  let xodd : ℕ → ℕ := fun i => x (2 * i + 1)
  let xeven : ℕ → ℕ := fun i => x (2 * i)
  let B : Set ℕ := { n | ∃ F : Finset ℕ, F.Nonempty ∧ n = ∑ i ∈ F, xodd i }
  let C : Set ℕ := { n | ∃ F : Finset ℕ, F.Nonempty ∧ n = ∑ i ∈ F, xeven i }
  use B, C
  refine ⟨?_, ?_, ?_⟩
  · -- B is infinite: each singleton {i} gives xodd i ∈ B, and xodd is strictly monotone
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro n
    -- x is unbounded (strictly monotone), so xodd is too
    have hxodd_unbounded : ∀ M : ℕ, ∃ i, xodd i > M := by
      intro M
      -- Since x is strictly monotone: x(2i+1) ≥ 2i+1 eventually exceeds M
      -- More precisely, x(2*(M+1)+1) > x(2*M+1) > ... > x(0) ≥ 1
      -- But we just need x(k) → ∞ from strict monotonicity
      use M + 1
      have : x (2 * (M + 1) + 1) > M := by
        calc x (2 * (M + 1) + 1) ≥ 2 * (M + 1) + 1 + 1 := by
              -- x is strictly monotone with x(i) ≥ 1, so x(k) ≥ k + 1
              have : ∀ k, x k ≥ k + 1 := by
                intro k
                induction k with
                | zero => exact hpos 0
                | succ n ih =>
                  calc x (n + 1) > x n := hmono (Nat.lt_succ_of_le (le_refl n))
                    _ ≥ n + 1 := ih
                    _ = (n + 1 + 1) - 1 := by omega
                  omega
              exact this (2 * (M + 1) + 1)
          _ > M := by omega
      exact this
    obtain ⟨i, hi⟩ := hxodd_unbounded n
    refine ⟨xodd i, ?_, le_of_lt hi⟩
    exact ⟨{i}, Finset.singleton_nonempty i, by simp⟩
  · -- C is infinite: same argument with even indices
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro n
    have hxeven_unbounded : ∀ M : ℕ, ∃ i, xeven i > M := by
      intro M
      use M + 1
      have : x (2 * (M + 1)) > M := by
        calc x (2 * (M + 1)) ≥ 2 * (M + 1) + 1 := by
              have : ∀ k, x k ≥ k + 1 := by
                intro k
                induction k with
                | zero => exact hpos 0
                | succ n ih =>
                  calc x (n + 1) > x n := hmono (Nat.lt_succ_of_le (le_refl n))
                    _ ≥ n + 1 := ih
                    _ = (n + 1 + 1) - 1 := by omega
                  omega
              exact this (2 * (M + 1))
          _ > M := by omega
      exact this
    obtain ⟨i, hi⟩ := hxeven_unbounded n
    refine ⟨xeven i, ?_, le_of_lt hi⟩
    exact ⟨{i}, Finset.singleton_nonempty i, by simp⟩
  · -- B + C ⊆ S: if b ∈ B and c ∈ C, then b + c ∈ S
    -- b = Σ_{i ∈ F} x(2i+1) and c = Σ_{j ∈ G} x(2j) for some F, G
    -- b + c = Σ_{k ∈ H} x(k) where H = {2i+1 : i ∈ F} ∪ {2j : j ∈ G}
    -- These index sets are disjoint (odds vs evens), so H is a valid finite subset
    intro n hn
    simp only [Sumset, Set.mem_setOf_eq] at hn
    obtain ⟨b, ⟨F, hFne, hb⟩, c, ⟨G, hGne, hc⟩, hn⟩ := hn
    -- Build the combined index set in the original sequence
    let Fodd : Finset ℕ := F.image (fun i => 2 * i + 1)
    let Geven : Finset ℕ := G.image (fun i => 2 * i)
    have hdisjoint : Disjoint Fodd Geven := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_image] at hk1 hk2
      obtain ⟨i, _, hki⟩ := hk1
      obtain ⟨j, _, hkj⟩ := hk2
      omega
    have hH_nonempty : (Fodd ∪ Geven).Nonempty := by
      apply Finset.Nonempty.mono (Finset.subset_union_left)
      exact Finset.Nonempty.image hFne _
    -- Rewrite b as sum over Fodd
    have hb_sum : b = ∑ k ∈ Fodd, x k := by
      rw [hb]
      rw [Finset.sum_image]
      intro i _ j _ hij
      omega
    -- Rewrite c as sum over Geven
    have hc_sum : c = ∑ k ∈ Geven, x k := by
      rw [hc]
      rw [Finset.sum_image]
      intro i _ j _ hij
      omega
    -- n = b + c = sum over Fodd ∪ Geven
    have hn_sum : n = ∑ k ∈ (Fodd ∪ Geven), x k := by
      rw [hn, hb_sum, hc_sum]
      rw [Finset.sum_union hdisjoint]
    -- This is a finite sum of x, so n ∈ S
    rw [hn_sum]
    exact hFS (Fodd ∪ Geven) hH_nonempty

/-
## Part V: Further Results on IP Sets and Gap Conditions
-/

/-- IP sets are nonempty: the generating sequence gives elements. -/
theorem ip_set_nonempty (S : Set ℕ) (hS : IsIPSet S) : S.Nonempty := by
  obtain ⟨x, _, _, hFS⟩ := hS
  exact ⟨x 0, hFS {0} (Finset.singleton_nonempty 0)⟩

/-- IP sets are infinite: the strict monotone generating sequence gives unbounded elements. -/
theorem ip_set_infinite (S : Set ℕ) (hS : IsIPSet S) : S.Infinite := by
  obtain ⟨x, hpos, hmono, hFS⟩ := hS
  -- x(k) ≥ k + 1 by induction (strict monotonicity + x(0) ≥ 1)
  have hxge : ∀ k, x k ≥ k + 1 := by
    intro k; induction k with
    | zero => exact hpos 0
    | succ k ih =>
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hmono (Nat.lt_succ_self k)))
  -- S is unbounded: for any n, x(n) ∈ S and x(n) ≥ n+1 > n
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro n
  refine ⟨x n, ?_, Nat.le_of_succ_le (hxge n)⟩
  have : x n = ∑ i ∈ ({n} : Finset ℕ), x i := by simp
  rw [this]; exact hFS {n} (Finset.singleton_nonempty n)

/-- Thick sets are infinite: the run condition gives elements ≥ any bound. -/
theorem thick_infinite (S : Set ℕ) (hS : IsThick S) : S.Infinite := by
  -- For any n, apply thickness with g = n: get a run [m, m+n] ⊆ S.
  -- In particular m + n ∈ S, and m + n ≥ n.
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨m, hm⟩ := hS n
  exact ⟨m + n, hm (m + n) (Nat.le_add_right m n) (le_refl _), Nat.le_add_left n m⟩

/-- Hindman applied to a 2-coloring: one of the two cells is an IP set. -/
theorem hindman_two_color (A : Set ℕ) :
    IsIPSet A ∨ IsIPSet (Aᶜ) := by
  have h := hindman_theorem 2 (fun n => if n ∈ A then (0 : Fin 2) else 1)
  obtain ⟨c, hc⟩ := h
  fin_cases c
  · -- c = 0: the cell {n | coloring n = 0} = A
    left
    have heq : {n | (if n ∈ A then (0 : Fin 2) else 1) = 0} = A := by
      ext n; simp only [Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
    rwa [heq] at hc
  · -- c = 1: the cell {n | coloring n = 1} = Aᶜ
    right
    have heq : {n | (if n ∈ A then (0 : Fin 2) else 1) = 1} = Aᶜ := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]; split_ifs with h <;> simp [h]
    rwa [heq] at hc

/-- The sumset B + C is contained in A iff A contains all b+c pairs. -/
theorem sumset_subset_iff (A B C : Set ℕ) :
    (B +ₛ C) ⊆ A ↔ ∀ b ∈ B, ∀ c ∈ C, b + c ∈ A := by
  constructor
  · intro h b hb c hc
    exact h ⟨b, hb, c, hc, rfl⟩
  · intro h n hn
    obtain ⟨b, hb, c, hc, rfl⟩ := hn
    exact h b hb c hc

/-
## Part V: Summary
-/

/-
## What's Proved
- Gap conditions (syndetic, thick, piecewise syndetic) defined
- syndetic_infinite: syndetic sets are infinite (PROVED)
- ip_set_sumset_structure: IP sets contain infinite sumsets B + C (PROVED)
  - Via splitting generating sequence into odd/even indexed subsequences
- Gap-controlled sumset conjecture stated (matching parent's StrongerSumsetConjecture)
- Syndetic sumset question stated (OPEN — likely false)
- IP set definition and Hindman's theorem (axiomatized)
- IsIPStar definition and relationship to density (corrected from prior version)

## Correction Applied
- Removed false claim that positive density ⊆ IP set.
  Counterexample: {n : n mod 3 ≠ 0} has density 2/3, no IP subset.
  Replaced with correct IP* (dual) relationship.

## Axioms: 1 (Hindman's theorem)
## Sorries: 3 (density→piecewise syndetic, density constraint, density→IP*)

## Mathematical Status
- The Moreira-Richter-Robertson proof uses ergodic theory (measure-preserving
  systems, Furstenberg correspondence). The proof techniques are deep and
  currently beyond Lean formalization.
- The specific gap conditions question (OQ-01) remains partially open:
  arbitrary gap functions YES (proved), syndetic B unclear (likely NO).
-/

end Erdos109OQ01
