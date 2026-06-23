/-
# Erdős Problem #1084: Unit Distances Among Separated Points

Let f_d(n) be the maximum number of pairs at distance exactly 1 among
n points in ℝ^d with all pairwise distances ≥ 1. Estimate f_d(n).

## Key Results

- d = 1: f_1(n) = n - 1
- d = 2: f_2(n) = ⌊3n - √(12n-3)⌋ (Harborth, 1974)
- d = 2: f_2(n) < 3n - c√n (Erdős)
- d = 3: 6n - c₁n^{2/3} < f_3(n) < 6n - c₂n^{2/3} (conjectured,
  upper bound by Bezdek–Reid 2013)
- General: (d - o(1))n ≤ f_d(n) ≤ 2^{O(d)} · n

## Proved Theorems

- `unit_distance_1d_triangle`: In ℝ, if two points are both at unit
  distance from a third, with all pairwise distances ≥ 1, the two
  points are distance 2 apart (on opposite sides).
- `unit_distance_1d_degree_at_most_two`: A point in ℝ has at most
  2 neighbors at unit distance among mutually separated points.
- `f1_upper_bound`: For any 1D separated config on n points, the
  number of unit-distance pairs is at most n - 1. Proved via
  injection of unit pairs into Fin n via left-endpoint map.
- `f1_achievable`: The consecutive integer configuration 0, 1, ..., n-1
  achieves exactly n-1 unit-distance pairs.

## References

- Erdős (1946, 1975)
- Harborth (1974): exact formula for d = 2
- Bezdek–Reid (2013): d = 3 upper bound
- <https://erdosproblems.com/1084>
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A configuration of n points in ℝ^d where all pairwise distances are ≥ 1. -/
structure SeparatedConfig (d n : ℕ) where
  points : Fin n → EuclideanSpace ℝ (Fin d)
  separated : ∀ i j : Fin n, i ≠ j →
    dist (points i) (points j) ≥ 1

/-- The number of unit-distance pairs in a configuration. -/
noncomputable def unitDistPairs {d n : ℕ} (C : SeparatedConfig d n) : ℕ :=
  Finset.card (Finset.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ dist (C.points p.1) (C.points p.2) = 1)
    Finset.univ)

/-- f_d(n): maximum number of unit-distance pairs among n separated
    points in ℝ^d. -/
axiom maxUnitDistPairs (d n : ℕ) : ℕ

/- ## One-Dimensional Case: Working in ℝ Directly

For the 1D case, we work with real numbers directly instead of
EuclideanSpace ℝ (Fin 1), since |x - y| is more natural than
dist in EuclideanSpace for 1D proofs.
-/

/-- A separated configuration on the real line. -/
structure SeparatedConfig1D (n : ℕ) where
  points : Fin n → ℝ
  separated : ∀ i j : Fin n, i ≠ j →
    |points i - points j| ≥ 1

/-- Unit-distance pairs in a 1D configuration. -/
noncomputable def unitDistPairs1D {n : ℕ} (C : SeparatedConfig1D n) : ℕ :=
  (Finset.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ |C.points p.1 - C.points p.2| = 1)
    Finset.univ).card

/- ### Key 1D Lemma: Unit-Distance Triangle -/

/-- In ℝ, if two points y, z are both at unit distance from x,
    with all pairwise distances ≥ 1, then y and z are at distance 2
    (on opposite sides of x). -/
theorem unit_distance_1d_triangle (x y z : ℝ)
    (hxy : |x - y| = 1) (hxz : |x - z| = 1)
    (hyz : |y - z| ≥ 1) : |y - z| = 2 := by
  have hxy' := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hxy
  have hxz' := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hxz
  rcases hxy' with hxy' | hxy' <;> rcases hxz' with hxz' | hxz'
  · have : y = z := by linarith
    rw [this] at hyz; rw [sub_self, abs_zero] at hyz; linarith
  · have : y - z = -2 := by linarith
    rw [this]; norm_num
  · have : y - z = 2 := by linarith
    rw [this]; norm_num
  · have : y = z := by linarith
    rw [this] at hyz; rw [sub_self, abs_zero] at hyz; linarith

/-- In ℝ, a point can have at most 2 unit-distance neighbors among
    mutually separated points. If x has three unit neighbors y, z, w
    with all pairwise distances ≥ 1, we reach a contradiction.

    Proof: |x-y| = |x-z| = |x-w| = 1 means each of y,z,w is x+1 or x-1.
    By pigeonhole, two must be equal, contradicting separation ≥ 1. -/
theorem unit_distance_1d_degree_at_most_two (x y z w : ℝ)
    (hxy : |x - y| = 1) (hxz : |x - z| = 1) (hxw : |x - w| = 1)
    (hyz : |y - z| ≥ 1) (hyw : |y - w| ≥ 1) (hzw : |z - w| ≥ 1) :
    False := by
  have hxy' := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hxy
  have hxz' := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hxz
  have hxw' := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hxw
  rcases hxy' with hxy' | hxy' <;> rcases hxz' with hxz' | hxz' <;>
    rcases hxw' with hxw' | hxw'
  -- In each case, two variables are equal, so their separation is 0, not ≥ 1
  · have heq : y = z := by linarith
    subst heq; rw [sub_self, abs_zero] at hyz; linarith
  · have heq : y = z := by linarith
    subst heq; rw [sub_self, abs_zero] at hyz; linarith
  · have heq : y = w := by linarith
    subst heq; rw [sub_self, abs_zero] at hyw; linarith
  · have heq : z = w := by linarith
    subst heq; rw [sub_self, abs_zero] at hzw; linarith
  · have heq : z = w := by linarith
    subst heq; rw [sub_self, abs_zero] at hzw; linarith
  · have heq : y = w := by linarith
    subst heq; rw [sub_self, abs_zero] at hyw; linarith
  · have heq : y = z := by linarith
    subst heq; rw [sub_self, abs_zero] at hyz; linarith
  · have heq : y = z := by linarith
    subst heq; rw [sub_self, abs_zero] at hyz; linarith

/- ### Helper Lemmas for 1D Counting -/

/-- Distinct naturals have absolute difference ≥ 1 as reals. -/
private lemma nat_abs_sub_ge_one {a b : ℕ} (h : a ≠ b) :
    |(a : ℝ) - (b : ℝ)| ≥ 1 := by
  rcases Nat.lt_or_gt_of_ne h with hab | hab
  · have : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hab
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- For consecutive naturals, the real absolute difference is 1. -/
private lemma nat_consecutive_abs_eq_one (i : ℕ) :
    |(i : ℝ) - ((i + 1 : ℕ) : ℝ)| = 1 := by
  have : (i : ℝ) - ((i + 1 : ℕ) : ℝ) = -1 := by push_cast; ring
  rw [this, abs_neg, abs_one]

/- ### 1D Bounds -/

/-- If |a - b| = 1 and a ≤ b, then b = a + 1. -/
private lemma unit_dist_left {a b : ℝ} (hunit : |a - b| = 1) (hle : a ≤ b) :
    b = a + 1 := by
  have := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hunit
  rcases this with h | h <;> linarith

/-- For a 1D separated config, the number of unit-distance pairs
    is at most n - 1. (Upper bound for f_1(n).)

    Proof: Inject unit pairs into Fin n via the "left endpoint" map
    (the index whose real value is smaller). Injectivity: two pairs
    sharing a left endpoint at value v must both have their other
    index at value v + 1; by separation those indices coincide. The
    index with the globally maximum value cannot be a left endpoint,
    so the image has at most n - 1 elements. -/
theorem f1_upper_bound (n : ℕ) (hn : n ≥ 1) (C : SeparatedConfig1D n) :
    unitDistPairs1D C ≤ n - 1 := by
  unfold unitDistPairs1D
  set S := Finset.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ |C.points p.1 - C.points p.2| = 1)
    Finset.univ
  -- Find the index with the maximum point value
  obtain ⟨M, -, hM⟩ := Finset.exists_max_image Finset.univ C.points
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  -- Left-endpoint map: returns the index with smaller point value
  let f : Fin n × Fin n → Fin n := fun p =>
    if C.points p.1 ≤ C.points p.2 then p.1 else p.2
  -- f maps S into Finset.univ \ {M} (the max can never be a left endpoint)
  have himg : ∀ p ∈ S, f p ∈ Finset.univ.erase M := by
    rintro ⟨i, j⟩ hp
    have ⟨_, hlt, hunit⟩ := Finset.mem_filter.mp hp
    simp only [Finset.mem_erase, Ne, Finset.mem_univ, and_true, f]
    split_ifs with hle
    · -- Left endpoint is i; if i = M then j has value > max, contradiction
      intro heq; subst heq
      linarith [unit_dist_left hunit hle, hM j (Finset.mem_univ j)]
    · -- Left endpoint is j; if j = M then i has value > max, contradiction
      intro heq; subst heq; push_neg at hle
      have hswap : |C.points j - C.points i| = 1 := by rw [abs_sub_comm]; exact hunit
      linarith [unit_dist_left hswap (le_of_lt hle), hM i (Finset.mem_univ i)]
  -- f is injective on S
  have hinj : Set.InjOn f ↑S := by
    rintro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ hfeq
    have ⟨_, hlt₁, hu₁⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h₁)
    have ⟨_, hlt₂, hu₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h₂)
    show (i₁, j₁) = (i₂, j₂)
    simp only [f] at hfeq
    by_cases hle₁ : C.points i₁ ≤ C.points j₁ <;>
      by_cases hle₂ : C.points i₂ ≤ C.points j₂
    · -- Both: left = first index, so i₁ = i₂; right endpoints match by separation
      rw [if_pos hle₁, if_pos hle₂] at hfeq
      have hv₁ := unit_dist_left hu₁ hle₁
      have hv₂ := unit_dist_left hu₂ hle₂
      have hj : j₁ = j₂ := by
        by_contra hne
        have hsep := C.separated j₁ j₂ hne
        have : C.points j₁ = C.points j₂ := by linarith [congrArg C.points hfeq]
        rw [this, sub_self, abs_zero] at hsep; linarith
      exact Prod.ext hfeq hj
    · -- Mixed: i₁ = j₂, derive index ordering contradiction
      rw [if_pos hle₁, if_neg hle₂] at hfeq
      exfalso; push_neg at hle₂
      have hv₁ := unit_dist_left hu₁ hle₁
      have hu₂' : |C.points j₂ - C.points i₂| = 1 := by rw [abs_sub_comm]; exact hu₂
      have hv₂ := unit_dist_left hu₂' (le_of_lt hle₂)
      have hji : j₁ = i₂ := by
        by_contra hne
        have hsep := C.separated j₁ i₂ hne
        have : C.points j₁ = C.points i₂ := by linarith [congrArg C.points hfeq]
        rw [this, sub_self, abs_zero] at hsep; linarith
      -- i₁ < j₁ = i₂ < j₂ = i₁, contradiction
      simp only [Fin.lt_def, Fin.ext_iff] at hlt₁ hlt₂ hfeq hji
      omega
    · -- Symmetric mixed case: j₁ = i₂, same contradiction
      rw [if_neg hle₁, if_pos hle₂] at hfeq
      exfalso; push_neg at hle₁
      have hu₁' : |C.points j₁ - C.points i₁| = 1 := by rw [abs_sub_comm]; exact hu₁
      have hv₁ := unit_dist_left hu₁' (le_of_lt hle₁)
      have hv₂ := unit_dist_left hu₂ hle₂
      have hji : j₂ = i₁ := by
        by_contra hne
        have hsep := C.separated j₂ i₁ hne
        have : C.points j₂ = C.points i₁ := by linarith [congrArg C.points hfeq]
        rw [this, sub_self, abs_zero] at hsep; linarith
      simp only [Fin.lt_def, Fin.ext_iff] at hlt₁ hlt₂ hfeq hji
      omega
    · -- Both: left = second index, so j₁ = j₂; right endpoints match by separation
      rw [if_neg hle₁, if_neg hle₂] at hfeq
      push_neg at hle₁ hle₂
      have hu₁' : |C.points j₁ - C.points i₁| = 1 := by rw [abs_sub_comm]; exact hu₁
      have hu₂' : |C.points j₂ - C.points i₂| = 1 := by rw [abs_sub_comm]; exact hu₂
      have hv₁ := unit_dist_left hu₁' (le_of_lt hle₁)
      have hv₂ := unit_dist_left hu₂' (le_of_lt hle₂)
      have hi : i₁ = i₂ := by
        by_contra hne
        have hsep := C.separated i₁ i₂ hne
        have : C.points i₁ = C.points i₂ := by linarith [congrArg C.points hfeq]
        rw [this, sub_self, abs_zero] at hsep; linarith
      exact Prod.ext hi hfeq
  -- Apply the injection bound: |S| ≤ |univ \ {M}| = n - 1
  have hsub : S.image f ⊆ Finset.univ.erase M := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact himg p hp
  calc S.card
      = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ.erase M).card := Finset.card_le_card hsub
    _ = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ M), Finset.card_univ, Fintype.card_fin]

/-- The consecutive integer configuration achieves n-1 unit pairs.
    Place points at 0, 1, 2, ..., n-1.

    Proof: We place points at integer positions 0, 1, ..., n-1.
    Separation holds because distinct integers differ by ≥ 1.
    The unit-distance pairs are exactly the consecutive pairs
    (i, i+1) for i = 0, ..., n-2, giving n-1 pairs. -/
theorem f1_achievable (n : ℕ) (hn : n ≥ 1) :
    ∃ C : SeparatedConfig1D n, unitDistPairs1D C = n - 1 := by
  -- Configuration: points at 0, 1, 2, ..., n-1
  let C : SeparatedConfig1D n :=
    ⟨fun i => (i.val : ℝ), fun i j hij => nat_abs_sub_ge_one (Fin.val_ne_of_ne hij)⟩
  refine ⟨C, ?_⟩
  simp only [unitDistPairs1D]
  -- Map from Fin (n-1) to consecutive pairs: k ↦ (k, k+1)
  set φ : Fin (n - 1) → Fin n × Fin n :=
    fun k => (⟨k.val, by omega⟩, ⟨k.val + 1, by omega⟩) with hφ_def
  -- φ is injective
  have hinj : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Prod.mk.injEq, Fin.mk.injEq] at hxy
    exact Fin.ext hxy.1
  -- Show: filter set = image of φ, then card = n - 1
  suffices hset : Finset.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ |C.points p.1 - C.points p.2| = 1)
      Finset.univ = Finset.image φ Finset.univ by
    rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · -- Forward: (a, b) is unit pair → it's a consecutive pair from φ
    rintro ⟨hab, hunit⟩
    have hlt : a.val < b.val := hab
    have hlt' : (a.val : ℝ) < (b.val : ℝ) := Nat.cast_lt.mpr hlt
    have hdiff : (b.val : ℝ) - (a.val : ℝ) = 1 := by
      rwa [abs_sub_comm, abs_of_pos (by linarith)] at hunit
    have hba : b.val = a.val + 1 := by
      exact_mod_cast (show (b.val : ℝ) = (a.val : ℝ) + 1 by linarith)
    exact ⟨⟨a.val, by omega⟩, by simp only [φ]; exact Prod.ext (Fin.ext rfl) (Fin.ext hba.symm)⟩
  · -- Backward: consecutive pair from φ is a unit pair
    rintro ⟨k, hk⟩
    have ha : a = ⟨k.val, by omega⟩ := by
      have := congr_arg Prod.fst hk; simp only [φ] at this; exact this.symm
    have hb : b = ⟨k.val + 1, by omega⟩ := by
      have := congr_arg Prod.snd hk; simp only [φ] at this; exact this.symm
    subst ha; subst hb
    constructor
    · show (⟨k.val, _⟩ : Fin n) < ⟨k.val + 1, _⟩
      exact Fin.mk_lt_mk.mpr (Nat.lt_succ_of_le le_rfl)
    · exact nat_consecutive_abs_eq_one k.val

/- ## Two-Dimensional Case -/

/- ## Three-Dimensional Case -/

/- ## General Dimension -/
