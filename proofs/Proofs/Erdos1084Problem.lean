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

/-- For a 1D separated config, the number of unit-distance pairs
    is at most n - 1. (Upper bound for f_1(n).)

    Proof sketch: Each point has at most 2 unit neighbors (one on
    each side). The unit-distance graph is a union of paths, hence
    a forest with at most n-1 edges. -/
axiom f1_upper_bound (n : ℕ) (hn : n ≥ 1) (C : SeparatedConfig1D n) :
  unitDistPairs1D C ≤ n - 1

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

/-- f_1(n) = n - 1 -/
axiom f1_exact (n : ℕ) (hn : n ≥ 1) :
  maxUnitDistPairs 1 n = n - 1

/- ## Two-Dimensional Case -/

/-- Erdős's upper bound: f_2(n) < 3n - c√n for some c > 0. -/
axiom f2_upper_erdos :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (maxUnitDistPairs 2 n : ℝ) < 3 * n - c * Real.sqrt n

/-- Harborth's exact formula (1974):
    f_2(n) = ⌊3n - √(12n - 3)⌋ for all n ≥ 2. -/
axiom harborth_exact (n : ℕ) (hn : n ≥ 2) :
  maxUnitDistPairs 2 n = Nat.floor (3 * (n : ℝ) - Real.sqrt (12 * n - 3))

/-- The triangular lattice achieves the maximum. -/
axiom triangular_lattice_optimal (n : ℕ) (hn : n ≥ 2) :
  ∃ C : SeparatedConfig 2 n, unitDistPairs C = maxUnitDistPairs 2 n

/-- Upper bound: f_2(n) < 3n (each point has ≤ 6 unit neighbors). -/
axiom f2_trivial_upper (n : ℕ) (hn : n ≥ 1) :
  maxUnitDistPairs 2 n < 3 * n

/- ## Three-Dimensional Case -/

/-- Leading coefficient in d=3: f_3(n) ~ 6n. -/
axiom f3_leading :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
    |(maxUnitDistPairs 3 n : ℝ) / n - 6| < ε

/-- Bezdek–Reid (2013): f_3(n) < 6n - 0.926 · n^(2/3). -/
axiom bezdek_reid_upper :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (maxUnitDistPairs 3 n : ℝ) < 6 * n - c * (n : ℝ) ^ (2/3 : ℝ)

/-- Erdős conjecture for d=3: f_3(n) = 6n - Θ(n^{2/3}). -/
axiom erdos_1084_d3_conjecture :
  ∃ c₁ c₂ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
      6 * (n : ℝ) - c₁ * (n : ℝ) ^ (2/3 : ℝ) ≤ (maxUnitDistPairs 3 n : ℝ) ∧
      (maxUnitDistPairs 3 n : ℝ) ≤ 6 * (n : ℝ) - c₂ * (n : ℝ) ^ (2/3 : ℝ)

/- ## General Dimension -/

/-- Lower bound: f_d(n) ≥ (d - o(1)) · n. -/
axiom fd_lower_general :
  ∀ d : ℕ, d ≥ 1 → ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
      (maxUnitDistPairs d n : ℝ) ≥ ((d : ℝ) - ε) * n

/-- Upper bound: f_d(n) ≤ 2^{O(d)} · n. -/
axiom fd_upper_general :
  ∃ C : ℝ, C > 0 ∧ ∀ d : ℕ, d ≥ 1 → ∀ n : ℕ, n ≥ 1 →
    (maxUnitDistPairs d n : ℝ) ≤ (2 : ℝ) ^ (C * d) * n
