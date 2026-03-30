/-
  Erdős Problem #106: Square Packing in the Unit Square

  Source: https://erdosproblems.com/106
  Status: OPEN

  Statement:
  Draw n squares inside the unit square with no common interior point.
  Let f(n) be the maximum possible sum of the side-lengths. Is f(k²+1) = k?

  Background:
  This problem dates back over 60 years. Erdős proved f(2) = 1 in an early
  paper for Hungarian high school students. The question asks whether adding
  one more square beyond a perfect k×k grid doesn't increase the sum.

  Known results:
  • f(2) = 1 (Erdős)
  • f(5) = 2 (Newman)
  • f(k²) = k (trivial from Cauchy-Schwarz: sum ≤ √(n·area) = √n)
  • f(k²+1) ≥ k (via k×k grid construction)
  • Halász bounds: f(k²+2c+1) ≥ k + c/k for c ≥ 1

  Erdős-Soifer conjecture: f(k²+2c+1) = k + c/k for |c| < k

  References:
  [Er94b] Erdős, "Some old and new problems in combinatorial geometry" (1994)
  [ErSo95] Erdős-Soifer, "Squares packing" (1995)
  [Ha84] Halász (1984) - improved lower bounds
  [BKU24] Baek-Koizumi-Ueoro (2024) - axis-parallel case

  Tags: discrete-geometry, packing, squares, optimization, open-problem
-/

import Mathlib

open Set Real

/-
## Squares in the Plane

A square is defined by its center and side length.
-/

/-- A square in the plane with sides parallel to axes -/
structure Square where
  center : ℝ × ℝ
  side : ℝ
  side_pos : side > 0

/-- The interior of a square -/
def Square.interior (s : Square) : Set (ℝ × ℝ) :=
  {p | |p.1 - s.center.1| < s.side / 2 ∧ |p.2 - s.center.2| < s.side / 2}

/-- The closure of a square (including boundary) -/
def Square.closure (s : Square) : Set (ℝ × ℝ) :=
  {p | |p.1 - s.center.1| ≤ s.side / 2 ∧ |p.2 - s.center.2| ≤ s.side / 2}

/-- Two squares have disjoint interiors -/
def DisjointInteriors (s₁ s₂ : Square) : Prop :=
  Disjoint s₁.interior s₂.interior

/-
## The Unit Square

The unit square [0,1] × [0,1].
-/

/-- The unit square -/
def unitSquare : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- A square is contained in the unit square -/
def ContainedInUnit (s : Square) : Prop :=
  s.closure ⊆ unitSquare

/-
## Valid Packings

A packing is a collection of squares with disjoint interiors inside the unit square.
-/

/-- A valid packing of n squares -/
structure Packing (n : ℕ) where
  squares : Fin n → Square
  contained : ∀ i, ContainedInUnit (squares i)
  disjoint : ∀ i j, i ≠ j → DisjointInteriors (squares i) (squares j)

/-- Sum of side lengths in a packing -/
noncomputable def Packing.sumSides {n : ℕ} (P : Packing n) : ℝ :=
  ∑ i : Fin n, (P.squares i).side

/-
## The Function f(n)

f(n) is the maximum sum of side lengths over all packings of n squares.
-/

/-- f(n): maximum sum of side lengths for n squares -/
noncomputable def f (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ P : Packing n, P.sumSides = s}

/-- f is well-defined: bounded above by √n (Cauchy-Schwarz) -/
axiom f_bounded : ∀ n : ℕ, f n ≤ Real.sqrt n

/-- f is monotone increasing -/
axiom f_mono : ∀ n m : ℕ, n ≤ m → f n ≤ f m

/-
## Known Exact Values
-/

/-- f(1) = 1: one square fills the unit square -/
theorem f_1 : f 1 = 1 := by
  have := f_perfect_square 1 (by omega)
  simpa using this

/-- f(2) = 1 (Erdős) -/
axiom f_2 : f 2 = 1

/-- f(4) = 2: four squares of side 1/2 -/
theorem f_4 : f 4 = 2 := by
  have := f_perfect_square 2 (by omega)
  norm_num at this
  exact this

/-- f(5) = 2 (Newman) -/
/-- f(9) = 3: nine squares of side 1/3 -/
theorem f_9 : f 9 = 3 := by
  have := f_perfect_square 3 (by omega)
  norm_num at this
  exact this

/-
## Perfect Squares: f(k²) = k
-/

/-- For perfect squares, f(k²) = k -/
axiom f_perfect_square : ∀ k : ℕ, k ≥ 1 → f (k^2) = k

/-- Cauchy-Schwarz upper bound: f(n) ≤ √n -/
theorem f_upper_bound (n : ℕ) : f n ≤ Real.sqrt n := f_bounded n

/-- The k×k grid achieves f(k²) = k -/
theorem perfect_square_achieved (k : ℕ) (hk : k ≥ 1) :
    ∃ P : Packing (k^2), P.sumSides = k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  -- Key arithmetic: center ± side/2 = n/k or (n+1)/k
  have ctr_lo : ∀ n : ℕ, (2 * (n : ℝ) + 1) / (2 * ↑k) - 1 / ↑k / 2 = ↑n / ↑k := by
    intro n; field_simp; ring
  have ctr_hi : ∀ n : ℕ, (2 * (n : ℝ) + 1) / (2 * ↑k) + 1 / ↑k / 2 = (↑n + 1) / ↑k := by
    intro n; field_simp; ring
  -- Row/column bounds
  have hrow : ∀ i : Fin (k ^ 2), i.val / k < k :=
    fun i => Nat.div_lt_of_lt_mul (show i.val < k * k from (sq k).symm ▸ i.isLt)
  have hcol : ∀ i : Fin (k ^ 2), i.val % k < k :=
    fun i => Nat.mod_lt _ (by omega)
  -- Construct the packing
  refine ⟨{
    squares := fun i => {
      center := ((2 * (↑(i.val / k) : ℝ) + 1) / (2 * ↑k),
                 (2 * (↑(i.val % k) : ℝ) + 1) / (2 * ↑k))
      side := 1 / ↑k
      side_pos := by positivity }
    contained := ?contained
    disjoint := ?disjoint
  }, ?sum_eq⟩
  case contained =>
    intro i p hp
    simp only [Square.closure, Set.mem_setOf_eq] at hp
    simp only [unitSquare, Set.mem_setOf_eq]
    obtain ⟨hpx, hpy⟩ := hp
    rw [abs_le] at hpx hpy
    set r := i.val / k; set c := i.val % k
    -- p.1 ∈ [r/k, (r+1)/k] and p.2 ∈ [c/k, (c+1)/k]
    have hx_lo : (↑r : ℝ) / ↑k ≤ p.1 := by linarith [ctr_lo r, hpx.1]
    have hx_hi : p.1 ≤ (↑r + 1) / ↑k := by linarith [ctr_hi r, hpx.2]
    have hy_lo : (↑c : ℝ) / ↑k ≤ p.2 := by linarith [ctr_lo c, hpy.1]
    have hy_hi : p.2 ≤ (↑c + 1) / ↑k := by linarith [ctr_hi c, hpy.2]
    have hr_ub : (↑r : ℝ) + 1 ≤ ↑k := by exact_mod_cast (hrow i)
    have hc_ub : (↑c : ℝ) + 1 ≤ ↑k := by exact_mod_cast (hcol i)
    exact ⟨le_trans (div_nonneg (Nat.cast_nonneg r) (le_of_lt hk0)) hx_lo,
           le_trans hx_hi ((div_le_one hk0).mpr hr_ub),
           le_trans (div_nonneg (Nat.cast_nonneg c) (le_of_lt hk0)) hy_lo,
           le_trans hy_hi ((div_le_one hk0).mpr hc_ub)⟩
  case disjoint =>
    intro i j hij
    rw [DisjointInteriors, Set.disjoint_left]
    intro p hp1 hp2
    simp only [Square.interior, Set.mem_setOf_eq] at hp1 hp2
    obtain ⟨hpx1, hpy1⟩ := hp1; obtain ⟨hpx2, hpy2⟩ := hp2
    rw [abs_lt] at hpx1 hpy1 hpx2 hpy2
    set r₁ := i.val / k; set c₁ := i.val % k
    set r₂ := j.val / k; set c₂ := j.val % k
    -- p.1 in (r₁/k, (r₁+1)/k) ∩ (r₂/k, (r₂+1)/k) forces r₁ = r₂
    have hr_eq : r₁ = r₂ := by
      by_contra h
      rcases lt_or_gt_of_ne h with hr | hr
      · -- r₁ < r₂: (r₁+1)/k ≤ r₂/k contradicts p.1 < (r₁+1)/k and r₂/k < p.1
        have : (↑r₁ + 1 : ℝ) ≤ ↑r₂ := by exact_mod_cast hr
        linarith [ctr_hi r₁, hpx1.2, ctr_lo r₂, hpx2.1, div_le_div_right hk0 |>.mpr this]
      · have : (↑r₂ + 1 : ℝ) ≤ ↑r₁ := by exact_mod_cast hr
        linarith [ctr_hi r₂, hpx2.2, ctr_lo r₁, hpx1.1, div_le_div_right hk0 |>.mpr this]
    -- Similarly c₁ = c₂
    have hc_eq : c₁ = c₂ := by
      by_contra h
      rcases lt_or_gt_of_ne h with hc | hc
      · have : (↑c₁ + 1 : ℝ) ≤ ↑c₂ := by exact_mod_cast hc
        linarith [ctr_hi c₁, hpy1.2, ctr_lo c₂, hpy2.1, div_le_div_right hk0 |>.mpr this]
      · have : (↑c₂ + 1 : ℝ) ≤ ↑c₁ := by exact_mod_cast hc
        linarith [ctr_hi c₂, hpy2.2, ctr_lo c₁, hpy1.1, div_le_div_right hk0 |>.mpr this]
    -- r₁ = r₂ ∧ c₁ = c₂ → i = j, contradicting hij
    exact absurd (Fin.ext (show i.val = j.val by
      calc i.val = k * r₁ + c₁ := (Nat.div_add_mod i.val k).symm
        _ = k * r₂ + c₂ := by rw [hr_eq, hc_eq]
        _ = j.val := Nat.div_add_mod j.val k)) hij
  case sum_eq =>
    simp only [Packing.sumSides, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

/-
## The Main Conjecture: f(k²+1) = k
-/

/-- Lower bound: f(k²+1) ≥ k from the k×k grid -/
theorem f_k2_plus_1_lower : ∀ k : ℕ, k ≥ 1 → f (k^2 + 1) ≥ k := by
  intro k hk
  have h1 : f (k^2) ≤ f (k^2 + 1) := f_mono (k^2) (k^2 + 1) (by omega)
  have h2 : f (k^2) = ↑k := f_perfect_square k hk
  linarith

/-- The main conjecture: f(k²+1) = k -/
def erdos106Conjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → f (k^2 + 1) = k

/-- Equivalently: one extra square doesn't help -/
theorem conjecture_equiv :
    erdos106Conjecture ↔ ∀ k ≥ 1, f (k^2 + 1) = f (k^2) := by
  constructor
  · intro h k hk
    rw [h k hk, f_perfect_square k hk]
  · intro h k hk
    rw [h k hk, f_perfect_square k hk]

/-
## Halász Lower Bounds

f(k²+2c+1) ≥ k + c/k for c ≥ 1
-/

/-- Halász bound for odd increments -/
axiom halasz_odd : ∀ k c : ℕ, k ≥ 1 → c ≥ 1 →
  f (k^2 + 2*c + 1) ≥ k + (c : ℝ) / k

/-- Halász bound for even increments -/
/-
## The Erdős-Soifer Conjecture

f(k²+2c+1) = k + c/k for |c| < k
-/

/-- The stronger Erdős-Soifer conjecture -/
def erdosSoiferConjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → ∀ c : ℤ, |c| < k →
    f (k^2 + (2*c + 1).toNat) = k + (c : ℝ) / k

/-- Praton's equivalence: main conjecture ↔ Erdős-Soifer conjecture -/
/-
## Axis-Parallel Case

When all squares have sides parallel to the unit square.
-/

/-- g(n): max sum with axis-parallel constraint (always satisfied in our def) -/
noncomputable def g (n : ℕ) : ℝ := f n

/-- Baek-Koizumi-Ueoro (2024): g(k²+1) = k for axis-parallel squares -/
axiom bku_theorem : ∀ k : ℕ, k ≥ 1 → g (k^2 + 1) = k

/-
## When Does f(n+1) = f(n)?
-/

/-- Set of n where adding one square doesn't help -/
def plateauSet : Set ℕ := {n | f (n + 1) = f n}

/-- 1 ∈ plateauSet since f(2) = f(1) = 1 -/
theorem one_in_plateau : 1 ∈ plateauSet := by
  unfold plateauSet
  simp only [Set.mem_setOf_eq]
  rw [f_2, f_1]

/-- k² ∈ plateauSet ↔ main conjecture for that k -/
theorem perfect_square_plateau (k : ℕ) (hk : k ≥ 1) :
    k^2 ∈ plateauSet ↔ f (k^2 + 1) = k := by
  unfold plateauSet
  simp only [Set.mem_setOf_eq]
  rw [f_perfect_square k hk]

/-
## The Open Problem
-/

/-- The main open question -/
def erdos106OpenProblem : Prop := erdos106Conjecture

#check f
#check erdos106Conjecture
#check erdosSoiferConjecture
#check halasz_odd
#check bku_theorem
