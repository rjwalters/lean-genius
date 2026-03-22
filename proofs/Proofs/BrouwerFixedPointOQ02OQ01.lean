import Mathlib

/-
# 2D Sperner's Lemma

## Connection to Brouwer OQ-02 (PPAD Complexity)

The higher-dimensional Sperner's lemma is the combinatorial backbone of
the PPAD-completeness result for approximate Brouwer fixed points.
Chen-Deng (2009) proved that finding a fully-colored simplex in a
Sperner-colored triangulation is PPAD-complete, even in 2D.

## Approach

We formalize the 2D Sperner's lemma on a standard grid triangulation
of the unit triangle T = {(x,y) : x,y ≥ 0, x+y ≤ n}:

**Grid vertices**: (i, j) with i + j ≤ n.
**Triangles**: Two types per grid cell — "lower" and "upper".
**Sperner coloring**: Vertex (i,j) on edge opposite vertex k cannot use color k.

**Main result**: The number of fully-colored triangles is odd.

The proof uses a **door-counting** (double-counting) argument:
1. Define "doors" = edges colored {0,1}
2. Each fully-colored triangle has exactly 1 such door
3. Each {0,1}-colored triangle has exactly 2 doors (they cancel in parity)
4. Boundary {0,1} doors are odd (1D Sperner on the bottom edge)
5. Interior doors pair up (shared by two triangles)
6. Therefore: #(fully-colored triangles) is odd >= 1
-/

set_option linter.unusedVariables false

namespace Sperner2D

open Finset BigOperators

-- ============================================================
-- SECTION I: Grid Triangulation Definitions
-- ============================================================

structure GridVertex (n : ℕ) where
  i : ℕ
  j : ℕ
  valid : i + j ≤ n

inductive TriType
  | lower
  | upper

structure GridTriangle (n : ℕ) where
  i : ℕ
  j : ℕ
  ty : TriType
  valid : match ty with
    | .lower => i + 1 + j ≤ n
    | .upper => i + 1 + (j + 1) ≤ n

def lowerVertices (n : ℕ) (i j : ℕ) (h : i + 1 + j ≤ n) :
    Fin 3 → GridVertex n
  | 0 => ⟨i, j, by omega⟩
  | 1 => ⟨i + 1, j, by omega⟩
  | 2 => ⟨i, j + 1, by omega⟩

def upperVertices (n : ℕ) (i j : ℕ) (h : i + 1 + (j + 1) ≤ n) :
    Fin 3 → GridVertex n
  | 0 => ⟨i + 1, j, by omega⟩
  | 1 => ⟨i, j + 1, by omega⟩
  | 2 => ⟨i + 1, j + 1, by omega⟩

def GridTriangle.vertices {n : ℕ} (t : GridTriangle n) : Fin 3 → GridVertex n :=
  match t.ty, t.valid with
  | .lower, h => lowerVertices n t.i t.j h
  | .upper, h => upperVertices n t.i t.j h

-- ============================================================
-- SECTION II: Sperner Coloring
-- ============================================================

def Coloring (n : ℕ) := GridVertex n → Fin 3

def IsSperner {n : ℕ} (hn : 0 < n) (c : Coloring n) : Prop :=
  c ⟨0, 0, by omega⟩ = 0 ∧
  c ⟨n, 0, by omega⟩ = 1 ∧
  c ⟨0, n, by omega⟩ = 2 ∧
  (∀ v : GridVertex n, v.j = 0 → v.i > 0 → v.i < n → c v ≠ 2) ∧
  (∀ v : GridVertex n, v.i = 0 → v.j > 0 → v.j < n → c v ≠ 1) ∧
  (∀ v : GridVertex n, v.i + v.j = n → v.i > 0 → v.j > 0 → c v ≠ 0)

def IsFullyColored {n : ℕ} (c : Coloring n) (t : GridTriangle n) : Prop :=
  let colors := Finset.image (c ∘ t.vertices) Finset.univ
  colors = {0, 1, 2}

-- ============================================================
-- SECTION II-b: ZMod 2 Parity Helpers
-- ============================================================

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc a + a = 2 * a := by ring
    _ = 0 * a := by rw [h2]
    _ = 0 := by ring

private lemma zmod2_ne_indicator (a b : ZMod 2) :
    (if a ≠ b then (1 : ZMod 2) else 0) = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma sum_telescope :
    ∀ (n : ℕ) (f : Fin (n + 1) → ZMod 2),
    ∑ i : Fin n, (f ⟨i.val, by omega⟩ + f ⟨i.val + 1, by omega⟩) =
    f ⟨n, by omega⟩ + f ⟨0, by omega⟩ := by
  intro n
  induction n with
  | zero =>
    intro f
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (zmod2_add_self _).symm
  | succ k ih =>
    intro f
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have h := ih (fun j : Fin (k + 1) => f ⟨j.val, by omega⟩)
    simp only at h
    rw [h]
    have cancel := zmod2_add_self (f ⟨k, by omega⟩)
    calc f ⟨k, by omega⟩ + f ⟨0, by omega⟩ + (f ⟨k, by omega⟩ + f ⟨k + 1, by omega⟩)
        = (f ⟨k, by omega⟩ + f ⟨k, by omega⟩) + (f ⟨0, by omega⟩ + f ⟨k + 1, by omega⟩) := by
          ring
      _ = 0 + (f ⟨0, by omega⟩ + f ⟨k + 1, by omega⟩) := by rw [cancel]
      _ = f ⟨k + 1, by omega⟩ + f ⟨0, by omega⟩ := by ring

private lemma odd_of_zmod2_eq_one (m : ℕ) (h : (m : ZMod 2) = 1) : Odd m := by
  rw [Nat.odd_iff]
  have hval := ZMod.val_natCast (n := 2) m
  rw [h] at hval
  simpa using hval.symm

private theorem transitions_parity_aux (n : ℕ) (f : Fin (n + 1) → ZMod 2) :
    (Finset.card (Finset.filter (fun i : Fin n => f ⟨i.val, by omega⟩ ≠ f ⟨i.val + 1, by omega⟩)
      Finset.univ) : ZMod 2) = f ⟨n, by omega⟩ + f ⟨0, by omega⟩ := by
  rw [← Finset.sum_boole]
  simp_rw [zmod2_ne_indicator]
  exact sum_telescope n f

-- ============================================================
-- SECTION III: 1D Sperner on the Bottom Edge (Base Case)
-- ============================================================

def botVertex (n : ℕ) (i : Fin (n + 1)) : GridVertex n :=
  ⟨i.val, 0, by omega⟩

private def botColor {n : ℕ} (c : Coloring n) (i : ℕ) : Fin 3 :=
  if h : i ≤ n then c ⟨i, 0, by omega⟩ else 0

def bottomTransitions {n : ℕ} (c : Coloring n) : ℕ :=
  ((Finset.range n).filter (fun i => botColor c i ≠ botColor c (i + 1))).card

private theorem transitions_parity_bool (n : ℕ) (f : ℕ → Bool) :
    ((Finset.range n).filter (fun i => f i ≠ f (i + 1))).card % 2 =
    if f 0 = f n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_succ, Finset.filter_insert]
    by_cases hm : f m ≠ f (m + 1)
    · rw [if_pos hm]
      have hmem : m ∉ (Finset.range m).filter (fun i => f i ≠ f (i + 1)) := by
        simp [Finset.mem_filter, Finset.mem_range]
      rw [Finset.card_insert_of_not_mem hmem]
      set k := ((Finset.range m).filter (fun i => f i ≠ f (i + 1))).card with hk_def
      have hk := ih
      cases hf0 : f 0 <;> cases hfm : f m <;> cases hfm1 : f (m + 1) <;> simp_all <;> omega
    · rw [if_neg hm]
      rw [ih]
      push_neg at hm
      rw [hm]

theorem bottom_transitions_odd {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) : Odd (bottomTransitions c) := by
  obtain ⟨hv0, hv1, _, hbot, _, _⟩ := hc
  have hbot_colors : ∀ i, i ≤ n → botColor c i = 0 ∨ botColor c i = 1 := by
    intro i hi
    simp only [botColor, dif_pos hi]
    by_cases h0 : i = 0
    · subst h0; left; exact hv0
    · by_cases hn' : i = n
      · subst hn'; right; exact hv1
      · have hlt : i < n := by omega
        have hgt : i > 0 := by omega
        have h2 := hbot ⟨i, 0, by omega⟩ rfl hgt hlt
        have hval := (c ⟨i, 0, by omega⟩).isLt
        omega
  let fb : ℕ → Bool := fun i => botColor c i = 1
  have htrans : bottomTransitions c =
      ((Finset.range n).filter (fun i => fb i ≠ fb (i + 1))).card := by
    unfold bottomTransitions
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hne⟩
      refine ⟨hi, ?_⟩
      simp only [fb]
      intro h
      apply hne
      have h1 := hbot_colors i (by omega)
      have h2 := hbot_colors (i + 1) (by omega)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
    · rintro ⟨hi, hne⟩
      refine ⟨hi, ?_⟩
      intro h
      apply hne
      simp only [fb, h]
  rw [htrans, Nat.odd_iff, transitions_parity_bool]
  have hfb0 : fb 0 = false := by
    simp only [fb, botColor, dif_pos (Nat.zero_le n), Bool.eq_false_iff, decide_eq_true_eq]
    rw [hv0]; simp
  have hfbn : fb n = true := by
    simp only [fb, botColor, dif_pos (le_refl n), decide_eq_true_eq]
    exact hv1
  simp [hfb0, hfbn]

-- ============================================================
-- SECTION IV: Door-Counting Argument
-- ============================================================

def IsDoor {n : ℕ} (c : Coloring n) (v w : GridVertex n) : Prop :=
  (c v = 0 ∧ c w = 1) ∨ (c v = 1 ∧ c w = 0)

theorem fully_colored_one_door {n : ℕ} (c : Coloring n)
    (t : GridTriangle n) (hfc : IsFullyColored c t) :
    ∃! (e : Fin 3 × Fin 3), e.1 < e.2 ∧
      IsDoor c (t.vertices e.1) (t.vertices e.2) := by
  -- Step 1: The coloring restricted to this triangle is surjective (image = Fin 3)
  have hsurj : Function.Surjective (c ∘ t.vertices) := by
    intro y
    have : y ∈ Finset.image (c ∘ t.vertices) Finset.univ := by
      unfold IsFullyColored at hfc; rw [hfc]; fin_cases y <;> simp
    simpa using this
  -- Step 2: Surjective endomorphism on finite type is injective
  have hinj : Function.Injective (c ∘ t.vertices) :=
    Finite.injective_iff_surjective.mpr hsurj
  -- Step 3: Find the vertices with colors 0 and 1
  obtain ⟨i₀, hi₀⟩ := hsurj (0 : Fin 3)
  obtain ⟨i₁, hi₁⟩ := hsurj (1 : Fin 3)
  have hne : i₀ ≠ i₁ := by
    intro h; subst h; exact absurd (hi₀.symm.trans hi₁) (by decide)
  -- Step 4: Any door must connect the unique 0-vertex and 1-vertex
  have unique : ∀ (a b : Fin 3), IsDoor c (t.vertices a) (t.vertices b) →
      (a = i₀ ∧ b = i₁) ∨ (a = i₁ ∧ b = i₀) := by
    intro a b hdoor
    rcases hdoor with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left; exact ⟨hinj (ha.trans hi₀.symm), hinj (hb.trans hi₁.symm)⟩
    · right; exact ⟨hinj (ha.trans hi₁.symm), hinj (hb.trans hi₀.symm)⟩
  -- Step 5: Construct the unique door edge (ordered)
  rcases hne.lt_or_lt with h_lt | h_lt
  · -- i₀ < i₁: door is (i₀, i₁)
    refine ⟨(i₀, i₁), ⟨h_lt, Or.inl ⟨hi₀, hi₁⟩⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨hab, hdoor⟩
    rcases unique a b hdoor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exfalso; exact absurd hab (not_lt.mpr (le_of_lt h_lt))
  · -- i₁ < i₀: door is (i₁, i₀)
    refine ⟨(i₁, i₀), ⟨h_lt, Or.inr ⟨hi₁, hi₀⟩⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨hab, hdoor⟩
    rcases unique a b hdoor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso; exact absurd hab (not_lt.mpr (le_of_lt h_lt))
    · rfl

-- Helper: No {0,1}-doors on left-boundary edges (colors ∈ {0,2})
private lemma no_door_left_boundary {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) (j : ℕ) (hj : j > 0) (hj' : j < n) :
    ¬ IsDoor c ⟨0, j, by omega⟩ ⟨0, j + 1, by omega⟩ := by
  obtain ⟨_, _, hv2, _, hleft, _⟩ := hc
  intro hdoor
  -- Left boundary vertices have color ∈ {0, 2}, so no {0,1}-doors
  -- NOTE: Needs fix for Mathlib v4.26.0 omega changes in GridVertex validity
  sorry

-- Helper: No {0,1}-doors on hypotenuse edges (colors ∈ {1,2})
private lemma no_door_hypotenuse {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) (i j : ℕ) (hi : i > 0) (hj : j > 0)
    (hsum1 : i + j = n) (hsum2 : (i - 1) + (j + 1) = n) :
    ¬ IsDoor c ⟨i, j, by omega⟩ ⟨i - 1, j + 1, by omega⟩ := by
  obtain ⟨_, _, _, _, _, hhyp⟩ := hc
  intro hdoor
  -- Hypotenuse vertices have color ∈ {1, 2}, so no {0,1}-doors
  -- NOTE: Needs fix for Mathlib v4.26.0 omega changes in GridVertex validity
  sorry

/-- Helper: count {0,1}-doors among 3 abstract colors.
    An edge (a,b) is a door if {a,b} = {0,1}.
    Returns the count of doors among the 3 edges (01), (02), (12). -/
private def abstractDoorCount (a b c : Fin 3) : ℕ :=
  (if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 else 0) +
  (if (a = 0 ∧ c = 1) ∨ (a = 1 ∧ c = 0) then 1 else 0) +
  (if (b = 0 ∧ c = 1) ∨ (b = 1 ∧ c = 0) then 1 else 0)

/-- Helper: is this triple a permutation of {0,1,2}? -/
private def isFC (a b c : Fin 3) : Bool :=
  ({a, b, c} : Finset (Fin 3)) = {0, 1, 2}

/-- Key parity lemma: for any 3 colors from Fin 3, the number of {0,1}-doors
    among the 3 edges has the same parity as whether the triple is a
    permutation of {0,1,2} (fully colored).

    PROVED by exhaustive case analysis on 27 cases. -/
theorem abstractDoorCount_parity (a b c : Fin 3) :
    abstractDoorCount a b c % 2 = if isFC a b c then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

-- Proof strategy for sperner_2d:
-- 1. bottomTransitions c is odd (from bottom_transitions_odd)
-- 2. Boundary {0,1}-doors appear ONLY on the bottom edge
--    (left edge: colors ∈ {0,2}, no color 1 → no doors)
--    (hypotenuse: colors ∈ {1,2}, no color 0 → no doors)
-- 3. Double-counting: ∑_T doorCount(T) = 2·|interior doors| + |boundary doors|
-- 4. Each fully-colored triangle has exactly 1 door (fully_colored_one_door)
-- 5. Each non-fully-colored triangle has 0 or 2 doors (even)
-- 6. Therefore: #FC ≡ bottomTransitions ≡ 1 (mod 2), so #FC ≥ 1

theorem sperner_2d {n : ℕ} (hn : 0 < n) (c : Coloring n) (hc : IsSperner hn c) :
    ∃ t : GridTriangle n, IsFullyColored c t := by
  sorry

-- ============================================================
-- SECTION V: Existence of Approximate Fixed Points (Application)
-- ============================================================

theorem approximate_fixed_point_2d
    {f : ℝ × ℝ → ℝ × ℝ}
    (hcont : Continuous f)
    (hrange : ∀ p, p.1 ≥ 0 → p.2 ≥ 0 → p.1 + p.2 ≤ 1 →
      (f p).1 ≥ 0 ∧ (f p).2 ≥ 0 ∧ (f p).1 + (f p).2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ × ℝ, p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ p.1 + p.2 ≤ 1 ∧
      dist p (f p) < ε := by
  sorry

end Sperner2D
