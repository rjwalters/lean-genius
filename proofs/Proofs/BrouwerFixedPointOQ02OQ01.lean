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

@[ext]
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

-- In ZMod 2: a + b = 0 ↔ a = b (since -1 = 1)
private lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

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
-- SECTION III-b: Extended Coloring and Row Transitions
-- ============================================================

/-- Extended coloring: returns actual color for valid vertices, 0 outside grid -/
def gColor {n : ℕ} (c : Coloring n) (i j : ℕ) : Fin 3 :=
  if h : i + j ≤ n then c ⟨i, j, h⟩ else 0

private lemma gColor_bot {n : ℕ} (c : Coloring n) (i : ℕ) (hi : i ≤ n) :
    gColor c i 0 = botColor c i := by
  simp only [gColor, botColor, show i + 0 ≤ n by omega, dif_pos, dif_pos hi]

/-- Count of horizontal {0,1}-door transitions at row j -/
def hTrans {n : ℕ} (c : Coloring n) (j : ℕ) : ℕ :=
  ((Finset.range (n - j)).filter (fun i =>
    (gColor c i j = 0 ∧ gColor c (i + 1) j = 1) ∨
    (gColor c i j = 1 ∧ gColor c (i + 1) j = 0))).card

theorem hTrans_top {n : ℕ} (c : Coloring n) : hTrans c n = 0 := by
  simp [hTrans, Nat.sub_self]

/-- Count of {0,1}-doors among the 3 edges of a triangle with vertex colors a, b, c -/
def abstractDoorCount (a b c₃ : Fin 3) : ℕ :=
  (if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 else 0) +
  (if (a = 0 ∧ c₃ = 1) ∨ (a = 1 ∧ c₃ = 0) then 1 else 0) +
  (if (b = 0 ∧ c₃ = 1) ∨ (b = 1 ∧ c₃ = 0) then 1 else 0)

-- ============================================================
-- SECTION IV: Door-Counting Argument
-- ============================================================

def IsDoor {n : ℕ} (c : Coloring n) (v w : GridVertex n) : Prop :=
  (c v = 0 ∧ c w = 1) ∨ (c v = 1 ∧ c w = 0)

theorem fully_colored_one_door {n : ℕ} (c : Coloring n)
    (t : GridTriangle n) (hfc : IsFullyColored c t) :
    ∃! (e : Fin 3 × Fin 3), e.1 < e.2 ∧
      IsDoor c (t.vertices e.1) (t.vertices e.2) := by
  have hsurj : Function.Surjective (c ∘ t.vertices) := by
    intro y
    have : y ∈ Finset.image (c ∘ t.vertices) Finset.univ := by
      unfold IsFullyColored at hfc; rw [hfc]; fin_cases y <;> simp
    simpa using this
  have hinj : Function.Injective (c ∘ t.vertices) :=
    Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨i₀, hi₀⟩ := hsurj (0 : Fin 3)
  obtain ⟨i₁, hi₁⟩ := hsurj (1 : Fin 3)
  have hne : i₀ ≠ i₁ := by
    intro h; subst h; exact absurd (hi₀.symm.trans hi₁) (by decide)
  have unique : ∀ (a b : Fin 3), IsDoor c (t.vertices a) (t.vertices b) →
      (a = i₀ ∧ b = i₁) ∨ (a = i₁ ∧ b = i₀) := by
    intro a b hdoor
    rcases hdoor with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left; exact ⟨hinj (ha.trans hi₀.symm), hinj (hb.trans hi₁.symm)⟩
    · right; exact ⟨hinj (ha.trans hi₁.symm), hinj (hb.trans hi₀.symm)⟩
  rcases hne.lt_or_lt with h_lt | h_lt
  · refine ⟨(i₀, i₁), ⟨h_lt, Or.inl ⟨hi₀, hi₁⟩⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨hab, hdoor⟩
    rcases unique a b hdoor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hab (lt_asymm h_lt)
  · refine ⟨(i₁, i₀), ⟨h_lt, Or.inr ⟨hi₁, hi₀⟩⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨hab, hdoor⟩
    rcases unique a b hdoor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hab (lt_asymm h_lt)
    · rfl

-- Helper: No {0,1}-doors on left-boundary edges (colors ∈ {0,2})
private lemma no_door_left_boundary {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) (j : ℕ) (hj : j > 0) (hj' : j < n) :
    ¬ IsDoor c ⟨0, j, by omega⟩ ⟨0, j + 1, by omega⟩ := by
  obtain ⟨_, _, hv2, _, hleft, _⟩ := hc
  have h1 : c ⟨0, j, by omega⟩ ≠ 1 := hleft ⟨0, j, by omega⟩ rfl hj hj'
  have h2 : c ⟨0, j + 1, by omega⟩ ≠ 1 := by
    by_cases hjn : j + 1 = n
    · have heqv : (⟨0, j + 1, by omega⟩ : GridVertex n) = ⟨0, n, by omega⟩ := by
        ext <;> dsimp <;> omega
      rw [heqv, hv2]; decide
    · have hgt : j + 1 > 0 := by omega
      have hlt : j + 1 < n := by omega
      exact hleft ⟨0, j + 1, by omega⟩ rfl hgt hlt
  intro hdoor
  rcases hdoor with ⟨_, h01⟩ | ⟨h10, _⟩
  · exact h2 h01
  · exact h1 h10

-- Helper: No {0,1}-doors on hypotenuse edges (colors ∈ {1,2})
private lemma no_door_hypotenuse {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) (i j : ℕ) (hi : i > 0) (hj : j > 0)
    (hsum1 : i + j = n) (hsum2 : (i - 1) + (j + 1) = n) :
    ¬ IsDoor c ⟨i, j, by omega⟩ ⟨i - 1, j + 1, by omega⟩ := by
  obtain ⟨_, _, hv2, _, _, hhyp⟩ := hc
  intro hdoor
  rcases hdoor with ⟨h0, _⟩ | ⟨_, h0⟩
  · exact hhyp ⟨i, j, by omega⟩ hsum1 hi hj h0
  · -- c(i-1, j+1) = 0 but hypotenuse has colors ≠ 0
    by_cases hi1 : 1 ≤ i - 1
    · have hgt : i - 1 > 0 := by omega
      have hgt2 : j + 1 > 0 := by omega
      exact hhyp ⟨i - 1, j + 1, by omega⟩ hsum2 hgt hgt2 h0
    · have heqv : (⟨i - 1, j + 1, by omega⟩ : GridVertex n) = ⟨0, n, by omega⟩ := by
        ext <;> dsimp <;> omega
      rw [heqv, hv2] at h0; exact absurd h0 (by decide)

-- ============================================================
-- SECTION IV-b: Row-Sweep Parity Argument for Sperner's Lemma
-- ============================================================

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

-- hTrans at row 0 equals bottomTransitions under Sperner condition
private lemma hTrans_zero_eq {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) :
    hTrans c 0 = bottomTransitions c := by
  obtain ⟨hv0, hv1, _, hbot, _, _⟩ := hc
  simp only [hTrans, bottomTransitions, Nat.sub_zero]
  congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · -- {0,1}-door → different colors (trivial since 0 ≠ 1)
    rintro ⟨hi, h⟩
    rw [gColor_bot c i (by omega), gColor_bot c (i + 1) (by omega)] at h
    exact ⟨hi, by rcases h with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> [rw [h0, h1]; rw [h0, h1]] <;> decide⟩
  · -- different colors → {0,1}-door (on bottom edge, colors ∈ {0,1})
    rintro ⟨hi, hne⟩
    refine ⟨hi, ?_⟩
    rw [gColor_bot c i (by omega), gColor_bot c (i + 1) (by omega)]
    have hbc : ∀ k, k ≤ n → botColor c k = 0 ∨ botColor c k = 1 := by
      intro k hk; simp only [botColor, dif_pos hk]
      by_cases h0 : k = 0
      · subst h0; left; exact hv0
      · by_cases hn' : k = n
        · subst hn'; right; exact hv1
        · have hgt : k > 0 := by omega
          have hlt : k < n := by omega
          have := hbot ⟨k, 0, by omega⟩ rfl hgt hlt
          have hval := (c ⟨k, 0, by omega⟩).isLt; omega
    rcases hbc i (by omega) with h1 | h1 <;> rcases hbc (i + 1) (by omega) with h2 | h2 <;>
      rw [h1, h2] at hne ⊢
    · exact absurd rfl hne
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
    · exact absurd rfl hne

-- ============================================================
-- Strip Parity: Double-Counting Proof Infrastructure
-- ============================================================

-- {0,1}-door indicator in ZMod 2
private def doorZ {n : ℕ} (c : Coloring n) (i₁ j₁ i₂ j₂ : ℕ) : ZMod 2 :=
  if (gColor c i₁ j₁ = 0 ∧ gColor c i₂ j₂ = 1) ∨
     (gColor c i₁ j₁ = 1 ∧ gColor c i₂ j₂ = 0) then 1 else 0

-- Three vertex colors not all distinct yield even door count (0 or 2)
private lemma door_parity_of_not_fc (a b c₃ : Fin 3)
    (h : ¬(({a, b, c₃} : Finset (Fin 3)) = {0, 1, 2})) :
    (if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then (1 : ZMod 2) else 0) +
    (if (a = 0 ∧ c₃ = 1) ∨ (a = 1 ∧ c₃ = 0) then 1 else 0) +
    (if (b = 0 ∧ c₃ = 1) ∨ (b = 1 ∧ c₃ = 0) then 1 else 0) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c₃ <;> simp_all (config := { decide := true }) <;> decide

-- gColor equals actual color for valid vertices
private lemma gColor_eq {n : ℕ} (c : Coloring n) (i j : ℕ) (h : i + j ≤ n) :
    gColor c i j = c ⟨i, j, h⟩ := by
  simp [gColor, dif_pos h]

-- Per-triangle door sums = 0 for non-FC triangles
private lemma lower_door_sum_zero {n : ℕ} (c : Coloring n) (i j : ℕ)
    (hv : i + 1 + j ≤ n) (hno : ¬ IsFullyColored c ⟨i, j, .lower, hv⟩) :
    doorZ c i j (i+1) j + doorZ c i j i (j+1) + doorZ c (i+1) j i (j+1) = 0 := by
  have hi : i + j ≤ n := by omega
  have hi1 : (i + 1) + j ≤ n := by omega
  have hj1 : i + (j + 1) ≤ n := by omega
  simp only [doorZ, gColor_eq c i j hi, gColor_eq c (i+1) j hi1, gColor_eq c i (j+1) hj1]
  apply door_parity_of_not_fc
  intro heq; exact hno (by
    show Finset.image (c ∘ (GridTriangle.mk i j .lower hv).vertices) Finset.univ = {0, 1, 2}
    have himgeq : Finset.image (c ∘ (GridTriangle.mk i j .lower hv).vertices) Finset.univ =
        {c ⟨i, j, hi⟩, c ⟨i + 1, j, hi1⟩, c ⟨i, j + 1, hj1⟩} := by
      apply Finset.ext; intro x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
                  Finset.mem_singleton]
      constructor
      · rintro ⟨k, hk⟩
        fin_cases k <;>
          simp only [Function.comp, GridTriangle.vertices, lowerVertices] at hk <;>
          simp [hk]
      · rintro (hx | hx | hx) <;> subst hx
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    rw [himgeq]; exact heq)

private lemma upper_door_sum_zero {n : ℕ} (c : Coloring n) (i j : ℕ)
    (hv : i + 1 + (j + 1) ≤ n) (hno : ¬ IsFullyColored c ⟨i, j, .upper, hv⟩) :
    doorZ c (i+1) j i (j+1) + doorZ c (i+1) j (i+1) (j+1) +
    doorZ c i (j+1) (i+1) (j+1) = 0 := by
  have h1 : (i + 1) + j ≤ n := by omega
  have h2 : i + (j + 1) ≤ n := by omega
  have h3 : (i + 1) + (j + 1) ≤ n := by omega
  simp only [doorZ, gColor_eq c (i+1) j h1, gColor_eq c i (j+1) h2, gColor_eq c (i+1) (j+1) h3]
  apply door_parity_of_not_fc
  intro heq; exact hno (by
    show Finset.image (c ∘ (GridTriangle.mk i j .upper hv).vertices) Finset.univ = {0, 1, 2}
    have himgeq : Finset.image (c ∘ (GridTriangle.mk i j .upper hv).vertices) Finset.univ =
        {c ⟨i + 1, j, h1⟩, c ⟨i, j + 1, h2⟩, c ⟨i + 1, j + 1, h3⟩} := by
      apply Finset.ext; intro x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
                  Finset.mem_singleton]
      constructor
      · rintro ⟨k, hk⟩
        fin_cases k <;>
          simp only [Function.comp, GridTriangle.vertices, upperVertices] at hk <;>
          simp [hk]
      · rintro (hx | hx | hx) <;> subst hx
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    rw [himgeq]; exact heq)

-- ZMod 2 sum helpers for internal-edge cancellation
private lemma finset_sum_range_succ' {α : Type*} [AddCommMonoid α] (k : ℕ) (f : ℕ → α) :
    (Finset.range (k + 1)).sum f = f 0 + (Finset.range k).sum (fun i => f (i + 1)) := by
  induction k with
  | zero => simp
  | succ k' ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; abel

private lemma zmod2_sum_shift_cancel (m : ℕ) (hm : 0 < m) (f : ℕ → ZMod 2) :
    (Finset.range m).sum f +
    (Finset.range (m - 1)).sum (fun i => f (i + 1)) = f 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp only [Nat.succ_sub_one]
  rw [finset_sum_range_succ' k f]
  have hc := zmod2_add_self ((Finset.range k).sum (fun i => f (i + 1)))
  calc f 0 + (Finset.range k).sum (fun i => f (i + 1)) +
      (Finset.range k).sum (fun i => f (i + 1))
      = f 0 + ((Finset.range k).sum (fun i => f (i + 1)) +
        (Finset.range k).sum (fun i => f (i + 1))) := by abel
    _ = f 0 + 0 := by rw [hc]
    _ = f 0 := by ring

private lemma zmod2_sum_tail_cancel (m : ℕ) (hm : 0 < m) (f : ℕ → ZMod 2) :
    (Finset.range m).sum f + (Finset.range (m - 1)).sum f = f (m - 1) := by
  conv_lhs => lhs; rw [show m = (m - 1) + 1 by omega]
  rw [Finset.sum_range_succ]
  have hc := zmod2_add_self ((Finset.range (m - 1)).sum f)
  calc (Finset.range (m - 1)).sum f + f (m - 1) + (Finset.range (m - 1)).sum f
      = ((Finset.range (m - 1)).sum f + (Finset.range (m - 1)).sum f) + f (m - 1) := by abel
    _ = 0 + f (m - 1) := by rw [hc]
    _ = f (m - 1) := by ring

private lemma doorZ_left_boundary {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) (j : ℕ) (hj : j + 1 ≤ n) :
    doorZ c 0 j 0 (j + 1) = 0 := by
  unfold doorZ
  rw [gColor_eq c 0 j (by omega : 0 + j ≤ n),
      gColor_eq c 0 (j + 1) (by omega : 0 + (j + 1) ≤ n)]
  obtain ⟨hv0, _, hv2, _, hleft, _⟩ := hc
  have h1 : ¬(c ⟨0, j, by omega⟩ = (1 : Fin 3)) := by
    by_cases hj0 : j = 0
    · subst hj0; rw [hv0]; decide
    · have hgt : j > 0 := by omega
      have hlt : j < n := by omega
      exact hleft ⟨0, j, by omega⟩ rfl hgt hlt
  have h2 : ¬(c ⟨0, j + 1, by omega⟩ = (1 : Fin 3)) := by
    by_cases hjn : j + 1 = n
    · have heqv : (⟨0, j + 1, by omega⟩ : GridVertex n) = ⟨0, n, by omega⟩ := by
        ext <;> dsimp <;> omega
      rw [heqv, hv2]; decide
    · have hgt : j + 1 > 0 := by omega
      have hlt : j + 1 < n := by omega
      exact hleft ⟨0, j + 1, by omega⟩ rfl hgt hlt
  simp only [h2, h1, and_false, false_and, or_self, ite_false]

private lemma doorZ_hyp_boundary {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) (j : ℕ) (hj : j + 1 ≤ n) :
    doorZ c (n - j) j (n - j - 1) (j + 1) = 0 := by
  obtain ⟨_, hv1, hv2, _, _, hhyp⟩ := hc
  simp only [doorZ]
  rw [gColor_eq c (n - j) j (by omega), gColor_eq c (n - j - 1) (j + 1) (by omega)]
  have h1 : c ⟨n - j, j, by omega⟩ ≠ 0 := by
    by_cases hj0 : j = 0
    · subst hj0; simp only [Nat.sub_zero]; rw [hv1]; decide
    · have hsum : (n - j) + j = n := by omega
      have hgt1 : n - j > 0 := by omega
      have hgt2 : j > 0 := by omega
      exact hhyp ⟨n - j, j, by omega⟩ hsum hgt1 hgt2
  have h2 : c ⟨n - j - 1, j + 1, by omega⟩ ≠ 0 := by
    by_cases hjn : j + 1 = n
    · have heqv : (⟨n - j - 1, j + 1, by omega⟩ : GridVertex n) = ⟨0, n, by omega⟩ := by
        ext <;> dsimp <;> omega
      rw [heqv, hv2]; decide
    · have hsum : (n - j - 1) + (j + 1) = n := by omega
      have hgt1 : n - j - 1 > 0 := by omega
      have hgt2 : j + 1 > 0 := by omega
      exact hhyp ⟨n - j - 1, j + 1, by omega⟩ hsum hgt1 hgt2
  rw [if_neg]
  rintro (⟨ha, _⟩ | ⟨_, hb⟩)
  · exact h1 ha
  · exact h2 hb

-- Convert hTrans (Nat card) to ZMod 2 sum of doorZ indicators
private lemma hTrans_cast {n : ℕ} (c : Coloring n) (j : ℕ) :
    (hTrans c j : ZMod 2) =
    (Finset.range (n - j)).sum (fun i => doorZ c i j (i + 1) j) := by
  simp only [hTrans, doorZ]
  exact (Finset.sum_boole _ _).symm

-- ============================================================
-- MAIN LEMMA: strip_parity via ZMod 2 double-counting
-- ============================================================
-- In the strip between rows j and j+1 (width m = n - j):
--   Lower triangles L(i): edges p_i, l_i, d_i (i = 0,...,m-1)
--   Upper triangles U(i): edges d_i, l_{i+1}, q_i (i = 0,...,m-2)
-- Each non-FC triangle has door sum 0 in ZMod 2.
-- After summing and cancelling doubled internal edges:
--   sum_p + sum_q + l_0 + d_{m-1} = 0
-- Sperner ⟹ l_0 = 0, d_{m-1} = 0 ⟹ sum_p + sum_q = 0.

private lemma strip_parity {n : ℕ} (hn : 0 < n) (c : Coloring n) (hc : IsSperner hn c)
    (j : ℕ) (hj : j + 1 ≤ n)
    (hno_fc : ∀ t : GridTriangle n, ¬ IsFullyColored c t) :
    hTrans c j % 2 = hTrans c (j + 1) % 2 := by
  -- Suffices: (hTrans j + hTrans (j+1) : ZMod 2) = 0
  suffices hsuff : (hTrans c j : ZMod 2) + (hTrans c (j + 1) : ZMod 2) = 0 by
    have h2 : (2 : ℕ) ≠ 0 := by omega
    rw [hTrans_cast, hTrans_cast] at hsuff
    -- Convert back: ZMod 2 sum = 0 implies Nat parity equal
    rw [← hTrans_cast, ← hTrans_cast] at hsuff
    rw [← Nat.cast_add] at hsuff
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hsuff
    omega
  set m := n - j with hm_def
  have hm_pos : 0 < m := by omega
  rw [hTrans_cast, hTrans_cast, show n - (j + 1) = m - 1 by omega]
  -- Edge indicator shorthand
  let p : ℕ → ZMod 2 := fun i => doorZ c i j (i + 1) j
  let q : ℕ → ZMod 2 := fun i => doorZ c i (j+1) (i + 1) (j+1)
  let l : ℕ → ZMod 2 := fun i => doorZ c i j i (j + 1)
  let d : ℕ → ZMod 2 := fun i => doorZ c (i+1) j i (j + 1)
  -- Each lower triangle has door parity 0
  have hSL : (Finset.range m).sum (fun i => p i + l i + d i) = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      simp only [Finset.mem_range] at hi
      exact lower_door_sum_zero c i j (by omega) (hno_fc ⟨i, j, .lower, by omega⟩))
  -- Each upper triangle has door parity 0
  have hSU : (Finset.range (m - 1)).sum (fun i => d i + l (i + 1) + q i) = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      simp only [Finset.mem_range] at hi
      -- Upper triangle U(i) has doorZ c (i+1) j (i+1) (j+1) = l (i+1) by definition
      exact upper_door_sum_zero c i j (by omega) (hno_fc ⟨i, j, .upper, by omega⟩))
  -- Split into component sums
  have hSL' : (Finset.range m).sum p + (Finset.range m).sum l +
      (Finset.range m).sum d = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; exact hSL
  have hSU' : (Finset.range (m - 1)).sum d + (Finset.range (m - 1)).sum (fun i => l (i + 1)) +
      (Finset.range (m - 1)).sum q = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; exact hSU
  -- Cancellation: doubled internal edges vanish mod 2
  have hL := zmod2_sum_shift_cancel m hm_pos l   -- sum_l + sum_l_shifted = l(0)
  have hD := zmod2_sum_tail_cancel m hm_pos d  -- sum_d + sum_d' = d(m-1)
  -- Boundary conditions
  have hl0 : l 0 = 0 := doorZ_left_boundary hn c hc j hj
  have hdm : d (m - 1) = 0 := by
    show doorZ c (m - 1 + 1) j (m - 1) (j + 1) = 0
    rw [show m - 1 + 1 = m from by omega, hm_def]
    exact doorZ_hyp_boundary hn c hc j hj
  -- Substitute boundaries into cancellation lemmas
  rw [hl0] at hL  -- sum_l + sum_l_shifted = 0
  rw [hdm] at hD  -- sum_d + sum_d' = 0
  -- From a + b = 0 in ZMod 2, derive b = a
  have hSl_eq : (Finset.range (m - 1)).sum (fun i => l (i + 1)) = (Finset.range m).sum l :=
    (zmod2_eq_of_add_eq_zero hL).symm
  have hSd_eq : (Finset.range (m - 1)).sum d = (Finset.range m).sum d :=
    (zmod2_eq_of_add_eq_zero hD).symm
  -- Substitute into hSU': sum_d + sum_l + sum_q = 0
  rw [hSd_eq, hSl_eq] at hSU'
  -- Final: sum_p + sum_q = 0 by adding hSL' and hSU' (doubled terms cancel)
  have h2l := zmod2_add_self ((Finset.range m).sum l)
  have h2d := zmod2_add_self ((Finset.range m).sum d)
  calc (Finset.range m).sum p + (Finset.range (m - 1)).sum q
      = (Finset.range m).sum p + (Finset.range (m - 1)).sum q + 0 + 0 := by ring
    _ = (Finset.range m).sum p + (Finset.range (m - 1)).sum q +
        ((Finset.range m).sum l + (Finset.range m).sum l) +
        ((Finset.range m).sum d + (Finset.range m).sum d) := by rw [h2l, h2d]
    _ = ((Finset.range m).sum p + (Finset.range m).sum l + (Finset.range m).sum d) +
        ((Finset.range m).sum d + (Finset.range m).sum l +
         (Finset.range (m - 1)).sum q) := by ring
    _ = 0 + 0 := by rw [hSL', hSU']
    _ = 0 := by ring

-- MAIN THEOREM: 2D Sperner's lemma via row-sweep parity
theorem sperner_2d {n : ℕ} (hn : 0 < n) (c : Coloring n) (hc : IsSperner hn c) :
    ∃ t : GridTriangle n, IsFullyColored c t := by
  by_contra hno_fc
  push_neg at hno_fc
  have h_odd := bottom_transitions_odd hn c hc
  have h_eq := hTrans_zero_eq hn c hc
  have h_top : hTrans c n = 0 := hTrans_top c
  have h_const : ∀ j, j ≤ n → hTrans c j % 2 = hTrans c 0 % 2 := by
    intro j hj
    induction j with
    | zero => rfl
    | succ k ih =>
      have := strip_parity hn c hc k (by omega) hno_fc
      omega
  have h_contr := h_const n (le_refl n)
  rw [h_top, h_eq] at h_contr
  exact absurd h_odd (by rw [Nat.odd_iff]; omega)

-- ============================================================
-- SECTION V: Existence of Approximate Fixed Points (Application)
-- ============================================================

-- Convert grid vertex to real coordinates in the unit simplex
noncomputable def gridToReal (n : ℕ) (v : GridVertex n) : ℝ × ℝ :=
  ((v.i : ℝ) / n, (v.j : ℝ) / n)

-- Displacement-based Sperner coloring from continuous function f.
-- Color vertex with index of most negative barycentric displacement.
-- When all displacements are equal (f(p)=p at boundary), uses face-aware
-- tie-breaking to ensure Sperner boundary conditions are satisfied.
--
-- Key property: on face opposite vertex k, the k-th barycentric displacement
-- d_k ≥ 0 (since f maps simplex to simplex). When f(p) ≠ p, some d_j < 0 ≤ d_k,
-- so k is never the minimum. The face-aware branch handles the f(p) = p case.
noncomputable def displacementColoring (n : ℕ)
    (f : ℝ × ℝ → ℝ × ℝ) : Coloring n := fun v =>
  let p := gridToReal n v
  let d1 := (f p).1 - p.1
  let d2 := (f p).2 - p.2
  let d0 := -(d1 + d2)
  -- All displacements equal (boundary fixed point): face-aware tie-breaking
  if d0 = d1 ∧ d1 = d2 then
    if v.i = 0 ∧ v.j = 0 then 0              -- corner (0,0): need color 0
    else if v.j = 0 ∧ v.i + v.j = n then 1    -- corner (n,0): need color 1
    else if v.i = 0 ∧ v.i + v.j = n then 2    -- corner (0,n): need color 2
    else if v.i + v.j = n then 1               -- hypotenuse: avoid color 0
    else if v.i = 0 then 2                     -- left edge: avoid color 1
    else 0                                     -- bottom/interior: avoid color 2
  -- Standard: most negative displacement (d_k on face opp k is ≥ 0, so safe)
  else if d0 ≤ d1 ∧ d0 ≤ d2 then 0
  else if d1 ≤ d2 then 1
  else 2

-- Helper: grid vertices map into the simplex
private lemma gridToReal_in_simplex {n : ℕ} (hn : 0 < n) (v : GridVertex n) :
    (gridToReal n v).1 ≥ 0 ∧ (gridToReal n v).2 ≥ 0 ∧
    (gridToReal n v).1 + (gridToReal n v).2 ≤ 1 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  refine ⟨div_nonneg (Nat.cast_nonneg v.i) hn_pos.le,
         div_nonneg (Nat.cast_nonneg v.j) hn_pos.le, ?_⟩
  have : (gridToReal n v).1 + (gridToReal n v).2 = (↑v.i + ↑v.j : ℝ) / ↑n := by
    simp only [gridToReal]; ring
  rw [this, div_le_one hn_pos]
  exact_mod_cast v.valid

-- The displacement coloring satisfies Sperner conditions when f has no grid fixed point.
-- When f(v) = v at some grid vertex, the coloring may assign incorrect labels at that vertex,
-- but the caller handles this case separately (since v is already an exact fixed point).
private lemma displacementColoring_isSperner (n : ℕ) (hn : 0 < n)
    (f : ℝ × ℝ → ℝ × ℝ)
    (hrange : ∀ p, p.1 ≥ 0 → p.2 ≥ 0 → p.1 + p.2 ≤ 1 →
      (f p).1 ≥ 0 ∧ (f p).2 ≥ 0 ∧ (f p).1 + (f p).2 ≤ 1)
    (hno_fix : ∀ v : GridVertex n, f (gridToReal n v) ≠ gridToReal n v) :
    IsSperner hn (displacementColoring n f) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) c(0,0) = 0: at origin, d1=f₁≥0, d2=f₂≥0, d0=-(f₁+f₂)≤0 is the minimum
  · simp only [displacementColoring, gridToReal, Nat.cast_zero, zero_div, sub_zero]
    obtain ⟨hf1, hf2, _⟩ := hrange (0, 0) le_rfl le_rfl (by norm_num)
    by_cases htie : -((f (0, 0)).1 + (f (0, 0)).2) = (f (0, 0)).1 ∧
        (f (0, 0)).1 = (f (0, 0)).2
    · rw [if_pos htie]; simp
    · rw [if_neg htie, if_pos ⟨by linarith, by linarith⟩]
  -- (2) c(n,0) = 1: d1=f₁-1≤0, d2=f₂≥0, so d1≤d2. d0≤d1 iff f=(1,0) (fixed point).
  · simp only [displacementColoring, gridToReal, Nat.cast_zero, zero_div, sub_zero, div_self hn']
    obtain ⟨hf1, hf2, hf12⟩ := hrange (1, 0) (by norm_num) le_rfl (by norm_num)
    by_cases htie : -((f (1, 0)).1 - 1 + (f (1, 0)).2) = (f (1, 0)).1 - 1 ∧
        (f (1, 0)).1 - 1 = (f (1, 0)).2
    · -- Tie means f=(1,0), contradicting hno_fix
      exfalso
      have hf1_eq : (f (1, 0)).1 = 1 := by nlinarith [htie.1, htie.2]
      have hf2_eq : (f (1, 0)).2 = 0 := by linarith [htie.2]
      exact hno_fix ⟨n, 0, by omega⟩ (by
        simp only [gridToReal, Nat.cast_zero, zero_div, div_self hn']
        exact Prod.ext hf1_eq hf2_eq)
    · rw [if_neg htie, if_neg, if_pos (show (f (1, 0)).1 - 1 ≤ (f (1, 0)).2 by linarith)]
      intro ⟨h_le, _⟩
      have hf1_eq : (f (1, 0)).1 = 1 := by nlinarith
      have hf2_eq : (f (1, 0)).2 = 0 := by linarith
      exact absurd (show f (gridToReal n ⟨n, 0, by omega⟩) = gridToReal n ⟨n, 0, by omega⟩ from by
        simp only [gridToReal, Nat.cast_zero, zero_div, div_self hn']
        exact Prod.ext hf1_eq hf2_eq) (hno_fix ⟨n, 0, by omega⟩)
  -- (3) c(0,n) = 2: d1=f₁≥0, d2=f₂-1≤0, d0=1-f₁-f₂≥0. Neither if-branch unless fixed pt.
  · simp only [displacementColoring, gridToReal, Nat.cast_zero, zero_div, sub_zero, div_self hn']
    obtain ⟨hf1, hf2, hf12⟩ := hrange (0, 1) le_rfl (by norm_num) (by norm_num)
    by_cases htie : -((f (0, 1)).1 + ((f (0, 1)).2 - 1)) = (f (0, 1)).1 ∧
        (f (0, 1)).1 = (f (0, 1)).2 - 1
    · -- Tie means f=(0,1), contradicting hno_fix
      exfalso
      have hf2_eq : (f (0, 1)).2 = 1 := by nlinarith [htie.1, htie.2]
      have hf1_eq : (f (0, 1)).1 = 0 := by linarith [htie.2]
      exact hno_fix ⟨0, n, by omega⟩ (by
        simp only [gridToReal, Nat.cast_zero, zero_div, div_self hn']
        exact Prod.ext hf1_eq hf2_eq)
    · rw [if_neg htie, if_neg, if_neg]
      · -- ¬(d1 ≤ d2): f₁ > f₂-1, unless f=(0,1) (fixed point)
        intro h_le
        have hf2_eq : (f (0, 1)).2 = 1 := by nlinarith
        have hf1_eq : (f (0, 1)).1 = 0 := by linarith
        exact absurd (show f (gridToReal n ⟨0, n, by omega⟩) = gridToReal n ⟨0, n, by omega⟩ from by
          simp only [gridToReal, Nat.cast_zero, zero_div, div_self hn']
          exact Prod.ext hf1_eq hf2_eq) (hno_fix ⟨0, n, by omega⟩)
      · -- ¬(d0 ≤ d1 ∧ d0 ≤ d2): d0 ≤ d2 requires f₂=1, f₁=0 (fixed point)
        intro ⟨_, h_le⟩
        have hf2_eq : (f (0, 1)).2 = 1 := by nlinarith
        have hf1_eq : (f (0, 1)).1 = 0 := by linarith
        exact absurd (show f (gridToReal n ⟨0, n, by omega⟩) = gridToReal n ⟨0, n, by omega⟩ from by
          simp only [gridToReal, Nat.cast_zero, zero_div, div_self hn']
          exact Prod.ext hf1_eq hf2_eq) (hno_fix ⟨0, n, by omega⟩)
  -- (4) Bottom edge: j=0, 0<i<n → c ≠ 2
  -- Color=2 requires d1>d2≥0 (since d2=f₂-0=f₂≥0), giving d1>0.
  -- But d0>d1 or d0>d2 then gives f₂<0, contradicting hrange.
  · intro v hj hi0 hin heq
    simp only [displacementColoring] at heq
    by_cases htie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
        ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
        (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
      (f (gridToReal n v)).1 - (gridToReal n v).1 =
        (f (gridToReal n v)).2 - (gridToReal n v).2
    · -- Tie case: on bottom edge (j=0, 0<i<n), tie-breaking gives color 0 ≠ 2
      rw [if_pos htie] at heq
      -- On bottom edge with i>0, i<n, j=0: ¬(i=0∧j=0), ¬(j=0∧i+j=n) iff ¬(i=n)
      -- If i<n: ¬(j=0∧i+j=n), ¬(i=0∧i+j=n), ¬(i+j=n), ¬(i=0) → else → color 0
      have : ¬(v.i = 0 ∧ v.j = 0) := by omega
      have : ¬(v.j = 0 ∧ v.i + v.j = n) := by omega
      have : ¬(v.i = 0 ∧ v.i + v.j = n) := by omega
      have : ¬(v.i + v.j = n) := by omega
      have : ¬(v.i = 0) := by omega
      simp_all
    · rw [if_neg htie] at heq
      split_ifs at heq with h2 h3
      · exact absurd heq (by decide)
      · exact absurd heq (by decide)
      · -- ¬(d0 ≤ d1 ∧ d0 ≤ d2), ¬(d1 ≤ d2), color = 2
        have hv := gridToReal_in_simplex hn v
        obtain ⟨_, hf2, _⟩ := hrange _ hv.1 hv.2.1 hv.2.2
        have hpj : (gridToReal n v).2 = 0 := by
          simp [gridToReal, hj, Nat.cast_zero, zero_div]
        have hd2 : (f (gridToReal n v)).2 - (gridToReal n v).2 ≥ 0 := by linarith [hpj]
        push_neg at h3 -- h3: d2 < d1
        exact h2 ⟨by linarith, by linarith⟩
  -- (5) Left edge: i=0, 0<j<n → c ≠ 1
  -- Symmetric to bottom edge: d1=f₁-0=f₁≥0, d1≤d2, d0>d1 or d0>d2 gives f₁<0.
  · intro v hvi hj0 hjn heq
    simp only [displacementColoring] at heq
    -- Handle tie-breaking case first
    by_cases htie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
        ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
        (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
      (f (gridToReal n v)).1 - (gridToReal n v).1 =
        (f (gridToReal n v)).2 - (gridToReal n v).2
    · -- Tie case: on left edge (i=0, j>0, j<n), tie-breaking gives color 2
      rw [if_pos htie] at heq
      -- On left edge with j>0, j<n: ¬(i=0∧j=0), ¬(j=0∧i+j=n), ¬(i=0∧i+j=n), ¬(i+j=n), i=0 → color 2
      have : ¬(v.i = 0 ∧ v.j = 0) := by omega
      have : ¬(v.j = 0 ∧ v.i + v.j = n) := by omega
      have : ¬(v.i = 0 ∧ v.i + v.j = n) := by omega
      have : ¬(v.i + v.j = n) := by omega
      have : v.i = 0 := hvi
      simp_all
    · rw [if_neg htie] at heq
      split_ifs at heq with h2 h3
      · exact absurd heq (by decide)
      · -- d1 ≤ d2, color = 1. Derive contradiction: d0 ≤ d1 ∧ d0 ≤ d2.
        have hv := gridToReal_in_simplex hn v
        obtain ⟨hf1, _, _⟩ := hrange _ hv.1 hv.2.1 hv.2.2
        have hpi : (gridToReal n v).1 = 0 := by
          simp [gridToReal, hvi, Nat.cast_zero, zero_div]
        have hd1 : (f (gridToReal n v)).1 - (gridToReal n v).1 ≥ 0 := by linarith [hpi]
        exact h2 ⟨by linarith, by linarith⟩
      · exact absurd heq (by decide)
  -- (6) Hypotenuse: i+j=n, i>0, j>0 → c ≠ 0
  -- d0=1-f₁-f₂≥0. d0≤d1∧d0≤d2 forces f₁+f₂=1 and f₁=p₁, f₂=p₂, i.e. fixed point.
  · intro v hsum hi0 hj0 heq
    simp only [displacementColoring] at heq
    by_cases htie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
        ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
        (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
      (f (gridToReal n v)).1 - (gridToReal n v).1 =
        (f (gridToReal n v)).2 - (gridToReal n v).2
    · -- Tie case: on hypotenuse (i+j=n, i>0, j>0), tie-breaking gives color 1 ≠ 0
      rw [if_pos htie] at heq
      -- On hypotenuse with i>0, j>0: ¬(i=0∧j=0), ¬(j=0∧i+j=n), ¬(i=0∧i+j=n), i+j=n → color 1
      have : ¬(v.i = 0 ∧ v.j = 0) := by omega
      have : ¬(v.j = 0 ∧ v.i + v.j = n) := by omega
      have : ¬(v.i = 0 ∧ v.i + v.j = n) := by omega
      have : v.i + v.j = n := hsum
      simp_all
    · rw [if_neg htie] at heq
      split_ifs at heq with h2 h3
      · -- d0 ≤ d1 ∧ d0 ≤ d2, color = 0. Derive fixed point contradiction.
        have hv := gridToReal_in_simplex hn v
        obtain ⟨hf1, hf2, hf12⟩ := hrange _ hv.1 hv.2.1 hv.2.2
        have hpsum : (gridToReal n v).1 + (gridToReal n v).2 = 1 := by
          have : (gridToReal n v).1 + (gridToReal n v).2 = (↑v.i + ↑v.j : ℝ) / ↑n := by
            simp only [gridToReal]; ring
          rw [this, div_eq_one_iff_eq hn']
          exact_mod_cast hsum
        obtain ⟨h_le1, h_le2⟩ := h2
        have hfsum : (f (gridToReal n v)).1 + (f (gridToReal n v)).2 = 1 := by nlinarith
        have hf1_eq : (f (gridToReal n v)).1 = (gridToReal n v).1 := by nlinarith
        have hf2_eq : (f (gridToReal n v)).2 = (gridToReal n v).2 := by nlinarith
        exact absurd (Prod.ext hf1_eq hf2_eq) (hno_fix v)
      · exact absurd heq (by decide)
      · exact absurd heq (by decide)

-- Color 0 implies d₁ + d₂ ≥ 0 (d₀ = -(d₁+d₂) is the minimum, hence ≤ 0)
private lemma color_zero_sum_nonneg {n : ℕ} {f : ℝ × ℝ → ℝ × ℝ} (v : GridVertex n)
    (hc : displacementColoring n f v = 0) :
    (f (gridToReal n v)).1 - (gridToReal n v).1 +
    ((f (gridToReal n v)).2 - (gridToReal n v).2) ≥ 0 := by
  simp only [displacementColoring] at hc
  by_cases htie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
      ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
      (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
    (f (gridToReal n v)).1 - (gridToReal n v).1 =
      (f (gridToReal n v)).2 - (gridToReal n v).2
  · -- Tie-breaking case: d0=d1=d2. Since d0+d1+d2=0, all are 0. Sum ≥ 0.
    obtain ⟨heq1, heq2⟩ := htie
    nlinarith
  · rw [if_neg htie] at hc
    split_ifs at hc with h2 h3
    · -- d0 ≤ d1 ∧ d0 ≤ d2: 3(d1+d2) ≥ 0
      obtain ⟨h_le1, h_le2⟩ := h2
      nlinarith
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)

-- Color 1 implies d₁ ≤ 0 (d₁ is the minimum displacement component)
private lemma color_one_d1_nonpos {n : ℕ} {f : ℝ × ℝ → ℝ × ℝ} (v : GridVertex n)
    (hc : displacementColoring n f v = 1) :
    (f (gridToReal n v)).1 - (gridToReal n v).1 ≤ 0 := by
  simp only [displacementColoring] at hc
  by_cases htie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
      ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
      (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
    (f (gridToReal n v)).1 - (gridToReal n v).1 =
      (f (gridToReal n v)).2 - (gridToReal n v).2
  · -- Tie: d0=d1=d2, so d1=0
    obtain ⟨heq1, _⟩ := htie; nlinarith
  · rw [if_neg htie] at hc
    split_ifs at hc with h2 h3
    · exact absurd hc (by decide)
    · by_contra hd; push_neg at hd; exact h2 ⟨by linarith, by linarith⟩
    · exact absurd hc (by decide)

-- Color 2 implies d₂ ≤ 0 (d₂ is the minimum displacement component)
private lemma color_two_d2_nonpos {n : ℕ} {f : ℝ × ℝ → ℝ × ℝ} (v : GridVertex n)
    (hc : displacementColoring n f v = 2) :
    (f (gridToReal n v)).2 - (gridToReal n v).2 ≤ 0 := by
  simp only [displacementColoring] at hc
  by_cases htie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
      ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
      (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
    (f (gridToReal n v)).1 - (gridToReal n v).1 =
      (f (gridToReal n v)).2 - (gridToReal n v).2
  · -- Tie: d0=d1=d2, so d2=0
    obtain ⟨_, heq2⟩ := htie; nlinarith
  · rw [if_neg htie] at hc
    split_ifs at hc with h2 h3
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · by_contra hd; push_neg at hd h3; exact h2 ⟨by linarith, by linarith⟩

-- Approximate Brouwer fixed point via Sperner's lemma + uniform continuity.
theorem approximate_fixed_point_2d
    {f : ℝ × ℝ → ℝ × ℝ}
    (hcont : Continuous f)
    (hrange : ∀ p, p.1 ≥ 0 → p.2 ≥ 0 → p.1 + p.2 ≤ 1 →
      (f p).1 ≥ 0 ∧ (f p).2 ≥ 0 ∧ (f p).1 + (f p).2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ × ℝ, p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ p.1 + p.2 ≤ 1 ∧
      dist p (f p) < ε := by
  -- Step 1: f is uniformly continuous on the compact unit square (contains the simplex)
  have huc : UniformContinuousOn f (Set.Icc ((0:ℝ), (0:ℝ)) ((1:ℝ), (1:ℝ))) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  -- Step 2: Get δ for tolerance ε/4
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (ε / 4) (by linarith)
  -- Step 3: Choose n so that grid mesh 1/n < min(δ, ε/4)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / δ) (4 / ε))
  have hn_pos : 0 < n := by
    by_contra h; push_neg at h; interval_cases n
    simp at hn; linarith [div_pos (one_pos) hδ_pos]
  -- Step 4: Either grid fixed point (done) or Sperner coloring
  by_cases h : ∃ v : GridVertex n, f (gridToReal n v) = gridToReal n v
  · obtain ⟨v, hv⟩ := h
    have hv_in := gridToReal_in_simplex hn_pos v
    exact ⟨gridToReal n v, hv_in.1, hv_in.2.1, hv_in.2.2, by rw [hv, dist_self]; exact hε⟩
  · push_neg at h
    have hSperner := displacementColoring_isSperner n hn_pos f hrange h
    obtain ⟨t, ht⟩ := sperner_2d hn_pos (displacementColoring n f) hSperner
    -- Step 5: Find vertices with colors 1 and 2 in the fully-colored triangle
    have ⟨i₁, hi₁⟩ : ∃ i : Fin 3, displacementColoring n f (t.vertices i) = 1 := by
      have : (1 : Fin 3) ∈ Finset.image ((displacementColoring n f) ∘ t.vertices) Finset.univ :=
        by unfold IsFullyColored at ht; rw [ht]; simp
      simpa using this
    have ⟨i₂, hi₂⟩ : ∃ i : Fin 3, displacementColoring n f (t.vertices i) = 2 := by
      have : (2 : Fin 3) ∈ Finset.image ((displacementColoring n f) ∘ t.vertices) Finset.univ :=
        by unfold IsFullyColored at ht; rw [ht]; simp
      simpa using this
    -- Find the color-0 vertex (use it as approximate fixed point for tightest bound)
    have ⟨i₀, hi₀⟩ : ∃ i : Fin 3, displacementColoring n f (t.vertices i) = 0 := by
      have : (0 : Fin 3) ∈ Finset.image ((displacementColoring n f) ∘ t.vertices) Finset.univ :=
        by unfold IsFullyColored at ht; rw [ht]; simp
      simpa using this
    -- Pick the color-0 vertex as our approximate fixed point
    set v₀ := t.vertices i₀
    have hv₀_in := gridToReal_in_simplex hn_pos v₀
    refine ⟨gridToReal n v₀, hv₀_in.1, hv₀_in.2.1, hv₀_in.2.2, ?_⟩
    -- Key displacement facts from coloring
    have hd0_sum := color_zero_sum_nonneg v₀ hi₀       -- d₁(v₀) + d₂(v₀) ≥ 0
    have hd1_neg := color_one_d1_nonpos (t.vertices i₁) hi₁  -- d₁(v₁) ≤ 0
    have hd2_neg := color_two_d2_nonpos (t.vertices i₂) hi₂  -- d₂(v₂) ≤ 0
    -- Abbreviations for readability
    set p₀ := gridToReal n v₀
    set p₁ := gridToReal n (t.vertices i₁)
    set p₂ := gridToReal n (t.vertices i₂)
    -- Key bound: 1/n < ε/4 (from n > 4/ε)
    have hn_real : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have h_inv_n : 1 / (n : ℝ) < ε / 4 := by
      have h1 : (n : ℝ) > 4 / ε := lt_of_le_of_lt (le_max_right _ _) hn
      have h2 : ↑n * ε > 4 := by
        have := mul_lt_mul_of_pos_right h1 hε
        rwa [div_mul_cancel₀ _ (ne_of_gt hε)] at this
      have hne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_real
      -- 1/n < ε/4 iff 4 < n*ε (cross-multiply, both positive)
      rw [div_lt_div_iff₀ hn_real (show (0:ℝ) < 4 by norm_num), one_mul]; linarith
    -- Key bound: 1/n < δ (from n > 1/δ)
    have h_inv_n_lt_delta : 1 / (n : ℝ) < δ := by
      have h1 : (n : ℝ) > 1 / δ := lt_of_le_of_lt (le_max_left _ _) hn
      have h2 : ↑n * δ > 1 := by
        have := mul_lt_mul_of_pos_right h1 hδ_pos
        rwa [div_mul_cancel₀ _ (ne_of_gt hδ_pos)] at this
      rw [div_lt_iff₀ hn_real]; linarith
    -- Grid simplex vertices are in [0,1]×[0,1] (needed for UC application)
    have hv_in_box : ∀ v : GridVertex n,
        (gridToReal n v) ∈ Set.Icc ((0:ℝ), (0:ℝ)) ((1:ℝ), (1:ℝ)) := by
      intro v
      have hv_simp := gridToReal_in_simplex hn_pos v
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hv_simp.1, hv_simp.2.1, hv_simp.2.2]
    -- Grid triangle vertices differ by at most 1 in each coordinate
    -- so |pᵢ.k - pⱼ.k| ≤ 1/n for any two triangle vertices and coordinate k
    -- Triangle vertices are within L∞ distance 1/n of each other
    -- (Grid vertices differ by at most 1 in each ℕ coordinate, so ≤ 1/n in ℝ)
    -- Helper: |a/n - b/n| ≤ 1/n when |a - b| ≤ 1 (for natural a, b)
    have coord_dist : ∀ (a b : ℕ), (a : ℤ) - b ≤ 1 → (b : ℤ) - a ≤ 1 →
        dist ((a : ℝ) / n) ((b : ℝ) / n) ≤ 1 / (n : ℝ) := by
      intro a b hab hba
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hn_real]
      apply div_le_div_of_nonneg_right _ (le_of_lt hn_real)
      have : |(↑a : ℝ) - ↑b| ≤ 1 := by
        rw [abs_le]; exact ⟨by exact_mod_cast (by omega : -1 ≤ (a : ℤ) - b),
                            by exact_mod_cast (by omega : (a : ℤ) - b ≤ 1)⟩
      linarith
    have h_dist_bound : ∀ (i j : Fin 3),
        dist (gridToReal n (t.vertices i)) (gridToReal n (t.vertices j)) ≤ 1 / (n : ℝ) := by
      intro i j
      simp only [Prod.dist_eq, gridToReal, GridTriangle.vertices]
      rcases t with ⟨ti, tj, ty, hvalid⟩
      rcases ty with _ | _ <;> simp only [lowerVertices, upperVertices] <;>
      fin_cases i <;> fin_cases j <;> simp only <;>
      apply max_le <;> apply coord_dist <;> omega
    -- By uniform continuity: dist(f(pᵢ), f(pⱼ)) < ε/4 for triangle vertices
    have h_f_close : ∀ (i j : Fin 3),
        dist (f (gridToReal n (t.vertices i))) (f (gridToReal n (t.vertices j))) < ε / 4 := by
      intro i j
      have hdist := h_dist_bound i j
      exact hδ _ (hv_in_box _) _ (hv_in_box _) (lt_of_le_of_lt hdist h_inv_n_lt_delta)
    -- Component-level bounds from UC: |f(pᵢ).k - f(pⱼ).k| < ε/4
    have h_f_comp : ∀ (i j : Fin 3),
        |(f (gridToReal n (t.vertices i))).1 - (f (gridToReal n (t.vertices j))).1| < ε / 4 ∧
        |(f (gridToReal n (t.vertices i))).2 - (f (gridToReal n (t.vertices j))).2| < ε / 4 := by
      intro i j
      have hfij := h_f_close i j
      rw [Prod.dist_eq] at hfij
      simp only [Real.dist_eq] at hfij
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hfij,
             lt_of_le_of_lt (le_max_right _ _) hfij⟩
    -- Transfer d₁ from color-1 vertex to v₀:
    -- d₁(v₀) = (f(p₀).1 - f(p₁).1) + d₁(v₁) + (p₁.1 - p₀.1) < ε/4 + 0 + ε/4 = ε/2
    have hd1_upper : (f p₀).1 - p₀.1 < ε / 2 := by
      have hfc := (h_f_comp i₀ i₁).1
      have hpc : |(gridToReal n (t.vertices i₀)).1 - (gridToReal n (t.vertices i₁)).1| ≤ 1 / ↑n := by
        have := h_dist_bound i₀ i₁
        rw [Prod.dist_eq] at this
        exact le_trans (le_max_left _ _) this
      -- |a| < b → a < b ∧ -a < b, i.e., -b < a ∧ a < b
      have h_fc_bounds := abs_lt.mp hfc
      have h_pc_bounds := abs_lt.mp (lt_of_le_of_lt hpc h_inv_n)
      -- h_fc_bounds.2 : (f p₀).1 - (f p₁).1 < ε/4
      -- h_pc_bounds.1 : -(ε/4) < p₀.1 - p₁.1, i.e., p₁.1 - p₀.1 < ε/4
      linarith [h_fc_bounds.2, h_pc_bounds.1, hd1_neg]
    -- Transfer d₂ from color-2 vertex to v₀: d₂(v₀) < ε/2
    have hd2_upper : (f p₀).2 - p₀.2 < ε / 2 := by
      have hfc := (h_f_comp i₀ i₂).2
      have hpc : |(gridToReal n (t.vertices i₀)).2 - (gridToReal n (t.vertices i₂)).2| ≤ 1 / ↑n := by
        have := h_dist_bound i₀ i₂
        rw [Prod.dist_eq] at this
        exact le_trans (le_max_right _ _) this
      have h_fc_bounds := abs_lt.mp hfc
      have h_pc_bounds := abs_lt.mp (lt_of_le_of_lt hpc h_inv_n)
      -- h_fc_bounds.2 : (f p₀).2 - (f p₂).2 < ε/4
      -- h_pc_bounds.1 : -(ε/4) < p₀.2 - p₂.2, i.e., p₂.2 - p₀.2 < ε/4
      linarith [h_fc_bounds.2, h_pc_bounds.1, hd2_neg]
    -- Lower bounds from color-0: d₁(v₀) + d₂(v₀) ≥ 0
    -- Combined: d₁(v₀) ≥ -d₂(v₀) > -ε/2 and d₂(v₀) ≥ -d₁(v₀) > -ε/2
    have hd1_lower : (f p₀).1 - p₀.1 > -(ε / 2) := by linarith
    have hd2_lower : (f p₀).2 - p₀.2 > -(ε / 2) := by linarith
    -- Therefore dist = max(|d₁|, |d₂|) < ε/2 < ε
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    apply max_lt <;> rw [abs_lt] <;> constructor <;> linarith

end Sperner2D
