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

-- The tie-breaking condition in displacementColoring implies f(v)=v, which contradicts hno_fix
private lemma displacementColoring_no_tie {n : ℕ} {f : ℝ × ℝ → ℝ × ℝ}
    (v : GridVertex n) (hne : f (gridToReal n v) ≠ gridToReal n v) :
    ¬(-((f (gridToReal n v)).1 - (gridToReal n v).1 +
        ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
      (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
      (f (gridToReal n v)).1 - (gridToReal n v).1 =
      (f (gridToReal n v)).2 - (gridToReal n v).2) := by
  rintro ⟨h1, h2⟩
  exact hne (Prod.ext (by linarith) (by linarith))

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
  · simp only [displacementColoring]
    rw [if_neg (displacementColoring_no_tie ⟨0, 0, by omega⟩ (hno_fix ⟨0, 0, by omega⟩))]
    simp only [gridToReal, Nat.cast_zero, zero_div, sub_zero]
    obtain ⟨hf1, hf2, _⟩ := hrange (0, 0) le_rfl le_rfl (by norm_num)
    rw [if_pos ⟨by linarith, by linarith⟩]
  -- (2) c(n,0) = 1: d1=f₁-1≤0, d2=f₂≥0, so d1≤d2. d0≤d1 iff f=(1,0) (fixed point).
  · simp only [displacementColoring]
    rw [if_neg (displacementColoring_no_tie ⟨n, 0, by omega⟩ (hno_fix ⟨n, 0, by omega⟩))]
    simp only [gridToReal, Nat.cast_zero, zero_div, sub_zero, div_self hn']
    obtain ⟨hf1, hf2, hf12⟩ := hrange (1, 0) (by norm_num) le_rfl (by norm_num)
    rw [if_neg, if_pos (show (f (1, 0)).1 - 1 ≤ (f (1, 0)).2 by linarith)]
    intro ⟨h_le, _⟩
    have hf1_eq : (f (1, 0)).1 = 1 := by nlinarith
    have hf2_eq : (f (1, 0)).2 = 0 := by linarith
    exact absurd (show f (gridToReal n ⟨n, 0, by omega⟩) = gridToReal n ⟨n, 0, by omega⟩ from by
      simp only [gridToReal, Nat.cast_zero, zero_div, div_self hn']
      exact Prod.ext hf1_eq hf2_eq) (hno_fix ⟨n, 0, by omega⟩)
  -- (3) c(0,n) = 2: d1=f₁≥0, d2=f₂-1≤0, d0=1-f₁-f₂≥0. Neither if-branch unless fixed pt.
  · simp only [displacementColoring]
    rw [if_neg (displacementColoring_no_tie ⟨0, n, by omega⟩ (hno_fix ⟨0, n, by omega⟩))]
    simp only [gridToReal, Nat.cast_zero, zero_div, sub_zero, div_self hn']
    obtain ⟨hf1, hf2, hf12⟩ := hrange (0, 1) le_rfl (by norm_num) (by norm_num)
    rw [if_neg, if_neg]
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
    rw [if_neg (displacementColoring_no_tie v (hno_fix v))] at heq
    split_ifs at heq with h1 h2
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
    · -- h1: ¬(d0 ≤ d1 ∧ d0 ≤ d2), h2: ¬(d1 ≤ d2)
      -- Since d2=f₂≥0 and d1>d2≥0, both d1,d2>0, so d0=-(d1+d2)<0≤d1,d2.
      -- Hence d0≤d1 ∧ d0≤d2, contradicting h1.
      have hv := gridToReal_in_simplex hn v
      obtain ⟨_, hf2, _⟩ := hrange _ hv.1 hv.2.1 hv.2.2
      have hpj : (gridToReal n v).2 = 0 := by
        simp [gridToReal, hj, Nat.cast_zero, zero_div]
      have hd2 : (f (gridToReal n v)).2 - (gridToReal n v).2 ≥ 0 := by linarith [hpj]
      push_neg at h2 -- h2: d2 < d1
      exact h1 ⟨by linarith, by linarith⟩
  -- (5) Left edge: i=0, 0<j<n → c ≠ 1
  -- Symmetric to bottom edge: d1=f₁-0=f₁≥0, d1≤d2, d0>d1 or d0>d2 gives f₁<0.
  · intro v hi hj0 hjn heq
    simp only [displacementColoring] at heq
    rw [if_neg (displacementColoring_no_tie v (hno_fix v))] at heq
    split_ifs at heq with h1 h2
    · exact absurd heq (by decide)
    · -- h1: ¬(d0 ≤ d1 ∧ d0 ≤ d2), h2: d1 ≤ d2 (TRUE from split_ifs)
      -- Since d1=f₁≥0 and d2≥d1≥0, d0=-(d1+d2)≤0≤d1,d2.
      -- Hence d0≤d1 ∧ d0≤d2, contradicting h1.
      have hv := gridToReal_in_simplex hn v
      obtain ⟨hf1, _, _⟩ := hrange _ hv.1 hv.2.1 hv.2.2
      have hpi : (gridToReal n v).1 = 0 := by
        simp [gridToReal, hi, Nat.cast_zero, zero_div]
      have hd1 : (f (gridToReal n v)).1 - (gridToReal n v).1 ≥ 0 := by linarith [hpi]
      exact h1 ⟨by linarith, by linarith⟩
    · exact absurd heq (by decide)
  -- (6) Hypotenuse: i+j=n, i>0, j>0 → c ≠ 0
  -- d0=1-f₁-f₂≥0. d0≤d1∧d0≤d2 forces f₁+f₂=1 and f₁=p₁, f₂=p₂, i.e. fixed point.
  · intro v hsum hi0 hj0 heq
    simp only [displacementColoring] at heq
    rw [if_neg (displacementColoring_no_tie v (hno_fix v))] at heq
    split_ifs at heq with h1 h2
    · have hv := gridToReal_in_simplex hn v
      obtain ⟨hf1, hf2, hf12⟩ := hrange _ hv.1 hv.2.1 hv.2.2
      have hpsum : (gridToReal n v).1 + (gridToReal n v).2 = 1 := by
        have : (gridToReal n v).1 + (gridToReal n v).2 = (↑v.i + ↑v.j : ℝ) / ↑n := by
          simp only [gridToReal]; ring
        rw [this, div_eq_one_iff_eq hn']
        exact_mod_cast hsum
      obtain ⟨h_le1, h_le2⟩ := h1
      have hfsum : (f (gridToReal n v)).1 + (f (gridToReal n v)).2 = 1 := by nlinarith
      have hf1_eq : (f (gridToReal n v)).1 = (gridToReal n v).1 := by nlinarith
      have hf2_eq : (f (gridToReal n v)).2 = (gridToReal n v).2 := by nlinarith
      exact absurd (Prod.ext hf1_eq hf2_eq) (hno_fix v)
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)

-- Coordinate bounds for vertices of a grid triangle
private lemma triangle_vertex_i_sub_le {n : ℕ} {t : GridTriangle n} (a b : Fin 3) :
    (t.vertices a).i ≤ (t.vertices b).i + 1 := by
  rcases t with ⟨ti, tj, ty, hv⟩
  cases ty <;> fin_cases a <;> fin_cases b <;>
    simp [GridTriangle.vertices, lowerVertices, upperVertices] <;> omega

private lemma triangle_vertex_j_sub_le {n : ℕ} {t : GridTriangle n} (a b : Fin 3) :
    (t.vertices a).j ≤ (t.vertices b).j + 1 := by
  rcases t with ⟨ti, tj, ty, hv⟩
  cases ty <;> fin_cases a <;> fin_cases b <;>
    simp [GridTriangle.vertices, lowerVertices, upperVertices] <;> omega

-- Vertices of a grid triangle are within 1/n in L∞ distance
private lemma triangle_vertices_close {n : ℕ} (hn : 0 < n) (t : GridTriangle n)
    (a b : Fin 3) :
    dist (gridToReal n (t.vertices a)) (gridToReal n (t.vertices b)) ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [Prod.dist_eq, Real.dist_eq, gridToReal]
  have hi1 : (↑(t.vertices a).i : ℝ) ≤ ↑(t.vertices b).i + 1 := by
    exact_mod_cast triangle_vertex_i_sub_le a b
  have hi2 : (↑(t.vertices b).i : ℝ) ≤ ↑(t.vertices a).i + 1 := by
    exact_mod_cast triangle_vertex_i_sub_le b a
  have hj1 : (↑(t.vertices a).j : ℝ) ≤ ↑(t.vertices b).j + 1 := by
    exact_mod_cast triangle_vertex_j_sub_le a b
  have hj2 : (↑(t.vertices b).j : ℝ) ≤ ↑(t.vertices a).j + 1 := by
    exact_mod_cast triangle_vertex_j_sub_le b a
  apply max_le <;> {
    rw [← sub_div, abs_div, abs_of_pos hn']
    gcongr; rw [abs_le]; constructor <;> linarith
  }

-- Grid vertices lie in [0,1]²
private lemma gridToReal_mem_Icc {n : ℕ} (hn : 0 < n) (v : GridVertex n) :
    gridToReal n v ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hvi : (v.i : ℝ) ≤ n := by exact_mod_cast (show v.i ≤ n from le_of_add_le_left v.valid)
  have hvj : (v.j : ℝ) ≤ n := by exact_mod_cast (show v.j ≤ n from le_of_add_le_right v.valid)
  simp only [Set.mem_Icc, Prod.le_def, gridToReal]
  exact ⟨⟨by positivity, by positivity⟩,
         ⟨by rwa [div_le_one hn'], by rwa [div_le_one hn']⟩⟩

-- Color 1 implies d₁ ≤ 0 (d₁ is the minimum displacement component)
private lemma color_one_d1_nonpos {n : ℕ} {f : ℝ × ℝ → ℝ × ℝ} (v : GridVertex n)
    (hc : displacementColoring n f v = 1) :
    (f (gridToReal n v)).1 - (gridToReal n v).1 ≤ 0 := by
  simp only [displacementColoring] at hc
  by_cases h_tie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
      ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
    (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
    (f (gridToReal n v)).1 - (gridToReal n v).1 =
    (f (gridToReal n v)).2 - (gridToReal n v).2
  · linarith [h_tie.1, h_tie.2]  -- tie → d₁ = 0
  · rw [if_neg h_tie] at hc
    split_ifs at hc with h1 h2
    · exact absurd hc (by decide)
    · by_contra hd; push_neg at hd; exact h1 ⟨by linarith, by linarith⟩
    · exact absurd hc (by decide)

-- Color 2 implies d₂ ≤ 0 (d₂ is the minimum displacement component)
private lemma color_two_d2_nonpos {n : ℕ} {f : ℝ × ℝ → ℝ × ℝ} (v : GridVertex n)
    (hc : displacementColoring n f v = 2) :
    (f (gridToReal n v)).2 - (gridToReal n v).2 ≤ 0 := by
  simp only [displacementColoring] at hc
  by_cases h_tie : -((f (gridToReal n v)).1 - (gridToReal n v).1 +
      ((f (gridToReal n v)).2 - (gridToReal n v).2)) =
    (f (gridToReal n v)).1 - (gridToReal n v).1 ∧
    (f (gridToReal n v)).1 - (gridToReal n v).1 =
    (f (gridToReal n v)).2 - (gridToReal n v).2
  · linarith [h_tie.1, h_tie.2]  -- tie → d₂ = 0
  · rw [if_neg h_tie] at hc
    split_ifs at hc with h1 h2
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · by_contra hd; push_neg at hd h2; exact h1 ⟨by linarith, by linarith⟩

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
    by_contra h; push_neg at h; interval_cases n; simp at hn; linarith
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
    -- Pick vertex 0 of the triangle as our approximate fixed point
    set v₀ := t.vertices 0
    have hv₀_in := gridToReal_in_simplex hn_pos v₀
    refine ⟨gridToReal n v₀, hv₀_in.1, hv₀_in.2.1, hv₀_in.2.2, ?_⟩
    -- Step 6: Bound displacement using color analysis + uniform continuity
    -- d₁(color-1 vertex) ≤ 0 and d₂(color-2 vertex) ≤ 0 (from color lemmas).
    -- By uniform continuity across the triangle (diameter ≤ 1/n in max-norm),
    -- d₁(v₀) < ε/2 and d₂(v₀) < ε/2. Color 0 structure at v₀ gives lower bounds.
    -- Therefore dist = max(|d₁|, |d₂|) < ε/2 < ε in the max-norm on ℝ × ℝ.
    have hd1_neg := color_one_d1_nonpos (t.vertices i₁) hi₁
    have hd2_neg := color_two_d2_nonpos (t.vertices i₂) hi₂
    -- Extract color-0 vertex
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin 3, displacementColoring n f (t.vertices i) = 0 := by
      have : (0 : Fin 3) ∈ Finset.image ((displacementColoring n f) ∘ t.vertices) Finset.univ :=
        by unfold IsFullyColored at ht; rw [ht]; simp
      simpa using this
    -- Numerical bounds: 1/n < δ and 1/n < ε/4
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have h_inv_delta : 1 / (n : ℝ) < δ := by
      have h1 : (n : ℝ) > 1 / δ := lt_of_le_of_lt (le_max_left _ _) (by exact_mod_cast hn)
      have h_nδ : 1 < (n : ℝ) * δ :=
        calc (1 : ℝ) = 1 / δ * δ := by field_simp
          _ < (n : ℝ) * δ := mul_lt_mul_of_pos_right h1 hδ_pos
      rw [div_lt_iff₀ hn']; linarith
    have h_inv_eps4 : 1 / (n : ℝ) < ε / 4 := by
      have h1 : (n : ℝ) > 4 / ε := lt_of_le_of_lt (le_max_right _ _) (by exact_mod_cast hn)
      have h_nε : 4 < (n : ℝ) * ε :=
        calc (4 : ℝ) = 4 / ε * ε := by field_simp
          _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right h1 hε
      rw [div_lt_div_iff₀ hn' (by norm_num : (0:ℝ) < 4)]; linarith
    -- All triangle vertices are in [0,1]² and within δ of each other
    have h_mem : ∀ k : Fin 3,
        gridToReal n (t.vertices k) ∈ Set.Icc ((0:ℝ),(0:ℝ)) ((1:ℝ),(1:ℝ)) :=
      fun k => gridToReal_mem_Icc hn_pos (t.vertices k)
    have h_close : ∀ a b : Fin 3,
        dist (gridToReal n (t.vertices a)) (gridToReal n (t.vertices b)) < δ :=
      fun a b => lt_of_le_of_lt (triangle_vertices_close hn_pos t a b) h_inv_delta
    -- Uniform continuity: f-values at triangle vertices are within ε/4
    have h_f_close : ∀ a b : Fin 3,
        dist (f (gridToReal n (t.vertices a))) (f (gridToReal n (t.vertices b))) < ε / 4 :=
      fun a b => hδ _ (h_mem a) _ (h_mem b) (h_close a b)
    -- Abbreviations for readability
    set p₀ := gridToReal n v₀ with hp₀_def
    set p₁ := gridToReal n (t.vertices i₁) with hp₁_def
    set p₂ := gridToReal n (t.vertices i₂) with hp₂_def
    set p₀' := gridToReal n (t.vertices i₀) with hp₀'_def
    -- Extract component-wise f-closeness from L∞ distance
    have hfc1 : ∀ a b : Fin 3,
        |(f (gridToReal n (t.vertices a))).1 - (f (gridToReal n (t.vertices b))).1| < ε / 4 := by
      intro a b; have h := h_f_close a b
      calc _ ≤ dist (f (gridToReal n (t.vertices a))).1 (f (gridToReal n (t.vertices b))).1 :=
                le_of_eq (Real.dist_eq _ _).symm
           _ ≤ max (dist (f (gridToReal n (t.vertices a))).1 (f (gridToReal n (t.vertices b))).1)
                   (dist (f (gridToReal n (t.vertices a))).2 (f (gridToReal n (t.vertices b))).2) :=
                le_max_left _ _
           _ = dist (f (gridToReal n (t.vertices a))) (f (gridToReal n (t.vertices b))) :=
                Prod.dist_eq.symm
           _ < ε / 4 := h
    have hfc2 : ∀ a b : Fin 3,
        |(f (gridToReal n (t.vertices a))).2 - (f (gridToReal n (t.vertices b))).2| < ε / 4 := by
      intro a b; have h := h_f_close a b
      calc _ ≤ dist (f (gridToReal n (t.vertices a))).2 (f (gridToReal n (t.vertices b))).2 :=
                le_of_eq (Real.dist_eq _ _).symm
           _ ≤ max (dist (f (gridToReal n (t.vertices a))).1 (f (gridToReal n (t.vertices b))).1)
                   (dist (f (gridToReal n (t.vertices a))).2 (f (gridToReal n (t.vertices b))).2) :=
                le_max_right _ _
           _ = dist (f (gridToReal n (t.vertices a))) (f (gridToReal n (t.vertices b))) :=
                Prod.dist_eq.symm
           _ < ε / 4 := h
    -- Extract component-wise vertex closeness
    have hpc1 : ∀ a b : Fin 3,
        |(gridToReal n (t.vertices a)).1 - (gridToReal n (t.vertices b)).1| < ε / 4 := by
      intro a b
      have h := triangle_vertices_close hn_pos t a b
      calc _ ≤ dist (gridToReal n (t.vertices a)).1 (gridToReal n (t.vertices b)).1 :=
                le_of_eq (Real.dist_eq _ _).symm
           _ ≤ max (dist (gridToReal n (t.vertices a)).1 (gridToReal n (t.vertices b)).1)
                   (dist (gridToReal n (t.vertices a)).2 (gridToReal n (t.vertices b)).2) :=
                le_max_left _ _
           _ = dist (gridToReal n (t.vertices a)) (gridToReal n (t.vertices b)) :=
                Prod.dist_eq.symm
           _ ≤ 1 / (n : ℝ) := h
           _ < ε / 4 := h_inv_eps4
    have hpc2 : ∀ a b : Fin 3,
        |(gridToReal n (t.vertices a)).2 - (gridToReal n (t.vertices b)).2| < ε / 4 := by
      intro a b
      have h := triangle_vertices_close hn_pos t a b
      calc _ ≤ dist (gridToReal n (t.vertices a)).2 (gridToReal n (t.vertices b)).2 :=
                le_of_eq (Real.dist_eq _ _).symm
           _ ≤ max (dist (gridToReal n (t.vertices a)).1 (gridToReal n (t.vertices b)).1)
                   (dist (gridToReal n (t.vertices a)).2 (gridToReal n (t.vertices b)).2) :=
                le_max_right _ _
           _ = dist (gridToReal n (t.vertices a)) (gridToReal n (t.vertices b)) :=
                Prod.dist_eq.symm
           _ ≤ 1 / (n : ℝ) := h
           _ < ε / 4 := h_inv_eps4
    -- One-sided bounds from absolute values (for linarith)
    -- Upper bounds: a ≤ |a| < c gives a < c
    -- Lower bounds: |a| < c gives -c < a via abs_lt
    -- f-value bounds at v₀ vs v₁, v₂, v₀'
    have hf01_1 := lt_of_le_of_lt (le_abs_self _) (hfc1 0 i₁)  -- (f p₀).1 - (f p₁).1 < ε/4
    have hf02_2 := lt_of_le_of_lt (le_abs_self _) (hfc2 0 i₂)  -- (f p₀).2 - (f p₂).2 < ε/4
    have hf00'_1 := lt_of_le_of_lt (le_abs_self _) (hfc1 0 i₀)  -- (f p₀).1 - (f p₀').1 < ε/4
    have hf00'_1' := (abs_lt.mp (hfc1 0 i₀)).1  -- -(ε/4) < (f p₀).1 - (f p₀').1
    have hf00'_2 := lt_of_le_of_lt (le_abs_self _) (hfc2 0 i₀)  -- (f p₀).2 - (f p₀').2 < ε/4
    have hf00'_2' := (abs_lt.mp (hfc2 0 i₀)).1  -- -(ε/4) < (f p₀).2 - (f p₀').2
    -- vertex component bounds at v₀ vs v₁, v₂, v₀'
    have hp01_1 := lt_of_le_of_lt (le_abs_self _) (hpc1 i₁ 0)  -- p₁.1 - p₀.1 < ε/4
    have hp02_2 := lt_of_le_of_lt (le_abs_self _) (hpc2 i₂ 0)  -- p₂.2 - p₀.2 < ε/4
    have hp00'_1' := (abs_lt.mp (hpc1 i₀ 0)).1  -- -(ε/4) < p₀'.1 - p₀.1
    have hp00'_2' := (abs_lt.mp (hpc2 i₀ 0)).1  -- -(ε/4) < p₀'.2 - p₀.2
    -- f-closeness between i₀ and i₂ (for d₂ at color-0 vertex)
    have hf0'2_2 := lt_of_le_of_lt (le_abs_self _) (hfc2 i₀ i₂)  -- (f p₀').2 - (f p₂).2 < ε/4
    have hp0'2_2 := lt_of_le_of_lt (le_abs_self _) (hpc2 i₂ i₀)  -- p₂.2 - p₀'.2 < ε/4
    -- f-closeness between i₀ and i₁ (for d₁ at color-0 vertex)
    have hf0'1_1 := lt_of_le_of_lt (le_abs_self _) (hfc1 i₀ i₁)  -- (f p₀').1 - (f p₁).1 < ε/4
    have hp0'1_1 := lt_of_le_of_lt (le_abs_self _) (hpc1 i₁ i₀)  -- p₁.1 - p₀'.1 < ε/4
    -- === UPPER BOUNDS on displacements at v₀ ===
    -- d₁(v₀) = [(f p₀).1 - (f p₁).1] + [(f p₁).1 - p₁.1] + [p₁.1 - p₀.1] < ε/4 + 0 + ε/4
    have hd1_ub : (f p₀).1 - p₀.1 < ε / 2 := by linarith
    have hd2_ub : (f p₀).2 - p₀.2 < ε / 2 := by linarith
    -- === Color-0 displacement constraints ===
    -- At the color-0 vertex, d₀ ≤ d₁ ∧ d₀ ≤ d₂ (standard branch, tie-breaking ruled out)
    have h0_disp :
        -((f p₀').1 - p₀'.1 + ((f p₀').2 - p₀'.2)) ≤ (f p₀').1 - p₀'.1 ∧
        -((f p₀').1 - p₀'.1 + ((f p₀').2 - p₀'.2)) ≤ (f p₀').2 - p₀'.2 := by
      -- Tie-breaking requires f(v) = v, which contradicts h
      have h_ne := h (t.vertices i₀)
      have h_not_tie : ¬(-((f p₀').1 - p₀'.1 + ((f p₀').2 - p₀'.2)) =
          (f p₀').1 - p₀'.1 ∧ (f p₀').1 - p₀'.1 = (f p₀').2 - p₀'.2) := by
        rintro ⟨h1, h2⟩
        exact h_ne (Prod.ext (by linarith) (by linarith))
      simp only [displacementColoring] at hi₀
      rw [if_neg h_not_tie] at hi₀
      split_ifs at hi₀ with h_std
      · exact h_std
      all_goals exact absurd hi₀ (by decide)
    -- d₁(v₀') is bounded below: from 2d₁'+d₂' ≥ 0 and d₂'(v₀') < ε/2
    -- d₂(v₀') < (f p₂).2 - p₂.2 + ε/2 ≤ 0 + ε/2 = ε/2
    have hd2'_ub : (f p₀').2 - p₀'.2 < ε / 2 := by linarith
    -- From 2d₁' + d₂' ≥ 0: d₁' ≥ -d₂'/2 > -ε/4
    have hd1'_lb : (f p₀').1 - p₀'.1 > -(ε / 4) := by linarith [h0_disp.1]
    -- Similarly: d₁(v₀') < ε/2 and d₁'+2d₂' ≥ 0 gives d₂' > -ε/4
    have hd1'_ub : (f p₀').1 - p₀'.1 < ε / 2 := by linarith
    have hd2'_lb : (f p₀').2 - p₀'.2 > -(ε / 4) := by linarith [h0_disp.2]
    -- === LOWER BOUNDS on displacements at v₀ (via transfer from color-0 vertex) ===
    -- d₁(v₀) > d₁(v₀') - ε/2 > -ε/4 - ε/2 = -3ε/4 > -ε
    have hd1_lb : (f p₀).1 - p₀.1 > -ε := by linarith
    have hd2_lb : (f p₀).2 - p₀.2 > -ε := by linarith
    -- === Combine into dist < ε ===
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    apply max_lt <;> rw [abs_sub_comm, abs_lt]
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩

end Sperner2D
