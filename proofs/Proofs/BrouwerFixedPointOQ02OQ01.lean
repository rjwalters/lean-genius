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
**Triangles**: Two types per grid cell — "lower" ▽ and "upper" △.
**Sperner coloring**: Vertex (i,j) on edge opposite vertex k cannot use color k.

**Main result**: The number of fully-colored triangles is odd.

The proof uses a **door-counting** (double-counting) argument:
1. Define "doors" = edges colored {0,1}
2. Each fully-colored triangle has exactly 1 such door
3. Each {0,1}-colored triangle has exactly 2 doors (they cancel in parity)
4. Boundary {0,1} doors are odd (1D Sperner on the bottom edge)
5. Interior doors pair up (shared by two triangles)
6. Therefore: #(fully-colored triangles) is odd ≥ 1
-/

set_option linter.unusedVariables false

namespace Sperner2D

open Finset BigOperators

-- ============================================================
-- SECTION I: Grid Triangulation Definitions
-- ============================================================

/-- A grid vertex in the n-th subdivision of the unit triangle.
    (i, j) with i + j ≤ n represents the point (i/n, j/n). -/
structure GridVertex (n : ℕ) where
  i : ℕ
  j : ℕ
  valid : i + j ≤ n

/-- Two types of triangles in the standard triangulation. -/
inductive TriType
  | lower  -- △ with vertices (i,j), (i+1,j), (i,j+1)
  | upper  -- ▽ with vertices (i+1,j), (i,j+1), (i+1,j+1)

/-- A triangle in the n-th subdivision. -/
structure GridTriangle (n : ℕ) where
  i : ℕ
  j : ℕ
  ty : TriType
  valid : match ty with
    | .lower => i + 1 + j ≤ n  -- needs (i+1, j) and (i, j+1) valid
    | .upper => i + 1 + (j + 1) ≤ n  -- needs (i+1, j+1) valid

/-- The three vertices of a lower triangle (i,j). -/
def lowerVertices (n : ℕ) (i j : ℕ) (h : i + 1 + j ≤ n) :
    Fin 3 → GridVertex n
  | 0 => ⟨i, j, by omega⟩
  | 1 => ⟨i + 1, j, by omega⟩
  | 2 => ⟨i, j + 1, by omega⟩

/-- The three vertices of an upper triangle (i,j). -/
def upperVertices (n : ℕ) (i j : ℕ) (h : i + 1 + (j + 1) ≤ n) :
    Fin 3 → GridVertex n
  | 0 => ⟨i + 1, j, by omega⟩
  | 1 => ⟨i, j + 1, by omega⟩
  | 2 => ⟨i + 1, j + 1, by omega⟩

/-- The vertices of a grid triangle. -/
def GridTriangle.vertices {n : ℕ} (t : GridTriangle n) : Fin 3 → GridVertex n :=
  match t.ty, t.valid with
  | .lower, h => lowerVertices n t.i t.j h
  | .upper, h => upperVertices n t.i t.j h

-- ============================================================
-- SECTION II: Sperner Coloring
-- ============================================================

/-- A coloring of grid vertices into {0, 1, 2}. -/
def Coloring (n : ℕ) := GridVertex n → Fin 3

/-- The Sperner boundary condition for the unit triangle T = conv{e₀, e₁, e₂}
    where e₀ = (0,0), e₁ = (n,0), e₂ = (0,n):

    - Bottom edge (j = 0): colors ∈ {0, 1} (no color 2)
    - Left edge (i = 0): colors ∈ {0, 2} (no color 1)
    - Hypotenuse (i + j = n): colors ∈ {1, 2} (no color 0)
    - Vertex e₀ = (0,0): color 0
    - Vertex e₁ = (n,0): color 1
    - Vertex e₂ = (0,n): color 2 -/
def IsSperner {n : ℕ} (hn : 0 < n) (c : Coloring n) : Prop :=
  -- Vertex conditions
  c ⟨0, 0, by omega⟩ = 0 ∧
  c ⟨n, 0, by omega⟩ = 1 ∧
  c ⟨0, n, by omega⟩ = 2 ∧
  -- Edge conditions
  (∀ v : GridVertex n, v.j = 0 → v.i > 0 → v.i < n → c v ≠ 2) ∧
  (∀ v : GridVertex n, v.i = 0 → v.j > 0 → v.j < n → c v ≠ 1) ∧
  (∀ v : GridVertex n, v.i + v.j = n → v.i > 0 → v.j > 0 → c v ≠ 0)

/-- A triangle is "fully colored" if its three vertices have all three colors. -/
def IsFullyColored {n : ℕ} (c : Coloring n) (t : GridTriangle n) : Prop :=
  let colors := Finset.image (c ∘ t.vertices) Finset.univ
  colors = {0, 1, 2}

-- ============================================================
-- SECTION III: 1D Sperner on the Bottom Edge (Base Case)
-- ============================================================

/-- A helper: the bottom edge vertex (i, 0). -/
def botVertex (n : ℕ) (i : Fin (n + 1)) : GridVertex n :=
  ⟨i.val, 0, by omega⟩

/-- Color of the i-th vertex on the bottom edge, with bounds check. -/
private def botColor {n : ℕ} (c : Coloring n) (i : ℕ) : Fin 3 :=
  if h : i ≤ n then c ⟨i, 0, by omega⟩ else 0

/-- The number of color transitions along the bottom edge.
    A "transition" at position i means the color at (i,0) differs from (i+1,0). -/
def bottomTransitions {n : ℕ} (c : Coloring n) : ℕ :=
  ((Finset.range n).filter (fun i => botColor c i ≠ botColor c (i + 1))).card

-- ----------------------------------------------------------
-- Parity lemma: transition count for a binary sequence
-- ----------------------------------------------------------

/-- For a binary (Bool) sequence, the number of transitions mod 2
    equals 0 if endpoints match, 1 if they differ. -/
private theorem transitions_parity_bool (n : ℕ) (f : ℕ → Bool) :
    ((Finset.range n).filter (fun i => f i ≠ f (i + 1))).card % 2 =
    if f 0 = f n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_succ, Finset.filter_insert]
    by_cases hm : f m ≠ f (m + 1)
    · -- f m ≠ f (m + 1): the filter includes m
      rw [if_pos hm]
      have hmem : m ∉ (Finset.range m).filter (fun i => f i ≠ f (i + 1)) := by
        simp [Finset.mem_filter, Finset.mem_range]
      rw [Finset.card_insert_of_not_mem hmem]
      -- Use ih to relate old card to f 0 vs f m
      set k := ((Finset.range m).filter (fun i => f i ≠ f (i + 1))).card with hk_def
      have hk := ih
      -- For Bool, f m ≠ f (m+1) flips the endpoint comparison
      cases hf0 : f 0 <;> cases hfm : f m <;> cases hfm1 : f (m + 1) <;> simp_all <;> omega
    · -- f m = f (m + 1): filter unchanged
      rw [if_neg hm]
      rw [ih]
      push_neg at hm
      rw [hm]

/-- On the bottom edge (j=0), a Sperner coloring has an odd
    number of transitions (adjacent pairs with different colors).

    Proof: The Sperner condition restricts bottom edge colors to {0, 1},
    with c(0,0) = 0 and c(n,0) = 1. Project to Bool and apply parity lemma. -/
theorem bottom_transitions_odd {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) : Odd (bottomTransitions c) := by
  obtain ⟨hv0, hv1, _, hbot, _, _⟩ := hc
  -- Bottom edge colors are in {0, 1} (Sperner: no color 2 on bottom)
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
        -- c v ≠ 2 means c v = 0 or c v = 1 (since Fin 3 = {0, 1, 2})
        have hval := (c ⟨i, 0, by omega⟩).isLt
        omega
  -- Project to Bool: 0 ↦ false, 1 ↦ true
  let fb : ℕ → Bool := fun i => botColor c i = 1
  -- Transitions of c match transitions of fb (since colors are binary)
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
      -- If both are in {0,1} and (bc i = 1) = (bc (i+1) = 1), then bc i = bc (i+1)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
    · rintro ⟨hi, hne⟩
      refine ⟨hi, ?_⟩
      intro h
      apply hne
      simp only [fb, h]
  rw [htrans, Nat.odd_iff, transitions_parity_bool]
  -- fb 0 = false (c(0,0) = 0 ≠ 1) and fb n = true (c(n,0) = 1)
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

/-- An edge in the triangulation is a "door" if it is colored {0, 1}
    (one vertex has color 0, the other has color 1). -/
def IsDoor {n : ℕ} (c : Coloring n) (v w : GridVertex n) : Prop :=
  (c v = 0 ∧ c w = 1) ∨ (c v = 1 ∧ c w = 0)

/-- Each fully-colored triangle has exactly one {0,1}-door among its edges.
    (The door is the edge connecting the color-0 and color-1 vertices.) -/
theorem fully_colored_one_door {n : ℕ} (c : Coloring n)
    (t : GridTriangle n) (hfc : IsFullyColored c t) :
    ∃! (e : Fin 3 × Fin 3), e.1 < e.2 ∧
      IsDoor c (t.vertices e.1) (t.vertices e.2) := by
  sorry

/-- Sperner's Lemma (2D): Every Sperner-colored triangulation of the
    triangle with n subdivisions has an odd number of fully-colored triangles.
    In particular, at least one fully-colored triangle exists. -/
theorem sperner_2d {n : ℕ} (hn : 0 < n) (c : Coloring n) (hc : IsSperner hn c) :
    ∃ t : GridTriangle n, IsFullyColored c t := by
  -- The proof follows from the door-counting argument:
  -- 1. Count {0,1}-doors on the boundary: odd (bottom_edge_doors_odd)
  -- 2. Interior doors pair up (shared by two triangles): even contribution
  -- 3. Each fully-colored triangle contributes 1 door
  -- 4. Each {0,1}-only triangle contributes 2 doors (even)
  -- 5. Parity: #(fully-colored) ≡ #(boundary doors) ≡ 1 (mod 2)
  -- 6. Therefore #(fully-colored) ≥ 1
  sorry

-- ============================================================
-- SECTION V: Existence of Approximate Fixed Points (Application)
-- ============================================================

/-- From Sperner's lemma, approximate fixed points exist for continuous
    maps f : T → T on the 2D triangle. As n → ∞, the fully-colored
    triangles converge to an exact fixed point. This is the 2D case of
    the Brouwer Fixed Point Theorem.

    The PPAD-completeness result (Chen-Deng 2009) shows that finding
    such a fully-colored triangle (equivalently, an approximate fixed
    point) is PPAD-complete, even for this 2D case. -/
theorem approximate_fixed_point_2d
    {f : ℝ × ℝ → ℝ × ℝ}
    (hcont : Continuous f)
    (hrange : ∀ p, p.1 ≥ 0 → p.2 ≥ 0 → p.1 + p.2 ≤ 1 →
      (f p).1 ≥ 0 ∧ (f p).2 ≥ 0 ∧ (f p).1 + (f p).2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ × ℝ, p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ p.1 + p.2 ≤ 1 ∧
      dist p (f p) < ε := by
  -- Choose n large enough that 1/n < ε
  -- Apply sperner_2d to get a fully-colored triangle
  -- The center of that triangle is an approximate fixed point
  sorry

end Sperner2D
