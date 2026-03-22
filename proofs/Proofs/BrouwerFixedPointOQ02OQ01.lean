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

/-- The number of color transitions along the bottom edge.
    A "transition" at position i means the color at (i,0) differs from (i+1,0). -/
def bottomTransitions {n : ℕ} (c : Coloring n) : ℕ :=
  Finset.card (Finset.filter
    (fun i : Fin n => c (botVertex n ⟨i.val, by omega⟩) ≠ c (botVertex n ⟨i.val + 1, by omega⟩))
    Finset.univ)

/-- The number of transitions in a sequence modulo 2 equals
    the XOR of first and last values (telescoping in ZMod 2).
    If f(0) = 0 and f(n) = 1 (as ZMod 2 values), transitions are odd. -/
private theorem transitions_parity_aux :
    ∀ (n : ℕ) (f : Fin (n + 1) → ZMod 2),
    (Finset.card (Finset.filter (fun i : Fin n => f ⟨i.val, by omega⟩ ≠ f ⟨i.val + 1, by omega⟩)
      Finset.univ) : ZMod 2) = f ⟨n, by omega⟩ + f ⟨0, by omega⟩ := by
  -- Proof by induction on n.
  -- Base (n=0): Fin 0 = ∅, card = 0, RHS = f(0)+f(0) = 0 in ZMod 2.
  -- Step (n=m+1): Split filter into first m transitions + last transition.
  --   By IH: first m transitions ≡ f(m)+f(0) mod 2.
  --   Last: +1 if f(m)≠f(m+1), +0 otherwise.
  --   Total: f(m)+f(0) + (f(m)+f(m+1)) = f(m+1)+f(0) in ZMod 2 (f(m) cancels).
  sorry

/-- On the bottom edge (j=0), a Sperner coloring has an odd
    number of transitions (adjacent pairs with different colors).
    This is the 1D parity lemma applied to the bottom edge. -/
theorem bottom_transitions_odd {n : ℕ} (hn : 0 < n) (c : Coloring n)
    (hc : IsSperner hn c) : Odd (bottomTransitions c) := by
  obtain ⟨hv0, hv1, _, hbot, _, _⟩ := hc
  -- The bottom edge uses only colors 0 and 1 (Sperner condition).
  -- Going from color 0 to color 1 requires an odd number of transitions.
  -- We reduce to transitions_parity_aux via a ZMod 2 projection.
  sorry

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
