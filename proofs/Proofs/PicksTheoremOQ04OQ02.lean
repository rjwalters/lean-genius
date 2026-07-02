import Mathlib

/-
# Pick's Theorem OQ-04-OQ-02: Orientation and cyclic-rotation symmetry of the shoelace sum

## What This Proves

The signed shoelace (surveyor's) sum of a lattice polygon,

    S(v₀, …, v_{m-1}) = Σ_k (x_k · y_{k+1} − x_{k+1} · y_k)     (indices mod m),

carries the two structural symmetries that make "signed area" meaningful.  This
file gives a *fully verified, axiom-free* Lean proof of both, answering the
second open question left by `PicksTheoremOQ04` (the general shoelace / fan
bridge file):

1.  **Orientation reversal** (`shoelace_reverse`):
        S(reverse vs) = − S(vs).
    Traversing the boundary in the opposite direction flips the sign of the
    signed area.  This is the formal statement that the shoelace sum *orients*
    the polygon.

2.  **Cyclic-rotation invariance** (`shoelace_rotate_one`, `shoelace_rotl`,
    `shoelace_rotl_iterate`):
        S(rotate vs) = S(vs).
    Relabelling which vertex is "first" — a cyclic rotation of the vertex list —
    leaves the sum unchanged, because a closed polygon has no distinguished
    starting vertex.

## Method

Both results factor through a single clean device.  We introduce the **open
edge sum** `edgeSum` of a polyline (the sum of `cross` over consecutive pairs,
*without* the closing edge) and prove the bridge

    shoelaceAux first l = edgeSum (l ++ [first])                (`shoelaceAux_eq_edgeSum`)

so the closed shoelace loop is exactly the open edge sum of the list with its
starting vertex appended as the closing vertex.  Then:

* `edgeSum_snoc` : appending a vertex adds exactly one edge term;
* `edgeSum_reverse` : `edgeSum (reverse l) = − edgeSum l`, from the antisymmetry
  `cross a b = − cross b a` of the wedge product;
* rotation-by-one is a re-association of the same closed edge multiset.

Everything is `Int`-valued and decidable, so the closing examples reduce by
`decide`.

## Relation to the gallery
- `PicksTheoremOQ04.lean` — the general shoelace sum, fan-triangulation bridge,
  translation invariance, and the integrality bridge to Pick.  This file reuses
  its `cross` / `shoelace` primitives and answers its open question (2).
- `PicksTheorem.lean` — the base Pick relation `A = i + b/2 − 1`.

0 sorries, 0 axioms.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PicksTheoremOQ04OQ02

/-- A lattice point: a pair of integers. -/
abbrev Pt := ℤ × ℤ

-- ============================================================
-- PART 1: The wedge product and its antisymmetry
-- ============================================================

/-- The 2D wedge / cross product of two position vectors,
    `cross a b = x_a · y_b − y_a · x_b`.  This is the per-edge term of the
    shoelace sum. -/
def cross (a b : Pt) : ℤ := a.1 * b.2 - a.2 * b.1

@[simp] lemma cross_self (a : Pt) : cross a a = 0 := by unfold cross; ring

/-- The wedge product is antisymmetric: `cross a b = − cross b a`.  This single
    algebraic fact is what forces the sign flip under orientation reversal. -/
lemma cross_antisymm (a b : Pt) : cross a b = - cross b a := by unfold cross; ring

-- ============================================================
-- PART 2: The closed shoelace sum and the open edge sum
-- ============================================================

/-- `shoelaceAux first vs` sums `cross` over consecutive vertices of `vs`, then
    closes the loop with the edge from the last vertex of `vs` back to `first`. -/
def shoelaceAux (first : Pt) : List Pt → ℤ
  | [] => 0
  | [a] => cross a first
  | a :: b :: t => cross a b + shoelaceAux first (b :: t)

/-- The signed shoelace sum of a closed polygon given by its vertex list in
    cyclic order: `shoelace [v₀, …, v_{m-1}] = Σ_k cross(v_k, v_{k+1 mod m})`. -/
def shoelace : List Pt → ℤ
  | [] => 0
  | v0 :: rest => shoelaceAux v0 (v0 :: rest)

/-- The **open** edge sum of a polyline: the sum of `cross` over consecutive
    pairs, with *no* closing edge.  `edgeSum [a, b, c] = cross a b + cross b c`. -/
def edgeSum : List Pt → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: t => cross a b + edgeSum (b :: t)

-- ============================================================
-- PART 3: The bridge  shoelaceAux first l = edgeSum (l ++ [first])
-- ============================================================

/-- **Bridge.**  The closed shoelace chain based at `first` equals the open edge
    sum of the list with `first` appended as the closing vertex.  This is the
    single fact that lets us transport reversal and rotation results between the
    closed loop and the (much more flexible) open polyline. -/
lemma shoelaceAux_eq_edgeSum (first : Pt) (l : List Pt) :
    shoelaceAux first l = edgeSum (l ++ [first]) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simp [shoelaceAux, edgeSum]
    | cons b t' =>
      simp only [List.cons_append] at ih ⊢
      simp only [shoelaceAux, edgeSum]
      rw [ih]

/-- Specialisation of the bridge to the public `shoelace` entry point. -/
lemma shoelace_eq_edgeSum (v0 : Pt) (rest : List Pt) :
    shoelace (v0 :: rest) = edgeSum ((v0 :: rest) ++ [v0]) :=
  shoelaceAux_eq_edgeSum v0 (v0 :: rest)

-- ============================================================
-- PART 4: The snoc law for the open edge sum
-- ============================================================

/-- **Snoc law.**  Appending a vertex `x` after a polyline that currently ends in
    `y` adds exactly the single edge term `cross y x`. -/
lemma edgeSum_snoc (l : List Pt) (y x : Pt) :
    edgeSum (l ++ [y] ++ [x]) = edgeSum (l ++ [y]) + cross y x := by
  induction l with
  | nil => simp [edgeSum]
  | cons a t ih =>
    cases t with
    | nil => simp [edgeSum]
    | cons b t' =>
      simp only [List.cons_append] at ih ⊢
      simp only [edgeSum]
      rw [ih]; ring

-- ============================================================
-- PART 5: Orientation reversal  (edgeSum, then shoelace)
-- ============================================================

/-- **Reversal of the open edge sum.**  Reversing a polyline reverses every edge,
    and `cross` is antisymmetric, so the whole open edge sum negates. -/
lemma edgeSum_reverse (l : List Pt) : edgeSum l.reverse = - edgeSum l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      -- (a :: b :: t').reverse = ((b :: t').reverse) ++ [a] = (t'.reverse ++ [b]) ++ [a]
      rw [List.reverse_cons, List.reverse_cons, edgeSum_snoc t'.reverse b a,
        ← List.reverse_cons, ih]
      -- goal: - edgeSum (b :: t') + cross b a = - edgeSum (a :: b :: t')
      show - edgeSum (b :: t') + cross b a = - edgeSum (a :: b :: t')
      rw [show edgeSum (a :: b :: t') = cross a b + edgeSum (b :: t') from rfl,
        cross_antisymm b a]
      ring

/-- Auxiliary reversal identity keeping the base vertex `v0` fixed at the front:
    reversing only the *tail* negates the shoelace sum.  Proved by pulling the
    closed loop through `edgeSum_reverse`. -/
lemma shoelace_reverse_tail (v0 : Pt) (rest : List Pt) :
    shoelace (v0 :: rest.reverse) = - shoelace (v0 :: rest) := by
  rw [shoelace_eq_edgeSum, shoelace_eq_edgeSum, ← edgeSum_reverse]
  congr 1
  -- ((v0 :: rest) ++ [v0]).reverse = v0 :: (rest.reverse ++ [v0]) = (v0 :: rest.reverse) ++ [v0]
  simp [List.reverse_append]

-- ============================================================
-- PART 6: Cyclic rotation invariance
-- ============================================================

/-- **Rotation by one.**  Moving the first vertex to the back of the list leaves
    the shoelace sum unchanged: a closed polygon has no distinguished start. -/
theorem shoelace_rotate_one (v0 : Pt) (rest : List Pt) :
    shoelace (rest ++ [v0]) = shoelace (v0 :: rest) := by
  cases rest with
  | nil => rfl
  | cons r0 rest' =>
    have hL : shoelace ((r0 :: rest') ++ [v0])
        = edgeSum ((r0 :: rest') ++ [v0]) + cross v0 r0 := by
      have hbridge : shoelace ((r0 :: rest') ++ [v0])
          = edgeSum (((r0 :: rest') ++ [v0]) ++ [r0]) := by
        show shoelace (r0 :: (rest' ++ [v0]))
            = edgeSum ((r0 :: (rest' ++ [v0])) ++ [r0])
        exact shoelace_eq_edgeSum r0 (rest' ++ [v0])
      rw [hbridge, edgeSum_snoc (r0 :: rest') v0 r0]
    have hR : shoelace (v0 :: r0 :: rest')
        = cross v0 r0 + edgeSum ((r0 :: rest') ++ [v0]) := by
      rw [shoelace_eq_edgeSum]
      show edgeSum (v0 :: r0 :: (rest' ++ [v0]))
          = cross v0 r0 + edgeSum ((r0 :: rest') ++ [v0])
      rfl
    -- reassemble: LHS list `(r0 :: rest') ++ [v0]` is defeq to `r0 :: (rest' ++ [v0])`
    show shoelace ((r0 :: rest') ++ [v0]) = shoelace (v0 :: r0 :: rest')
    rw [hL, hR]; ring

/-- One step of cyclic rotation: move the first vertex to the back. -/
def rotl : List Pt → List Pt
  | [] => []
  | v0 :: rest => rest ++ [v0]

/-- Rotation invariance in terms of the explicit one-step rotation `rotl`. -/
theorem shoelace_rotl (vs : List Pt) : shoelace (rotl vs) = shoelace vs := by
  cases vs with
  | nil => rfl
  | cons v0 rest => exact shoelace_rotate_one v0 rest

/-- Rotation invariance under any number of one-step rotations: the shoelace sum
    is a genuine invariant of the cyclic vertex order. -/
theorem shoelace_rotl_iterate (n : ℕ) (vs : List Pt) :
    shoelace (rotl^[n] vs) = shoelace vs := by
  induction n generalizing vs with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, shoelace_rotl]

-- ============================================================
-- PART 7: Orientation reversal for the full polygon
-- ============================================================

/-- **Orientation reversal (headline result).**  Reversing the vertex order of a
    closed polygon negates its shoelace sum:  `S(reverse vs) = − S(vs)`.

    Combines the tail-reversal identity `shoelace_reverse_tail` with rotation
    invariance to move the fixed base vertex back into place. -/
theorem shoelace_reverse (vs : List Pt) : shoelace vs.reverse = - shoelace vs := by
  cases vs with
  | nil => rfl
  | cons v0 rest =>
    -- (v0 :: rest).reverse = rest.reverse ++ [v0], a rotation of v0 :: rest.reverse
    rw [List.reverse_cons, shoelace_rotate_one v0 rest.reverse]
    exact shoelace_reverse_tail v0 rest

-- ============================================================
-- PART 8: Concrete verification
-- ============================================================

/-- Unit right triangle, counter-clockwise: `S = 1`. -/
example : shoelace [(0, 0), (1, 0), (0, 1)] = 1 := by decide

/-- The same triangle reversed (clockwise): `S = −1`. -/
example : shoelace [(0, 1), (1, 0), (0, 0)] = -1 := by decide

/-- Reversal law on the concrete triangle. -/
example : shoelace ([(0, 0), (1, 0), (0, 1)] : List Pt).reverse
    = - shoelace [(0, 0), (1, 0), (0, 1)] := by decide

/-- Cyclic rotation of the triangle keeps `S = 1`. -/
example : shoelace [(1, 0), (0, 1), (0, 0)] = 1 := by decide

/-- Rotation law on the concrete triangle, one step. -/
example :
    shoelace ([(1, 0), (0, 1)] ++ [((0, 0) : Pt)]) = shoelace [(0, 0), (1, 0), (0, 1)] := by
  decide

/-- `3 × 4` rectangle, counter-clockwise: `S = 24`; reversed: `S = −24`. -/
example : shoelace [(0, 0), (3, 0), (3, 4), (0, 4)] = 24 := by decide
example : shoelace ([(0, 0), (3, 0), (3, 4), (0, 4)] : List Pt).reverse = -24 := by decide

end PicksTheoremOQ04OQ02
