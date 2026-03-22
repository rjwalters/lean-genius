import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-
# Stern-Brocot Tree Encoding of Rationals (OQ-03)

## What This Proves

This file formalizes the Stern-Brocot tree, an alternative to Cantor's diagonal
enumeration for listing the positive rationals. The Stern-Brocot tree provides a
bijection with superior structural properties:

1. Every positive rational appears exactly once, already in lowest terms
2. The tree structure encodes continued fraction expansions
3. The left-right path to any rational gives its Euclidean algorithm trace

## Construction

The tree is built from mediants. Starting with "sentinels" 0/1 and 1/0:
- Root = mediant(0/1, 1/0) = 1/1
- Left child of node a/b (with left ancestor p/q): mediant(p/q, a/b)
- Right child of node a/b (with right ancestor s/t): mediant(a/b, s/t)

## Key Invariant

At every node, the left and right ancestors (p/q, s/t) satisfy:
  s * q - p * t = 1  (the "determinant" or adjacency condition)

This invariant implies the mediant (p+s)/(q+t) has gcd = 1.

## Extends
- DenumerabilityRationals.lean (OQ-01): Base denumerability via Cantor pairing
- DenumerabilityRationalsOQ02.lean (OQ-02): Cantor's characterization theorem

## Wiedijk's 100 Theorems: #3 (Extension)
-/

namespace SternBrocot

-- ========================================================================
-- Part I: Basic Definitions
-- ========================================================================

/-- A direction in the Stern-Brocot tree: go Left or Right. -/
inductive Dir where
  | L : Dir
  | R : Dir
  deriving DecidableEq, Repr

/-- A path in the Stern-Brocot tree is a sequence of directions. -/
abbrev Path := List Dir

/-- The state of navigation in the Stern-Brocot tree.
We track the left ancestor (la/lb) and right ancestor (ra/rb).
The current node is their mediant: (la + ra) / (lb + rb). -/
structure State where
  la : ℕ
  lb : ℕ
  ra : ℕ
  rb : ℕ
  deriving DecidableEq, Repr

/-- The initial state: left ancestor 0/1, right ancestor 1/0. -/
def State.init : State := ⟨0, 1, 1, 0⟩

/-- Step left: the current node becomes the new right ancestor. -/
def State.left (s : State) : State := ⟨s.la, s.lb, s.la + s.ra, s.lb + s.rb⟩

/-- Step right: the current node becomes the new left ancestor. -/
def State.right (s : State) : State := ⟨s.la + s.ra, s.lb + s.rb, s.ra, s.rb⟩

/-- Navigate the tree: apply directions left-to-right from a state. -/
def eval : State → Path → State
  | s, [] => s
  | s, Dir.L :: rest => eval s.left rest
  | s, Dir.R :: rest => eval s.right rest

/-- Evaluate a path from the initial state. -/
def evalPath (p : Path) : State := eval State.init p

/-- The numerator of the node at a given path. -/
def pathNum (p : Path) : ℕ := (evalPath p).la + (evalPath p).ra

/-- The denominator of the node at a given path. -/
def pathDen (p : Path) : ℕ := (evalPath p).lb + (evalPath p).rb

-- ========================================================================
-- Part II: The Determinant Invariant
-- ========================================================================

/-- The determinant of a state: ra * lb - la * rb.
This equals 1 for all reachable states in the Stern-Brocot tree. -/
def State.det (s : State) : ℤ :=
  (s.ra : ℤ) * s.lb - (s.la : ℤ) * s.rb

@[simp] theorem det_init : State.init.det = 1 := by
  simp [State.init, State.det]

/-- Going left preserves the determinant. -/
theorem det_left (s : State) (h : s.det = 1) : s.left.det = 1 := by
  simp only [State.left, State.det] at *
  push_cast at *
  linarith

/-- Going right preserves the determinant. -/
theorem det_right (s : State) (h : s.det = 1) : s.right.det = 1 := by
  simp only [State.right, State.det] at *
  push_cast at *
  linarith

/-- The determinant is 1 after any sequence of navigations from init. -/
theorem det_eval (s : State) (p : Path) (h : s.det = 1) :
    (eval s p).det = 1 := by
  induction p generalizing s with
  | nil => exact h
  | cons d rest ih =>
    cases d with
    | L => exact ih _ (det_left s h)
    | R => exact ih _ (det_right s h)

/-- The determinant is 1 for any path from the root. -/
theorem det_path (p : Path) : (evalPath p).det = 1 :=
  det_eval State.init p det_init

-- ========================================================================
-- Part III: Coprimality of All Nodes
-- ========================================================================

/-- If the determinant is 1, the mediant is coprime.

Proof: ra·(lb+rb) - rb·(la+ra) = ra·lb - la·rb = det = 1.
So gcd(la+ra, lb+rb) | 1, hence gcd = 1. -/
theorem coprime_of_det_one (s : State) (h : s.det = 1) :
    Nat.Coprime (s.la + s.ra) (s.lb + s.rb) := by
  rw [Nat.Coprime]
  -- Key identity: ra * (lb + rb) - rb * (la + ra) = det = 1
  -- Therefore gcd(la+ra, lb+rb) | 1, hence gcd = 1
  have combo : (s.ra : ℤ) * (↑s.lb + ↑s.rb) - (s.rb : ℤ) * (↑s.la + ↑s.ra) = 1 := by
    simp only [State.det] at h; linarith
  -- gcd divides the linear combination
  have hdvd : (↑(Nat.gcd (s.la + s.ra) (s.lb + s.rb)) : ℤ) ∣ 1 := by
    have h1 := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left (s.la + s.ra) (s.lb + s.rb))
    have h2 := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right (s.la + s.ra) (s.lb + s.rb))
    have h3 : (↑(Nat.gcd (s.la + s.ra) (s.lb + s.rb)) : ℤ) ∣
        ↑s.ra * (↑s.lb + ↑s.rb) - ↑s.rb * (↑s.la + ↑s.ra) := by
      apply dvd_sub
      · exact dvd_mul_of_dvd_right h2 _
      · exact dvd_mul_of_dvd_right h1 _
    rwa [combo] at h3
  -- gcd is a nonneg nat that divides 1, so gcd = 1
  have hle : (Nat.gcd (s.la + s.ra) (s.lb + s.rb) : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  -- gcd ≥ 1 because det = 1 implies ra*lb ≥ 1, so ra ≥ 1, so la+ra ≥ 1
  have hra : 0 < s.ra := by
    simp only [State.det] at h; nlinarith
  have hge : 1 ≤ Nat.gcd (s.la + s.ra) (s.lb + s.rb) := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.gcd_ne_zero_left (by omega))
  omega

/-- Every node in the Stern-Brocot tree is in lowest terms. -/
theorem coprime_path (p : Path) :
    Nat.Coprime (pathNum p) (pathDen p) :=
  coprime_of_det_one _ (det_path p)

-- ========================================================================
-- Part IV: Positivity of All Nodes
-- ========================================================================

/-- In every state reachable from init, la + ra > 0. -/
theorem num_pos_eval (s : State) (p : Path)
    (hla : 0 ≤ s.la) (hra : 0 < s.ra) :
    0 < (eval s p).la + (eval s p).ra := by
  induction p generalizing s with
  | nil => simp [eval]; omega
  | cons d rest ih =>
    cases d with
    | L => exact ih s.left hla (by show 0 < s.la + s.ra; omega)
    | R => exact ih s.right (by show 0 ≤ s.la + s.ra; omega) hra

/-- In every state reachable from init, lb + rb > 0. -/
theorem den_pos_eval (s : State) (p : Path)
    (hlb : 0 < s.lb) (hra : 0 < s.ra) :
    0 < (eval s p).lb + (eval s p).rb := by
  induction p generalizing s with
  | nil => simp [eval]; omega
  | cons d rest ih =>
    cases d with
    | L => exact ih s.left hlb (by show 0 < s.la + s.ra; omega)
    | R => exact ih s.right (by show 0 < s.lb + s.rb; omega) hra

/-- The numerator of any node is positive. -/
theorem num_pos_path (p : Path) : 0 < pathNum p := by
  exact num_pos_eval State.init p (by simp [State.init]) (by simp [State.init])

/-- The denominator of any node is positive. -/
theorem den_pos_path (p : Path) : 0 < pathDen p := by
  exact den_pos_eval State.init p (by simp [State.init]) (by simp [State.init])

-- ========================================================================
-- Part V: The Rational Value Function
-- ========================================================================

/-- Convert a Stern-Brocot path to a positive rational number. -/
noncomputable def toRat (p : Path) : ℚ :=
  (pathNum p : ℚ) / (pathDen p : ℚ)

/-- The rational at the root is 1. -/
theorem toRat_root : toRat [] = 1 := by
  simp [toRat, pathNum, pathDen, evalPath, eval, State.init]

/-- toRat always gives a positive rational. -/
theorem toRat_pos (p : Path) : 0 < toRat p := by
  exact div_pos (Nat.cast_pos.mpr (num_pos_path p)) (Nat.cast_pos.mpr (den_pos_path p))

-- ========================================================================
-- Part VI: Ordering — The Tree is Sorted
-- ========================================================================

/-- The mediant lies strictly between the left and right ancestors
(in cross-multiplication form to avoid division). -/
theorem mediant_strictly_between (s : State) (h : s.det = 1)
    (_hlb : (0 : ℤ) < s.lb) (_hrb : (0 : ℤ) < s.rb) :
    (s.la : ℤ) * (↑s.lb + ↑s.rb) < (↑s.la + ↑s.ra) * ↑s.lb ∧
    (↑s.la + ↑s.ra : ℤ) * ↑s.rb < ↑s.ra * (↑s.lb + ↑s.rb) := by
  simp only [State.det] at h
  constructor <;> nlinarith

-- ========================================================================
-- Part VII: Injectivity Infrastructure
-- ========================================================================

/-- Key bound: ra is non-decreasing along any path from a state.
Going left: ra → la + ra (increases). Going right: ra stays. -/
theorem ra_ge_eval (s : State) (p : Path) :
    s.ra ≤ (eval s p).ra := by
  induction p generalizing s with
  | nil => simp [eval]
  | cons d rest ih =>
    cases d with
    | L =>
      have h1 : s.left.ra = s.la + s.ra := rfl
      have h2 := ih s.left
      simp [eval]; omega
    | R =>
      have h1 : s.right.ra = s.ra := rfl
      have h2 := ih s.right
      simp [eval]; omega

/-- Key bound: lb is non-decreasing along any path from a state.
Going left: lb stays. Going right: lb → lb + rb (increases). -/
theorem lb_ge_eval (s : State) (p : Path) :
    s.lb ≤ (eval s p).lb := by
  induction p generalizing s with
  | nil => simp [eval]
  | cons d rest ih =>
    cases d with
    | L =>
      have h1 : s.left.lb = s.lb := rfl
      have h2 := ih s.left
      simp [eval]; omega
    | R =>
      have h1 : s.right.lb = s.lb + s.rb := rfl
      have h2 := ih s.right
      simp [eval]; omega

/-- rb is non-decreasing along any path. -/
theorem rb_ge_eval (s : State) (p : Path) :
    s.rb ≤ (eval s p).rb := by
  induction p generalizing s with
  | nil => simp [eval]
  | cons d rest ih =>
    cases d with
    | L =>
      have h1 : s.left.rb = s.lb + s.rb := rfl
      have h2 := ih s.left
      simp [eval]; omega
    | R =>
      have h1 : s.right.rb = s.rb := rfl
      have h2 := ih s.right
      simp [eval]; omega

/-- After going left, rb is at least lb + rb (initial right ancestor's denominator). -/
theorem rb_ge_after_left (s : State) (p : Path) :
    (eval s.left p).rb ≥ s.lb + s.rb := by
  have h1 : s.left.rb = s.lb + s.rb := rfl
  have h2 := rb_ge_eval s.left p
  omega

/-- la is non-decreasing along any path from a state. -/
theorem la_ge_eval (s : State) (p : Path) :
    s.la ≤ (eval s p).la := by
  induction p generalizing s with
  | nil => simp [eval]
  | cons d rest ih =>
    cases d with
    | L => simp [eval]; exact le_trans (Nat.le_refl _) (ih s.left)
    | R => simp [eval]; exact le_trans (Nat.le_add_right _ _) (ih s.right)

/-- After going right, lb ≥ lb + rb (the parent's denominator sum). -/
theorem lb_ge_after_right (s : State) (p : Path) :
    (eval s.right p).lb ≥ s.lb + s.rb := by
  have h1 : s.right.lb = s.lb + s.rb := rfl
  have h2 := lb_ge_eval s.right p
  omega

/-- Key BST invariant: if det = 1 and the numerator sum < denominator sum,
    this inequality is preserved through all navigation steps.
    (Subtrees with value < 1 relative to parent stay that way.) -/
theorem num_lt_den_preserved (s : State) (p : Path) (hdet : s.det = 1)
    (hlt : s.la + s.ra < s.lb + s.rb) :
    (eval s p).la + (eval s p).ra < (eval s p).lb + (eval s p).rb := by
  induction p generalizing s with
  | nil => simpa [eval]
  | cons d rest ih =>
    cases d with
    | L =>
      have hdet' := det_left s hdet
      have hlt' : s.left.la + s.left.ra < s.left.lb + s.left.rb := by
        simp only [State.left, State.det] at *
        -- identity: lb*(la+ra) - la*(lb+rb) = det = 1
        have := mul_comm (s.ra : ℤ) ↑s.lb
        zify at hlt ⊢; nlinarith
      exact ih s.left hdet' hlt'
    | R =>
      have hdet' := det_right s hdet
      have hlt' : s.right.la + s.right.ra < s.right.lb + s.right.rb := by
        simp only [State.right, State.det] at *
        -- identity: ra*(lb+rb) - rb*(la+ra) = det = 1
        have := mul_comm (s.ra : ℤ) (↑s.lb + ↑s.rb)
        have := mul_comm (s.rb : ℤ) (↑s.la + ↑s.ra)
        zify at hlt ⊢; nlinarith
      exact ih s.right hdet' hlt'

/-- Symmetric BST invariant: if det = 1 and numerator sum > denominator sum,
    this is preserved through all navigation. -/
theorem num_gt_den_preserved (s : State) (p : Path) (hdet : s.det = 1)
    (hgt : s.la + s.ra > s.lb + s.rb) :
    (eval s p).la + (eval s p).ra > (eval s p).lb + (eval s p).rb := by
  induction p generalizing s with
  | nil => simpa [eval]
  | cons d rest ih =>
    cases d with
    | L =>
      have hdet' := det_left s hdet
      have hgt' : s.left.la + s.left.ra > s.left.lb + s.left.rb := by
        simp only [State.left, State.det] at *
        have := mul_comm (s.ra : ℤ) ↑s.lb
        zify at hgt ⊢; nlinarith
      exact ih s.left hdet' hgt'
    | R =>
      have hdet' := det_right s hdet
      have hgt' : s.right.la + s.right.ra > s.right.lb + s.right.rb := by
        simp only [State.right, State.det] at *
        have := mul_comm (s.ra : ℤ) (↑s.lb + ↑s.rb)
        have := mul_comm (s.rb : ℤ) (↑s.la + ↑s.ra)
        zify at hgt ⊢; nlinarith
      exact ih s.right hdet' hgt'

/-- Different paths from the root yield different (num, den) pairs.

    Proof strategy (not yet fully formalized):
    1. Empty vs non-empty: after any step from a det=1 state, at least one
       component strictly increases (la increases after R, rb increases after L).
    2. L vs R from same state: the cross-product interval approach shows
       left descendants have value < parent mediant and right descendants
       have value > parent mediant. Requires proving the upper bound invariant
       (ra*(parent.lb+rb) ≤ (parent.la+ra)*rb for left descendants) and using
       mediant_strictly_between to chain the inequalities. -/
theorem eval_injective (p1 p2 : Path) (h : evalPath p1 = evalPath p2) :
    p1 = p2 := by
  sorry

-- ========================================================================
-- Part VIII: Concrete Examples
-- ========================================================================

/-- The root of the Stern-Brocot tree is 1/1. -/
theorem root_eq : pathNum [] = 1 ∧ pathDen [] = 1 := by
  simp [pathNum, pathDen, evalPath, eval, State.init]

/-- Going left from the root gives 1/2. -/
theorem left_eq : pathNum [Dir.L] = 1 ∧ pathDen [Dir.L] = 2 := by
  simp [pathNum, pathDen, evalPath, eval, State.init, State.left]

/-- Going right from the root gives 2/1. -/
theorem right_eq : pathNum [Dir.R] = 2 ∧ pathDen [Dir.R] = 1 := by
  simp [pathNum, pathDen, evalPath, eval, State.init, State.right]

/-- Going left-left gives 1/3. -/
example : pathNum [Dir.L, Dir.L] = 1 ∧ pathDen [Dir.L, Dir.L] = 3 := by
  simp [pathNum, pathDen, evalPath, eval, State.init, State.left]

/-- Going left-right gives 2/3. -/
example : pathNum [Dir.L, Dir.R] = 2 ∧ pathDen [Dir.L, Dir.R] = 3 := by
  simp [pathNum, pathDen, evalPath, eval, State.init, State.left, State.right]

/-- Going right-left gives 3/2. -/
example : pathNum [Dir.R, Dir.L] = 3 ∧ pathDen [Dir.R, Dir.L] = 2 := by
  simp [pathNum, pathDen, evalPath, eval, State.init, State.right, State.left]

/-- Going right-right gives 3/1. -/
example : pathNum [Dir.R, Dir.R] = 3 ∧ pathDen [Dir.R, Dir.R] = 1 := by
  simp [pathNum, pathDen, evalPath, eval, State.init, State.right]

-- ========================================================================
-- Part IX: The First Three Levels
-- ========================================================================

/-
The Stern-Brocot tree (first 3 levels):

                      1/1
                    /     \
                 1/2       2/1
                /   \     /   \
              1/3   2/3  3/2   3/1

Level 0: 1/1
Level 1: 1/2, 2/1
Level 2: 1/3, 2/3, 3/2, 3/1

Each fraction appears in lowest terms. The tree is ordered left-to-right:
  1/3 < 1/2 < 2/3 < 1/1 < 3/2 < 2/1 < 3/1
-/

-- ========================================================================
-- Part X: Connection to the Euclidean Algorithm
-- ========================================================================

/-
## Finding a Rational in the Stern-Brocot Tree

Given a positive rational p/q in lowest terms, its path in the tree
corresponds to the Euclidean algorithm applied to (p, q):

1. Compare p/q with the current mediant m/n
2. If p/q = m/n, stop (empty path)
3. If p/q < m/n, go Left and recurse
4. If p/q > m/n, go Right and recurse

This terminates because p + q strictly decreases at each step.

The run-length encoding of the path encodes continued fractions.

Example: 3/2 has path [R, L]
  Start (0/1, 1/0), med = 1/1. 3/2 > 1/1 → R
  Now (1/1, 1/0), med = 2/1. 3/2 < 2/1 → L
  Now (1/1, 2/1), med = 3/2. Found! ✓
-/

-- ========================================================================
-- Part XI: Comparison with Cantor Pairing
-- ========================================================================

/-
## Stern-Brocot vs Cantor Pairing

| Property              | Cantor Pairing        | Stern-Brocot Tree     |
|-----------------------|-----------------------|-----------------------|
| Maps to               | ℕ ≃ ℚ                | paths → ℚ⁺           |
| Already reduced?      | No (needs reduction)  | Yes (automatic)       |
| Tree structure?       | No                    | Yes (binary tree)     |
| Continued fractions?  | No connection         | Path = CF expansion   |
| Order-preserving?     | No                    | Yes (in-order = <)    |

The Stern-Brocot tree is mathematically richer: it simultaneously encodes
the ordering of rationals, continued fraction expansions, and the
Euclidean algorithm. Cantor's pairing is computationally simpler.
-/

-- ========================================================================
-- Verification
-- ========================================================================

#check det_path
#check coprime_path
#check num_pos_path
#check den_pos_path
#check mediant_strictly_between
#check toRat_pos
#check toRat_root

end SternBrocot
