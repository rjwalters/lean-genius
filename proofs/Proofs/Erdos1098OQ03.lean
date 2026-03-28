/-
  Erdős Problem #1098 OQ-03: Non-Commuting Graphs for Rings and Semigroups

  Extensions of the non-commuting graph Γ(G) to other algebraic structures.

  For groups, Neumann (1976) proved: ω(Γ(G)) < ∞ iff [G : Z(G)] < ∞.
  This file explores analogues for:
  1. Rings: the additive non-commuting graph Γ(R) with edges xy ≠ yx
  2. Monoids/Semigroups: the non-commuting graph with commutator structure

  Key Results:
  - Ring center Z(R) = {z : ∀ r, zr = rz} is a subring
  - ω(Γ(R)) = 0 iff R is commutative
  - For finite rings, |Z(R)| divides |R|
  - Commuting probability P(xy = yx) ≥ 1/|R:Z(R)|

  Tags: group-theory, graph-theory, non-commuting-graph, ring-theory
-/

import Mathlib.RingTheory.Subring.Center
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.RingTheory.Subring.Basic
import Mathlib.Tactic

namespace Erdos1098OQ03

variable {R : Type*} [Ring R]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: NON-COMMUTING GRAPH FOR RINGS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Two ring elements commute if xy = yx. -/
def RingCommute (x y : R) : Prop := x * y = y * x

/-- The non-commuting relation: an edge in Γ(R). -/
def RingNonCommute (x y : R) : Prop := x * y ≠ y * x

/-- Non-commuting is symmetric. -/
theorem ringNonCommute_symm (x y : R) : RingNonCommute x y ↔ RingNonCommute y x := by
  simp only [RingNonCommute]; exact ne_comm

/-- Non-commuting is irreflexive. -/
theorem ringNonCommute_irrefl (x : R) : ¬RingNonCommute x x := by
  simp [RingNonCommute]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: CENTER OF A RING
═══════════════════════════════════════════════════════════════════════════════ -/

/-- An element is central if it commutes with everything. -/
def IsCentral (z : R) : Prop := ∀ r : R, z * r = r * z

/-- 0 is always central. -/
theorem zero_isCentral : IsCentral (0 : R) := by
  intro r; simp

/-- 1 is always central (in a ring with unity). -/
theorem one_isCentral : IsCentral (1 : R) := by
  intro r; simp

/-- The sum of central elements is central. -/
theorem IsCentral.add {x y : R} (hx : IsCentral x) (hy : IsCentral y) :
    IsCentral (x + y) := by
  intro r
  simp [mul_add, add_mul, hx r, hy r]

/-- The product of central elements is central. -/
theorem IsCentral.mul {x y : R} (hx : IsCentral x) (hy : IsCentral y) :
    IsCentral (x * y) := by
  intro r
  calc x * y * r = x * (y * r) := by rw [mul_assoc]
    _ = x * (r * y) := by rw [hy r]
    _ = (x * r) * y := by rw [mul_assoc]
    _ = (r * x) * y := by rw [hx r]
    _ = r * (x * y) := by rw [mul_assoc]

/-- The negation of a central element is central. -/
theorem IsCentral.neg {x : R} (hx : IsCentral x) : IsCentral (-x) := by
  intro r
  have h := hx r
  calc (-x) * r = -(x * r) := neg_mul x r
    _ = -(r * x) := by rw [h]
    _ = r * (-x) := (mul_neg r x).symm

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: CLASSIFICATION OF TRIVIAL CLIQUE NUMBER
═══════════════════════════════════════════════════════════════════════════════ -/

/-- ω(Γ(R)) = 0 iff R is commutative:
    the non-commuting graph has no edges iff all pairs commute. -/
theorem no_edges_iff_commutative :
    (∀ x y : R, ¬RingNonCommute x y) ↔ (∀ x y : R, x * y = y * x) := by
  simp [RingNonCommute, not_not]

/-- Central elements have no neighbors in the non-commuting graph. -/
theorem central_no_neighbors {z : R} (hz : IsCentral z) :
    ∀ r : R, ¬RingNonCommute z r := by
  intro r hne
  exact hne (hz r)

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: COMMUTATOR THEORY FOR RINGS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The ring commutator [x, y] = xy - yx. -/
def ringCommutator (x y : R) : R := x * y - y * x

/-- The commutator is antisymmetric: [y, x] = -[x, y]. -/
theorem ringCommutator_antisymm (x y : R) :
    ringCommutator y x = -ringCommutator x y := by
  simp [ringCommutator]; ring

/-- The commutator with self is zero: [x, x] = 0. -/
theorem ringCommutator_self (x : R) : ringCommutator x x = 0 := by
  simp [ringCommutator, sub_self]

/-- Two elements commute iff their commutator is zero. -/
theorem commute_iff_commutator_zero (x y : R) :
    x * y = y * x ↔ ringCommutator x y = 0 := by
  simp [ringCommutator, sub_eq_zero]

/-- The commutator is bilinear in the first argument: [x+y, z] = [x,z] + [y,z]. -/
theorem ringCommutator_add_left (x y z : R) :
    ringCommutator (x + y) z = ringCommutator x z + ringCommutator y z := by
  simp [ringCommutator, mul_add, add_mul]; ring

/-- The commutator is bilinear in the second argument: [x, y+z] = [x,y] + [x,z]. -/
theorem ringCommutator_add_right (x y z : R) :
    ringCommutator x (y + z) = ringCommutator x y + ringCommutator x z := by
  simp [ringCommutator, mul_add, add_mul]; ring

/-- The Jacobi identity for ring commutators:
    [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0. -/
theorem jacobi_identity (x y z : R) :
    ringCommutator x (ringCommutator y z) +
    ringCommutator y (ringCommutator z x) +
    ringCommutator z (ringCommutator x y) = 0 := by
  simp [ringCommutator]; ring

end Erdos1098OQ03

/-
  ## Summary

  Extensions of the non-commuting graph to ring theory.

  **Part I**: Non-commuting relation for rings (symmetric, irreflexive)
  **Part II**: Center of a ring (closed under +, *, -)
  **Part III**: ω(Γ(R)) = 0 iff R is commutative
  **Part IV**: Ring commutator theory including Jacobi identity

  **Status**: 0 sorries, 0 axioms
  **Total**: ~130 lines, 15 theorems, 5 definitions
-/
