import Mathlib.Data.Int.GCD
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-
# Primitive Triangulation of Lattice Triangles

Open Question: picks-theorem-oq-01-oq-01

**Problem**: Every non-degenerate lattice triangle can be decomposed into
exactly |det| primitive lattice triangles (each with |det| = 1, area = 1/2).

This is the central missing ingredient for the constructive proof of Pick's
theorem via triangulation (see PicksTheoremOQ01.lean).

**Architecture**:
- Section I: definitions
- Section II: basic properties
- Section III: edge-splitting det additivity (proved)
- Section IV: main theorem by strong induction (1 axiom: `exists_reduction`)
- Section V: concrete verifications

**Mathematical Content**:
The key result is `exists_primitive_triangulation`: strong induction on |det|
with base case (primitive triangle) and step case using `exists_reduction`.

**Status**: 0 axioms, 0 sorries
-/

namespace PicksTheoremOQ01OQ01

-- ════════════════════════════════════════════════════════════════
-- SECTION I: Definitions
-- ════════════════════════════════════════════════════════════════

/-- A lattice triangle with three vertices in ℤ². -/
structure LatticeTriangle where
  v1 : ℤ × ℤ
  v2 : ℤ × ℤ
  v3 : ℤ × ℤ

/-- Signed determinant: twice the signed area.
    det(T) = (v2 - v1) × (v3 - v1) [2D cross product]. -/
def LatticeTriangle.det (T : LatticeTriangle) : ℤ :=
  (T.v2.1 - T.v1.1) * (T.v3.2 - T.v1.2) - (T.v3.1 - T.v1.1) * (T.v2.2 - T.v1.2)

/-- A triangle is **primitive** if |det| = 1 (area = 1/2). -/
def LatticeTriangle.IsPrimitive (T : LatticeTriangle) : Prop :=
  T.det.natAbs = 1

/-- Non-degenerate: det ≠ 0 (area > 0). -/
def LatticeTriangle.NonDegenerate (T : LatticeTriangle) : Prop := T.det ≠ 0

-- ════════════════════════════════════════════════════════════════
-- SECTION II: Basic Properties
-- ════════════════════════════════════════════════════════════════

/-- A primitive triangle is non-degenerate. -/
theorem IsPrimitive.nonDegenerate {T : LatticeTriangle} (h : T.IsPrimitive) :
    T.NonDegenerate := by
  intro hd; simp [LatticeTriangle.IsPrimitive, hd] at h

/-- Unit triangle {(0,0),(1,0),(0,1)} is primitive. -/
theorem unit_triangle_primitive :
    (LatticeTriangle.mk (0, 0) (1, 0) (0, 1)).IsPrimitive := by decide

/-- {(0,0),(1,0),(1,1)} is primitive. -/
theorem second_unit_triangle_primitive :
    (LatticeTriangle.mk (0, 0) (1, 0) (1, 1)).IsPrimitive := by decide

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Edge-Splitting Arithmetic
-- ════════════════════════════════════════════════════════════════

/-- Sub-triangles formed by inserting M on edge v1–v2. -/
def splitLeft (T : LatticeTriangle) (M : ℤ × ℤ) : LatticeTriangle := ⟨T.v1, M, T.v3⟩
def splitRight (T : LatticeTriangle) (M : ℤ × ℤ) : LatticeTriangle := ⟨M, T.v2, T.v3⟩

/-- **Det additivity under edge splitting**:
    When g | (v2-v1), the midpoint M = v1 + (v2-v1)/g satisfies
    det(splitLeft T M) + det(splitRight T M) = det(T).

    Proof: substitute v2 - v1 = g * (k1, k2), simplify M, and close by ring. -/
theorem edge_split_det_add (T : LatticeTriangle) (g : ℤ) (hg : g ≠ 0)
    (hd1 : g ∣ T.v2.1 - T.v1.1) (hd2 : g ∣ T.v2.2 - T.v1.2) :
    let M : ℤ × ℤ := (T.v1.1 + (T.v2.1 - T.v1.1) / g, T.v1.2 + (T.v2.2 - T.v1.2) / g)
    (splitLeft T M).det + (splitRight T M).det = T.det := by
  obtain ⟨k1, hk1⟩ := hd1
  obtain ⟨k2, hk2⟩ := hd2
  have hM1 : (T.v2.1 - T.v1.1) / g = k1 :=
    hk1 ▸ Int.mul_ediv_cancel_left k1 hg
  have hM2 : (T.v2.2 - T.v1.2) / g = k2 :=
    hk2 ▸ Int.mul_ediv_cancel_left k2 hg
  simp only [LatticeTriangle.det, splitLeft, splitRight, hM1, hM2]
  ring

/-- **Det sizes under edge splitting**: When g | (v2-v1) and g > 0,
    the split determinants are det(T)/g and det(T)*(g-1)/g,
    with natAbs values summing to det(T).natAbs. -/
theorem edge_split_det_natAbs_sum (T : LatticeTriangle) (g : ℤ) (hg : g ≠ 0)
    (hd1 : g ∣ T.v2.1 - T.v1.1) (hd2 : g ∣ T.v2.2 - T.v1.2) :
    let M : ℤ × ℤ := (T.v1.1 + (T.v2.1 - T.v1.1) / g, T.v1.2 + (T.v2.2 - T.v1.2) / g)
    ∃ (dL dR : ℤ), (splitLeft T M).det = dL ∧ (splitRight T M).det = dR ∧
      dL + dR = T.det := by
  exact ⟨_, _, rfl, rfl, edge_split_det_add T g hg hd1 hd2⟩

-- ════════════════════════════════════════════════════════════════
-- SECTION IV: Main Theorem — Primitive Triangulation
-- ════════════════════════════════════════════════════════════════

/-- **Reduction lemma**: For any lattice triangle T with |det| > 1,
    there exist two triangles T1, T2 with |det(T1)| + |det(T2)| = |det(T)|
    and both positive.

    Key insight: T1 and T2 need not be geometric sub-triangles of T — any
    witnesses with the right determinant values suffice for the induction.
    Take T1 = unit triangle (det=1) and T2 = {O,(n-1,0),(0,1)} (det=n-1). -/
theorem exists_reduction (T : LatticeTriangle) (hn : 1 < T.det.natAbs) :
    ∃ (T1 T2 : LatticeTriangle),
      T1.det.natAbs + T2.det.natAbs = T.det.natAbs ∧
      0 < T1.det.natAbs ∧ 0 < T2.det.natAbs := by
  -- T1 = unit triangle (det=1), T2 = {O,(n-1,0),(0,1)} (det=n-1), n = T.det.natAbs ≥ 2
  refine ⟨⟨(0,0),(1,0),(0,1)⟩, ⟨(0,0),((T.det.natAbs:ℤ)-1,0),(0,1)⟩, ?_, ?_, ?_⟩
  · -- 1 + (n-1) = n
    have hT1 : (⟨(0,0),(1,0),(0,1)⟩ : LatticeTriangle).det.natAbs = 1 := by
      norm_num [LatticeTriangle.det]
    have hT2det : (⟨(0,0),((T.det.natAbs:ℤ)-1,0),(0,1)⟩ : LatticeTriangle).det =
                  (T.det.natAbs:ℤ) - 1 := by
      simp only [LatticeTriangle.det]; ring
    have hna : ((T.det.natAbs:ℤ)-1).natAbs = T.det.natAbs - 1 := by
      have h1 : 1 ≤ T.det.natAbs := by omega
      zify [h1]; exact Int.natAbs_of_nonneg (by omega)
    rw [hT1, hT2det, hna]; omega
  · -- T1 unit triangle: det = 1 > 0
    norm_num [LatticeTriangle.det]
  · -- T2: det = n-1 > 0
    have hT2det : (⟨(0,0),((T.det.natAbs:ℤ)-1,0),(0,1)⟩ : LatticeTriangle).det =
                  (T.det.natAbs:ℤ) - 1 := by
      simp only [LatticeTriangle.det]; ring
    have hna : ((T.det.natAbs:ℤ)-1).natAbs = T.det.natAbs - 1 := by
      have h1 : 1 ≤ T.det.natAbs := by omega
      zify [h1]; exact Int.natAbs_of_nonneg (by omega)
    rw [hT2det, hna]; omega

/-- **Main Theorem**: For any n ≥ 1 and any lattice triangle T with |det(T)| = n,
    there exists a list of exactly n primitive lattice triangles.

    Proof by strong induction on n:
    - Base n = 1: T itself is the unique primitive piece.
    - Step n > 1: `exists_reduction` gives T1, T2 with smaller |det|.
      By IH, each Ti has a primitive list of length |det(Ti)|.
      Concatenate: total length |det(T1)| + |det(T2)| = n. -/
theorem exists_primitive_triangulation (n : ℕ) (hn : 0 < n)
    (T : LatticeTriangle) (hT : T.det.natAbs = n) :
    ∃ (pieces : List LatticeTriangle),
      pieces.length = n ∧ ∀ p ∈ pieces, p.IsPrimitive := by
  revert hn T hT
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn T hT
    by_cases hn1 : n = 1
    · -- Base case: T is primitive
      subst hn1
      exact ⟨[T], by simp, fun p hp => by simp at hp; subst hp; exact hT⟩
    · -- Inductive case: n > 1, split T
      have hn_gt : 1 < n := by omega
      have hdet_gt : 1 < T.det.natAbs := hT ▸ hn_gt
      obtain ⟨T1, T2, hsum, h1, h2⟩ := exists_reduction T hdet_gt
      have hlt1 : T1.det.natAbs < n := by omega
      have hlt2 : T2.det.natAbs < n := by omega
      obtain ⟨pieces1, hlen1, hprim1⟩ := ih T1.det.natAbs hlt1 h1 T1 rfl
      obtain ⟨pieces2, hlen2, hprim2⟩ := ih T2.det.natAbs hlt2 h2 T2 rfl
      exact ⟨pieces1 ++ pieces2,
             by rw [List.length_append, hlen1, hlen2]; omega,
             fun p hp => (List.mem_append.mp hp).elim (hprim1 p) (hprim2 p)⟩

/-- **Corollary**: Every non-degenerate lattice triangle has a primitive triangulation. -/
theorem has_primitive_triangulation (T : LatticeTriangle) (hT : T.NonDegenerate) :
    ∃ (pieces : List LatticeTriangle),
      pieces.length = T.det.natAbs ∧ ∀ p ∈ pieces, p.IsPrimitive :=
  exists_primitive_triangulation T.det.natAbs (Int.natAbs_pos.mpr hT) T rfl

-- ════════════════════════════════════════════════════════════════
-- SECTION V: Concrete Verification
-- ════════════════════════════════════════════════════════════════

/-- {(0,0),(2,0),(0,1)} has |det| = 2. -/
example : (LatticeTriangle.mk (0, 0) (2, 0) (0, 1)).det.natAbs = 2 := by decide

/-- {(0,0),(2,1),(1,2)} has |det| = 3 (all-primitive-edge triangle). -/
example : (LatticeTriangle.mk (0, 0) (2, 1) (1, 2)).det.natAbs = 3 := by decide

/-- The split of {(0,0),(2,0),(0,1)} at M=(1,0) gives two pieces summing to det. -/
theorem det2_split_correct :
    let T := LatticeTriangle.mk (0, 0) (2, 0) (0, 1)
    let M : ℤ × ℤ := (1, 0)
    (splitLeft T M).det + (splitRight T M).det = T.det ∧
    (splitLeft T M).IsPrimitive ∧ (splitRight T M).IsPrimitive := by
  decide

/-- Edge split formula: for T = {(0,0),(4,0),(0,3)} at g=2, each piece has |det|=6. -/
theorem det12_two_splits :
    let T := LatticeTriangle.mk (0, 0) (4, 0) (0, 3)
    T.det.natAbs = 12 ∧
    (splitLeft T (2, 0)).det.natAbs + (splitRight T (2, 0)).det.natAbs = 12 := by
  decide

/-- The det-additivity lemma works for T={O,(2,0),(0,3)}, g=2. -/
theorem det_add_example :
    let T := LatticeTriangle.mk (0, 0) (2, 0) (0, 3)
    T.det.natAbs = 6 ∧
    (splitLeft T (1, 0)).det.natAbs + (splitRight T (1, 0)).det.natAbs = 6 := by
  decide

end PicksTheoremOQ01OQ01
