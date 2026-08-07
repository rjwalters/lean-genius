import Proofs.Erdos85SaturatedExteriorDefectSplit

/-!
# The owner-fiber incidence operator

For a map `owner : X → Y`, its incidence matrix `C` has one `1` in every
column.  The matrix `CᵀC - I` is therefore exactly the disjoint union of
clique adjacency matrices on the owner fibers.  This file develops the
algebraic interface needed for the characteristic-three residual analysis.
-/

namespace Erdos85

noncomputable section

open Matrix
open scoped Matrix

def ownerIncidenceMatrix
    {X Y K : Type*} [DecidableEq Y] [Zero K] [One K]
    (owner : X → Y) : Matrix Y X K :=
  fun a x => if owner x = a then 1 else 0

def ownerFiberFinset
    {X Y : Type*} [Fintype X] [DecidableEq Y]
    (owner : X → Y) (a : Y) : Finset X :=
  Finset.univ.filter fun x => owner x = a

/-- `CᵀC` records equality of owners. -/
theorem ownerIncidence_transpose_mul_apply
    {X Y K : Type*} [Fintype Y] [DecidableEq Y]
    [Semiring K] (owner : X → Y) (x z : X) :
    (Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
      ownerIncidenceMatrix (K := K) owner) x z =
        if owner x = owner z then 1 else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    ownerIncidenceMatrix]
  by_cases h : owner x = owner z
  · rw [if_pos h]
    simpa [h] using (Finset.sum_boole (R := K)
      (fun a : Y => owner x = a) Finset.univ)
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hxa : owner x = a
    · have hza : owner z ≠ a := by
        intro hza
        exact h (hxa.trans hza.symm)
      simp [hxa, hza]
    · simp [hxa]

/-- `CCᵀ` is diagonal, with the owner-fiber cardinalities on its diagonal. -/
theorem ownerIncidence_mul_transpose_apply
    {X Y K : Type*} [Fintype X] [DecidableEq Y]
    [Semiring K] (owner : X → Y) (a b : Y) :
    (ownerIncidenceMatrix (K := K) owner *
      Matrix.transpose (ownerIncidenceMatrix (K := K) owner)) a b =
        if a = b then (ownerFiberFinset owner a).card else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    ownerIncidenceMatrix, ownerFiberFinset]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    calc
      (∑ x, (if owner x = a then (1 : K) else 0) *
          if owner x = a then 1 else 0) =
          ∑ x, if owner x = a then (1 : K) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : owner x = a <;> simp [hx]
      _ = ((Finset.univ.filter fun x => owner x = a).card : K) := by
        simpa using (Finset.sum_boole (R := K)
          (fun x : X => owner x = a) Finset.univ)
  · rw [if_neg hab]
    simp only [Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxa : owner x = a
    · have hxb : owner x ≠ b := fun hxb => hab (hxa.symm.trans hxb)
      rw [if_pos hxa, if_neg hxb]
      simp
    · simp [hxa]

def ownerFiberCliqueMatrix
    {X Y K : Type*} [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Ring K] (owner : X → Y) : Matrix X X K :=
  Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
      ownerIncidenceMatrix (K := K) owner - 1

/-- The owner-fiber operator is the adjacency matrix of the disjoint union
of cliques on the fibers. -/
theorem ownerFiberCliqueMatrix_apply
    {X Y K : Type*} [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Ring K] (owner : X → Y) (x z : X) :
    ownerFiberCliqueMatrix (K := K) owner x z =
      if x = z then 0 else if owner x = owner z then 1 else 0 := by
  rw [ownerFiberCliqueMatrix, Matrix.sub_apply,
    ownerIncidence_transpose_mul_apply]
  by_cases hxz : x = z
  · subst z
    simp
  · simp [Matrix.one_apply, hxz]

/-- Uniform fiber size makes `CCᵀ` a scalar matrix. -/
theorem ownerIncidence_mul_transpose_eq_smul_one
    {X Y K : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] [Semiring K]
    (owner : X → Y) (m : ℕ)
    (hcard : ∀ a, (ownerFiberFinset owner a).card = m) :
    ownerIncidenceMatrix (K := K) owner *
        Matrix.transpose (ownerIncidenceMatrix (K := K) owner) =
      (m : K) • (1 : Matrix Y Y K) := by
  ext a b
  rw [ownerIncidence_mul_transpose_apply]
  by_cases hab : a = b
  · subst b
    simp [hcard]
  · simp [hab, Matrix.smul_apply]

/-- If the common fiber cardinality is `1` in the coefficient ring, the
fiber-clique operator satisfies `K² = -K`. -/
theorem ownerFiberCliqueMatrix_mul_self_eq_neg
    {X Y K : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [CommRing K]
    (owner : X → Y) (m : ℕ)
    (hcard : ∀ a, (ownerFiberFinset owner a).card = m)
    (hm : (m : K) = 1) :
    ownerFiberCliqueMatrix (K := K) owner *
        ownerFiberCliqueMatrix (K := K) owner =
      -ownerFiberCliqueMatrix (K := K) owner := by
  let C := ownerIncidenceMatrix (K := K) owner
  have hCC : C * Matrix.transpose C = (1 : Matrix Y Y K) := by
    have h := ownerIncidence_mul_transpose_eq_smul_one
      (K := K) owner m hcard
    rw [hm, one_smul] at h
    exact h
  change (Matrix.transpose C * C - 1) *
      (Matrix.transpose C * C - 1) = -(Matrix.transpose C * C - 1)
  calc
    (Matrix.transpose C * C - 1) * (Matrix.transpose C * C - 1) =
        (Matrix.transpose C * C) * (Matrix.transpose C * C) -
          Matrix.transpose C * C - Matrix.transpose C * C + 1 := by
            noncomm_ring
    _ = Matrix.transpose C * (C * Matrix.transpose C) * C -
          Matrix.transpose C * C - Matrix.transpose C * C + 1 := by
            simp only [Matrix.mul_assoc]
    _ = Matrix.transpose C * C - Matrix.transpose C * C -
          Matrix.transpose C * C + 1 := by rw [hCC]; simp
    _ = -(Matrix.transpose C * C - 1) := by noncomm_ring

/-- A fiber of size `112` is congruent to one in characteristic three. -/
theorem ownerFiberCliqueMatrix_mul_self_eq_neg_zmodThree
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (owner : X → Y)
    (hcard : ∀ a, (ownerFiberFinset owner a).card = 112) :
    ownerFiberCliqueMatrix (K := ZMod 3) owner *
        ownerFiberCliqueMatrix (K := ZMod 3) owner =
      -ownerFiberCliqueMatrix (K := ZMod 3) owner := by
  apply ownerFiberCliqueMatrix_mul_self_eq_neg owner 112 hcard
  decide

end

end Erdos85
