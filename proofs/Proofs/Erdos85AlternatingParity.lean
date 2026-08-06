import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Alternating parity over `𝔽₂`

Over `ZMod 2` a symmetric matrix with zero diagonal is *alternating*: it
is the mod-two reduction of an integer skew-symmetric matrix.  Integer
skew-symmetric matrices of odd size have zero determinant, so an odd-size
alternating matrix over `ZMod 2` is singular.

Consequently, if an alternating matrix on an even-size index type kills
the all-ones vector, its kernel contains a second vector distinct from
both `0` and the all-ones vector: deleting one index leaves an odd-size
alternating principal submatrix, which is singular, and the resulting
kernel vector extends by zero across the deleted index.

This is the `𝔽₂` engine behind the even-degree excess-one defect-kernel
theorem of the Erdős–85 program.
-/

namespace Erdos85

open Matrix

/-- Negation is the identity on `ZMod 2`. -/
theorem zmodTwo_neg_eq : ∀ x : ZMod 2, -x = x := by decide

/-- Casting the value of a `ZMod 2` element through `ℤ` is the identity. -/
theorem zmodTwo_intCast_val : ∀ x : ZMod 2, ((x.val : ℤ) : ZMod 2) = x := by
  decide

/-- An odd-size symmetric zero-diagonal matrix over `ZMod 2` is singular:
`Fin` version, proved via an integer skew-symmetric lift. -/
theorem det_eq_zero_of_symm_diag_zero_of_odd_fin {m : ℕ} (hm : Odd m)
    (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (hsymm : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0) :
    A.det = 0 := by
  set K : Matrix (Fin m) (Fin m) ℤ :=
    Matrix.of (fun i j =>
      if i < j then ((A i j).val : ℤ) else -((A i j).val : ℤ)) with hKdef
  have hKskew : Kᵀ = -K := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, hKdef,
      Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [if_neg (asymm h), if_pos h, hsymm j i]
    · subst h
      rw [if_neg (lt_irrefl i), hdiag i]
      simp
    · rw [if_pos h, if_neg (asymm h), hsymm j i, neg_neg]
  have hKdet : K.det = 0 := by
    have h1 : K.det = -K.det := by
      calc
        K.det = Kᵀ.det := (Matrix.det_transpose K).symm
        _ = (-K).det := by rw [hKskew]
        _ = (-1) ^ m * K.det := by
          rw [Matrix.det_neg]
          simp
        _ = -K.det := by rw [hm.neg_one_pow, neg_one_mul]
    linarith
  have hmap : K.map (Int.castRingHom (ZMod 2)) = A := by
    ext i j
    simp only [Matrix.map_apply, hKdef, Matrix.of_apply]
    split_ifs with h
    · exact zmodTwo_intCast_val (A i j)
    · calc ((Int.castRingHom (ZMod 2)) (-((A i j).val : ℤ))) =
          -(((A i j).val : ℤ) : ZMod 2) := by
            simp
        _ = A i j := by rw [zmodTwo_intCast_val (A i j), zmodTwo_neg_eq]
  calc
    A.det = (K.map (Int.castRingHom (ZMod 2))).det := by rw [hmap]
    _ = (Int.castRingHom (ZMod 2)) K.det := (RingHom.map_det _ K).symm
    _ = 0 := by rw [hKdet]; simp

/-- An odd-size symmetric zero-diagonal matrix over `ZMod 2` is singular:
general index type. -/
theorem det_eq_zero_of_symm_diag_zero_of_odd_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hodd : Odd (Fintype.card ι)) (A : Matrix ι ι (ZMod 2))
    (hsymm : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0) :
    A.det = 0 := by
  let e := Fintype.equivFin ι
  have h := det_eq_zero_of_symm_diag_zero_of_odd_fin hodd
    (Matrix.reindex e e A)
    (fun i j => by
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hsymm _ _)
    (fun i => by
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hdiag _)
  rwa [Matrix.det_reindex_self] at h

/-- **Second kernel vector.**  An alternating matrix over `ZMod 2` on an
even-size index type that kills the all-ones vector also kills a vector
that is neither `0` nor all-ones: the principal submatrix obtained by
deleting one index is alternating of odd size, hence singular, and its
kernel vector extends by zero. -/
theorem exists_kernel_vector_ne_zero_ne_ones
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (heven : Even (Fintype.card ι)) (A : Matrix ι ι (ZMod 2))
    (hsymm : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hones : A.mulVec (fun _ => 1) = 0) :
    ∃ w : ι → ZMod 2,
      A.mulVec w = 0 ∧ w ≠ 0 ∧ w ≠ fun _ => 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₀⟩ := ‹Nonempty ι›
  let B : Matrix {i : ι // i ≠ v₀} {i : ι // i ≠ v₀} (ZMod 2) :=
    Matrix.of fun i j => A i.1 j.1
  have hcard : Fintype.card {i : ι // i ≠ v₀} = Fintype.card ι - 1 := by
    have h := Fintype.card_subtype_compl (fun i : ι => i = v₀)
    rw [Fintype.card_subtype_eq] at h
    exact h
  have hodd : Odd (Fintype.card {i : ι // i ≠ v₀}) := by
    obtain ⟨k, hk⟩ := heven
    have hpos : 0 < Fintype.card ι := Fintype.card_pos
    exact ⟨k - 1, by omega⟩
  have hBdet : B.det = 0 :=
    det_eq_zero_of_symm_diag_zero_of_odd_card hodd B
      (fun i j => hsymm i.1 j.1) (fun i => hdiag i.1)
  obtain ⟨c, hc0, hBc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hBdet
  set w : ι → ZMod 2 :=
    fun i => if h : i = v₀ then 0 else c ⟨i, h⟩ with hwdef
  have hw_v₀ : w v₀ = 0 := by
    simp [hwdef]
  have hw_ne : ∀ i (h : i ≠ v₀), w i = c ⟨i, h⟩ := by
    intro i h
    simp only [hwdef]
    exact dif_neg h
  have hcomp_ne : ∀ u, u ≠ v₀ → A.mulVec w u = 0 := by
    intro u hu
    have h := congrFun hBc ⟨u, hu⟩
    rw [Matrix.mulVec, dotProduct] at h
    simp only [Matrix.of_apply, Pi.zero_apply, B] at h
    rw [Matrix.mulVec, dotProduct]
    calc
      ∑ i : ι, A u i * w i
          = ∑ i ∈ Finset.univ.erase v₀, A u i * w i :=
        (Finset.sum_erase _ (by rw [hw_v₀, mul_zero])).symm
      _ = ∑ i : {i : ι // i ≠ v₀}, A u i.1 * w i.1 :=
        Finset.sum_subtype (Finset.univ.erase v₀)
          (fun x => by simp) (fun i => A u i * w i)
      _ = ∑ i : {i : ι // i ≠ v₀}, A u i.1 * c i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hw_ne i.1 i.2]
      _ = 0 := h
  have htotal : ∑ u, A.mulVec w u = 0 := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_mul]
    have hcol : ∑ u, A u i = 0 := by
      have h := congrFun hones i
      simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] at h
      calc
        ∑ u, A u i = ∑ u, A i u :=
          Finset.sum_congr rfl fun u _ => hsymm u i
        _ = 0 := h
    rw [hcol, zero_mul]
  have hcomp_v₀ : A.mulVec w v₀ = 0 := by
    have h := htotal
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v₀)] at h
    have hrest : ∑ u ∈ Finset.univ.erase v₀, A.mulVec w u = 0 :=
      Finset.sum_eq_zero fun u hu =>
        hcomp_ne u (Finset.ne_of_mem_erase hu)
    rw [hrest, add_zero] at h
    exact h
  refine ⟨w, ?_, ?_, ?_⟩
  · funext u
    by_cases hu : u = v₀
    · subst hu
      exact hcomp_v₀
    · exact hcomp_ne u hu
  · intro hcontra
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc0
    apply hj
    have := congrFun hcontra j.1
    rw [hw_ne j.1 j.2] at this
    simpa using this
  · intro hcontra
    have := congrFun hcontra v₀
    rw [hw_v₀] at this
    exact zero_ne_one this

end Erdos85
