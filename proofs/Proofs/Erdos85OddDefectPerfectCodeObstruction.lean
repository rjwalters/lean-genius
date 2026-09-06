import Proofs.Erdos85CubicTraceParity

/-!
# An odd perfect code obstructs even defect-overlap diagonals

Node A.5.3: this excludes every commuting cubic internal adjacency for the
interval defect on Z/(3q), once the cross equation's even-overlap condition
is imposed. The matrix theorem below is generic. Its perfect-code hypothesis
is explicit; no existence of such a code in arbitrary defect components is
asserted. The cyclic-coordinate instantiation is not formalized here.
-/

open Finset Matrix

namespace Erdos85

/-- A symmetric integer matrix with even diagonal cannot commute with a
symmetric defect matrix, have an even product diagonal, and have odd row sum
on an odd perfect code of that defect. -/
theorem odd_defect_perfectCode_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (H D : Matrix V V ℤ) (P : Finset V) (r : ℤ)
    (hH : H.IsSymm) (hD : D.IsSymm) (hcomm : H * D = D * H)
    (hdiagH : ∀ x, Even (H x x))
    (hdiagHD : ∀ x, Even ((H * D) x x))
    (hrow : ∀ x, ∑ y, H x y = r)
    (hcode : ∀ y, ∑ z ∈ P, D y z = 1 - if y ∈ P then 1 else 0)
    (hP : Odd (P.card : ℤ)) (hr : Odd r) : False := by
  have hHD : (H * D).IsSymm := by
    change (H * D)ᵀ = H * D
    rw [Matrix.transpose_mul, hH.eq, hD.eq, hcomm]
  have hrowHD (x : V) :
      (∑ z ∈ P, (H * D) x z) = r - ∑ z ∈ P, H x z := by
    calc
      (∑ z ∈ P, (H * D) x z) =
          ∑ y, H x y * (∑ z ∈ P, D y z) := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = r - ∑ z ∈ P, H x z := by
        simp_rw [hcode, mul_sub, mul_one, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_sub_distrib, hrow]
        simp
  have heH : Even (∑ x ∈ P, ∑ z ∈ P, H x z) :=
    even_sum_product_of_symmetric_even_diag P H
      (fun i _ j _ => (hH.apply i j).symm) (fun i _ => hdiagH i)
  have heHD : Even (∑ x ∈ P, ∑ z ∈ P, (H * D) x z) :=
    even_sum_product_of_symmetric_even_diag P (H * D)
      (fun i _ j _ => (hHD.apply i j).symm) (fun i _ => hdiagHD i)
  have htotal :
      (∑ x ∈ P, ∑ z ∈ P, (H * D) x z) +
      (∑ x ∈ P, ∑ z ∈ P, H x z) = (P.card : ℤ) * r := by
    simp_rw [hrowHD]
    rw [Finset.sum_sub_distrib]
    simp
  have he : Even ((P.card : ℤ) * r) := htotal ▸ heHD.add heH
  obtain ⟨a, ha⟩ := hP.mul hr
  obtain ⟨b, hb⟩ := he
  omega

#print axioms odd_defect_perfectCode_false

end Erdos85
