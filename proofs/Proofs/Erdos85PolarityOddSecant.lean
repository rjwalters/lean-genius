import Proofs.Erdos85PolarityAbsoluteSetDeletion
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The two-secant bound in odd characteristic

When 2 is nonzero, a polar line contains at most two absolute points.  The
proof uses the Gram determinant of three hypothetical distinct absolute
points.  Their pairwise dot products are nonzero, so the Gram determinant is
nonzero; but all three vectors lie in the orthogonal complement of one nonzero
vector, forcing their row matrix to be singular.
-/

open SimpleGraph Matrix
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

/-- Vector-level Gram determinant obstruction. -/
private theorem not_three_isotropic_in_orthogonal_plane
    {K : Type u} [Field K] (h2 : (2 : K) ≠ 0)
    (a b c v : Fin 3 → K) (hv : v ≠ 0)
    (haa : a ⬝ᵥ a = 0) (hbb : b ⬝ᵥ b = 0) (hcc : c ⬝ᵥ c = 0)
    (hav : a ⬝ᵥ v = 0) (hbv : b ⬝ᵥ v = 0) (hcv : c ⬝ᵥ v = 0)
    (hab : a ⬝ᵥ b ≠ 0) (hac : a ⬝ᵥ c ≠ 0) (hbc : b ⬝ᵥ c ≠ 0) :
    False := by
  let A : Matrix (Fin 3) (Fin 3) K := ![a, b, c]
  have hAv : A *ᵥ v = 0 := by
    funext i
    fin_cases i <;> simp [A, Matrix.mulVec, hav, hbv, hcv]
  have hdetA : A.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hAv⟩
  have hdetGram : (A * Aᵀ).det = 0 := by
    rw [Matrix.det_mul, hdetA, zero_mul]
  have hgram : A * Aᵀ =
      !![(0 : K), a ⬝ᵥ b, a ⬝ᵥ c;
         a ⬝ᵥ b, 0, b ⬝ᵥ c;
         a ⬝ᵥ c, b ⬝ᵥ c, 0] := by
    have haa' : ∑ x, a x * a x = 0 := by simpa [dotProduct] using haa
    have hbb' : ∑ x, b x * b x = 0 := by simpa [dotProduct] using hbb
    have hcc' : ∑ x, c x * c x = 0 := by simpa [dotProduct] using hcc
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, dotProduct, haa', hbb', hcc', mul_comm]
  rw [hgram, Matrix.det_fin_three] at hdetGram
  simp at hdetGram
  have hn : 2 * (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hab) hac) hbc
  apply hn
  linear_combination hdetGram

/-- In characteristic different from two, every nonabsolute polar line is a
two-secant of the absolute locus. -/
theorem absoluteTwoSecant_of_two_ne_zero
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    AbsoluteTwoSecant K := by
  intro v hv
  by_contra hle
  have hlt : 2 < ((graph K).neighborFinset v ∩ absolutePoints K).card :=
    Nat.lt_of_not_ge hle
  rw [Finset.two_lt_card] at hlt
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := hlt
  have hav := (graph_adj_iff v a).mp (by simpa using (Finset.mem_inter.mp ha).1)
  have hbv := (graph_adj_iff v b).mp (by simpa using (Finset.mem_inter.mp hb).1)
  have hcv := (graph_adj_iff v c).mp (by simpa using (Finset.mem_inter.mp hc).1)
  have haa := (mem_absolutePoints K a).mp (Finset.mem_inter.mp ha).2
  have hbb := (mem_absolutePoints K b).mp (Finset.mem_inter.mp hb).2
  have hcc := (mem_absolutePoints K c).mp (Finset.mem_inter.mp hc).2
  have habno : ¬ Projectivization.orthogonal a b := by
    intro hortho
    have hadj : (graph K).Adj a b := (graph_adj_iff a b).mpr ⟨hab, hortho⟩
    exact (not_selfOrthogonal_of_adj_selfOrthogonal hadj haa) hbb
  have hacno : ¬ Projectivization.orthogonal a c := by
    intro hortho
    have hadj : (graph K).Adj a c := (graph_adj_iff a c).mpr ⟨hac, hortho⟩
    exact (not_selfOrthogonal_of_adj_selfOrthogonal hadj haa) hcc
  have hbcno : ¬ Projectivization.orthogonal b c := by
    intro hortho
    have hadj : (graph K).Adj b c := (graph_adj_iff b c).mpr ⟨hbc, hortho⟩
    exact (not_selfOrthogonal_of_adj_selfOrthogonal hadj hbb) hcc
  apply not_three_isotropic_in_orthogonal_plane h2
    a.rep b.rep c.rep v.rep v.rep_nonzero
  · exact (Projectivization.orthogonal_mk a.rep_nonzero a.rep_nonzero).mp
      (by simpa using haa)
  · exact (Projectivization.orthogonal_mk b.rep_nonzero b.rep_nonzero).mp
      (by simpa using hbb)
  · exact (Projectivization.orthogonal_mk c.rep_nonzero c.rep_nonzero).mp
      (by simpa using hcc)
  · exact (Projectivization.orthogonal_mk a.rep_nonzero v.rep_nonzero).mp
      (by simpa using Projectivization.orthogonal_comm.mp hav.2)
  · exact (Projectivization.orthogonal_mk b.rep_nonzero v.rep_nonzero).mp
      (by simpa using Projectivization.orthogonal_comm.mp hbv.2)
  · exact (Projectivization.orthogonal_mk c.rep_nonzero v.rep_nonzero).mp
      (by simpa using Projectivization.orthogonal_comm.mp hcv.2)
  · exact fun hdot => habno (by
      simpa using
        (Projectivization.orthogonal_mk a.rep_nonzero b.rep_nonzero).mpr hdot)
  · exact fun hdot => hacno (by
      simpa using
        (Projectivization.orthogonal_mk a.rep_nonzero c.rep_nonzero).mpr hdot)
  · exact fun hdot => hbcno (by
      simpa using
        (Projectivization.orthogonal_mk b.rep_nonzero c.rep_nonzero).mpr hdot)

end Erdos85.Polarity

