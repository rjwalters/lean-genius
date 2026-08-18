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

/-- Every cardinality up to the absolute locus gives an odd-characteristic
controlled-deletion witness of degree `q-1`. -/
theorem c4FreeMinDegreeWitness_odd_delete_absolute_card
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {k : ℕ}
    (hk : k ≤ (absolutePoints K).card)
    (hremain : 1 ≤ (Nat.card K + 1) * Nat.card K + 1 - k) :
    C4FreeMinDegreeWitness
      ((Nat.card K + 1) * Nat.card K + 1 - k) (Nat.card K - 1) := by
  obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hk
  apply c4FreeMinDegreeWitness_delete_absolute_set
    K (absoluteTwoSecant_of_two_ne_zero K h2) D hDcard hremain
  intro y hy
  exact (mem_absolutePoints K y).mp (hDsub hy)

/-- Corresponding threshold lower bound at every attainable deleted order. -/
theorem minDegreeForC4_odd_delete_absolute_card_lower
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) {k : ℕ}
    (hk : k ≤ (absolutePoints K).card)
    (hremain : 4 ≤ (Nat.card K + 1) * Nat.card K + 1 - k) :
    Nat.card K - 1 < minDegreeForC4
      ((Nat.card K + 1) * Nat.card K + 1 - k) := by
  exact (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hremain).1
    (c4FreeMinDegreeWitness_odd_delete_absolute_card K h2 hk (by omega))

/-- Every odd-characteristic orthogonal polarity has at least two distinct
absolute points.  Starting from one isotropic line, a second is obtained by
solving the quadratic equation along a transverse affine line. -/
theorem two_le_card_absolutePoints_of_two_ne_zero
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    2 ≤ (absolutePoints K).card := by
  obtain ⟨a, haa⟩ := exists_selfOrthogonal K
  obtain ⟨b, habno⟩ := Projectivization.exists_not_self_orthogonal a
  have haavec : a.rep ⬝ᵥ a.rep = 0 :=
    (Projectivization.orthogonal_mk a.rep_nonzero a.rep_nonzero).mp
      (by simpa using haa)
  have habvec : a.rep ⬝ᵥ b.rep ≠ 0 := by
    intro hdot
    apply habno
    simpa using
      (Projectivization.orthogonal_mk a.rep_nonzero b.rep_nonzero).mpr hdot
  let t : K := -(b.rep ⬝ᵥ b.rep) / (2 * (a.rep ⬝ᵥ b.rep))
  let c : Fin 3 → K := b.rep + t • a.rep
  have hcprops : c ⬝ᵥ c = 0 ∧ a.rep ⬝ᵥ c = a.rep ⬝ᵥ b.rep := by
    dsimp [c, t]
    have hden : 2 * (a.rep ⬝ᵥ b.rep) ≠ 0 := mul_ne_zero h2 habvec
    constructor
    · simp only [add_dotProduct, dotProduct_add, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, haavec, mul_zero, add_zero]
      rw [show b.rep ⬝ᵥ a.rep = a.rep ⬝ᵥ b.rep by
        exact dotProduct_comm b.rep a.rep]
      field_simp
      ring
    · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, haavec,
        mul_zero, add_zero]
  have hc0 : c ≠ 0 := by
    intro hc
    have hz : a.rep ⬝ᵥ c = 0 := by rw [hc]; simp
    exact habvec (hcprops.2.symm.trans hz)
  let cp := Projectivization.mk K c hc0
  have hcpabs : Projectivization.orthogonal cp cp :=
    (Projectivization.orthogonal_mk hc0 hc0).mpr hcprops.1
  have hacno : ¬ Projectivization.orthogonal a cp := by
    intro hac
    have hdot : a.rep ⬝ᵥ c = 0 :=
      (Projectivization.orthogonal_mk a.rep_nonzero hc0).mp
        (by simpa [cp] using hac)
    exact habvec (hcprops.2.symm.trans hdot)
  have hac : a ≠ cp := by
    intro heq
    apply hacno
    rw [← heq]
    exact haa
  have hsub : {a, cp} ⊆ absolutePoints K := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_absolutePoints K _).mpr haa
    · exact (mem_absolutePoints K _).mpr hcpabs
  have hcard := Finset.card_le_card hsub
  simpa [hac] using hcard

/-- Unconditional two-absolute-point deletion in odd characteristic. -/
theorem c4FreeMinDegreeWitness_odd_delete_two
    (K : Type u) [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    C4FreeMinDegreeWitness
      ((Nat.card K + 1) * Nat.card K + 1 - 2) (Nat.card K - 1) := by
  apply c4FreeMinDegreeWitness_odd_delete_absolute_card K h2
    (two_le_card_absolutePoints_of_two_ne_zero K h2)
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  have hN : 3 ≤ (Nat.card K + 1) * Nat.card K + 1 := by nlinarith
  omega


end Erdos85.Polarity
