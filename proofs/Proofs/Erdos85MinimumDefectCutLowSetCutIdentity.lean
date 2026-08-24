import Proofs.Erdos85MinimumDefectCutLowSet
import Proofs.Erdos85DefectCutCenteredImage

/-!
# The defect cut of a minimum-cut low set

This is equation (7) in the connected-defect minimum-cut argument.  A shore
whose adjacency occupancy is `a` off a set `Z` and `a+1` on `Z` transfers,
after applying adjacency once more, to the defect-Laplacian boundary of the
shore.  Squaring the resulting occupancy profile computes the defect cut of
`Z` exactly.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The graph-facing form of equation (7).  The sum on the right is over the
defect degrees from `S` to its complement. -/
theorem binarySquare_lowSet_defectCut_eq_shoreCut_add_sum_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1)
    (S Z : Finset V) (hScard : S.card = q * a + 1)
    (hocc : ∀ x, (G.neighborFinset x ∩ S).card =
      a + if x ∈ Z then 1 else 0) :
    finsetGraphCutSize (secondOrderDefectGraph G) Z =
      finsetGraphCutSize (secondOrderDefectGraph G) S +
        ∑ x ∈ S,
          ((secondOrderDefectGraph G).neighborFinset x ∩
            (Finset.univ \ S)).card ^ 2 := by
  classical
  let D := secondOrderDefectGraph G
  let b := fun x : V => (G.neighborFinset x ∩ Z).card
  let d := fun x : V => (D.neighborFinset x ∩ (Finset.univ \ S)).card
  have hZcard : Z.card = q := by
    have hsum : (∑ x : V, (G.neighborFinset x ∩ S).card) = q * S.card := by
      rw [sum_card_neighbor_inter_eq_sum_degree]
      calc
        (∑ x ∈ S, G.degree x) = ∑ _x ∈ S, q := by
          apply Finset.sum_congr rfl
          intro x _
          exact hreg x
        _ = q * S.card := by simp [mul_comm]
    simp_rw [hocc] at hsum
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hsum
    have hind : (∑ x : V, if x ∈ Z then 1 else 0) = Z.card := by
      simp
    rw [hind, hScard] at hsum
    nlinarith
  have hqpos : 1 ≤ q := by
    have hsle : S.card ≤ Fintype.card V := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ S)
    rw [hScard, hcard] at hsle
    nlinarith
  have htransfer : ∀ x, (b x : ℤ) =
      1 + (if x ∈ S then (d x : ℤ) else
        -(((D.neighborFinset x ∩ S).card : ℕ) : ℤ)) := by
    intro x
    let A := G.adjMatrix ℤ
    let DM := D.adjMatrix ℤ
    let chiS := finsetIndicatorInt S
    let chiZ := finsetIndicatorInt Z
    let one : V → ℤ := fun _ => 1
    have hchi : A.mulVec chiS = (a : ℤ) • one + chiZ := by
      ext y
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [adjMatrix_mulVec_finsetIndicatorInt_apply]
      rw [hocc]
      by_cases hy : y ∈ Z <;>
        simp [one, chiZ, finsetIndicatorInt_apply, hy]
    have hsq : A * A = ((q : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - DM := by
      exact adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
    have hAone : A.mulVec one = (q : ℤ) • one := by
      ext y
      change (G.adjMatrix ℤ).mulVec (Function.const V 1) y = (q : ℤ) * 1
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hreg y]
    have hJchi :
        (FriendshipTheoremOQ01.onesMatrix V).mulVec chiS =
          (S.card : ℤ) • one := by
      ext y
      simpa [chiS, one] using
        onesMatrix_mulVec_finsetIndicatorInt_apply S y
    have himage : A.mulVec chiZ =
        (((q : ℤ) - 1) • (1 : Matrix V V ℤ) - DM).mulVec chiS + one := by
      have hh := congrArg (fun v => A.mulVec v) hchi
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAone, smul_smul,
        Matrix.mulVec_mulVec chiS A A, hsq, Matrix.sub_mulVec, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hJchi] at hh
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hScard] at hh
      ext y
      have hy := congrFun hh y
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy ⊢
      push_cast at hy
      dsimp [one] at hy ⊢
      linarith
    have hx := congrFun himage x
    rw [adjMatrix_mulVec_finsetIndicatorInt_apply] at hx
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      finsetIndicatorInt_apply] at hx
    have hDM : DM.mulVec chiS x =
        ((D.neighborFinset x ∩ S).card : ℤ) := by
      exact adjMatrix_mulVec_finsetIndicatorInt_apply D S x
    rw [hDM] at hx
    by_cases hxS : x ∈ S
    · simp only [hxS, if_pos] at hx ⊢
      have hsplit : (D.neighborFinset x ∩ S).card + d x = q - 1 := by
        dsimp only [d]
        have hpart : D.neighborFinset x =
            (D.neighborFinset x ∩ S) ∪
              (D.neighborFinset x ∩ (Finset.univ \ S)) := by
          ext y
          by_cases hy : y ∈ S <;> simp [hy]
        have hdisj : Disjoint (D.neighborFinset x ∩ S)
            (D.neighborFinset x ∩ (Finset.univ \ S)) := by
          rw [Finset.disjoint_left]
          intro y hy₁ hy₂
          have hy₁' := Finset.mem_inter.mp hy₁
          have hy₂' := Finset.mem_inter.mp hy₂
          exact (Finset.mem_sdiff.mp hy₂'.2).2 hy₁'.2
        have hpartCard := congrArg Finset.card hpart
        rw [Finset.card_union_of_disjoint hdisj] at hpartCard
        calc
          _ = (D.neighborFinset x).card := hpartCard.symm
          _ = D.degree x := D.card_neighborFinset_eq_degree x
          _ = q - 1 := hDreg x
      have hsplitZ := congrArg (fun n : ℕ => (n : ℤ)) hsplit
      push_cast at hsplitZ
      rw [Nat.cast_sub hqpos] at hsplitZ
      norm_num at hsplitZ
      simp [b, chiS, finsetIndicatorInt_apply, one, hxS] at hx
      linarith
    · simp only [hxS, if_false] at hx ⊢
      simpa [b, chiS, finsetIndicatorInt_apply, one, hxS, add_comm] using hx
  have hsumd : (∑ x ∈ S, d x) =
      finsetGraphCutSize D S := by
    unfold finsetGraphCutSize
    apply Finset.sum_congr rfl
    intro x _
    dsimp only [d]
    congr 1
    ext y
    simp
  have hmoment := c4Free_regular_square_cut_neighborMoment
    G hfree hreg hcard Z
  change (∑ x : V, b x ^ 2) = Z.card ^ 2 +
    finsetGraphCutSize D Z at hmoment
  have hbprod : (∑ x : V, b x * (b x - 1)) =
      ∑ x ∈ S, d x * (d x + 1) := by
    calc
      (∑ x : V, b x * (b x - 1)) =
          ∑ x ∈ S, b x * (b x - 1) := by
        apply (Finset.sum_subset (s₁ := S) (s₂ := Finset.univ) ?_ ?_).symm
        · exact Finset.subset_univ S
        · intro x _ hxS
          have ht := htransfer x
          simp only [hxS, if_false] at ht
          have hb_le : b x ≤ 1 := by omega
          interval_cases hb : b x <;> simp [hb]
      _ = ∑ x ∈ S, d x * (d x + 1) := by
        apply Finset.sum_congr rfl
        intro x hxS
        have ht := htransfer x
        simp only [hxS, if_pos] at ht
        have hbd : b x = 1 + d x := by exact_mod_cast ht
        rw [hbd]
        simp
        ring
  have hsumB : (∑ x : V, b x) = q * Z.card := by
    rw [sum_card_neighbor_inter_eq_sum_degree]
    calc
      (∑ x ∈ Z, G.degree x) = ∑ _x ∈ Z, q := by
        apply Finset.sum_congr rfl
        intro x _
        exact hreg x
      _ = q * Z.card := by simp [mul_comm]
  rw [hZcard] at hmoment hsumB
  have hsqexpand : (∑ x : V, b x ^ 2) =
      (∑ x : V, b x * (b x - 1)) + ∑ x : V, b x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : b x = 0
    · simp [hx]
    · have hxpos : 1 ≤ b x := Nat.one_le_iff_ne_zero.mpr hx
      rw [pow_two]
      calc
        b x * b x = b x * ((b x - 1) + 1) := by
          congr 1
          omega
        _ = b x * (b x - 1) + b x := by rw [mul_add, mul_one]
  rw [hsqexpand, hbprod, hsumB] at hmoment
  have hdexpand : (∑ x ∈ S, d x * (d x + 1)) =
      (∑ x ∈ S, d x ^ 2) + ∑ x ∈ S, d x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hdexpand, hsumd] at hmoment
  simp only [pow_two] at hmoment
  have hfinal : finsetGraphCutSize D Z =
      finsetGraphCutSize D S + ∑ x ∈ S, d x ^ 2 := by
    simp only [pow_two]
    omega
  simpa [D, d] using hfinal

#print axioms binarySquare_lowSet_defectCut_eq_shoreCut_add_sum_sq

end

end Erdos85
