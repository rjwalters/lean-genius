import Proofs.Erdos85BinarySquareDyadicSignedTerminal

/-!
# Private points in the endpoint partial-Baer design

At the pure endpoint `c = q`, the scalar identities say that `q` exceptional
lines have no triple point and every pair meets once.  This file turns those
counts into a pointwise structure theorem: every exceptional line has one
and only one point belonging to no other exceptional line.
-/

namespace Erdos85

noncomputable section

/-- Points of line `i` which do not occur in its intersection with any other
line of the family. -/
def partialBaerPrivatePoints
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (L : ι → Finset V) (i : ι) : Finset V :=
  L i \ ((Finset.univ.erase i).biUnion fun j => L i ∩ L j)

/-- Pairwise-one intersections and absence of triple points force exactly
one private point on every line when the number and size of the lines are
both `q`. -/
theorem partialBaer_privatePoints_card_eq_one
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {q : ℕ} (L : ι → Finset V)
    (hindex : Fintype.card ι = q)
    (hline : ∀ i, (L i).card = q)
    (hpair : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (htriple : ∀ x i j k, x ∈ L i → x ∈ L j → x ∈ L k →
      i = j ∨ i = k ∨ j = k)
    (i : ι) :
    (partialBaerPrivatePoints L i).card = 1 := by
  let J : Finset ι := Finset.univ.erase i
  let B : ι → Finset V := fun j => L i ∩ L j
  have hdisj : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (B j) (B k) := by
    intro j hj k hk hjk
    rw [Finset.disjoint_left]
    intro x hxj hxk
    have hxj' := Finset.mem_inter.mp hxj
    have hxk' := Finset.mem_inter.mp hxk
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rcases htriple x i j k hxj'.1 hxj'.2 hxk'.2 with hij | hik | hjkeq
    · exact hji hij.symm
    · exact hki hik.symm
    · exact hjk hjkeq
  have hJcard : J.card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      hindex]
  have hBcard : (J.biUnion B).card = q - 1 := by
    rw [Finset.card_biUnion hdisj]
    calc
      ∑ j ∈ J, (B j).card = ∑ _j ∈ J, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hpair i j (fun hij => (Finset.mem_erase.mp hj).1 hij.symm)
      _ = J.card := by simp
      _ = q - 1 := hJcard
  have hBsub : J.biUnion B ⊆ L i := by
    apply Finset.biUnion_subset.mpr
    intro j hj
    exact Finset.inter_subset_left
  have hqpos : 0 < q := by
    rw [← hindex]
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  change (L i \ J.biUnion B).card = 1
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub, hline i, hBcard]
  omega

/-- The unique private points form a canonical-size transversal: one may
choose one point from every line, the choices are pairwise distinct, and the
point chosen for a line lies on no other line of the family. -/
theorem exists_injective_partialBaer_privatePoint
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {q : ℕ} (L : ι → Finset V)
    (hindex : Fintype.card ι = q)
    (hline : ∀ i, (L i).card = q)
    (hpair : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (htriple : ∀ x i j k, x ∈ L i → x ∈ L j → x ∈ L k →
      i = j ∨ i = k ∨ j = k) :
    ∃ p : ι → V, Function.Injective p ∧
      ∀ i, p i ∈ L i ∧ ∀ j, j ≠ i → p i ∉ L j := by
  classical
  have hprivate : ∀ i, (partialBaerPrivatePoints L i).card = 1 :=
    partialBaer_privatePoints_card_eq_one L hindex hline hpair htriple
  let p : ι → V := fun i =>
    (Finset.card_pos.mp (by rw [hprivate i]; norm_num)).choose
  have hpPrivate : ∀ i, p i ∈ partialBaerPrivatePoints L i := by
    intro i
    exact (Finset.card_pos.mp (by rw [hprivate i]; norm_num)).choose_spec
  have hp : ∀ i, p i ∈ L i ∧ ∀ j, j ≠ i → p i ∉ L j := by
    intro i
    have hpi := Finset.mem_sdiff.mp (hpPrivate i)
    refine ⟨hpi.1, ?_⟩
    intro j hji hpj
    apply hpi.2
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, ?_⟩
    exact Finset.mem_inter.mpr ⟨hpi.1, hpj⟩
  refine ⟨p, ?_, hp⟩
  intro i j hpij
  by_contra hij
  exact (hp i).2 j (fun hji => hij hji.symm) (hpij ▸ (hp j).1)

end

end Erdos85

#print axioms Erdos85.partialBaer_privatePoints_card_eq_one
#print axioms Erdos85.exists_injective_partialBaer_privatePoint
