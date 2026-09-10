import Proofs.Erdos85ThreeBlockCandidateDomains

namespace Erdos85

private theorem rectangle_false {W : Type*} [Fintype W] [DecidableEq W]
    (B : W → W → Bool) (hf : encodedC4Free B = true)
    (x y a b : W) (hxy : x ≠ y) (hab : a ≠ b)
    (hxa : B x a = true) (hxb : B x b = true)
    (hya : B y a = true) (hyb : B y b = true) : False := by
  unfold encodedC4Free at hf
  simp only [decide_eq_true_eq] at hf
  have mem (z : W) (hx : B x z = true) (hy : B y z = true) :
      z ∈ Finset.univ.filter (fun w => B x w && B y w) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨hx,hy⟩
  exact hab (Finset.card_le_one.mp (hf x y hxy) a (mem a hxa hya) b (mem b hxb hyb))

/-- A shared internal edge between row zero and another row forms a C4
using the two identity cross edges. The permutation is unrestricted. -/
theorem threeBlockMatchingAdj_shared_edge
    (m : Fin 3 → BitVec 10) (π : Equiv.Perm (Fin 5))
    (hf : encodedC4Free (threeBlockMatchingAdj m π) = true)
    (k : Fin 3) (hk : k ≠ 0) (i j : Fin 5)
    (h0 : oneHighBranchBitAdj (m 0) i j = true)
    (h1 : oneHighBranchBitAdj (m k) j i = true) : False := by
  apply rectangle_false (threeBlockMatchingAdj m π) hf (0,i) (k,j) (0,j) (k,i)
  · exact fun h => hk (congrArg Prod.fst h).symm
  · exact fun h => hk (congrArg Prod.fst h).symm
  · simpa [threeBlockMatchingAdj] using h0
  · simp [threeBlockMatchingAdj,hk,Ne.symm hk]
  · simp [threeBlockMatchingAdj,hk]
  · simpa [threeBlockMatchingAdj] using h1

/-- The same C4 never uses the deficient row-one/row-two edges. -/
theorem threeBlockDeficientMatchingAdj_shared_edge
    (m : Fin 3 → BitVec 10) (π : Equiv.Perm (Fin 5)) (d : Fin 5)
    (hf : encodedC4Free (threeBlockDeficientMatchingAdj m π d) = true)
    (k : Fin 3) (hk : k ≠ 0) (i j : Fin 5)
    (h0 : oneHighBranchBitAdj (m 0) i j = true)
    (h1 : oneHighBranchBitAdj (m k) j i = true) : False := by
  apply rectangle_false (threeBlockDeficientMatchingAdj m π d) hf (0,i) (k,j) (0,j) (k,i)
  · exact fun h => hk (congrArg Prod.fst h).symm
  · exact fun h => hk (congrArg Prod.fst h).symm
  · simpa [threeBlockDeficientMatchingAdj] using h0
  · simp [threeBlockDeficientMatchingAdj,hk,Ne.symm hk]
  · simp [threeBlockDeficientMatchingAdj,hk]
  · simpa [threeBlockDeficientMatchingAdj] using h1

end Erdos85
#print axioms Erdos85.threeBlockMatchingAdj_shared_edge
#print axioms Erdos85.threeBlockDeficientMatchingAdj_shared_edge
