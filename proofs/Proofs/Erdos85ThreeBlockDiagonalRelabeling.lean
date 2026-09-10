import Proofs.Erdos85ThreeBlockCandidateDomains

namespace Erdos85

def threeBlockConjugate (π σ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 5) :=
  σ.symm.trans (π.trans σ)

theorem threeBlockMatchingAdj_diagonal_relabel
    (masks masks' : Fin 3 → BitVec 10) (π σ : Equiv.Perm (Fin 5))
    (hmask : ∀ k i j, oneHighBranchBitAdj (masks k) i j =
      oneHighBranchBitAdj (masks' k) (σ i) (σ j))
    (a b : Fin 3 × Fin 5) :
    threeBlockMatchingAdj masks π a b =
      threeBlockMatchingAdj masks' (threeBlockConjugate π σ) (a.1,σ a.2) (b.1,σ b.2) := by
  simp only [threeBlockMatchingAdj, hmask, threeBlockConjugate, Equiv.trans_apply,
    Equiv.symm_apply_apply, ne_eq, σ.injective.eq_iff]

theorem threeBlockDeficientMatchingAdj_diagonal_relabel
    (masks masks' : Fin 3 → BitVec 10) (π σ : Equiv.Perm (Fin 5)) (d : Fin 5)
    (hmask : ∀ k i j, oneHighBranchBitAdj (masks k) i j =
      oneHighBranchBitAdj (masks' k) (σ i) (σ j))
    (a b : Fin 3 × Fin 5) :
    threeBlockDeficientMatchingAdj masks π d a b =
      threeBlockDeficientMatchingAdj masks' (threeBlockConjugate π σ) (σ d)
        (a.1,σ a.2) (b.1,σ b.2) := by
  simp only [threeBlockDeficientMatchingAdj, hmask, threeBlockConjugate, Equiv.trans_apply,
    Equiv.symm_apply_apply, ne_eq, σ.injective.eq_iff]

end Erdos85
#print axioms Erdos85.threeBlockMatchingAdj_diagonal_relabel
#print axioms Erdos85.threeBlockDeficientMatchingAdj_diagonal_relabel
