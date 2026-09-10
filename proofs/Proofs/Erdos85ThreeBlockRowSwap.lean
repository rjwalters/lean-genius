import Proofs.Erdos85ThreeBlockCandidateDomains

namespace Erdos85

def threeBlockSwapRows : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Swapping the two noncanonical rows inverts their cross permutation. -/
theorem threeBlockMatchingAdj_swap_rows
    (m : Fin 3 → BitVec 10) (π : Equiv.Perm (Fin 5)) (p q : Fin 3 × Fin 5) :
    threeBlockMatchingAdj m π p q =
      threeBlockMatchingAdj (fun k => m (threeBlockSwapRows k)) π.symm
        (threeBlockSwapRows p.1,p.2) (threeBlockSwapRows q.1,q.2) := by
  rcases p with ⟨a,i⟩
  rcases q with ⟨b,j⟩
  fin_cases a <;> fin_cases b <;>
    simp [threeBlockMatchingAdj, threeBlockSwapRows, Equiv.swap_apply_def,
      Equiv.eq_symm_apply, eq_comm]

private theorem deficient_pair_reverse (π : Equiv.Perm (Fin 5)) (d i j : Fin 5) :
    decide (i ≠ d ∧ π i = j) = decide (j ≠ π d ∧ π.symm j = i) := by
  by_cases h : π i = j
  · subst j
    simp
  · have hh : π.symm j ≠ i := by
      intro he
      have := congrArg π he
      simp only [Equiv.apply_symm_apply] at this
      exact h this.symm
    simp [h,hh]

/-- The missing source moves from d to pi(d) when the deficient edge is reversed. -/
theorem threeBlockDeficientMatchingAdj_swap_rows
    (m : Fin 3 → BitVec 10) (π : Equiv.Perm (Fin 5)) (d : Fin 5)
    (p q : Fin 3 × Fin 5) :
    threeBlockDeficientMatchingAdj m π d p q =
      threeBlockDeficientMatchingAdj (fun k => m (threeBlockSwapRows k)) π.symm (π d)
        (threeBlockSwapRows p.1,p.2) (threeBlockSwapRows q.1,q.2) := by
  rcases p with ⟨a,i⟩
  rcases q with ⟨b,j⟩
  fin_cases a <;> fin_cases b <;>
    simp only [threeBlockDeficientMatchingAdj, threeBlockSwapRows, Equiv.swap_apply_def]
  all_goals first | rfl | exact deficient_pair_reverse π d i j | exact deficient_pair_reverse π d j i

end Erdos85
#print axioms Erdos85.threeBlockMatchingAdj_swap_rows
#print axioms Erdos85.threeBlockDeficientMatchingAdj_swap_rows
