import Proofs.Erdos85ThreeHighCrossMargins
import Proofs.Erdos85ThreeHighExternalBlockFactorization
import Proofs.Erdos85ThreeHighExternalPrefixPruning

namespace Erdos85

def threeHighCrossColumns (cross : ThreeHighCross) (j : Fin 8) : Finset (Fin 15) :=
  Finset.univ.filter fun i => cross i j

def threeHighCrossOfColumns (columns : Fin 8 → Finset (Fin 15)) : ThreeHighCross :=
  fun i j => decide (i ∈ columns j)

theorem threeHighCrossOfColumns_columns (cross : ThreeHighCross) :
    threeHighCrossOfColumns (threeHighCrossColumns cross) = cross := by
  funext i j
  simp [threeHighCrossOfColumns,threeHighCrossColumns]

def threeHighCrossColumnDomain (R : Fin 8 → Fin 8 → Bool) (j : Fin 8) :
    Finset (Finset (Fin 15)) :=
  Finset.univ.filter fun S =>
    S.card + encodedRowDegree (R j) + (if j.val < 6 then 1 else 0) = 4 ∧
      ∀ k : Fin 3, (S.filter fun i => ((@finProdFinEquiv 3 5).symm i).1 = k).card ≤ 1

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossColumnDomain_complete
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hcap : threeHighCrossBlockCap cross = true) (j : Fin 8) :
    threeHighCrossColumns cross j ∈ threeHighCrossColumnDomain R j := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,(threeHighCrossDomain_margins U R cross hc).2 j,?_⟩
  intro k
  unfold threeHighCrossBlockCap at hcap
  have hk := of_decide_eq_true hcap j k
  have he : (threeHighCrossColumns cross j).filter
      (fun i => ((@finProdFinEquiv 3 5).symm i).1 = k) =
      (Finset.univ.filter fun a : Fin 5 => cross ((@finProdFinEquiv 3 5) (k,a)) j).image
        (fun a => (@finProdFinEquiv 3 5) (k,a)) := by
    ext i
    obtain ⟨⟨l,a⟩,rfl⟩ := (@finProdFinEquiv 3 5).surjective i
    simp only [threeHighCrossColumns,Finset.mem_filter,Finset.mem_univ,true_and,
      Equiv.symm_apply_apply,Finset.mem_image]
    constructor
    · rintro ⟨hi,rfl⟩
      exact ⟨a,hi,rfl⟩
    · rintro ⟨b,hb,he⟩
      have hp := (@finProdFinEquiv 3 5).injective he
      cases hp
      exact ⟨hb,rfl⟩
  rw [he]
  exact (Finset.card_image_le).trans hk

end Erdos85
#print axioms Erdos85.threeHighCrossOfColumns_columns
#print axioms Erdos85.threeHighCrossColumnDomain_complete
