import Proofs.Erdos85ThreeSeparatorExceptionalDefectNeighborhood
import Proofs.Erdos85ThreeSeparatorPositiveSpikeSmallSideLocation

/-! # Location pressure on the exceptional-point matching image -/

open Finset

namespace Erdos85

/-- If a q-point matching image lies in `K`, while at most four points of K
can lie off `Y`, then at least `q-4` image points lie in `Y`. -/
theorem exceptionalImage_card_inter_largeShore_ge_sub_four
    {V : Type*} [DecidableEq V]
    (Q K Y S : Finset V) (q : ℕ)
    (hQK : Q ⊆ K) (hQcard : Q.card = q)
    (hKcover : K ⊆ Y ∪ S) (hKsmall : (K ∩ S).card ≤ 4) :
    q - 4 ≤ (Q ∩ Y).card := by
  have houtside : Q \ Y ⊆ K ∩ S := by
    intro z hz
    have hzQ := (Finset.mem_sdiff.mp hz).1
    have hzNotY := (Finset.mem_sdiff.mp hz).2
    have hzK := hQK hzQ
    have hzCover := hKcover hzK
    refine Finset.mem_inter.mpr ⟨hzK, ?_⟩
    rcases Finset.mem_union.mp hzCover with hzY | hzS
    · exact False.elim (hzNotY hzY)
    · exact hzS
  have houtsideCard : (Q \ Y).card ≤ 4 :=
    (Finset.card_le_card houtside).trans hKsmall
  have hsplit := Finset.card_sdiff_add_card_inter Q Y
  rw [hQcard] at hsplit
  omega

/-- Three-separator spelling of the B17 image-location bound. -/
theorem threeSeparator_exceptionalImage_largeShore_lower
    {V : Type*} [DecidableEq V]
    (Q K X Y W : Finset V) (q : ℕ)
    (hQK : Q ⊆ K) (hQcard : Q.card = q)
    (hKcover : K ⊆ Y ∪ (X ∪ W))
    (hSmall : (K ∩ (X ∪ W)).card ≤ 4) :
    q - 4 ≤ (Q ∩ Y).card :=
  exceptionalImage_card_inter_largeShore_ge_sub_four
    Q K Y (X ∪ W) q hQK hQcard hKcover hSmall

#print axioms exceptionalImage_card_inter_largeShore_ge_sub_four
#print axioms threeSeparator_exceptionalImage_largeShore_lower

end Erdos85
