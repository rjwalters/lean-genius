import Proofs.Erdos85EncodedExternalBlockCap
import Proofs.Erdos85OrderFortyNineThreeHighTripleCanonicalColorResiduals

namespace Erdos85

/-- The fixed U part of the canonical external-block cap. -/
def threeHighUnionBlockCap (UAdj : Fin 15 → Fin 15 → Bool) : Bool :=
  decide (∀ x k, ((Finset.univ : Finset (Fin 5)).filter
    (fun i => UAdj x ((@finProdFinEquiv 3 5) (k,i)))).card ≤ 1)

/-- Each secondary vertex meets each canonical U block at most once. -/
def threeHighCrossBlockCap (cross : Fin 15 → Fin 8 → Bool) : Bool :=
  decide (∀ j k, ((Finset.univ : Finset (Fin 5)).filter
    (fun i => cross ((@finProdFinEquiv 3 5) (k,i)) j)).card ≤ 1)

private theorem row_card (B : Fin 24 → Fin 24 → Bool) (x : Fin 24) (k : Fin 3) :
    ((threeHighCanonicalRow k).filter (fun y => B x y)).card =
      ((Finset.univ : Finset (Fin 5)).filter
        (fun i => B x (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i))))).card := by
  rw [threeHighCanonicalRow, Finset.filter_image]
  apply Finset.card_image_of_injective
  intro i j h
  have hv := congrArg Fin.val h
  have hp : (@finProdFinEquiv 3 5) (k,i) = (@finProdFinEquiv 3 5) (k,j) := by
    apply Fin.ext
    simpa only [threeHighEmptyUIndex, Fin.val_castAdd] using hv
  exact congrArg Prod.snd ((@finProdFinEquiv 3 5).injective hp)

/-- Factor the full E24 gate into a fixed U check and the cross-column check. -/
theorem threeHighExternalBlockCap_factor
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : Fin 15 → Fin 8 → Bool) :
    encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross) threeHighCanonicalRow =
      (threeHighUnionBlockCap UAdj && threeHighCrossBlockCap cross) := by
  apply Bool.eq_iff_iff.mpr
  simp only [encodedExternalBlockCap, threeHighUnionBlockCap, threeHighCrossBlockCap,
    Bool.and_eq_true, decide_eq_true_eq, row_card]
  constructor
  · intro h
    constructor
    · intro x k
      simpa only [threeHighEmptyAdj, threeHighEmptySplit_u] using h (threeHighEmptyUIndex x) k
    · intro j k
      simpa only [threeHighEmptyAdj, threeHighEmptySplit_u, threeHighEmptySplit_r] using
        h (threeHighEmptyRIndex j) k
  · rintro ⟨hU,hR⟩ x
    refine Fin.addCases (m := 23) (n := 1) (fun y => ?_) (fun y => ?_) x
    · refine Fin.addCases (m := 15) (n := 8) (fun i => ?_) (fun j => ?_) y
      · intro k
        change ((Finset.univ : Finset (Fin 5)).filter (fun a =>
          threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyUIndex i)
            (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,a))))).card ≤ 1
        simpa only [threeHighEmptyAdj, threeHighEmptySplit_u] using hU i k
      · intro k
        change ((Finset.univ : Finset (Fin 5)).filter (fun a =>
          threeHighEmptyAdj UAdj RAdj cross (threeHighEmptyRIndex j)
            (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,a))))).card ≤ 1
        simpa only [threeHighEmptyAdj, threeHighEmptySplit_u, threeHighEmptySplit_r] using hR j k
    · have hy : y = 0 := Subsingleton.elim _ _
      subst y
      intro k
      change ((Finset.univ : Finset (Fin 5)).filter
        (fun i => threeHighEmptyAdj UAdj RAdj cross 23
          (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i))))).card ≤ 1
      simp [threeHighEmptyAdj]

end Erdos85
#print axioms Erdos85.threeHighExternalBlockCap_factor
