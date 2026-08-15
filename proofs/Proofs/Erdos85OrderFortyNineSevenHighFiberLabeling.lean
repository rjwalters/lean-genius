import Proofs.Erdos85OrderFortyNineSevenHighLabelingBridge

/-!
# Fiber construction for seven-high canonical labelings

An exact high label together with the labeled high-support set is a complete
vertex key.  Equality of all graph-side and mask-side key-fiber cardinalities
therefore constructs the required permutation of all 49 vertices.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighLabeledSupport
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49) : Finset (Fin 7) :=
  (finsetInSubtype (orderFortyNineHighVertices G)
    (orderFortyNineHighSupport G x)).map e.toEmbedding

theorem sevenHighLabeledSupport_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49) :
    (sevenHighLabeledSupport G e x).card =
      (orderFortyNineHighSupport G x).card := by
  simp only [sevenHighLabeledSupport, Finset.card_map]
  apply card_finsetInSubtype_of_subset
  intro v hv
  exact (Finset.mem_inter.mp hv).2

def sevenHighMaskSupport (masks : Array Nat) (i : Fin 49) :
    Finset (Fin 7) :=
  Finset.univ.filter fun w =>
    (orderFortyNineSupportMask masks i).getLsbD w.val

def sevenHighGraphAlignedKey
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (x : Fin 49) : Option (Fin 7) × Finset (Fin 7) :=
  (if hx : x ∈ orderFortyNineHighVertices G then some (e ⟨x, hx⟩) else none,
    sevenHighLabeledSupport G e x)

def sevenHighMaskAlignedKey (masks : Array Nat) (i : Fin 49) :
    Option (Fin 7) × Finset (Fin 7) :=
  (if hi : i.val < 7 then some ⟨i.val, hi⟩ else none,
    sevenHighMaskSupport masks i)

theorem exists_sevenHigh_keyAlignedLabeling_of_fiberCardEq
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat)
    (hcard : ∀ key : Option (Fin 7) × Finset (Fin 7),
      Fintype.card {x : Fin 49 // sevenHighGraphAlignedKey G e x = key} =
      Fintype.card {i : Fin 49 // sevenHighMaskAlignedKey masks i = key}) :
    ∃ E : Equiv.Perm (Fin 49), ∀ x,
      sevenHighMaskAlignedKey masks (E x) =
        sevenHighGraphAlignedKey G e x := by
  let E := equivOfFiberCardEq
    (sevenHighGraphAlignedKey G e) (sevenHighMaskAlignedKey masks) hcard
  exact ⟨E, fun x => equivOfFiberCardEq_map _ _ hcard x⟩

theorem sevenHigh_keyAlignedLabeling_support
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) (x : Fin 49) :
    sevenHighMaskSupport masks (E x) = sevenHighLabeledSupport G e x := by
  exact congrArg Prod.snd (hE x)

theorem sevenHigh_keyAlignedLabeling_high_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) (x : Fin 49) :
    (E x).val < 7 ↔ x ∈ orderFortyNineHighVertices G := by
  have hfirst := congrArg Prod.fst (hE x)
  by_cases hi : (E x).val < 7 <;>
    by_cases hx : x ∈ orderFortyNineHighVertices G <;>
    simp [sevenHighMaskAlignedKey, sevenHighGraphAlignedKey, hi, hx] at hfirst ⊢

theorem sevenHigh_keyAlignedLabeling_high_image
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (masks : Array Nat) (E : Equiv.Perm (Fin 49))
    (hE : ∀ x, sevenHighMaskAlignedKey masks (E x) =
      sevenHighGraphAlignedKey G e x) (w : Fin 7) :
    E (e.symm w).1 = ⟨w.val, by omega⟩ := by
  have hfirst := congrArg Prod.fst (hE (e.symm w).1)
  have hsome :
      (if hi : (E (e.symm w).1).val < 7
        then some (⟨(E (e.symm w).1).val, hi⟩ : Fin 7)
        else none) = some w := by
    simpa [sevenHighMaskAlignedKey, sevenHighGraphAlignedKey] using hfirst
  by_cases hi : (E (e.symm w).1).val < 7
  · simp [hi] at hsome
    apply Fin.ext
    simpa using congrArg Fin.val hsome
  · simp [hi] at hsome

end

end Erdos85
