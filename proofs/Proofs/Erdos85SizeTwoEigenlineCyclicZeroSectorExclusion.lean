import Proofs.Erdos85SizeTwoEigenlineTriangleFreeCyclicAttachment
import Proofs.Erdos85MuThreeKSymmetryNativeClassification

/-!
# Native exclusion of every q=8 reflection-cyclic sector

The cyclic and mixed-grid APIs use extensionally identical cell subtypes but
different `Fintype` instances.  We transport the graph through the canonical
equivalence, making the finite-enumeration change explicit and harmless.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private instance ambientRelDecidable (q : ℕ) :
    DecidableRel (sizeTwoCyclicAmbientRel q) := fun x y => by
  unfold sizeTwoCyclicAmbientRel
  infer_instance

private instance reflectionRelDecidable (q : ℕ) (a : ZMod q) :
    DecidableRel (sizeTwoReflectionRel q a) := fun x y => by
  unfold sizeTwoReflectionRel
  infer_instance

def zmodEightEquivFin : ZMod 8 ≃ Fin 8 where
  toFun z := ⟨z.val, z.val_lt⟩
  invFun x := (x.val : ZMod 8)
  left_inv z := ZMod.natCast_zmod_val z
  right_inv x := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt x.isLt

def cyclicExteriorMixedEquiv (q : ℕ) [NeZero q] (a : ZMod q) :
    sizeTwoCyclicExteriorCell q a ≃ muThreeMixedCell (sizeTwoReflectionRel q a) where
  toFun u := ⟨u.1, u.2⟩
  invFun u := ⟨u.1, u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem cyclicExteriorMixedEquiv_apply_val
    (q : ℕ) [NeZero q] (a : ZMod q)
    (u : sizeTwoCyclicExteriorCell q a) :
    (cyclicExteriorMixedEquiv q a u).1 = u.1 := rfl

@[simp] theorem cyclicExteriorMixedEquiv_symm_val
    (q : ℕ) [NeZero q] (a : ZMod q)
    (u : muThreeMixedCell (sizeTwoReflectionRel q a)) :
    ((cyclicExteriorMixedEquiv q a).symm u).1 = u.1 := rfl

def cyclicExactMixedGraph
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a) :
    SimpleGraph (muThreeMixedCell (sizeTwoReflectionRel q a)) where
  Adj u v := code.graph.Adj
    ((cyclicExteriorMixedEquiv q a).symm u)
    ((cyclicExteriorMixedEquiv q a).symm v)
  symm := ⟨by
    intro u v h
    exact code.graph.adj_symm h⟩
  loopless := ⟨by
    intro u h
    exact code.graph.loopless.irrefl _ h⟩

private instance cyclicExactGraphDecidable
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a) :
    DecidableRel code.graph.Adj := Classical.decRel _

private instance cyclicExactMixedGraphDecidable
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a) :
    DecidableRel (cyclicExactMixedGraph code).Adj := Classical.decRel _

theorem cyclicExactMixedGraph_filter_card
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a)
    (u : muThreeMixedCell (sizeTwoReflectionRel q a))
    (P : muThreeMixedCell (sizeTwoReflectionRel q a) → Prop)
    [DecidablePred P] :
    (((cyclicExactMixedGraph code).neighborFinset u).filter P).card =
      ((code.graph.neighborFinset ((cyclicExteriorMixedEquiv q a).symm u)).filter
        fun v => P (cyclicExteriorMixedEquiv q a v)).card := by
  classical
  apply Finset.card_bij
      (fun v _ => (cyclicExteriorMixedEquiv q a).symm v)
  · intro v hv
    apply Finset.mem_filter.mpr
    have hv' := Finset.mem_filter.mp hv
    exact ⟨(code.graph.mem_neighborFinset _ _).mpr
      (by simpa [cyclicExactMixedGraph] using hv'.1), by simpa using hv'.2⟩
  · intro v₁ _ v₂ _ h
    exact (cyclicExteriorMixedEquiv q a).symm.injective h
  · intro v hv
    refine ⟨cyclicExteriorMixedEquiv q a v, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    have hv' := Finset.mem_filter.mp hv
    exact ⟨((cyclicExactMixedGraph code).mem_neighborFinset _ _).mpr
      (by simpa [cyclicExactMixedGraph] using hv'.1),
      by simpa using hv'.2⟩

theorem sizeTwoCyclicAmbientRel_iff_eq_sub_one
    (q : ℕ) (x y : ZMod q) :
    sizeTwoCyclicAmbientRel q x y ↔ y = x ∨ y = x - 1 := by
  constructor
  · rintro (h | h)
    · left
      have hz := congrArg (fun z : ZMod q => z + x) h
      simpa [sizeTwoCyclicAmbientRel] using hz
    · right
      have hz := congrArg (fun z : ZMod q => z + x) h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
  · rintro (rfl | rfl)
    · left; simp
    · right; ring

def sizeTwoCyclicExact_to_muThreeMixedGridCode_eight
    (a : ZMod 8) (code : SizeTwoCyclicExactPermutationCode 8 a) :
    MuThreeMixedGridCode
      (sizeTwoCyclicAmbientRel 8)
      (sizeTwoReflectionRel 8 a)
      (cyclicExactMixedGraph code) where
  card_left := by decide
  card_right := by decide
  H_twoRegular := by
    constructor <;> intro x <;> fin_cases x <;> native_decide
  K_twoRegular := by
    fin_cases a <;>
      constructor <;> intro x <;> fin_cases x <;> native_decide
  cycle_compatible := by
    intro c
    fin_cases a
    · left
      intro x y hxy hx
      revert hxy
      fin_cases x <;> fin_cases y <;> native_decide
    · right
      intro x y hxy hx hK
      revert hxy hK
      fin_cases x <;> fin_cases y <;> native_decide
    · right
      intro x y hxy hx hK
      revert hxy hK
      fin_cases x <;> fin_cases y <;> native_decide
    · right
      intro x y hxy hx hK
      revert hxy hK
      fin_cases x <;> fin_cases y <;> native_decide
    · right
      intro x y hxy hx hK
      revert hxy hK
      fin_cases x <;> fin_cases y <;> native_decide
    · right
      intro x y hxy hx hK
      revert hxy hK
      fin_cases x <;> fin_cases y <;> native_decide
    · right
      intro x y hxy hx hK
      revert hxy hK
      fin_cases x <;> fin_cases y <;> native_decide
    · left
      intro x y hxy hx
      revert hxy
      fin_cases x <;> fin_cases y <;> native_decide
  row_hit := by
    intro u x
    rw [cyclicExactMixedGraph_filter_card]
    have hhit := code.graph_row_hit ((cyclicExteriorMixedEquiv 8 a).symm u) x
    simpa [cyclicExteriorMixedEquiv,
      sizeTwoCyclicAmbientRel_iff_eq_sub_one] using hhit
  column_hit := by
    intro u y
    rw [cyclicExactMixedGraph_filter_card]
    have hhit := code.graph_column_hit ((cyclicExteriorMixedEquiv 8 a).symm u) y
    have hcond : sizeTwoCyclicAmbientRel 8 u.1.1 y ↔
        u.1.1 = y ∨ u.1.1 = y + 1 := by
      constructor
      · intro h
        rcases (sizeTwoCyclicAmbientRel_iff_eq_sub_one 8 u.1.1 y).mp h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h]; ring)
      · rintro (h | h)
        · exact (sizeTwoCyclicAmbientRel_iff_eq_sub_one 8 u.1.1 y).mpr (Or.inl h.symm)
        · apply (sizeTwoCyclicAmbientRel_iff_eq_sub_one 8 u.1.1 y).mpr
          right
          rw [h]
          ring
    simpa [cyclicExteriorMixedEquiv, hcond] using hhit
  rook := by
    intro u v w huv huw hvw
    constructor
    · intro hrow
      apply hvw
      apply (cyclicExteriorMixedEquiv 8 a).symm.injective
      have huv' : code.graph.Adj
          ((cyclicExteriorMixedEquiv 8 a).symm u)
          ((cyclicExteriorMixedEquiv 8 a).symm v) := by
        simpa [cyclicExactMixedGraph] using huv
      have huw' : code.graph.Adj
          ((cyclicExteriorMixedEquiv 8 a).symm u)
          ((cyclicExteriorMixedEquiv 8 a).symm w) := by
        simpa [cyclicExactMixedGraph] using huw
      have hcard := code.graph_row_hit
        ((cyclicExteriorMixedEquiv 8 a).symm u) v.1.1
      have hvMem := (code.graph.mem_neighborFinset _ _).mpr huv'
      have hwMem := (code.graph.mem_neighborFinset _ _).mpr huw'
      have : ((cyclicExteriorMixedEquiv 8 a).symm v) =
          ((cyclicExteriorMixedEquiv 8 a).symm w) := by
        by_contra hne
        let F := (code.graph.neighborFinset
          ((cyclicExteriorMixedEquiv 8 a).symm u)).filter fun z => z.1.1 = v.1.1
        have hvF : (cyclicExteriorMixedEquiv 8 a).symm v ∈ F := by
          exact Finset.mem_filter.mpr ⟨hvMem, rfl⟩
        have hwF : (cyclicExteriorMixedEquiv 8 a).symm w ∈ F := by
          exact Finset.mem_filter.mpr ⟨hwMem, by
            simpa [cyclicExteriorMixedEquiv] using hrow.symm⟩
        have htwo : 1 < F.card := Finset.one_lt_card.mpr ⟨_, hvF, _, hwF, hne⟩
        change F.card = _ at hcard
        rw [hcard] at htwo
        split at htwo <;> omega
      exact this
    · intro hcol
      apply hvw
      apply (cyclicExteriorMixedEquiv 8 a).symm.injective
      have huv' : code.graph.Adj
          ((cyclicExteriorMixedEquiv 8 a).symm u)
          ((cyclicExteriorMixedEquiv 8 a).symm v) := by
        simpa [cyclicExactMixedGraph] using huv
      have huw' : code.graph.Adj
          ((cyclicExteriorMixedEquiv 8 a).symm u)
          ((cyclicExteriorMixedEquiv 8 a).symm w) := by
        simpa [cyclicExactMixedGraph] using huw
      have hcard := code.graph_column_hit
        ((cyclicExteriorMixedEquiv 8 a).symm u) v.1.2
      have hvMem := (code.graph.mem_neighborFinset _ _).mpr huv'
      have hwMem := (code.graph.mem_neighborFinset _ _).mpr huw'
      have : ((cyclicExteriorMixedEquiv 8 a).symm v) =
          ((cyclicExteriorMixedEquiv 8 a).symm w) := by
        by_contra hne
        let F := (code.graph.neighborFinset
          ((cyclicExteriorMixedEquiv 8 a).symm u)).filter fun z => z.1.2 = v.1.2
        have hvF : (cyclicExteriorMixedEquiv 8 a).symm v ∈ F := by
          exact Finset.mem_filter.mpr ⟨hvMem, rfl⟩
        have hwF : (cyclicExteriorMixedEquiv 8 a).symm w ∈ F := by
          exact Finset.mem_filter.mpr ⟨hwMem, by
            simpa [cyclicExteriorMixedEquiv] using hcol.symm⟩
        have htwo : 1 < F.card := Finset.one_lt_card.mpr ⟨_, hvF, _, hwF, hne⟩
        change F.card = _ at hcard
        rw [hcard] at htwo
        split at htwo <;> omega
      exact this
  c4Free := by
    rintro ⟨f, hf, hadj⟩
    apply code.graph_not_containsC4
    refine ⟨fun i => (cyclicExteriorMixedEquiv 8 a).symm (f i),
      (cyclicExteriorMixedEquiv 8 a).symm.injective.comp hf, ?_⟩
    intro i j hij
    simpa [cyclicExactMixedGraph] using hadj i j hij

theorem sizeTwoCyclicExactPermutationCode_eight_isEmpty (a : ZMod 8) :
    IsEmpty (SizeTwoCyclicExactPermutationCode 8 a) := by
  constructor
  intro code
  let H := sizeTwoCyclicAmbientRel 8
  let K := sizeTwoReflectionRel 8 a
  have hcoord : ∀ x y,
      mu3NormalizeRelation zmodEightEquivFin zmodEightEquivFin H x y ↔
        y.val ∈ mu3H16Row x.val := by
    intro x y
    fin_cases x <;> fin_cases y <;> native_decide
  let classification : MuThreeKSymmetryClassification H :=
    muThreeKSymmetryClassification_H16_native
      zmodEightEquivFin zmodEightEquivFin H hcoord
  exact false_of_muThreeMixedGridCode_of_kSymmetryClassification
    H K (cyclicExactMixedGraph code) classification
      (sizeTwoCyclicExact_to_muThreeMixedGridCode_eight a code)

theorem sizeTwoCyclicExactPermutationCode_zero_eight_isEmpty :
    IsEmpty (SizeTwoCyclicExactPermutationCode 8 (0 : ZMod 8)) :=
  sizeTwoCyclicExactPermutationCode_eight_isEmpty 0

end

end Erdos85

#print axioms Erdos85.cyclicExactMixedGraph_filter_card
#print axioms Erdos85.sizeTwoCyclicExact_to_muThreeMixedGridCode_eight
#print axioms Erdos85.sizeTwoCyclicExactPermutationCode_eight_isEmpty
#print axioms Erdos85.sizeTwoCyclicExactPermutationCode_zero_eight_isEmpty
