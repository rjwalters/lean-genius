import Proofs.Erdos85DeficientNeighborBijection
import Mathlib.Logic.Equiv.Option

/-! Complete a deficient matching by its unique missing pair, recording that exception. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private def erase_equiv_ne {V : Type*} [DecidableEq V] (A : Finset V)
    (a : (↑A : Set V)) : {x : (↑A : Set V) // x ≠ a} ≃ (↑(A.erase a.val) : Set V) where
  toFun x := ⟨x.val.val, Finset.mem_erase.mpr ⟨(fun h => x.property (Subtype.ext h)), x.val.property⟩⟩
  invFun x := ⟨⟨x.val, Finset.mem_of_mem_erase x.property⟩,
    fun h => (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem deficient_neighbor_blocks_completion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcard : A.card = B.card)
    (hA : ∀ x ∈ A, (G.neighborFinset x ∩ B).card ≤ 1)
    (hB : ∀ y ∈ B, (G.neighborFinset y ∩ A).card ≤ 1)
    (hmass : (∑ x ∈ A, (G.neighborFinset x ∩ B).card) + 1 = A.card) :
    ∃ (a : (↑A : Set V)) (b : (↑B : Set V)) (e : (↑A : Set V) ≃ (↑B : Set V)),
      e a = b ∧ ∀ (x : (↑A : Set V)) (y : (↑B : Set V)),
        G.Adj x.val y.val ↔ x ≠ a ∧ e x = y := by
  classical
  obtain ⟨a, ha, b, hb, hza, hzb, e, he⟩ :=
    deficient_neighbor_blocks_equiv G A B hcard hA hB hmass
  let aa : (↑A : Set V) := ⟨a, ha⟩
  let bb : (↑B : Set V) := ⟨b, hb⟩
  let ea := erase_equiv_ne A aa
  let eb := erase_equiv_ne B bb
  let en : {x : (↑A : Set V) // x ≠ aa} ≃ {y : (↑B : Set V) // y ≠ bb} :=
    (ea.trans e).trans eb.symm
  let f : (↑A : Set V) ≃ (↑B : Set V) :=
    ((Equiv.optionSubtypeNe aa).symm.trans (Equiv.optionCongr en)).trans (Equiv.optionSubtypeNe bb)
  have hf0 : f aa = bb := by
    simp [f, Equiv.optionSubtypeNe_symm_self]
  have hf (x : (↑A : Set V)) (hx : x ≠ aa) :
      (f x).val = (e (ea ⟨x, hx⟩)).val := by
    simp [f, Equiv.optionSubtypeNe_symm_of_ne hx, en, eb, erase_equiv_ne]
  have hnoa (y : (↑B : Set V)) : ¬ G.Adj aa.val y.val := by
    intro h
    have hz := (hza a ha).mpr rfl
    have hm : y.val ∈ G.neighborFinset a ∩ B :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a y.val).mpr h, y.property⟩
    rw [Finset.card_eq_zero.mp hz] at hm
    exact Finset.notMem_empty _ hm
  have hnob (x : (↑A : Set V)) : ¬ G.Adj x.val bb.val := by
    intro h
    have hz := (hzb b hb).mpr rfl
    have hm : x.val ∈ G.neighborFinset b ∩ A :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b x.val).mpr h.symm, x.property⟩
    rw [Finset.card_eq_zero.mp hz] at hm
    exact Finset.notMem_empty _ hm
  refine ⟨aa, bb, f, hf0, ?_⟩
  intro x y
  constructor
  · intro hxy
    have hx : x ≠ aa := by intro h; subst x; exact hnoa y hxy
    have hy : y ≠ bb := by intro h; subst y; exact hnob x hxy
    refine ⟨hx, ?_⟩
    have hm : e (ea ⟨x, hx⟩) = eb ⟨y, hy⟩ := (he _ _).mp hxy
    apply Subtype.ext
    rw [hf x hx, hm]
    rfl
  · rintro ⟨hx, rfl⟩
    have hm : G.Adj (ea ⟨x, hx⟩).val (e (ea ⟨x, hx⟩)).val := (he _ _).mpr rfl
    change G.Adj x.val (f x).val
    rw [hf x hx]
    exact hm

end
end Erdos85
#print axioms Erdos85.deficient_neighbor_blocks_completion
