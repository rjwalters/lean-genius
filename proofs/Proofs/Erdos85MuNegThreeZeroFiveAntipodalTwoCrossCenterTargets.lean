import Proofs.Erdos85MuNegThreeZeroFiveAntipodalResidualTypeOneTargets
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalStarPeriodicity

/-! # Two distinct targets routed across antipodal centers -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every antipodal center has two distinct residual type-one targets, and
each is forced by a different coordinate center. -/
theorem h305_antipodal_exists_two_distinct_crossCenter_targets
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j}) :
    ∃ e f : R.edgeFinset, e ≠ f ∧
      e ∈ h305AntipodalResidualTypeOneTargets R Cedge u i a ∧
      f ∈ h305AntipodalResidualTypeOneTargets R Cedge u i a ∧
      ∃ k l : ZMod 8, k ≠ i ∧ k ≠ i + 4 ∧
        l ≠ i ∧ l ≠ i + 4 ∧
        e.1 ∈ h305AntipodalSaturatedStarUnion R u k ∧
        f.1 ∈ h305AntipodalSaturatedStarUnion R u l := by
  classical
  let Q := h305AntipodalResidualTypeOneTargets R Cedge u i a
  have hQ : 2 ≤ Q.card :=
    h305_antipodalResidualTypeOneTargets_card_two_le
      H R Cedge hservice hHreg hRreg hCreg hfree u v huinj hvinj hu
        hdisj hcover humode hvmode a i j hoffset ha
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  have unpack : ∀ b ∈ Q,
      b ∈ shoreTypeEdgeFinset R
          ((Finset.univ : Finset (ZMod 8)).image u) 1 ∧
        b.1 ∉ h305AntipodalSaturatedStarUnion R u i := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hbT := Finset.mem_filter.mp hb'.1
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbT.2⟩, hb'.2⟩
  obtain ⟨k, hki, hki4, hek⟩ :=
    h305_typeOne_outside_antipodalStar_forced_by_other_center
      R u i e (unpack e he).1 (unpack e he).2
  obtain ⟨l, hli, hli4, hfl⟩ :=
    h305_typeOne_outside_antipodalStar_forced_by_other_center
      R u i f (unpack f hf).1 (unpack f hf).2
  exact ⟨e, f, hef, he, hf, k, l, hki, hki4, hli, hli4, hek, hfl⟩

end

end Erdos85

#print axioms
  Erdos85.h305_antipodal_exists_two_distinct_crossCenter_targets
