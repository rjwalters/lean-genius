import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourModeRouting

/-!
# Sign-phase routing for the `mu=-1`, `(k,r)=(1,4)` terminal

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The owner certificates have two sign-phase variants.  An alternating
`+-1` line on `ZMod 8` is determined by its value at coordinate zero, and
the two shore phases are either equal or opposite.  This file packages that
normalization without committing to DIMACS numbering.
-/

namespace Erdos85

noncomputable section

/-- Terminal-facing phase data for two alternating sign shores. -/
def MuNegOneOneFourAlternatingSignPhases
    (su sv : ZMod 8 → ℤ) : Prop :=
  (su 0 = -1 ∨ su 0 = 1) ∧
  (sv 0 = -1 ∨ sv 0 = 1) ∧
  (∀ i, su i = su 0 ↔ ZModEightEvenOffset i) ∧
  (∀ j, sv j = sv 0 ↔ ZModEightEvenOffset j) ∧
  (su 0 = sv 0 ∨ su 0 = -sv 0)

/-- Each shore is its coordinate-zero phase on even coordinates and its
negative on odd coordinates; the two initial phases are equal or opposite.
These are exactly the two sigma variants of each owner certificate family. -/
theorem zmodEight_two_alternating_sign_phase_routing
    (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hflipu : ∀ i, su (i + 1) = -su i)
    (hflipv : ∀ j, sv (j + 1) = -sv j) :
    MuNegOneOneFourAlternatingSignPhases su sv := by
  refine ⟨hsu 0, hsv 0, ?_, ?_, ?_⟩
  · intro i
    simpa using
      (zmodEight_alternating_sign_eq_iff_evenOffset su hsu hflipu 0 i)
  · intro j
    simpa using
      (zmodEight_alternating_sign_eq_iff_evenOffset sv hsv hflipv 0 j)
  · rcases hsu 0 with hu | hu <;> rcases hsv 0 with hv | hv
    · exact Or.inl (hu.trans hv.symm)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl (hu.trans hv.symm)

/-- Add the two sigma phases to an already-normalized owner geometry
package while retaining its signed cross split and canonical shore family. -/
theorem muNegOneOneFour_ownerModes_with_signPhases
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hflipu : ∀ i, su (i + 1) = -su i)
    (hflipv : ∀ j, sv (j + 1) = -sv j)
    (howner : MuNegOneOneFourCrossExteriorSplit R u v su sv ∧
      MuNegOneOneFourCanonicalShoreModes R u v) :
    MuNegOneOneFourCrossExteriorSplit R u v su sv ∧
      MuNegOneOneFourCanonicalShoreModes R u v ∧
      MuNegOneOneFourAlternatingSignPhases su sv := by
  exact ⟨howner.1, howner.2,
    zmodEight_two_alternating_sign_phase_routing su sv hsu hsv hflipu hflipv⟩

end

end Erdos85

#print axioms Erdos85.zmodEight_two_alternating_sign_phase_routing
#print axioms Erdos85.muNegOneOneFour_ownerModes_with_signPhases
