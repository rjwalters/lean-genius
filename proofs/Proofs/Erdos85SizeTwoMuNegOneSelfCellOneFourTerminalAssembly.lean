import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourSignPhaseRouting

/-!
# Three-family terminal assembly for the `mu=-1`, `(k,r)=(1,4)` cell

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

This is the certificate-independent final consumer.  Contradictions for the
TF/TF, canonically oriented TF/triangle, and triangle/triangle owner models
rule out the complete geometry socket.  The reverse mixed orientation is
handled here by swapping shores, cross rows/columns, and sign phases.
-/

namespace Erdos85

noncomputable section

theorem muNegOneOneFour_alternatingSignPhases_swap
    (su sv : ZMod 8 → ℤ) :
    MuNegOneOneFourAlternatingSignPhases su sv ↔
      MuNegOneOneFourAlternatingSignPhases sv su := by
  constructor
  · rintro ⟨hsu, hsv, hpu, hpv, hphase⟩
    refine ⟨hsv, hsu, hpv, hpu, ?_⟩
    rcases hphase with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)
  · rintro ⟨hsv, hsu, hpv, hpu, hphase⟩
    refine ⟨hsu, hsv, hpu, hpv, ?_⟩
    rcases hphase with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)

/-- Abstract three-certificate capstone.  The mixed terminal is quantified
over the two ordered shores, so a single canonical TF/triangle theorem serves
both orientations. -/
theorem muNegOneOneFour_ownerGeometry_false_of_three_mode_terminals
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ)
    (howner : MuNegOneOneFourCrossExteriorSplit R u v su sv ∧
      MuNegOneOneFourCanonicalShoreModes R u v ∧
      MuNegOneOneFourAlternatingSignPhases su sv)
    (hTFTF : MuNegOneOneFourCrossExteriorSplit R u v su sv →
      MuNegOneOneFourAlternatingSignPhases su sv →
      MuNegOneOneFourTfShoreMode R u →
      MuNegOneOneFourTfShoreMode R v → False)
    (hTFtri : ∀ (w x : ZMod 8 → X) (sw sx : ZMod 8 → ℤ),
      MuNegOneOneFourCrossExteriorSplit R w x sw sx →
      MuNegOneOneFourAlternatingSignPhases sw sx →
      MuNegOneOneFourTfShoreMode R w →
      MuNegOneOneFourTriangleShoreMode R x → False)
    (htritri : MuNegOneOneFourCrossExteriorSplit R u v su sv →
      MuNegOneOneFourAlternatingSignPhases su sv →
      MuNegOneOneFourTriangleShoreMode R u →
      MuNegOneOneFourTriangleShoreMode R v → False) : False := by
  rcases howner with ⟨hcross, hmodes, hphase⟩
  rcases hmodes with htt | hmixed | hff
  · exact hTFTF hcross hphase htt.1 htt.2
  · rcases muNegOneOneFour_mixed_mode_normalize R u v su sv hcross hmixed with
        huv | hvu
    · exact hTFtri u v su sv huv.2.2 hphase huv.1 huv.2.1
    · exact hTFtri v u sv su hvu.2.2
        ((muNegOneOneFour_alternatingSignPhases_swap su sv).mp hphase)
        hvu.1 hvu.2.1
  · exact htritri hcross hphase hff.1 hff.2

/-- Feed the complete exterior-geometry socket and its alternating sign laws
directly into the abstract three-certificate capstone. -/
theorem muNegOneOneFour_completeExteriorGeometry_false_of_three_mode_terminals
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hflipu : ∀ i, su (i + 1) = -su i)
    (hflipv : ∀ j, sv (j + 1) = -sv j)
    (hgeom : MuNegOneOneFourShoreExteriorModel R u ∧
      MuNegOneOneFourShoreExteriorModel R v ∧
      MuNegOneOneFourCrossExteriorSplit R u v su sv)
    (hTFTF : MuNegOneOneFourCrossExteriorSplit R u v su sv →
      MuNegOneOneFourAlternatingSignPhases su sv →
      MuNegOneOneFourTfShoreMode R u →
      MuNegOneOneFourTfShoreMode R v → False)
    (hTFtri : ∀ (w x : ZMod 8 → X) (sw sx : ZMod 8 → ℤ),
      MuNegOneOneFourCrossExteriorSplit R w x sw sx →
      MuNegOneOneFourAlternatingSignPhases sw sx →
      MuNegOneOneFourTfShoreMode R w →
      MuNegOneOneFourTriangleShoreMode R x → False)
    (htritri : MuNegOneOneFourCrossExteriorSplit R u v su sv →
      MuNegOneOneFourAlternatingSignPhases su sv →
      MuNegOneOneFourTriangleShoreMode R u →
      MuNegOneOneFourTriangleShoreMode R v → False) : False := by
  have hmode :=
    muNegOneOneFour_completeExteriorGeometry_modeRouting R u v su sv hgeom
  have howner := muNegOneOneFour_ownerModes_with_signPhases R u v su sv
    hsu hsv hflipu hflipv hmode
  exact muNegOneOneFour_ownerGeometry_false_of_three_mode_terminals
    R u v su sv howner hTFTF hTFtri htritri

end


end Erdos85

#print axioms Erdos85.muNegOneOneFour_ownerGeometry_false_of_three_mode_terminals
#print axioms Erdos85.muNegOneOneFour_completeExteriorGeometry_false_of_three_mode_terminals
