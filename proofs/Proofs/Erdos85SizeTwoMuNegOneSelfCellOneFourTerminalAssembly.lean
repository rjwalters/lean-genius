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

/-- Graph-facing elimination socket for the unique `mu=-1` self-switch
cell.  Once the three owner-mode terminals are supplied, the same refined
witness produced by the aligned ledger must have switch target different
from `-1`. -/
theorem orderSixtyFour_sizeTwo_muNegOne_refined_switch_ne_self_of_oneFour_terminals
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hTFTF : let R := exteriorPairGraph G c.supp
      MuNegOneOneFourCrossExteriorSplit R u v
          (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) →
        MuNegOneOneFourAlternatingSignPhases
          (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) →
        MuNegOneOneFourTfShoreMode R u →
        MuNegOneOneFourTfShoreMode R v → False)
    (hTFtri : let R := exteriorPairGraph G c.supp
      ∀ (w x : ZMod 8 → c.supp) (sw sx : ZMod 8 → ℤ),
        MuNegOneOneFourCrossExteriorSplit R w x sw sx →
        MuNegOneOneFourAlternatingSignPhases sw sx →
        MuNegOneOneFourTfShoreMode R w →
        MuNegOneOneFourTriangleShoreMode R x → False)
    (htritri : let R := exteriorPairGraph G c.supp
      MuNegOneOneFourCrossExteriorSplit R u v
          (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) →
        MuNegOneOneFourAlternatingSignPhases
          (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) →
        MuNegOneOneFourTriangleShoreMode R u →
        MuNegOneOneFourTriangleShoreMode R v → False) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ, MuNegOneRefinedSectorCells N₁ N₂ k r ∧
      sizeTwoMuSwitchTarget (-1) k r ≠ -1 := by
  classical
  dsimp only at hTFTF hTFtri htritri ⊢
  obtain ⟨k, r, hcell, hne | hgeom⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_refined_switch_or_completeExteriorGeometry
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  · exact ⟨k, r, hcell, hne⟩
  · have hfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
    have hflip
        (w : ZMod 8 → c.supp)
        (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
          {w (z - 1), w (z + 1)}) :
        ∀ i, s (w (i + 1)).1 = -s (w i).1 := by
      intro i
      have hadj : (G.induce c.supp).Adj (w i) (w (i + 1)) := by
        rw [← (G.induce c.supp).mem_neighborFinset, hw]
        simp
      have hmem : (w (i + 1)).1 ∈ componentNeighborFinset G
          (secondOrderDefectGraph G) c (w i).1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (w (i + 1)).2⟩
      exact (internal_alternation G hfree (by omega) hreg hcard c hc s
        hs_in hs_out hfull (w i).2).2 _ hmem
    exact False.elim <|
      muNegOneOneFour_completeExteriorGeometry_false_of_three_mode_terminals
        (exteriorPairGraph G c.supp) u v
        (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
        (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
        (hflip u hu) (hflip v hv) hgeom hTFTF hTFtri htritri

end


end Erdos85

#print axioms Erdos85.muNegOneOneFour_ownerGeometry_false_of_three_mode_terminals
#print axioms Erdos85.muNegOneOneFour_completeExteriorGeometry_false_of_three_mode_terminals
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_refined_switch_ne_self_of_oneFour_terminals
