import Proofs.Erdos85NeighborStarWitnessBlockFlipParity
import Proofs.Erdos85RelayShoreWitnessPricedBoundary
import Proofs.Erdos85RelayWitnessBoundaryEndpointGeometry

/-!
# Canonical relay occurrences are neighbor-star flip representatives

For the full neighbor-star relay, orienting a relay cut from a shore `U`
records exactly one `U`-side representative of a mate pair crossing `U`.
C4-freeness makes its star witness canonical, so restricting the occurrence
labels to a block `R` is equivalent to summing those representatives over
`R`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A full-relay edge's canonical witness recovers the mate equation in
either orientation. -/
theorem fullRelayShoreOccurrenceWitness_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (U : Finset V) (o : Σ _ : {u : V // u ∈ U}, V)
    (ho : o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) U) :
    let y := fullRelayShoreOccurrenceWitness A hfree mate
      hclosed hinvol hfixed U o
    A.Adj y o.1.1 ∧ mate y o.1.1 = o.2 := by
  dsimp only
  have hcut := Finset.mem_sigma.mp ho
  have hcut' := Finset.mem_sdiff.mp hcut.2
  have hP : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).Adj o.1.1 o.2 := by
    simpa [SimpleGraph.mem_neighborFinset] using hcut'.1
  obtain ⟨w, hw, hmw⟩ := hP
  have hlabel := fullRelayShoreOccurrenceWitness_adj_endpoints
    A hfree mate hclosed hinvol hfixed U o ho
  have hwo2 : A.Adj w o.2 := by rw [← hmw]; exact hclosed w o.1.1 hw
  have hne : o.1.1 ≠ o.2 := by
    rw [← hmw]
    exact (hfixed w o.1.1 hw).symm
  have hyw : fullRelayShoreOccurrenceWitness A hfree mate
      hclosed hinvol hfixed U o = w :=
    commonNeighbor_unique_of_c4Free hfree hne
      hlabel.1.symm hlabel.2.symm hw.symm hwo2.symm
  rw [hyw]
  exact ⟨hw, hmw⟩

/-- **Canonical witness-block bijection.**  Labeled outgoing occurrences of
the full relay are counted exactly by the corresponding neighbor-star flip
representatives. -/
theorem labeled_fullRelayShoreOccurrenceBlock_card_eq_sum_neighborStarFlip
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (U R : Finset V) :
    (labeledOccurrenceBlock
      (shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) U)
      (fullRelayShoreOccurrenceWitness A hfree mate
        hclosed hinvol hfixed U) R).card =
      ∑ y ∈ R, (neighborStarFlipRepresentatives A mate y U).card := by
  let P := witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed
  let label := fullRelayShoreOccurrenceWitness A hfree mate
    hclosed hinvol hfixed U
  let S := labeledOccurrenceBlock (shoreGraphCutOccurrences P U) label R
  let Q := R.sigma fun y => neighborStarFlipRepresentatives A mate y U
  have hcard : S.card = Q.card := by
    apply Finset.card_bij (s := S) (t := Q)
      (fun o _ => ⟨label o, o.1.1⟩)
    · intro o ho
      have ho' := (Finset.mem_filter.mp ho)
      have hspec := fullRelayShoreOccurrenceWitness_spec
        A hfree mate hclosed hinvol hfixed U o ho'.1
      have hcut := Finset.mem_sigma.mp ho'.1
      have hcut' := Finset.mem_sdiff.mp hcut.2
      have hu : o.1.1 ∈ U := o.1.2
      have hout : o.2 ∉ U := by
        exact hcut'.2
      apply Finset.mem_sigma.mpr
      refine ⟨ho'.2, Finset.mem_filter.mpr ?_⟩
      refine ⟨?_, hu, ?_⟩
      · simpa [SimpleGraph.mem_neighborFinset] using hspec.1
      · rw [hspec.2]
        exact hout
    · intro o₁ ho₁ o₂ ho₂ heq
      have hfirst : o₁.1.1 = o₂.1.1 := congrArg Sigma.snd heq
      have hy : label o₁ = label o₂ := congrArg Sigma.fst heq
      have hs₁ := fullRelayShoreOccurrenceWitness_spec
        A hfree mate hclosed hinvol hfixed U o₁ (Finset.mem_filter.mp ho₁).1
      have hs₂ := fullRelayShoreOccurrenceWitness_spec
        A hfree mate hclosed hinvol hfixed U o₂ (Finset.mem_filter.mp ho₂).1
      change fullRelayShoreOccurrenceWitness A hfree mate
        hclosed hinvol hfixed U o₁ =
        fullRelayShoreOccurrenceWitness A hfree mate
          hclosed hinvol hfixed U o₂ at hy
      apply Sigma.ext
      · exact Subtype.ext hfirst
      · rw [← hs₁.2, ← hs₂.2, hy, hfirst]
    · intro q hq
      obtain ⟨y, v⟩ := q
      simp only [Q, Finset.mem_sigma] at hq
      have hv := Finset.mem_filter.mp hq.2
      have hvAdj : A.Adj y v := by
        simpa [SimpleGraph.mem_neighborFinset] using hv.1
      let o : Σ _ : {u : V // u ∈ U}, V :=
        ⟨⟨v, hv.2.1⟩, mate y v⟩
      have ho : o ∈ shoreGraphCutOccurrences P U := by
        simp [o, P, shoreGraphCutOccurrences,
          SimpleGraph.mem_neighborFinset, hv.2.2, hvAdj]
        exact ⟨y, hvAdj, rfl⟩
      have hspec := fullRelayShoreOccurrenceWitness_spec
        A hfree mate hclosed hinvol hfixed U o ho
      have hgeom := fullRelayShoreOccurrenceWitness_adj_endpoints
        A hfree mate hclosed hinvol hfixed U o ho
      have hlabel : label o = y := by
        apply commonNeighbor_unique_of_c4Free hfree (hfixed y v hvAdj)
        · exact hgeom.2.symm
        · exact hgeom.1.symm
        · exact hclosed y v hvAdj |>.symm
        · exact hvAdj.symm
      refine ⟨o, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨ho, hlabel ▸ hq.1⟩
      · show (⟨label o, o.1.1⟩ : Σ _ : V, V) = ⟨y, v⟩
        simp [o, hlabel]
  rw [show (labeledOccurrenceBlock
      (shoreGraphCutOccurrences P U) label R).card = S.card from rfl,
    hcard]
  simp [Q]

end

end Erdos85

#print axioms Erdos85.fullRelayShoreOccurrenceWitness_spec
#print axioms Erdos85.labeled_fullRelayShoreOccurrenceBlock_card_eq_sum_neighborStarFlip
