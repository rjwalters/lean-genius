import Proofs.Erdos85OddSquareOrderNineOrder34PuncturedProfileCapstone

/-! # Owner-puncture transfer for the order-27 articulation branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Direct sharp-partition extraction on the actual 50-point shore.  This
is preferable in the graph-facing wrapper to transferring the 51-point
complement partition: the articulation capstone already supplies this
shore's boundary equality. -/
theorem orderNine_order27_explicitPartition_of_large_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (T : Finset V) (hTcard : T.card = 50)
    (hTsub : T ⊆ (Finset.univ : Finset V) \ {h₁, h₂, h₃})
    (hboundary : (∑ x ∈ T,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) = 2)
    (hhigh₁ : (G.neighborFinset h₁ ∩ T).card = 6)
    (hhigh₂ : (G.neighborFinset h₂ ∩ T).card = 6)
    (hhigh₃ : (G.neighborFinset h₃ ∩ T).card = 6)
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10) :
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ T 5 42 := by
  have hTH : Disjoint T ({h₁, h₂, h₃} : Finset V) := by
    rw [Finset.disjoint_left]
    intro x hxT hxH
    exact (Finset.mem_sdiff.mp (hTsub hxT)).2 hxH
  have hsharp := orderNineOrdinarySharpPartition_of_boundary
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ T hTH hdegOrd hdegHigh 2
      hboundary (by
        simp [orderNineNearRegularCutLower, orderNineBalancedSquareSum,
          hTcard, hhigh₁, hhigh₂, hhigh₃])
  apply orderNineOrdinaryExplicitPartition_of_sharp
    G h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ T 5 42 hTH hdegOrd hsharp
  · omega
  · norm_num

/-- Erasing an ordinary owner from the target of a `5/6` partition changes
exactly its six ordinary neighbors from the upper class to the lower class.
This is the missing transfer between the 51-point unpunctured complement
returned by the sharp-partition theorem and the actual 50-point shore. -/
theorem orderNine_explicitPartition_five_48_erase_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ owner : V) (R : Finset V)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 5 48)
    (hownerR : owner ∈ R)
    (hordinaryNeighbors :
      (G.neighborFinset owner ∩
        ((Finset.univ : Finset V) \ {h₁, h₂, h₃})).card = 6)
    (hneighborsUpper : ∀ x ∈
      (Finset.univ : Finset V) \ {h₁, h₂, h₃},
      G.Adj x owner → (G.neighborFinset x ∩ R).card = 6) :
    orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ (R.erase owner) 5 42 := by
  classical
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  let fR := fun x : ↥(↑O : Set V) => (G.neighborFinset x.1 ∩ R).card
  let fT := fun x : ↥(↑O : Set V) =>
    (G.neighborFinset x.1 ∩ R.erase owner).card
  change (∀ x, fR x = 5 ∨ fR x = 6) ∧
    (Finset.univ.filter fun x => fR x = 6).card = 48 at hpart
  change (∀ x, fT x = 5 ∨ fT x = 6) ∧
    (Finset.univ.filter fun x => fT x = 6).card = 42
  have herase (x : V) :
      G.neighborFinset x ∩ R.erase owner =
        (G.neighborFinset x ∩ R).erase owner := by
    ext y
    simp [and_left_comm]
  have hfT_adj (x : ↥(↑O : Set V)) (hx : G.Adj x.1 owner) :
      fT x = fR x - 1 := by
    have hm : owner ∈ G.neighborFinset x.1 ∩ R := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x.1 owner).mpr hx, hownerR⟩
    dsimp [fT, fR]
    rw [herase, Finset.card_erase_of_mem hm]
  have hfT_not_adj (x : ↥(↑O : Set V)) (hx : ¬ G.Adj x.1 owner) :
      fT x = fR x := by
    have hm : owner ∉ G.neighborFinset x.1 ∩ R := by
      intro hm
      exact hx ((G.mem_neighborFinset x.1 owner).mp (Finset.mem_inter.mp hm).1)
    dsimp [fT, fR]
    rw [herase, Finset.erase_eq_self.mpr hm]
  have hlevels : ∀ x, fT x = 5 ∨ fT x = 6 := by
    intro x
    by_cases hx : G.Adj x.1 owner
    · have hu : fR x = 6 := hneighborsUpper x.1 x.2 hx
      left
      rw [hfT_adj x hx, hu]
    · simpa [hfT_not_adj x hx] using hpart.1 x
  let A := Finset.univ.filter fun x : ↥(↑O : Set V) => fR x = 6
  let B := Finset.univ.filter fun x : ↥(↑O : Set V) => fT x = 6
  let N := Finset.univ.filter fun x : ↥(↑O : Set V) => G.Adj x.1 owner
  have hBA : B = A \ N := by
    ext x
    simp only [B, A, N, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    by_cases hx : G.Adj x.1 owner
    · have hu : fR x = 6 := hneighborsUpper x.1 x.2 hx
      have hl : fT x = 5 := by rw [hfT_adj x hx, hu]
      simp [hx, hl]
    · rw [hfT_not_adj x hx]
      simp [hx]
  have hNsubA : N ⊆ A := by
    intro x hx
    have hxAdj : G.Adj x.1 owner := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      hneighborsUpper x.1 x.2 hxAdj⟩
  have hNcard : N.card = 6 := by
    have hequiv : N.card = (G.neighborFinset owner ∩ O).card := by
      apply Finset.card_bij (fun x _ => x.1)
      · intro x hx
        have hxAdj : G.Adj x.1 owner := (Finset.mem_filter.mp hx).2
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset owner x.1).mpr ((G.adj_comm _ _).mp hxAdj), x.2⟩
      · intro a₁ ha₁ a₂ ha₂ heq
        exact Subtype.ext heq
      · intro y hy
        have hyO := (Finset.mem_inter.mp hy).2
        refine ⟨⟨y, hyO⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (G.adj_comm _ _).mp ((G.mem_neighborFinset owner y).mp
            (Finset.mem_inter.mp hy).1)⟩
    rw [hequiv]
    exact hordinaryNeighbors
  refine ⟨hlevels, ?_⟩
  change B.card = 42
  rw [hBA, Finset.card_sdiff_of_subset hNsubA]
  have hAcard : A.card = 48 := hpart.2
  omega

/-- The punctured lower class consists of the old lower class together with
the six ordinary neighbors whose target incidence drops from six to five. -/
theorem orderNine_lowSet_five_erase_owner_eq_union_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ owner : V) (R : Finset V)
    (hownerR : owner ∈ R)
    (hneighborsUpper : ∀ x ∈
      (Finset.univ : Finset V) \ {h₁, h₂, h₃},
      G.Adj x owner → (G.neighborFinset x ∩ R).card = 6) :
    orderNineOrdinaryLowSet G h₁ h₂ h₃ (R.erase owner) 5 =
      orderNineOrdinaryLowSet G h₁ h₂ h₃ R 5 ∪
        (G.neighborFinset owner ∩
          ((Finset.univ : Finset V) \ {h₁, h₂, h₃})) := by
  classical
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  ext x
  have herase :
      G.neighborFinset x ∩ R.erase owner =
        (G.neighborFinset x ∩ R).erase owner := by
    ext y
    simp [and_left_comm]
  by_cases hxO : x ∈ O
  · by_cases hx : G.Adj x owner
    · have hu : (G.neighborFinset x ∩ R).card = 6 :=
        hneighborsUpper x hxO hx
      have hx' : G.Adj owner x := (G.adj_comm x owner).mp hx
      have hm : owner ∈ G.neighborFinset x ∩ R :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x owner).mpr hx, hownerR⟩
      have hnew : (G.neighborFinset x ∩ R.erase owner).card = 5 := by
        rw [herase, Finset.card_erase_of_mem hm, hu]
      simp [orderNineOrdinaryLowSet, O, hxO, hx', hu, hnew]
    · have hm : owner ∉ G.neighborFinset x ∩ R := by
        intro hm
        exact hx ((G.mem_neighborFinset x owner).mp (Finset.mem_inter.mp hm).1)
      have hsame : (G.neighborFinset x ∩ R.erase owner).card =
          (G.neighborFinset x ∩ R).card := by
        rw [herase, Finset.erase_eq_self.mpr hm]
      have hx' : ¬ G.Adj owner x := fun h ↦ hx ((G.adj_comm owner x).mp h)
      simp [orderNineOrdinaryLowSet, O, hxO, hx', hsame]
  · simp [orderNineOrdinaryLowSet, O, hxO]

/-- Consequently the corrected order-50-shore low set has cardinality 36,
the number used in audit equation (20). -/
theorem orderNine_lowSet_card_eq_thirtySix_after_owner_puncture
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ owner : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃)
    (h₂₃ : h₂ ≠ h₃) (R : Finset V)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R 5 48)
    (hownerR : owner ∈ R)
    (hordinaryNeighbors :
      (G.neighborFinset owner ∩
        ((Finset.univ : Finset V) \ {h₁, h₂, h₃})).card = 6)
    (hneighborsUpper : ∀ x ∈
      (Finset.univ : Finset V) \ {h₁, h₂, h₃},
      G.Adj x owner → (G.neighborFinset x ∩ R).card = 6) :
    (orderNineOrdinaryLowSet G h₁ h₂ h₃ (R.erase owner) 5).card = 36 := by
  have hnew := orderNine_explicitPartition_five_48_erase_owner
    G h₁ h₂ h₃ owner R hpart hownerR hordinaryNeighbors hneighborsUpper
  have hcardLow := orderNineOrdinaryLowSet_card G hcard
    h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ (R.erase owner) 5 42 hnew
  omega

#print axioms orderNine_explicitPartition_five_48_erase_owner
#print axioms orderNine_order27_explicitPartition_of_large_boundary
#print axioms orderNine_lowSet_five_erase_owner_eq_union_neighbors
#print axioms orderNine_lowSet_card_eq_thirtySix_after_owner_puncture

end

end Erdos85
