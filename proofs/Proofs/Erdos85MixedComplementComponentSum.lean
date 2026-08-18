import Proofs.Erdos85MixedParityAssembly
import Proofs.Erdos85UniquePartitionCounting

/-!
# Reindexing a mixed complement fiber by its unique source component

For one odd target cycle, every admissible displacement outside the diagonal
ordered-difference set has a unique off-target component supplying full pair
mass.  This file turns that uniqueness statement into the exact cardinality
sum consumed by the block-parity layers.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A single off-target component carrying full target mass forces the
difference to lie outside the target diagonal ordered-difference set. -/
theorem not_mem_diagonalODS_of_component_fullMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (heOdd : Odd e.supp.ncard) (δ : ZMod e.supp.ncard)
    (hδ0 : δ ≠ 0) (hδ1 : δ ≠ 1) (hδm1 : δ ≠ -1)
    (hmass : (∑ z : ZMod c.supp.ncard,
      anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard) :
    δ ∉ orderedDifferenceSet (mixedAnchorSupport G (u e 0) (u e)) := by
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let ℓ : C → ℕ := fun c ↦ c.supp.ncard
  have hsep : ∀ {a b : C}, a ≠ b → ∀ x y, u a x ≠ u b y := by
    intro a b hab x y hxy
    apply hab
    have hax : D.connectedComponentMk (u a x) = a :=
      (ConnectedComponent.mem_supp_iff a (u a x)).mp (by
        rw [← huRange a]
        exact ⟨x, rfl⟩)
    have hby : D.connectedComponentMk (u b y) = b :=
      (ConnectedComponent.mem_supp_iff b (u b y)).mp (by
        rw [← huRange b]
        exact ⟨y, rfl⟩)
    rw [← hax, ← hby, hxy]
  have hcover : ∀ v : V, ∃ a : C, ∃ x, u a x = v := by
    intro v
    let a : C := D.connectedComponentMk v
    have hv : v ∈ a.supp := (ConnectedComponent.mem_supp_iff a v).mpr rfl
    rw [← huRange a] at hv
    exact ⟨a, hv⟩
  intro hdiag
  have hoff := sum_offCycle_anchorPairMultiplicity G hfree hd heven hmin
    hcard (hu e) (hℓ3 e) heOdd (huD e) δ hδ0 hδ1 hδm1
  rw [if_pos hdiag] at hoff
  have hreindex := sum_filter_not_range_eq_sum_components_erase
    (ℓ := ℓ) u hu hsep hcover e
      (fun x ↦ anchorPairMultiplicity G x (u e) δ)
  rw [hreindex] at hoff
  have hcMem : c ∈ (Finset.univ.erase e : Finset C) := by simp [hce]
  have hle : (∑ z : ZMod c.supp.ncard,
      anchorPairMultiplicity G (u c z) (u e) δ) ≤
      ∑ a ∈ Finset.univ.erase e,
        ∑ z : ZMod a.supp.ncard,
          anchorPairMultiplicity G (u a z) (u e) δ := by
    exact Finset.single_le_sum
      (s := Finset.univ.erase e)
      (f := fun a : C ↦ ∑ z : ZMod a.supp.ncard,
        anchorPairMultiplicity G (u a z) (u e) δ)
      (fun _ _ ↦ Nat.zero_le _) hcMem
  rw [hmass, hoff] at hle
  have := hℓ3 e
  omega

/-- A target complement fiber is the sum of its per-source full-mass fibers. -/
theorem card_mixedComplementFiber_eq_sum_component_fullMass_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (heOdd : Odd e.supp.ncard) (t : ZMod p) :
    ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        δ ∉ orderedDifferenceSet
          (mixedAnchorSupport G (u e 0) (u e)))).card =
      ∑ c ∈ Finset.univ.erase e,
        ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t ∧
            (∑ z : ZMod c.supp.ncard,
              anchorPairMultiplicity G (u c z) (u e) δ) =
                e.supp.ncard)).card := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let T : Finset (ZMod e.supp.ncard) :=
    (admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        δ ∉ orderedDifferenceSet
          (mixedAnchorSupport G (u e 0) (u e)))
  let P : C → ZMod e.supp.ncard → Prop := fun c δ ↦
    (∑ z : ZMod c.supp.ncard,
      anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard
  have hunique : ∀ δ ∈ T, ∃! c : C,
      c ∈ Finset.univ.erase e ∧ P c δ := by
    intro δ hδ
    have hδ' := Finset.mem_filter.mp hδ
    have hadm := (mem_admissibleDifferences_iff δ).mp hδ'.1
    exact existsUnique_component_full_anchorPairMultiplicity G hfree hd
      heven hmin hcard u hu huRange huD hℓ3 e heOdd δ hadm.1
        hadm.2.1 hadm.2.2 hδ'.2.2
  have hcount := card_eq_sum_card_filter_of_existsUnique_mem
    (Finset.univ.erase e) T P hunique
  rw [hcount]
  apply Finset.sum_congr rfl
  intro c hc
  apply congrArg Finset.card
  ext δ
  simp only [T, P, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hadm, hcast, hdiag⟩, hmass⟩
    exact ⟨hadm, hcast, hmass⟩
  · rintro ⟨hadm, hcast, hmass⟩
    have hadm' := (mem_admissibleDifferences_iff δ).mp hadm
    have hce : c ≠ e := (Finset.mem_erase.mp hc).1
    have hdiag := not_mem_diagonalODS_of_component_fullMass G hfree hd
      heven hmin hcard u hu huRange huD hℓ3 c e hce heOdd δ hadm'.1
        hadm'.2.1 hadm'.2.2 hmass
    exact ⟨⟨hadm, hcast, hdiag⟩, hmass⟩

end

end Erdos85
