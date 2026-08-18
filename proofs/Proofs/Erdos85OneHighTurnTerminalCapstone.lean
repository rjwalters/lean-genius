import Proofs.Erdos85OneHighTurnOrderedAssembly
import Proofs.Erdos85OneHighV2CapacityCover

/-! # One-high terminal capstone with an ordered turn residual

This file assembles every already-closed one-high sector around the precise
remaining source-geometry obligation.  Crucially, the capacity orbit cover is
chosen before the structural split, so the same presentation is available to
the residual certificate branch.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The five decoded source alternatives not covered by the saturated
same-owner inventory: mate owners, or a source owner equal to the opposite
turn endpoint (possibly after applying the root mate). -/
def OneHighPinnedThreePairTurnNonSameOwnerExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (p : OneHighRawV2Presentation G hfree v)
      (T : OneHighPinnedThreePairTurn G hfree hv p),
      (T.qAB.sourceEdge.1 = p.mate T.qBC.sourceEdge.1 ∨
       T.qAB.sourceEdge.1 = T.c ∨
       T.qAB.sourceEdge.1 = p.mate T.c ∨
       T.qBC.sourceEdge.1 = T.a ∨
       T.qBC.sourceEdge.1 = p.mate T.a) → False

private theorem consecutive_minMax_ne_capstone
    {L : Type*} [LinearOrder L] {a b c : L}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (min a b, max a b) ≠ (min b c, max b c) := by
  intro hpair
  rcases le_total a b with habLe | hbaLe <;>
    rcases le_total b c with hbcLe | hcbLe
  · rw [min_eq_left habLe, max_eq_right habLe,
      min_eq_left hbcLe, max_eq_right hbcLe] at hpair
    exact hab (Prod.mk.inj hpair).1
  · rw [min_eq_left habLe, max_eq_right habLe,
      min_eq_right hcbLe, max_eq_left hcbLe] at hpair
    exact hac (Prod.mk.inj hpair).1
  · rw [min_eq_right hbaLe, max_eq_left hbaLe,
      min_eq_left hbcLe, max_eq_right hbcLe] at hpair
    exact hac (Prod.mk.inj hpair).2
  · rw [min_eq_right hbaLe, max_eq_left hbaLe,
      min_eq_right hcbLe, max_eq_left hcbLe] at hpair
    exact hbc (Prod.mk.inj hpair).1

/-- Turn multiplicity support always produces the pinned graph witness used by
the decoded source-sector split. -/
theorem nonempty_oneHighPinnedThreePairTurn_of_multiplicityTurn
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hturn : OneHighOddSupportThreePairTurnProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x ↦ p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))) :
    Nonempty (OneHighPinnedThreePairTurn G hfree hv p) := by
  obtain ⟨a, b, c, hab, hbc, hac, hAB, hBC, qAB, qBC, hsources⟩ :=
    exists_oneHighThreePairTurn_sourcePair_trichotomy G hfree hv p hturn
  have habv : a ≠ b := fun e => hab (congrArg
    (fun x => oneHighRootPair (p.branchLabel x)) e)
  have hbcv : b ≠ c := fun e => hbc (congrArg
    (fun x => oneHighRootPair (p.branchLabel x)) e)
  have hacv : a ≠ c := fun e => hac (congrArg
    (fun x => oneHighRootPair (p.branchLabel x)) e)
  have hsourceNe : qAB.sourceEdge ≠ qBC.sourceEdge := by
    intro heq
    apply consecutive_minMax_ne_capstone habv hbcv hacv
    rw [← qAB.key_eq, ← qBC.key_eq, heq]
  exact ⟨⟨a, b, c, hab, hbc, hac, hAB, hBC, qAB, qBC,
    hsourceNe, hsources⟩⟩

/-- Complete one-high assembly modulo the one genuinely unhandled source
geometry terminal and checked certificates for the 7,433 ordered residual.

The orbit cover first chooses the canonical presentation and capacity table.
The structural capstone is then applied to that exact presentation, avoiding
any illicit transport of a pinned turn across a relabeling. -/
theorem orderFortyNineStratumExcluded_one_of_orderedTurnResidual
    (hall : OneHighAllEvenSectorExcluded)
    (hhexagon : OneHighMateMissHexagonSectorExcluded)
    (hcross : OneHighCrossBlockSectorExcluded)
    (hother : OneHighPinnedThreePairTurnNonSameOwnerExcluded)
    (hchecked : ∀ (profile : Fin 5) table,
      table ∈ oneHighSaturatedOddTurnResidualInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 := by
  intro G _ _ _ hfree hmin hHigh
  obtain ⟨v, hv, p, table, hcapacity, hagree⟩ :=
    oneHighRawV2OrbitCover_capacityInventory G inferInstance inferInstance
      inferInstance hfree hmin hHigh
  rcases orderFortyNine_oneHigh_structural_sector_capstone
      G hfree hmin (Fintype.card_fin 49) hv p with
    heven | hmate | hturn | hcrossBlock
  · exact hall G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p heven
  · exact hhexagon G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hmate
  · obtain ⟨T⟩ := nonempty_oneHighPinnedThreePairTurn_of_multiplicityTurn
      G hfree hv p hturn
    rcases T.fully_decoded_source_sector G hfree hv p with
      hsame | hmateOwner | hc | hmc | ha | hma
    · exact false_of_sameOwnerPinnedThreePairTurn_of_structuralTerminals
        hhexagon hcross G hfree hmin hHigh hv p T hsame table
          hcapacity hagree (fun stored hmem =>
            hchecked ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ stored hmem)
    · exact hother G inferInstance inferInstance inferInstance
        hfree hmin hHigh hv p T (Or.inl hmateOwner)
    · exact hother G inferInstance inferInstance inferInstance
        hfree hmin hHigh hv p T (Or.inr (Or.inl hc))
    · exact hother G inferInstance inferInstance inferInstance
        hfree hmin hHigh hv p T (Or.inr (Or.inr (Or.inl hmc)))
    · exact hother G inferInstance inferInstance inferInstance
        hfree hmin hHigh hv p T (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact hother G inferInstance inferInstance inferInstance
        hfree hmin hHigh hv p T (Or.inr (Or.inr (Or.inr (Or.inr hma))))
  · exact hcross G inferInstance inferInstance inferInstance
      hfree hmin hHigh hv p hcrossBlock

end

end Erdos85
