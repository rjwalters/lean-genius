import Proofs.Erdos85FinalDyadicExceptionalSupportUpperBound

/-!
# Defect leakage from the negative-high block system

Every negative-high point has a defect neighbor in each empty block other
than its own.  Thus the induced defect graph on `M` has minimum degree at
least `|E|-1`; the remaining outside-shore defect degree is controlled by
the exceptional support deficit `q-c`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every negative-high point has at least one defect neighbor in every other
empty-center block. -/
theorem finalDyadic_negativeHigh_inducedDefect_degree_ge_empty_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {x : V} (hxM : x ∈ finalDyadicNegativeHighCutCenters G S j r) :
    (emptyLineCenters G S).card - 1 ≤
      ((secondOrderDefectGraph G).neighborFinset x ∩
        finalDyadicNegativeHighCutCenters G S j r).card := by
  let E := emptyLineCenters G S
  let M := finalDyadicNegativeHighCutCenters G S j r
  obtain ⟨e, heData, heUnique⟩ :=
    finalDyadic_negativeHigh_existsUnique_empty_owner
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf hxM
  have hex : ∀ f ∈ E.erase e, ∃ y,
      y ∈ G.neighborFinset f ∧
      y ∈ (secondOrderDefectGraph G).neighborFinset x := by
    intro f hf
    have hfData := Finset.mem_erase.mp hf
    obtain ⟨y, hyB, hyD⟩ :=
      exists_secondOrderDefect_neighbor_in_other_neighborBlock
        G hfree hreg
          (hemptyClique heData.1 hfData.2 hfData.1.symm) heData.2
    exact ⟨y, hyB, hyD⟩
  choose pick hpickB hpickD using hex
  let pick' : V → V := fun f => if hf : f ∈ E.erase e then pick f hf else f
  have hpickEq : ∀ f (hf : f ∈ E.erase e), pick' f = pick f hf := by
    intro f hf
    dsimp only [pick']
    rw [dif_pos hf]
  have hmaps : Set.MapsTo pick' (↑(E.erase e) : Set V)
      (↑((secondOrderDefectGraph G).neighborFinset x ∩ M) : Set V) := by
    intro f hf
    have hfFin : f ∈ E.erase e := hf
    have hfE : f ∈ E := Finset.mem_of_mem_erase hfFin
    have hpickM := finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hfE (hpickB f hfFin)
    rw [hpickEq f hfFin]
    exact Finset.mem_inter.mpr ⟨hpickD f hfFin, hpickM⟩
  have hinj : Set.InjOn pick' (↑(E.erase e) : Set V) := by
    intro f hf g hg hpick
    have hfFin : f ∈ E.erase e := hf
    have hgFin : g ∈ E.erase e := hg
    rw [hpickEq f hfFin, hpickEq g hgFin] at hpick
    by_contra hfg
    have hdisj := finalDyadic_emptyCenter_neighborFinset_disjoint
      G hfree S hemptyClique
        (Finset.mem_of_mem_erase hfFin)
        (Finset.mem_of_mem_erase hgFin) hfg
    have hpF : pick f hfFin ∈ G.neighborFinset f := hpickB f hfFin
    have hpG : pick f hfFin ∈ G.neighborFinset g :=
      hpick ▸ hpickB g hgFin
    exact (Finset.disjoint_left.mp hdisj hpF) hpG
  have hcardLe := Finset.card_le_card_of_injOn pick' hmaps hinj
  have heE : e ∈ E := heData.1
  rw [Finset.card_erase_of_mem heE] at hcardLe
  exact hcardLe

/-- Fraction-free leakage bound: twice the number of defect neighbors of a
negative-high point lying outside both `S` and `M` is at most the support
deficit `q-c`. -/
theorem finalDyadic_negativeHigh_twice_defectLeakage_le_supportDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {x : V} (hxM : x ∈ finalDyadicNegativeHighCutCenters G S j r) :
    2 * ((((secondOrderDefectGraph G).neighborFinset x \ S) \
      finalDyadicNegativeHighCutCenters G S j r).card) ≤ q - c := by
  let D := secondOrderDefectGraph G
  let E := emptyLineCenters G S
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hinside :=
    finalDyadic_negativeHigh_inducedDefect_degree_ge_empty_sub_one
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hxM
  change E.card - 1 ≤ (D.neighborFinset x ∩ M).card at hinside
  have hxNotS : x ∉ S := Finset.mem_compl.mp (Finset.mem_filter.mp hxM).1
  have hMsub : M ⊆ Sᶜ := fun y hy => (Finset.mem_filter.mp hy).1
  have hinter : (D.neighborFinset x \ S) ∩ M =
      D.neighborFinset x ∩ M := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hyD, _⟩, hyM⟩
      exact ⟨hyD, hyM⟩
    · rintro ⟨hyD, hyM⟩
      exact ⟨⟨hyD, Finset.mem_compl.mp (hMsub hyM)⟩, hyM⟩
  have hsplit := Finset.card_sdiff_add_card_inter
    (D.neighborFinset x \ S) M
  rw [hinter] at hsplit
  have hcut : (D.neighborFinset x ∩ S).card = 2 ^ j + r :=
    (Finset.mem_filter.mp hxM).2
  have hDcard : (D.neighborFinset x).card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree (by omega) hreg hcard]
  have hout : (D.neighborFinset x \ S).card = 2 ^ j - 1 - r := by
    have hpartition := Finset.card_sdiff_add_card_inter
      (D.neighborFinset x) S
    rw [hDcard, hcut, hqa] at hpartition
    omega
  rw [hout] at hsplit
  have hsum := exceptionalSignedSupport_card_eq_full_add_empty
    G S (by omega : 0 < q)
  rw [hsupport] at hsum
  have hdiff := finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv
  rw [hdisp] at hdiff
  change c = (fullLineCenters G S q).card + E.card at hsum
  change ((fullLineCenters G S q).card : ℤ) - E.card = 2 * r at hdiff
  have hpop : c = 2 * E.card + 2 * r := by omega
  change 2 * (((D.neighborFinset x \ S) \ M).card) ≤ q - c
  omega

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_negativeHigh_inducedDefect_degree_ge_empty_sub_one
#print axioms
  Erdos85.finalDyadic_negativeHigh_twice_defectLeakage_le_supportDeficit
