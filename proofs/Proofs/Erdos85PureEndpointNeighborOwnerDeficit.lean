import Proofs.Erdos85PureEndpointNeighborOwnerPacking

/-!
# Owner deficit in the forced half-occupancy packing

Two singleton blocks in an `m`-block packing of blocks of size at most two
save two owner incidences.  Consequently the local packing misses at least
two full centers.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- A family of sets of size at most two, with two distinct singleton-indexed
members, has union size at most `2|s|-2`. -/
theorem card_biUnion_le_two_mul_card_sub_two_of_two_singletons
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hfx : (f x).card = 1) (hfy : (f y).card = 1)
    (hle : ∀ z ∈ s, (f z).card ≤ 2) :
    (s.biUnion f).card ≤ 2 * s.card - 2 := by
  classical
  let t := (s.erase x).erase y
  have hyErase : y ∈ s.erase x := mem_erase.mpr ⟨hxy.symm, hy⟩
  have htCard : t.card = s.card - 2 := by
    dsimp [t]
    rw [card_erase_of_mem hyErase, card_erase_of_mem hx]
    omega
  have htSub : t ⊆ s := by
    intro z hz
    exact (mem_erase.mp (mem_erase.mp hz).2).2
  have hsTwo : 2 ≤ s.card := by
    have hpairSub : ({x, y} : Finset α) ⊆ s := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have := card_le_card hpairSub
    rw [card_pair hxy] at this
    exact this
  have htSum : (∑ z ∈ t, (f z).card) ≤ 2 * t.card := by
    calc
      (∑ z ∈ t, (f z).card) ≤ ∑ _z ∈ t, 2 :=
        sum_le_sum fun z hz => hle z (htSub hz)
      _ = 2 * t.card := by simp [mul_comm]
  have hsumDecomp :
      (∑ z ∈ s, (f z).card) =
        (∑ z ∈ t, (f z).card) + (f y).card + (f x).card := by
    calc
      (∑ z ∈ s, (f z).card) =
          (∑ z ∈ s.erase x, (f z).card) + (f x).card :=
        (s.sum_erase_add (fun z => (f z).card) hx).symm
      _ = ((∑ z ∈ t, (f z).card) + (f y).card) + (f x).card := by
        rw [show t = (s.erase x).erase y by rfl,
          (s.erase x).sum_erase_add (fun z => (f z).card) hyErase]
  calc
    (s.biUnion f).card ≤ ∑ z ∈ s, (f z).card := card_biUnion_le
    _ = (∑ z ∈ t, (f z).card) + 1 + 1 := by rw [hsumDecomp, hfx, hfy]
    _ ≤ 2 * s.card - 2 := by
      rw [htCard] at htSum
      omega

/-- At a preconnected pure endpoint, some half-occupancy vertex has a local
owner union of size at most `q-2`; equivalently at least two full centers own
none of its shore neighbors. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    ∃ w,
      (G.neighborFinset w ∩ S).card = m ∧
      ((G.neighborFinset w ∩ S).biUnion fun y =>
        G.neighborFinset y ∩ F).card ≤ q - 2 ∧
      2 ≤ (F \ ((G.neighborFinset w ∩ S).biUnion fun y =>
        G.neighborFinset y ∩ F)).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  obtain ⟨x, x', w, hxS, hx'S, hxx', hxOne, hx'One,
      hxw, hx'w, hwCard, _hwNotFull, hlabels, _hpair⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerPacking
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  have hxB : x ∈ B := mem_inter.mpr
    ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxS⟩
  have hx'B : x' ∈ B := mem_inter.mpr
    ⟨(G.mem_neighborFinset w x').mpr hx'w.symm, hx'S⟩
  have hle : ∀ y ∈ B, (owner y).card ≤ 2 := by
    intro y hy
    rcases hlabels y (by simpa [B] using hy) with h | h <;>
      simp [owner, F, h]
  have hUnionLe : (B.biUnion owner).card ≤ q - 2 := by
    have h := card_biUnion_le_two_mul_card_sub_two_of_two_singletons
      B owner hxB hx'B hxx' (by simpa [owner, F] using hxOne)
      (by simpa [owner, F] using hx'One) hle
    have hBcard : B.card = m := by simpa [B] using hwCard
    rw [hBcard, ← hqm] at h
    exact h
  have hUnionSub : B.biUnion owner ⊆ F := by
    intro i hi
    obtain ⟨y, _hyB, hiy⟩ := mem_biUnion.mp hi
    exact (mem_inter.mp hiy).2
  have hDeficit : 2 ≤ (F \ B.biUnion owner).card := by
    rw [card_sdiff_of_subset hUnionSub]
    have hFcard : F.card = q := by simpa [F] using hCcard
    omega
  exact ⟨w, by simpa [B] using hwCard,
    by simpa [B, owner, F] using hUnionLe,
    by simpa [B, owner, F] using hDeficit⟩

end

end Erdos85

#print axioms
  Erdos85.card_biUnion_le_two_mul_card_sub_two_of_two_singletons
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerDeficit
