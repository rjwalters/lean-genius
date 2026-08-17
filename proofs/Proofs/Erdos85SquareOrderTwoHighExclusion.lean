import Proofs.Erdos85SquareOrderTwoHighProfile
import Proofs.Erdos85SquareOrderTwoHighTerminal

/-! # Excluding the two-high square-order profile at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A square-order `64` tight-edge-cover core cannot have exactly two
degree-nine vertices.  The two incidence moments produce the unique common
high-neighbor point `x`.  At either high root, the other eight neighbors form
a class `A`; the six low neighbors of `x` form a miss set `S`.  The `56`
remaining low vertices must each meet `A` exactly once, forcing a one-regular
graph on seven vertices. -/
theorem false_of_squareOrder_eight_twoHigh
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8)
    (hcard : Fintype.card V = 8 * 8)
    (hhigh : (squareOrderHighVertices G 8).card = 2) : False := by
  classical
  let H := squareOrderHighVertices G 8
  let L := (Finset.univ : Finset V) \ H
  let k := squareOrderHighIncidenceCount G 8
  obtain ⟨x, hxTwo, hother⟩ :=
    squareOrder_eight_twoHigh_exists_unique_incidenceTwo
      G hfree hmin hcover hcard hhigh
  change k x = 2 at hxTwo
  change ∀ y : V, y ≠ x → k y ≤ 1 at hother
  have hxInter : (G.neighborFinset x ∩ H).card = 2 := by
    exact hxTwo
  have hxCoversH : G.neighborFinset x ∩ H = H := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    rw [hxInter]
    exact hhigh.le
  have hHnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    rw [show H.card = 2 by exact hhigh]
    omega
  obtain ⟨r, hrH⟩ := hHnonempty
  have hrxMem : r ∈ G.neighborFinset x := by
    have : r ∈ G.neighborFinset x ∩ H := by rw [hxCoversH]; exact hrH
    exact (Finset.mem_inter.mp this).1
  have hxr : G.Adj x r := (G.mem_neighborFinset x r).mp hrxMem
  have hrDegree : G.degree r = 9 := by
    exact (Finset.mem_filter.mp hrH).2
  have hxNotHigh : x ∉ H := by
    intro hxH
    have hxZero := squareOrder_highNeighborCount_eq_zero_of_high
      G hcover hxH
    change k x = 0 at hxZero
    omega
  have hxDegree : G.degree x = 8 := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (d := 8) (by omega) hmin hcover hcard x with hx | hx
    · exact hx
    · exact False.elim (hxNotHigh
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩))
  let A := (G.neighborFinset r).erase x
  let S := G.neighborFinset x \ H
  have hxInNr : x ∈ G.neighborFinset r := by
    exact (G.mem_neighborFinset r x).mpr hxr.symm
  have hAcard : A.card = 8 := by
    dsimp [A]
    rw [Finset.card_erase_of_mem hxInNr,
      G.card_neighborFinset_eq_degree, hrDegree]
  have hScard : S.card = 6 := by
    have hsplit := Finset.card_sdiff_add_card_inter
      (G.neighborFinset x) H
    have hNx : (G.neighborFinset x).card = 8 := by
      rw [G.card_neighborFinset_eq_degree, hxDegree]
    change S.card + (G.neighborFinset x ∩ H).card =
      (G.neighborFinset x).card at hsplit
    rw [hxInter, hNx] at hsplit
    omega
  have hroot := squareOrder_degree_succ_highRoot_structure
    G hfree (d := 8) (by omega) hmin hcard hrDegree
  have hA_low : ∀ a ∈ A, G.degree a = 8 := by
    intro a ha
    have hra : G.Adj r a := by
      exact (G.mem_neighborFinset r a).mp (Finset.mem_of_mem_erase ha)
    exact hroot.2.1 a hra
  have hA_incidenceOne : ∀ a ∈ A, k a = 1 := by
    intro a ha
    have hax : a ≠ x := Finset.ne_of_mem_erase ha
    have hle := hother a hax
    have hrHigh : r ∈ H := hrH
    have hra : r ∈ G.neighborFinset a := by
      have := Finset.mem_of_mem_erase ha
      exact (G.mem_neighborFinset a r).mpr
        ((G.mem_neighborFinset r a).mp this).symm
    have hpos : 0 < k a := by
      change 0 < (G.neighborFinset a ∩ H).card
      exact Finset.card_pos.mpr ⟨r, Finset.mem_inter.mpr ⟨hra, hrHigh⟩⟩
    omega
  let xr : {z : V // z ∈ G.neighborSet r} :=
    ⟨x, by simpa using hxr.symm⟩
  have hcommon := hroot.2.2 xr
  rw [degree_induce_neighborSet_eq_card_common] at hcommon
  obtain ⟨p, hpCommon⟩ := Finset.card_eq_one.mp hcommon
  have hpBoth : p ∈ G.neighborFinset r ∩ G.neighborFinset x := by
    rw [hpCommon]
    exact Finset.mem_singleton_self p
  have hpNx : p ∈ G.neighborFinset x := by
    exact (Finset.mem_inter.mp hpBoth).2
  have hpNr : p ∈ G.neighborFinset r := by
    exact (Finset.mem_inter.mp hpBoth).1
  have hpDegree : G.degree p = 8 := by
    exact hroot.2.1 p ((G.mem_neighborFinset r p).mp hpNr)
  have hpNotH : p ∉ H := by
    intro hpH
    have := (Finset.mem_filter.mp hpH).2
    omega
  have hpx : p ≠ x := by
    intro h
    subst p
    exact (G.ne_of_adj ((G.mem_neighborFinset x x).mp hpNx)) rfl
  have hpA : p ∈ A := Finset.mem_erase.mpr ⟨hpx, hpNr⟩
  have hpS : p ∈ S := Finset.mem_sdiff.mpr ⟨hpNx, hpNotH⟩
  have hinter : A ∩ S = {p} := by
    ext y
    constructor
    · intro hy
      have hyA := Finset.mem_inter.mp hy |>.1
      have hyS := Finset.mem_inter.mp hy |>.2
      have hyCommon : y ∈ G.neighborFinset r ∩ G.neighborFinset x :=
        Finset.mem_inter.mpr ⟨
          Finset.mem_of_mem_erase hyA, (Finset.mem_sdiff.mp hyS).1⟩
      rw [hpCommon] at hyCommon
      exact hyCommon
    · intro hy
      have hyp : y = p := Finset.mem_singleton.mp hy
      subst y
      exact Finset.mem_inter.mpr ⟨hpA, hpS⟩
  have hSsubL : S ⊆ L := by
    intro s hs
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ s,
      (Finset.mem_sdiff.mp hs).2⟩
  have hAsubL : A ⊆ L := by
    intro a ha
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ?_⟩
    intro haH
    have haHigh := (Finset.mem_filter.mp haH).2
    have haLow := hA_low a ha
    omega
  have hno : ∀ s ∈ S, ∀ a ∈ A, ¬ G.Adj s a := by
    intro s hs a ha hsa
    have hxs : G.Adj x s :=
      (G.mem_neighborFinset x s).mp (Finset.mem_sdiff.mp hs).1
    have har : G.Adj a r := by
      exact ((G.mem_neighborFinset r a).mp (Finset.mem_of_mem_erase ha)).symm
    have hxa : x ≠ a := (Finset.ne_of_mem_erase ha).symm
    have hsr : s ≠ r := by
      intro h
      subst s
      exact (Finset.mem_sdiff.mp hs).2 hrH
    exact hfree (containsC4_of_two_common hxa hsr
      hxs.symm hsa hxr.symm har.symm)
  have hLcard : L.card = 62 := by
    dsimp [L]
    rw [Finset.card_sdiff]
    simp [H, hhigh, hcard]
  have hLSCard : (L \ S).card = 56 := by
    rw [Finset.card_sdiff]
    have hinterLS : S ∩ L = S := Finset.inter_eq_left.mpr hSsubL
    rw [hinterLS, hLcard, hScard]
  have hcap : ∀ y ∈ L \ S, (G.neighborFinset y ∩ A).card ≤ 1 := by
    intro y hy
    have hyr : y ≠ r := by
      intro h
      subst y
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy).1).2 hrH
    have hsub : G.neighborFinset y ∩ A ⊆
        G.neighborFinset y ∩ G.neighborFinset r := by
      intro z hz
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
        Finset.mem_of_mem_erase (Finset.mem_inter.mp hz).2⟩
    exact (Finset.card_le_card hsub).trans
      (common_le_one_of_not_containsC4 hfree y r hyr)
  have hsumA : ∑ a ∈ A, (G.neighborFinset a ∩ L).card = 56 := by
    calc
      ∑ a ∈ A, (G.neighborFinset a ∩ L).card = ∑ _a ∈ A, 7 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hNa : (G.neighborFinset a).card = 8 := by
          rw [G.card_neighborFinset_eq_degree, hA_low a ha]
        have hHighPart : (G.neighborFinset a ∩ H).card = 1 :=
          hA_incidenceOne a ha
        have hpartition := Finset.card_sdiff_add_card_inter
          (G.neighborFinset a) H
        have hdiff : G.neighborFinset a \ H = G.neighborFinset a ∩ L := by
          ext z
          simp [L]
        rw [hdiff, hHighPart, hNa] at hpartition
        omega
      _ = 56 := by rw [Finset.sum_const, hAcard]; norm_num
  have hsumL : ∑ y ∈ L, (G.neighborFinset y ∩ A).card = 56 := by
    calc
      _ = ∑ a ∈ A, (G.neighborFinset a ∩ L).card :=
        (sum_card_neighbor_inter_comm G A L).symm
      _ = 56 := hsumA
  have hsumOutside : ∑ y ∈ L \ S, (G.neighborFinset y ∩ A).card = 56 := by
    have hsplitSum :
        (∑ y ∈ L \ S, (G.neighborFinset y ∩ A).card) +
          (∑ y ∈ S, (G.neighborFinset y ∩ A).card) =
            ∑ y ∈ L, (G.neighborFinset y ∩ A).card :=
      Finset.sum_sdiff hSsubL
    have hsumS : ∑ y ∈ S, (G.neighborFinset y ∩ A).card = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hno s hs a (Finset.mem_inter.mp ha).2
        ((G.mem_neighborFinset s a).mp (Finset.mem_inter.mp ha).1)
    rw [hsumL, hsumS] at hsplitSum
    omega
  have hone : ∀ y ∈ L \ S, (G.neighborFinset y ∩ A).card = 1 := by
    intro y hy
    by_contra hne
    have hyZero : (G.neighborFinset y ∩ A).card = 0 := by
      have := hcap y hy
      omega
    have herase : ∑ z ∈ (L \ S).erase y,
        (G.neighborFinset z ∩ A).card ≤ ((L \ S).erase y).card := by
      calc
        _ ≤ ∑ _z ∈ (L \ S).erase y, 1 :=
          Finset.sum_le_sum fun z hz => hcap z (Finset.mem_of_mem_erase hz)
        _ = ((L \ S).erase y).card := by simp
    have hsumErase := Finset.sum_erase_add (L \ S)
      (fun z => (G.neighborFinset z ∩ A).card) hy
    rw [hsumOutside, hyZero, add_zero] at hsumErase
    rw [Finset.card_erase_of_mem hy, hLSCard] at herase
    omega
  exact false_of_even_highRoot_saturation G (q := 8) (by decide)
    L A S p hAcard hpA hpS hinter hAsubL hno hone

end

end Erdos85
