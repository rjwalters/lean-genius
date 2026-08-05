import Proofs.Erdos85BoundaryQuotientIrreducible
import Proofs.Erdos85ComponentPeriodicityBound

/-!
# Divisibility structure of the boundary quotient

Periodicity of the rectangular blocks between two defect cycles, together
with detailed balance, forces the lengths of any two quotient-adjacent
cycles to be comparable under divisibility.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- If the target defect-cycle order is not divisible by the source order,
the corresponding quotient entry is at most one. -/
theorem secondOrder_componentQuotientMatrix_le_one_of_not_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hndvd : ¬ c.supp.ncard ∣ e.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e ≤ 1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨xc, hxc⟩ := c.nonempty_supp
  obtain ⟨xe, hxe⟩ := e.nonempty_supp
  obtain ⟨p, hp, hpverts⟩ :=
    exists_secondOrderDefect_cycle_spanning_component
      G hfree hd heven hmin hcard c hxc
  obtain ⟨q, hq, hqverts⟩ :=
    exists_secondOrderDefect_cycle_spanning_component
      G hfree hd heven hmin hcard e hxe
  have hplen : p.length = c.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
  have hqlen : q.length = e.supp.ncard := by
    calc
      q.length = Nat.card q.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hq).symm
      _ = q.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = e.supp.ncard := congrArg Set.ncard hqverts
  have hshift : q.length • (1 : ZMod p.length) ≠ 0 := by
    have hz : (q.length : ZMod p.length) ≠ 0 :=
      (not_congr (ZMod.natCast_eq_zero_iff q.length p.length)).mpr
        (by simpa [hplen, hqlen] using hndvd)
    simpa using hz
  exact componentQuotientMatrix_le_one_of_targetLength
    G D hfree
    (adjMatrix_comm_secondOrderDefect_of_even
      G hfree hd heven hmin hcard)
    (secondOrderDefectGraph_degree_eq_two
      G hfree hd heven hmin hcard)
    c e hp hq hpverts hqverts hshift

/-- A positive entry of the second-order component quotient can occur only
between cycle lengths comparable under divisibility. -/
theorem secondOrder_componentQuotientMatrix_pos_imp_size_dvd_or_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c e) :
    c.supp.ncard ∣ e.supp.ncard ∨ e.supp.ncard ∣ c.supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  change 0 < componentQuotientMatrix G D c e at hpos
  by_contra hnot
  push_neg at hnot
  obtain ⟨xc, hxc⟩ := c.nonempty_supp
  obtain ⟨xe, hxe⟩ := e.nonempty_supp
  obtain ⟨p, hp, hpverts⟩ :=
    exists_secondOrderDefect_cycle_spanning_component
      G hfree hd heven hmin hcard c hxc
  obtain ⟨q, hq, hqverts⟩ :=
    exists_secondOrderDefect_cycle_spanning_component
      G hfree hd heven hmin hcard e hxe
  have hplen : p.length = c.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
  have hqlen : q.length = e.supp.ncard := by
    calc
      q.length = Nat.card q.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hq).symm
      _ = q.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = e.supp.ncard := congrArg Set.ncard hqverts
  have hshiftCE : q.length • (1 : ZMod p.length) ≠ 0 := by
    have hz : (q.length : ZMod p.length) ≠ 0 :=
      (not_congr (ZMod.natCast_eq_zero_iff q.length p.length)).mpr
        (by simpa [hplen, hqlen] using hnot.1)
    simpa using hz
  have hshiftEC : p.length • (1 : ZMod q.length) ≠ 0 := by
    have hz : (p.length : ZMod q.length) ≠ 0 :=
      (not_congr (ZMod.natCast_eq_zero_iff p.length q.length)).mpr
        (by simpa [hplen, hqlen] using hnot.2)
    simpa using hz
  have hleCE : componentQuotientMatrix G D c e ≤ 1 :=
    componentQuotientMatrix_le_one_of_targetLength
      G D hfree
      (adjMatrix_comm_secondOrderDefect_of_even
        G hfree hd heven hmin hcard)
      (secondOrderDefectGraph_degree_eq_two
        G hfree hd heven hmin hcard)
      c e hp hq hpverts hqverts hshiftCE
  have hleEC : componentQuotientMatrix G D e c ≤ 1 :=
    componentQuotientMatrix_le_one_of_targetLength
      G D hfree
      (adjMatrix_comm_secondOrderDefect_of_even
        G hfree hd heven hmin hcard)
      (secondOrderDefectGraph_degree_eq_two
        G hfree hd heven hmin hcard)
      e c hq hp hqverts hpverts hshiftEC
  have hbalance := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  change c.supp.ncard * componentQuotientMatrix G D c e =
    e.supp.ncard * componentQuotientMatrix G D e c at hbalance
  have hcpos : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
  have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
  have hposEC : 0 < componentQuotientMatrix G D e c := by
    by_contra hz
    have hz' : componentQuotientMatrix G D e c = 0 := by omega
    have hproduct : 0 < c.supp.ncard *
        componentQuotientMatrix G D c e := Nat.mul_pos hcpos hpos
    have hzero : c.supp.ncard * componentQuotientMatrix G D c e = 0 := by
      simpa only [hz', mul_zero] using hbalance
    exact (Nat.ne_of_gt hproduct) hzero
  have hCE : componentQuotientMatrix G D c e = 1 := by omega
  have hEC : componentQuotientMatrix G D e c = 1 := by omega
  rw [hCE, hEC, mul_one, mul_one] at hbalance
  exact hnot.1 (hbalance.symm ▸ dvd_refl _)

/-- Along a positive quotient edge from a shorter defect cycle to a longer
one, the reverse entry is exactly one and the forward entry is exactly the
ratio of the cycle lengths. -/
theorem secondOrder_componentQuotientMatrix_entries_of_size_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G) c e) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e c = 1 ∧
      c.supp.ncard ∣ e.supp.ncard ∧
      c.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) c e =
          e.supp.ncard := by
  let D := secondOrderDefectGraph G
  have hndvd : ¬ e.supp.ncard ∣ c.supp.ncard := by
    intro hdvd
    have hleSize := Nat.le_of_dvd c.nonempty_supp.ncard_pos hdvd
    omega
  have hle := secondOrder_componentQuotientMatrix_le_one_of_not_dvd
    G hfree hd heven hmin hcard e c hndvd
  have hbalance := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  change c.supp.ncard * componentQuotientMatrix G D c e =
    e.supp.ncard * componentQuotientMatrix G D e c at hbalance
  change 0 < componentQuotientMatrix G D c e at hpos
  change componentQuotientMatrix G D e c ≤ 1 at hle
  have hposrev : 0 < componentQuotientMatrix G D e c := by
    by_contra hz
    have hz' : componentQuotientMatrix G D e c = 0 := by omega
    have hzero : c.supp.ncard * componentQuotientMatrix G D c e = 0 := by
      simpa only [hz', mul_zero] using hbalance
    have hprod : 0 < c.supp.ncard * componentQuotientMatrix G D c e :=
      Nat.mul_pos c.nonempty_supp.ncard_pos hpos
    exact (Nat.ne_of_gt hprod) hzero
  have hone : componentQuotientMatrix G D e c = 1 := by omega
  have heq : c.supp.ncard * componentQuotientMatrix G D c e =
      e.supp.ncard := by simpa only [hone, mul_one] using hbalance
  refine ⟨hone, ?_, heq⟩
  exact ⟨componentQuotientMatrix G D c e, heq.symm⟩

end

end Erdos85
