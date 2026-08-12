import Proofs.Erdos85ColorSectorPSD
import Proofs.Erdos85SecondOrderColorTrace
import Proofs.Erdos85ResidueSignedCount
import Proofs.Erdos85DegreeSixTriangleClosure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The degree-six color-sector split

This file connects the component-indexed color sector used by the PSD
argument to the vertex-indexed colored order used by the cubic trace.  The
key point is that triangle-free defect degree two propagates along every
edge, hence throughout every connected component of the second-order defect
graph.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Weighted Cauchy--Schwarz in the exact numerical form needed for the
unique degree-six triangle-free component.  This is stated for an abstract
balanced quotient so the analytic step is independent of graph plumbing. -/
theorem degreeSix_singleton_incidence_cauchy
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hpos : 0 < size c)
    (htotal : (∑ e : C, size e) = 33)
    (hrow : (∑ e : C, Q c e) = 6)
    (hdiag : Q c c = 2)
    (hbal : ∀ e, size c * Q c e = size e * Q e c)
    (hsq : (∑ e : C, Q c e * Q e c) = size c + 3) :
    size c * size c + 33 ≤ 18 * size c := by
  let S : Finset C := Finset.univ.erase c
  have hc : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have hsizeS : (∑ e ∈ S, size e) = 33 - size c := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset C) size hc
    dsimp [S]
    omega
  have hrowS : (∑ e ∈ S, Q c e) = 4 := by
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset C) (fun e => Q c e) hc
    dsimp [S]
    omega
  have hprodS : (∑ e ∈ S, Q c e * Q e c) = size c - 1 := by
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset C) (fun e => Q c e * Q e c) hc
    rw [hdiag] at hsplit
    dsimp [S]
    omega
  have hl : (size c : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) S
    (r := fun e => (Q c e : ℝ))
    (f := fun e => (size e : ℝ))
    (g := fun e => ((Q c e * Q e c : ℕ) : ℝ) / (size c : ℝ))
    (fun _ _ => by positivity) (fun _ _ => by positivity) (by
      intro e he
      have hb := hbal e
      have hbR : (size c : ℝ) * (Q c e : ℝ) =
          (size e : ℝ) * (Q e c : ℝ) := by exact_mod_cast hb
      apply le_of_eq
      rw [← mul_div_assoc]
      apply (eq_div_iff hl).2
      push_cast
      calc
        (Q c e : ℝ) ^ 2 * size c =
            (Q c e : ℝ) * ((size c : ℝ) * Q c e) := by ring
        _ = (Q c e : ℝ) * ((size e : ℝ) * Q e c) := by rw [hbR]
        _ = (size e : ℝ) * ((Q c e : ℝ) * Q e c) := by ring)
  have hsizeR : (∑ e ∈ S, (size e : ℝ)) = (33 - size c : ℕ) := by
    exact_mod_cast hsizeS
  have hrowR : (∑ e ∈ S, (Q c e : ℝ)) = 4 := by
    exact_mod_cast hrowS
  have hprodR :
      (∑ e ∈ S, (((Q c e * Q e c : ℕ) : ℝ) / (size c : ℝ))) =
        ((size c - 1 : ℕ) : ℝ) / (size c : ℝ) := by
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast hprodS
  rw [hsizeR, hrowR, hprodR] at hcs
  have hlR : (0 : ℝ) < size c := by exact_mod_cast hpos
  have hle33 : size c ≤ 33 := by
    have : size c ≤ ∑ e : C, size e := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hc
    omega
  have hsub33 : ((33 - size c : ℕ) : ℝ) = 33 - (size c : ℝ) := by
    rw [Nat.cast_sub hle33]
    norm_num
  have hsub1 : ((size c - 1 : ℕ) : ℝ) = (size c : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]
    norm_num
  norm_num [pow_two] at hcs
  rw [hsub33, hsub1] at hcs
  have hcs' := mul_le_mul_of_nonneg_right hcs hlR.le
  have hcs'' : 16 * (size c : ℝ) ≤
      (33 - (size c : ℝ)) * ((size c : ℝ) - 1) := by
    calc
      16 * (size c : ℝ) ≤
          ((33 - (size c : ℝ)) * (((size c : ℝ) - 1) / size c)) * size c :=
        hcs'
      _ = (33 - (size c : ℝ)) * ((size c : ℝ) - 1) := by
        field_simp [hl]
  exact_mod_cast (show ((size c : ℝ) * size c + 33 ≤ 18 * size c) by
    nlinarith [hcs''])

/-- The order-six singleton row has a forced asymmetric contact: one unit
leaves the order-six component and two units return from an order-three
component. -/
theorem degreeSix_orderSix_singleton_contact
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hsize : size c = 6)
    (hrow : (∑ e ∈ (Finset.univ.erase c), Q c e) = 4)
    (hprod : (∑ e ∈ (Finset.univ.erase c), Q c e * Q e c) = 5)
    (hbal : ∀ e, size c * Q c e = size e * Q e c) :
    ∃ e : C, e ≠ c ∧ size e = 3 ∧ Q c e = 1 ∧ Q e c = 2 := by
  let S : Finset C := Finset.univ.erase c
  let f : C → ℕ := fun e ↦ Q c e * (Q e c - 1)
  have hdecomp : ∀ e ∈ S, Q c e * Q e c = Q c e + f e := by
    intro e he
    by_cases hq : Q c e = 0
    · simp [f, hq]
    · have hr : 0 < Q e c := by
        by_contra hr0
        push Not at hr0
        have hrz : Q e c = 0 := by omega
        have hb := hbal e
        rw [hsize, hrz, mul_zero] at hb
        have : Q c e = 0 := by omega
        exact hq this
      calc
        Q c e * Q e c = Q c e * ((Q e c - 1) + 1) := by
          rw [Nat.sub_add_cancel hr]
        _ = Q c e + f e := by simp [f, Nat.mul_add, Nat.add_comm]
  have hfsum : (∑ e ∈ S, f e) = 1 := by
    have hrowS : (∑ e ∈ S, Q c e) = 4 := by simpa [S] using hrow
    have hsum : 5 = 4 + ∑ e ∈ S, f e := by
      calc
        5 = ∑ e ∈ S, Q c e * Q e c := hprod.symm
        _ = ∑ e ∈ S, (Q c e + f e) := Finset.sum_congr rfl hdecomp
        _ = (∑ e ∈ S, Q c e) + ∑ e ∈ S, f e := by
          rw [Finset.sum_add_distrib]
        _ = 4 + ∑ e ∈ S, f e := by rw [hrowS]
    omega
  have hfne : (∑ e ∈ S, f e) ≠ 0 := by omega
  obtain ⟨e, heS, hene⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfne
  have hfle : f e ≤ ∑ x ∈ S, f x :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) heS
  have hfe : f e = 1 := by omega
  have hmul : Q c e * (Q e c - 1) = 1 := by simpa [f] using hfe
  have hq : Q c e = 1 :=
    Nat.dvd_one.mp ⟨Q e c - 1, hmul.symm⟩
  have hrsub : Q e c - 1 = 1 :=
    Nat.dvd_one.mp ⟨Q c e, by simpa [Nat.mul_comm] using hmul.symm⟩
  have hr : Q e c = 2 := by omega
  have hb := hbal e
  rw [hsize, hq, hr] at hb
  have hse : size e = 3 := by omega
  exact ⟨e, (Finset.mem_erase.mp heS).1, hse, hq, hr⟩

/-- Two distinct nonnegative summands are bounded by the full finite sum. -/
theorem two_distinct_terms_le_sum
    {C : Type*} [Fintype C] [DecidableEq C]
    (f : C → ℕ) {c e : C} (hce : c ≠ e) :
    f c + f e ≤ ∑ x, f x := by
  have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
  have heMem : e ∈ (Finset.univ.erase c : Finset C) :=
    Finset.mem_erase.mpr ⟨fun h ↦ hce h.symm, Finset.mem_univ e⟩
  have hsplitc := Finset.sum_erase_add (Finset.univ : Finset C) f hcMem
  have hsplite := Finset.sum_erase_add (Finset.univ.erase c : Finset C) f heMem
  omega

/-- If a balanced nonnegative quotient row has the same ordinary and
two-step sums, every positive outgoing entry has reverse multiplicity one. -/
theorem reverse_eq_one_of_balanced_row_product_eq_row
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → C → ℕ) (size : C → ℕ) (c : C)
    (hcpos : 0 < size c)
    (hbal : ∀ e, size c * Q c e = size e * Q e c)
    (hsum : (∑ e, Q c e * Q e c) = ∑ e, Q c e) :
    ∀ e, 0 < Q c e → Q e c = 1 := by
  have hle : ∀ e : C, Q c e ≤ Q c e * Q e c := by
    intro e
    by_cases hq : Q c e = 0
    · simp [hq]
    · have hqpos : 0 < Q c e := Nat.pos_of_ne_zero hq
      have hrpos : 0 < Q e c := by
        by_contra hr
        push Not at hr
        have hr0 : Q e c = 0 := by omega
        have hb := hbal e
        rw [hr0, mul_zero] at hb
        exact (Nat.mul_pos hcpos hqpos).ne' hb
      calc
        Q c e = Q c e * 1 := by simp
        _ ≤ Q c e * Q e c := Nat.mul_le_mul_left _ hrpos
  intro e hq
  have hrpos : 0 < Q e c := by
    have := hle e
    by_contra hr
    push Not at hr
    have hr0 : Q e c = 0 := by omega
    rw [hr0, mul_zero] at this
    omega
  by_contra hrne
  have hrlt : Q c e < Q c e * Q e c := by
    have hr2 : 1 < Q e c := by omega
    simpa using (Nat.mul_lt_mul_left hq).mpr hr2
  have hstrict := Finset.sum_lt_sum
    (fun t _ ↦ hle t) ⟨e, Finset.mem_univ e, hrlt⟩
  rw [hsum] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Triangle-free defect degree two propagates across a second-order defect
edge. -/
theorem triangleFree_degree_two_of_secondOrder_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {x y : V} (hxy : (secondOrderDefectGraph G).Adj x y)
    (hx : (triangleFreeEdgeGraph G).degree x = 2) :
    (triangleFreeEdgeGraph G).degree y = 2 := by
  have hxmono := secondOrder_defect_local_monochromatic
    G hfree hd heven hmin hcard x
  have hxyT : (triangleFreeEdgeGraph G).Adj x y := by
    rcases hxmono with hxmono | hxmono
    · have hyMem : y ∈ triangleFreeNeighbors G x := by
        have hDmem : y ∈ (secondOrderDefectGraph G).neighborFinset x :=
          ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hxy
        rw [secondOrderDefectGraph_neighborFinset] at hDmem
        have hAempty : antipodalNeighbors G x = ∅ :=
          Finset.card_eq_zero.mp hxmono.1
        simpa [hAempty] using hDmem
      simpa [triangleFreeEdgeGraph_adj] using hyMem
    · have hxzero : (triangleFreeEdgeGraph G).degree x = 0 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
        exact hxmono.2
      omega
  rcases secondOrder_defect_local_monochromatic
      G hfree hd heven hmin hcard y with hymono | hymono
  · rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact hymono.2
  · have hzero : triangleFreeNeighbors G y = ∅ :=
      Finset.card_eq_zero.mp hymono.2
    have hmem : x ∈ triangleFreeNeighbors G y := by
      simpa [triangleFreeEdgeGraph_adj] using hxyT.symm
    rw [hzero] at hmem
    exact (Finset.notMem_empty x hmem).elim

/-- Triangle-free defect degree two is constant on every reachable class of
the second-order defect graph. -/
theorem triangleFree_degree_two_of_secondOrder_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {x y : V} (hxy : (secondOrderDefectGraph G).Reachable x y)
    (hx : (triangleFreeEdgeGraph G).degree x = 2) :
    (triangleFreeEdgeGraph G).degree y = 2 := by
  have hwalk : Relation.ReflTransGen (secondOrderDefectGraph G).Adj x y :=
    ((secondOrderDefectGraph G).reachable_iff_reflTransGen x y).mp hxy
  have hprop : ∀ {a b : V},
      Relation.ReflTransGen (secondOrderDefectGraph G).Adj a b →
      (triangleFreeEdgeGraph G).degree a = 2 →
      (triangleFreeEdgeGraph G).degree b = 2 := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hbc ih =>
        exact triangleFree_degree_two_of_secondOrder_adj
          G hfree hd heven hmin hcard hbc ih
  exact hprop hwalk hx

/-- A cyclic defect component belongs to the triangle-free color sector iff
one (and therefore every) vertex in it has triangle-free defect degree two. -/
theorem mem_triangleFreeCycleSector_iff_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    c ∈ triangleFreeCycleSector G u ↔
      (triangleFreeEdgeGraph G).degree (u c 0) = 2 := by
  constructor
  · intro hc
    have hG : G.Adj (u c 0) (u c 1) := by
      simpa using (mem_triangleFreeCycleSector_iff G u c).mp hc 0
    have hD : (secondOrderDefectGraph G).Adj (u c 0) (u c 1) := by
      rw [← (secondOrderDefectGraph G).mem_neighborFinset, huD]
      simp
    rcases secondOrder_defect_local_monochromatic
        G hfree hd heven hmin hcard (u c 0) with hmono | hmono
    · rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset]
      exact hmono.2
    · have hm := secondOrderDefectGraph_incident_edges_monochromatic
        G hfree hd heven hmin hcard hD hD
      rcases hm with hm | hm
      · have hmem := (antipodalGraph_adj G (u c 0) (u c 1)).mp hm.1
        exact ((mem_antipodalNeighbors G (u c 0) (u c 1)).mp hmem).2.1 hG |>.elim
      · have hzero : triangleFreeNeighbors G (u c 0) = ∅ :=
          Finset.card_eq_zero.mp hmono.2
        have hmem : u c 1 ∈ triangleFreeNeighbors G (u c 0) := by
          simpa [triangleFreeEdgeGraph_adj] using hm.1
        rw [hzero] at hmem
        exact (Finset.notMem_empty _ hmem).elim
  · intro hzero
    rw [mem_triangleFreeCycleSector_iff]
    intro x
    have hcx : (secondOrderDefectGraph G).connectedComponentMk (u c x) = c := by
      apply (ConnectedComponent.mem_supp_iff c (u c x)).mp
      rw [← huRange c]
      exact ⟨x, rfl⟩
    have hc0mem : u c 0 ∈ c.supp := by
      have heq := congrArg (fun S : Set V => u c 0 ∈ S) (huRange c)
      exact heq.mp ⟨0, rfl⟩
    have hc0 : (secondOrderDefectGraph G).connectedComponentMk (u c 0) = c :=
      (ConnectedComponent.mem_supp_iff c (u c 0)).mp hc0mem
    have hreach : (secondOrderDefectGraph G).Reachable (u c 0) (u c x) :=
      ConnectedComponent.eq.mp (hc0.trans hcx.symm)
    have hxdeg := triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach hzero
    have hD : (secondOrderDefectGraph G).Adj (u c x) (u c (x + 1)) := by
      rw [← (secondOrderDefectGraph G).mem_neighborFinset, huD]
      simp
    rcases secondOrder_defect_local_monochromatic
        G hfree hd heven hmin hcard (u c x) with hmono | hmono
    · have hmem : u c (x + 1) ∈ triangleFreeNeighbors G (u c x) := by
        have hDmem : u c (x + 1) ∈
            (secondOrderDefectGraph G).neighborFinset (u c x) :=
          ((secondOrderDefectGraph G).mem_neighborFinset
            (u c x) (u c (x + 1))).mpr hD
        rw [secondOrderDefectGraph_neighborFinset] at hDmem
        have hAempty : antipodalNeighbors G (u c x) = ∅ :=
          Finset.card_eq_zero.mp hmono.1
        simpa [hAempty] using hDmem
      exact (mem_triangleFreeNeighbors G (u c x) (u c (x + 1))).mp hmem |>.1
    · have hxzero : (triangleFreeEdgeGraph G).degree (u c x) = 0 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
        exact hmono.2
      omega

/-- The sector test may be made at any vertex of the component. -/
theorem mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent) {v : V}
    (hv : v ∈ c.supp) :
    c ∈ triangleFreeCycleSector G u ↔
      (triangleFreeEdgeGraph G).degree v = 2 := by
  have hvMk : (secondOrderDefectGraph G).connectedComponentMk v = c :=
    (ConnectedComponent.mem_supp_iff c v).mp hv
  have hu0mem : u c 0 ∈ c.supp := by
    have heq := congrArg (fun S : Set V => u c 0 ∈ S) (huRange c)
    exact heq.mp ⟨0, rfl⟩
  have hu0Mk : (secondOrderDefectGraph G).connectedComponentMk (u c 0) = c :=
    (ConnectedComponent.mem_supp_iff c (u c 0)).mp hu0mem
  have hreach : (secondOrderDefectGraph G).Reachable (u c 0) v :=
    ConnectedComponent.eq.mp (hu0Mk.trans hvMk.symm)
  constructor
  · intro hc
    apply triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach
    exact (mem_triangleFreeCycleSector_iff_degree_two
      G hfree hd heven hmin hcard u hu huRange huD c).mp hc
  · intro hvdeg
    apply (mem_triangleFreeCycleSector_iff_degree_two
      G hfree hd heven hmin hcard u hu huRange huD c).mpr
    exact triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach.symm hvdeg

/-- The vertex-colored order is exactly the sum of the orders of the
triangle-free cycle components. -/
theorem card_triangleFree_degree_two_eq_sum_sector_orders
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    (Finset.univ.filter fun v : V =>
        (triangleFreeEdgeGraph G).degree v = 2).card =
      ∑ c ∈ triangleFreeCycleSector G u, c.supp.ncard := by
  let S := triangleFreeCycleSector G u
  let U : Finset V := S.biUnion fun c => c.supp.toFinset
  have hsets : (Finset.univ.filter fun v : V =>
      (triangleFreeEdgeGraph G).degree v = 2) = U := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U,
      Finset.mem_biUnion]
    constructor
    · intro hv
      let c := (secondOrderDefectGraph G).connectedComponentMk v
      have hvc : v ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
      refine ⟨c, ?_, Set.mem_toFinset.mpr hvc⟩
      exact (mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
        G hfree hd heven hmin hcard u hu huRange huD c hvc).mpr hv
    · rintro ⟨c, hc, hvc⟩
      exact (mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
        G hfree hd heven hmin hcard u hu huRange huD c
        (Set.mem_toFinset.mp hvc)).mp hc
  rw [hsets]
  dsimp [U]
  rw [Finset.card_biUnion]
  · simp [S, Set.ncard_eq_toFinset_card']
  · intro c _ e _ hce
    exact Set.disjoint_toFinset.mpr
      (pairwise_disjoint_supp_connectedComponent (secondOrderDefectGraph G) hce)

/-- At the degree-six exact boundary there are either no triangle-free defect
components or exactly one.  Weighted Cauchy--Schwarz on its quotient row
restricts the latter's order to `3, 6, 9, 12, 15`. -/
theorem degreeSix_triangleFreeCycleSector_empty_or_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 6 * (6 - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard) :
    triangleFreeCycleSector G u = ∅ ∨
      ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
        triangleFreeCycleSector G u = {c} ∧
        (c.supp.ncard = 3 ∨ c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨
          c.supp.ncard = 12 ∨ c.supp.ncard = 15) := by
  let S := triangleFreeCycleSector G u
  have hle : S.card ≤ 1 := degreeSix_triangleFreeCycleSector_card_le_one
    G hfree hmin hcard u hu huRange huD hr
  have hcases : S.card = 0 ∨ S.card = 1 := by omega
  rcases hcases with hzero | hone
  · left
    exact Finset.card_eq_zero.mp hzero
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
    right
    refine ⟨c, hc, ?_⟩
    have hmod : c.supp.ncard % 3 = 0 := by
      have hcount := card_triangleFree_degree_two_eq_sum_sector_orders
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard
        u hu huRange huD
      have hcolor := degreeSix_secondOrder_colorOrder_mod_three
        G hfree hmin hcard
      rw [hcount] at hcolor
      have hc' : triangleFreeCycleSector G u = {c} := hc
      simpa [hc'] using hcolor
    let D := secondOrderDefectGraph G
    let Q := componentQuotientMatrix G D
    let size : D.ConnectedComponent → ℕ := fun e => e.supp.ncard
    have htotal : (∑ e : D.ConnectedComponent, size e) = 33 := by
      rw [sum_connectedComponent_supp_ncard D]
      norm_num at hcard ⊢
      exact hcard
    have hrow : (∑ e : D.ConnectedComponent, Q c e) = 6 := by
      exact sum_secondOrder_componentQuotientMatrix_row_eq_degree
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard c
    have hdiag : Q c c = 2 :=
      triangleFreeCycleSector_diagonalQuotient_eq_two G hfree
        (d := 6) (by norm_num) (by norm_num) hmin hcard
        u hu huRange huD hr (by
          have hcmem : c ∈ S := by rw [hc]; simp
          simpa [S] using hcmem)
    have hbal : ∀ e : D.ConnectedComponent,
        size c * Q c e = size e * Q e c := by
      intro e
      exact secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard c e
    have hsq : (∑ e : D.ConnectedComponent, Q c e * Q e c) = size c + 3 := by
      have h := secondOrder_componentQuotientMatrix_sq_apply
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard c c
      simpa [Matrix.mul_apply, Q, size, D, Nat.add_comm] using h
    have hineq := degreeSix_singleton_incidence_cauchy
      Q size c c.nonempty_supp.ncard_pos htotal hrow hdiag hbal hsq
    dsimp [size] at hineq
    have hle : c.supp.ncard ≤ 15 := by nlinarith
    omega

/-- A triangle-free-colored defect component cannot have order three: its
three rim edges would form a triangle in the triangle-free edge graph. -/
theorem triangleFreeCycleSector_component_order_ne_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c ∈ triangleFreeCycleSector G u) :
    c.supp.ncard ≠ 3 := by
  intro hthree
  have hG := (mem_triangleFreeCycleSector_iff G u c).mp hc
  have hTF : ∀ x : ZMod c.supp.ncard,
      (triangleFreeEdgeGraph G).Adj (u c x) (u c (x + 1)) := by
    intro x
    have hD : (secondOrderDefectGraph G).Adj (u c x) (u c (x + 1)) := by
      rw [← SimpleGraph.mem_neighborFinset, huD]
      simp
    rcases hD with hA | hT
    · have hnG := (mem_antipodalNeighbors G (u c x) (u c (x + 1))).mp hA
      exact (hnG.2.1 (hG x)).elim
    · exact hT
  have h01 := hTF (0 : ZMod c.supp.ncard)
  have h1m := hTF (1 : ZMod c.supp.ncard)
  have hm0 := hTF (-1 : ZMod c.supp.ncard)
  have h01' : (triangleFreeEdgeGraph G).Adj (u c 0) (u c 1) := by
    simpa using h01
  have h1m' : (triangleFreeEdgeGraph G).Adj (u c 1) (u c (-1)) := by
    have hind : (1 + 1 : ZMod c.supp.ncard) = -1 := by
      have h3zero : ((3 : ℕ) : ZMod c.supp.ncard) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact hthree.symm ▸ dvd_refl 3
      linear_combination h3zero
    rw [hind] at h1m
    exact h1m
  have hm0' : (triangleFreeEdgeGraph G).Adj (u c (-1)) (u c 0) := by
    simpa using hm0
  exact triangleFreeEdgeGraph_not_triangle G h01' h1m' hm0'

/-- In the singleton color-sector branch, its unique component has one of
the four surviving orders and its complete off-diagonal quotient row is
pinned by the degree-six row and square identities. -/
theorem degreeSix_singleton_component_quotient_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c}) :
    (c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨ c.supp.ncard = 12 ∨
      c.supp.ncard = 15) ∧
    componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 ∧
    (∑ e ∈ (Finset.univ.erase c),
      componentQuotientMatrix G (secondOrderDefectGraph G) c e) = 4 ∧
    (∑ e ∈ (Finset.univ.erase c),
      componentQuotientMatrix G (secondOrderDefectGraph G) c e *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c) =
      c.supp.ncard - 1 ∧
    ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard * componentQuotientMatrix G (secondOrderDefectGraph G) c e =
        e.supp.ncard * componentQuotientMatrix G
          (secondOrderDefectGraph G) e c := by
  have hc : c ∈ triangleFreeCycleSector G u := by rw [hsector]; simp
  have hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 :=
    triangleFreeCycleSector_diagonalQuotient_eq_two G hfree
      (d := 6) (by norm_num) (by norm_num) hmin (by norm_num at hcard ⊢; exact hcard)
      u hu huRange huD hr hc
  have hrow : (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c e) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hsq : (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c e *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c) =
      c.supp.ncard + 3 := by
    have h := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c c
    simpa [Matrix.mul_apply, Nat.add_comm] using h
  have hord := degreeSix_triangleFreeCycleSector_empty_or_singleton
    G hfree hmin (by norm_num at hcard ⊢; exact hcard)
      u hu huRange huD hr
  have hord0 : c.supp.ncard = 3 ∨ c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨
      c.supp.ncard = 12 ∨ c.supp.ncard = 15 := by
    rcases hord with hempty | ⟨e, he, heord⟩
    · rw [hsector] at hempty
      simpa using hempty
    · have hec : e = c := by
        have : c = e := by simpa [hsector] using he
        exact this.symm
      simpa [hec] using heord
  have hne3 := triangleFreeCycleSector_component_order_ne_three
    G u huD c hc
  have hordc : c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨
      c.supp.ncard = 12 ∨ c.supp.ncard = 15 := by
    omega
  have hcuniv : c ∈ (Finset.univ :
      Finset (secondOrderDefectGraph G).ConnectedComponent) :=
    Finset.mem_univ c
  have hrowErase := Finset.sum_erase_add
    (Finset.univ : Finset (secondOrderDefectGraph G).ConnectedComponent)
      (fun e ↦ componentQuotientMatrix G (secondOrderDefectGraph G) c e) hcuniv
  have hsqErase := Finset.sum_erase_add
    (Finset.univ : Finset (secondOrderDefectGraph G).ConnectedComponent)
      (fun e ↦ componentQuotientMatrix G (secondOrderDefectGraph G) c e *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c) hcuniv
  refine ⟨hordc, hdiag, ?_, ?_, ?_⟩
  · omega
  · rw [hdiag] at hsqErase
    omega
  · intro e
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c e

/-- Graph instantiation of the forced contact in the order-six singleton
branch.  The contact target is a distinct order-three component with quotient
entries `1` forward and `2` backward. -/
theorem degreeSix_orderSix_singleton_exists_orderThree_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hsector : triangleFreeCycleSector G u = {c})
    (hc6 : c.supp.ncard = 6) :
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ c ∧ e.supp.ncard = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 1 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 2 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e e = 0 ∧
      (∑ t ∈ (Finset.univ.erase e).erase c,
        componentQuotientMatrix G (secondOrderDefectGraph G) e t) = 4 ∧
      ∀ t : (secondOrderDefectGraph G).ConnectedComponent,
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) e t →
        componentQuotientMatrix G (secondOrderDefectGraph G) t e = 1 ∧
          t.supp.ncard = 3 *
            componentQuotientMatrix G (secondOrderDefectGraph G) e t := by
  obtain ⟨_, hdiag, hrow, hprod, hbal⟩ :=
    degreeSix_singleton_component_quotient_row
      G hfree hmin hcard u hu huRange huD hr c hsector
  obtain ⟨e, hne, he3, hce, hec⟩ := degreeSix_orderSix_singleton_contact
    (componentQuotientMatrix G (secondOrderDefectGraph G))
      (fun e ↦ e.supp.ncard) c hc6 hrow
      (by simpa [hc6] using hprod) hbal
  have hediag : componentQuotientMatrix G
      (secondOrderDefectGraph G) e e = 0 := by
    rcases oddComponent_diagonalQuotient_eq_zero_or_two
      G hfree (d := 6) (r := e.supp.ncard)
        (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) (hr e)
        (by rw [he3]; norm_num) e (u e) (hu e) (huRange e) (huD e) with
      hzero | htwo
    · exact hzero
    · have hcen : c ≠ e := fun h ↦ hne h.symm
      have hsq := secondOrder_componentQuotientMatrix_sq_apply
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) c e
      have hsum : (∑ t,
          componentQuotientMatrix G (secondOrderDefectGraph G) c t *
            componentQuotientMatrix G (secondOrderDefectGraph G) t e) = 3 := by
        simpa [Matrix.mul_apply, hcen, he3] using hsq
      have hlower := two_distinct_terms_le_sum
        (fun t ↦ componentQuotientMatrix G (secondOrderDefectGraph G) c t *
          componentQuotientMatrix G (secondOrderDefectGraph G) t e) hcen
      rw [hdiag, hce, htwo, hsum] at hlower
      omega
  have hrowe := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e
  refine ⟨e, hne, he3, hce, hec, hediag, ?_, ?_⟩
  · have heMem : e ∈ (Finset.univ :
        Finset (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_univ e
    have hcMem : c ∈ (Finset.univ.erase e :
        Finset (secondOrderDefectGraph G).ConnectedComponent) :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ c⟩
    have hsplitE := Finset.sum_erase_add
      (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ componentQuotientMatrix G (secondOrderDefectGraph G) e t) heMem
    have hsplitC := Finset.sum_erase_add
      (Finset.univ.erase e : Finset
        (secondOrderDefectGraph G).ConnectedComponent)
      (fun t ↦ componentQuotientMatrix G (secondOrderDefectGraph G) e t) hcMem
    omega
  have hsqe := secondOrder_componentQuotientMatrix_sq_apply
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e e
  have hprode : (∑ t,
      componentQuotientMatrix G (secondOrderDefectGraph G) e t *
        componentQuotientMatrix G (secondOrderDefectGraph G) t e) = 6 := by
    simpa [Matrix.mul_apply, he3] using hsqe
  have hreverse := reverse_eq_one_of_balanced_row_product_eq_row
    (componentQuotientMatrix G (secondOrderDefectGraph G))
      (fun t ↦ t.supp.ncard) e (by rw [he3]; norm_num)
      (fun t ↦ secondOrder_componentQuotientMatrix_balance
        G hfree (d := 6) (by norm_num) (by norm_num) hmin
          (by norm_num at hcard ⊢; exact hcard) e t)
      (by rw [hprode, hrowe])
  intro t hpos
  have hte := hreverse t hpos
  refine ⟨hte, ?_⟩
  have hbt := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) e t
  rw [he3, hte, mul_one] at hbt
  exact hbt.symm

/-- In the empty color-sector branch, the all-triangle defect decomposition
is impossible; hence an antipodal-colored defect cycle of order at least four
exists. -/
theorem degreeSix_exists_large_antipodal_component_of_sector_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hempty : triangleFreeCycleSector G u = ∅) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      4 ≤ c.supp.ncard ∧ c ∉ triangleFreeCycleSector G u := by
  by_contra hnone
  push Not at hnone
  have hthree : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3 := by
    intro c
    have hcnot : c ∉ triangleFreeCycleSector G u := by rw [hempty]; simp
    have hlt : ¬ 4 ≤ c.supp.ncard := fun hfour => hcnot (hnone c hfour)
    have hlower := hr c
    omega
  exact no_degreeSix_boundary_of_secondOrder_all_triangles
    G hfree hmin hcard hthree

end

end Erdos85
