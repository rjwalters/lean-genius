import Proofs.Erdos85DoubleCoverTargetUniqueness
import Proofs.Erdos85SquareMinimumLeakageArithmetic
import Proofs.Erdos85SquareQuotientGraphBound

/-!
# Leakage collapse for a unit minimum layer

This file applies cyclic-cover target uniqueness to the exact-square
component quotient.  Distinct minimum components cannot use the same larger
target.  Detailed balance then identifies each positive incidence with the
target's normalized component order, so total quotient leakage is paid for
by coefficient mass outside the minimum layer.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Total leakage from a coefficient-one minimum layer is bounded by all
coefficient mass outside that layer.** -/
theorem secondOrder_square_unitLayer_totalLeakage_le_outsideWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc₀unit : c₀.supp.ncard / p = 1) :
    let C := (secondOrderDefectGraph G).ConnectedComponent
    let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
    let M : Finset C := Finset.univ.filter
      (fun c ↦ c.supp.ncard = c₀.supp.ncard)
    (∑ c ∈ M, ∑ e ∈ Finset.univ \ M, Q c e) ≤ N - M.card := by
  classical
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let Q := componentQuotientMatrix G D
  let M : Finset C := Finset.univ.filter
    (fun c ↦ c.supp.ncard = c₀.supp.ncard)
  let w : C → ℕ := fun c ↦ c.supp.ncard / p
  have hpPos : 0 < p := hp.pos
  have hc₀Size : c₀.supp.ncard = p := by
    calc
      c₀.supp.ncard = p * (c₀.supp.ncard / p) :=
        (Nat.mul_div_cancel' (hall c₀)).symm
      _ = p := by rw [hc₀unit, mul_one]
  have hcoeffSum : ∑ c : C, w c = N := by
    have hsumSizes : (∑ c : C, c.supp.ncard) = N * p := by
      rw [sum_connectedComponent_supp_ncard D, hcard]
      exact hboundary
    have hmul : p * (∑ c : C, w c) = p * N := by
      calc
        p * (∑ c : C, w c) = ∑ c : C, p * w c := by
          rw [Finset.mul_sum]
        _ = ∑ c : C, c.supp.ncard := by
          apply Finset.sum_congr rfl
          intro c hc
          exact Nat.mul_div_cancel' (hall c)
        _ = N * p := hsumSizes
        _ = p * N := Nat.mul_comm N p
    exact Nat.eq_of_mul_eq_mul_left hpPos hmul
  have hunit : ∀ c ∈ M, w c = 1 := by
    intro c hc
    have hcSize : c.supp.ncard = c₀.supp.ncard :=
      (Finset.mem_filter.mp hc).2
    dsimp only [w]
    rw [hcSize, hc₀unit]
  have hminimum : ∀ c ∈ M, ∀ e : C, c.supp.ncard ≤ e.supp.ncard := by
    intro c hc e
    rw [(Finset.mem_filter.mp hc).2]
    exact hc₀min e
  have hlarger : ∀ c ∈ M, ∀ e ∈ Finset.univ \ M,
      c.supp.ncard < e.supp.ncard := by
    intro c hc e he
    have hle := hminimum c hc e
    have heNot : e ∉ M := (Finset.mem_sdiff.mp he).2
    have hne : e.supp.ncard ≠ c₀.supp.ncard := by
      intro heq
      exact heNot (Finset.mem_filter.mpr ⟨Finset.mem_univ e, heq⟩)
    have hcEq := (Finset.mem_filter.mp hc).2
    rw [hcEq] at hle ⊢
    omega
  have hunique : ∀ c₁ ∈ M, ∀ c₂ ∈ M,
      ∀ e ∈ Finset.univ \ M, 0 < Q c₁ e → 0 < Q c₂ e → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ e he hpos₁ hpos₂
    apply secondOrder_minimum_largerTarget_source_unique
      G hfree hd heven hmin hcard c₁ c₂ e
        (hminimum c₁ hc₁)
    · rw [(Finset.mem_filter.mp hc₁).2,
        (Finset.mem_filter.mp hc₂).2]
    · exact hlarger c₁ hc₁ e he
    · simpa [Q, D] using hpos₁
    · simpa [Q, D] using hpos₂
  have hexact : ∀ c ∈ M, ∀ e ∈ Finset.univ \ M,
      0 < Q c e → Q c e = w e := by
    intro c hc e he hpos
    have hs := secondOrder_minimumComponent_longer_edge_structure
      G hfree hd heven hmin hcard c e (hminimum c hc)
        (hlarger c hc e he) (by simpa [Q, D] using hpos)
    have hcSize : c.supp.ncard = p := by
      rw [(Finset.mem_filter.mp hc).2, hc₀Size]
    have heSize : e.supp.ncard = p * w e := by
      exact (Nat.mul_div_cancel' (hall e)).symm
    dsimp only [Q, D] at hpos ⊢
    dsimp only [w] at heSize
    rw [hcSize, heSize] at hs
    exact Nat.eq_of_mul_eq_mul_left hpPos hs.2.2.1
  exact unitLayer_total_incidence_le_outsideWeight
    M Q w N hunit hcoeffSum hunique hexact

/-- **Rowwise Cauchy inequality for the unit minimum layer.** -/
theorem secondOrder_square_unitLayer_row_cauchy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hdEq : d = s * s + 3)
    (c₀ c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀Size : c₀.supp.ncard = p)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc : c.supp.ncard = c₀.supp.ncard) :
    let C := (secondOrderDefectGraph G).ConnectedComponent
    let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
    let M : Finset C := Finset.univ.filter
      (fun e ↦ e.supp.ncard = c₀.supp.ncard)
    let L := ∑ e ∈ Finset.univ \ M, Q c e
    ((d : ℚ) - L) ^ 2 ≤ (M.card : ℚ) * ((s * s + p : ℕ) - L) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let Q := componentQuotientMatrix G D
  let M : Finset C := Finset.univ.filter
    (fun e ↦ e.supp.ncard = c₀.supp.ncard)
  let L := ∑ e ∈ Finset.univ \ M, Q c e
  change ((d : ℚ) - L) ^ 2 ≤
    (M.card : ℚ) * (((s * s + p : ℕ) : ℚ) - L)
  have hcmin : ∀ e : C, c.supp.ncard ≤ e.supp.ncard := by
    intro e
    rw [hc]
    exact hc₀min e
  have hrow := sum_secondOrder_componentQuotientMatrix_row_eq_degree
    G hfree hd heven hmin hcard c
  have hsplit := Finset.sum_sdiff (f := fun e ↦ Q c e)
    (Finset.subset_univ M)
  have hrowQ : ∑ e : C, Q c e = d := by
    simpa only [Q, D] using hrow
  have hinsideNat : ∑ e ∈ M, Q c e = d - L := by
    rw [hrowQ] at hsplit
    change L + ∑ e ∈ M, Q c e = d at hsplit
    omega
  have hLd : L ≤ d := by
    rw [hrowQ] at hsplit
    change L + ∑ e ∈ M, Q c e = d at hsplit
    omega
  have hexcessZ := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hmin hcard c hcmin
  have hexcessM :
      (∑ e ∈ M, (Q c e : ℤ) * ((Q c e : ℤ) - 1)) =
        (c.supp.ncard : ℤ) - 3 := by
    rw [Finset.sum_filter]
    simpa only [M, Q, D, hc] using hexcessZ
  have hexcessQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hexcessM
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
    Int.cast_one] at hexcessQ
  have hcSize : c.supp.ncard = p := hc.trans hc₀Size
  rw [hcSize] at hexcessQ
  have hinsideQ : (∑ e ∈ M, (Q c e : ℚ)) = (d : ℚ) - L := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ℚ)) hinsideNat
    rw [Nat.cast_sub hLd] at hcast
    simpa using hcast
  have hsumsqQ : (∑ e ∈ M, (Q c e : ℚ) ^ 2) =
      (s : ℚ) * s + p - L := by
    calc
      _ = ∑ e ∈ M,
          ((Q c e : ℚ) * ((Q c e : ℚ) - 1) + (Q c e : ℚ)) := by
            apply Finset.sum_congr rfl
            intro e he
            ring
      _ = (∑ e ∈ M, (Q c e : ℚ) * ((Q c e : ℚ) - 1)) +
          ∑ e ∈ M, (Q c e : ℚ) := by rw [Finset.sum_add_distrib]
      _ = ((p : ℚ) - 3) + ((d : ℚ) - L) := by
        rw [hexcessQ, hinsideQ]
        norm_num
      _ = (s : ℚ) * s + p - L := by
        rw [hdEq]
        push_cast
        ring
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := M) (f := fun e ↦ (Q c e : ℚ))
  rw [hinsideQ, hsumsqQ] at hCS
  simpa only [Nat.cast_add, Nat.cast_mul] using hCS

/-- **The unit minimum layer has subunit average leakage.** -/
theorem secondOrder_square_unitLayer_totalLeakage_lt_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s)
    (hNEq : N = d - s) (hs7 : 7 ≤ s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc₀unit : c₀.supp.ncard / p = 1) :
    let C := (secondOrderDefectGraph G).ConnectedComponent
    let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
    let M : Finset C := Finset.univ.filter
      (fun c ↦ c.supp.ncard = c₀.supp.ncard)
    let L : C → ℕ := fun c ↦ ∑ e ∈ Finset.univ \ M, Q c e
    2 ≤ M.card → ∑ c ∈ M, L c < M.card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let Q := componentQuotientMatrix G D
  let M : Finset C := Finset.univ.filter
    (fun c ↦ c.supp.ncard = c₀.supp.ncard)
  let L : C → ℕ := fun c ↦ ∑ e ∈ Finset.univ \ M, Q c e
  intro hM2
  change ∑ c ∈ M, L c < M.card
  have hc₀Size : c₀.supp.ncard = p := by
    calc
      c₀.supp.ncard = p * (c₀.supp.ncard / p) :=
        (Nat.mul_div_cancel' (hall c₀)).symm
      _ = p := by rw [hc₀unit, mul_one]
  have hmass := secondOrder_square_unitLayer_totalLeakage_le_outsideWeight
    G hfree hd heven hmin hcard hp hboundary hall c₀ hc₀min hc₀unit
  change (∑ c ∈ M, L c) ≤ N - M.card at hmass
  let I := {c // c ∈ M}
  let LQ : I → ℚ := fun c ↦ (L c.1 : ℕ)
  have hcardI : (Fintype.card I : ℚ) = (M.card : ℚ) := by
    simp [I]
  have hsumI : (∑ c : I, LQ c) = ((∑ c ∈ M, L c : ℕ) : ℚ) := by
    push_cast
    simpa [I, LQ] using Finset.sum_attach M (fun c ↦ (L c : ℚ))
  have hrowI : ∀ c : I,
      ((d : ℚ) - LQ c) ^ 2 ≤
        (M.card : ℚ) * ((s * s + p : ℕ) - LQ c) := by
    intro c
    have hcSize : c.1.supp.ncard = c₀.supp.ncard :=
      (Finset.mem_filter.mp c.2).2
    simpa only [LQ, L, M, Q, D, Nat.cast_add, Nat.cast_mul] using
      secondOrder_square_unitLayer_row_cauchy
        G hfree hd heven hmin hcard hdEq c₀ c.1 hc₀Size hc₀min hcSize
  have hagg := aggregate_minimumLayer_row_cauchy
    (I := I) (d : ℚ) ((s * s + p : ℕ) : ℚ) (M.card : ℚ)
      ((∑ c ∈ M, L c : ℕ) : ℚ) LQ hcardI hsumI
      (fun c ↦ by simpa only [Nat.cast_add, Nat.cast_mul] using hrowI c)
  have hmassQ : (M.card : ℚ) + ((∑ c ∈ M, L c : ℕ) : ℚ) ≤ N := by
    let w : C → ℕ := fun c ↦ c.supp.ncard / p
    have hpPos : 0 < p := hp.pos
    have hcoeffSum : ∑ c : C, w c = N := by
      have hsumSizes : (∑ c : C, c.supp.ncard) = N * p := by
        rw [sum_connectedComponent_supp_ncard D, hcard]
        exact hboundary
      have hmul : p * (∑ c : C, w c) = p * N := by
        calc
          p * (∑ c : C, w c) = ∑ c : C, p * w c := by
            rw [Finset.mul_sum]
          _ = ∑ c : C, c.supp.ncard := by
            apply Finset.sum_congr rfl
            intro c hc
            exact Nat.mul_div_cancel' (hall c)
          _ = N * p := hsumSizes
          _ = p * N := Nat.mul_comm N p
      exact Nat.eq_of_mul_eq_mul_left hpPos hmul
    have hMle : M.card ≤ N := by
      calc
        M.card = ∑ _c ∈ M, 1 := by simp
        _ = ∑ c ∈ M, w c := by
          apply Finset.sum_congr rfl
          intro c hc
          have hcSize := (Finset.mem_filter.mp hc).2
          dsimp only [w]
          rw [hcSize, hc₀unit]
        _ ≤ ∑ c : C, w c := Finset.sum_le_sum_of_subset
          (Finset.subset_univ M)
        _ = N := hcoeffSum
    exact_mod_cast (by omega : M.card + ∑ c ∈ M, L c ≤ N)
  have hltQ := square_minimum_totalLeakage_lt_card
    (s : ℚ) d p N (M.card : ℚ) ((∑ c ∈ M, L c : ℕ) : ℚ)
      (by exact_mod_cast hs7) (by exact_mod_cast hM2) (by positivity)
      (by exact_mod_cast hdEq) (by exact_mod_cast hpEq)
      (by
        have hsd : s ≤ d := by rw [hdEq]; nlinarith
        exact_mod_cast hNEq)
      hmassQ (by simpa only [Nat.cast_add, Nat.cast_mul] using hagg)
  exact_mod_cast hltQ

/-- With at least two minimum components, one minimum component has no
quotient edge to any larger component. -/
theorem exists_secondOrder_square_unitComponent_zeroLeakage
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s)
    (hNEq : N = d - s) (hs7 : 7 ≤ s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc₀unit : c₀.supp.ncard / p = 1) :
    let C := (secondOrderDefectGraph G).ConnectedComponent
    let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
    let M : Finset C := Finset.univ.filter
      (fun c ↦ c.supp.ncard = c₀.supp.ncard)
    2 ≤ M.card → ∃ c ∈ M, ∑ e ∈ Finset.univ \ M, Q c e = 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let Q := componentQuotientMatrix G D
  let M : Finset C := Finset.univ.filter
    (fun c ↦ c.supp.ncard = c₀.supp.ncard)
  let L : C → ℕ := fun c ↦ ∑ e ∈ Finset.univ \ M, Q c e
  intro hM2
  have htotal := secondOrder_square_unitLayer_totalLeakage_lt_card
    G hfree hd heven hmin hcard hp hboundary hdEq hpEq hNEq hs7 hall
      c₀ hc₀min hc₀unit hM2
  change ∑ c ∈ M, L c < M.card at htotal
  let I := {c // c ∈ M}
  have hgap : ∀ c : I, 0 < L c.1 → 2 ≤ L c.1 := by
    intro c hcpos
    have hne : ∑ e ∈ Finset.univ \ M, Q c.1 e ≠ 0 := by
      simpa [L] using (Nat.ne_of_gt hcpos)
    obtain ⟨e, he, he0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hepos : 0 < Q c.1 e := Nat.pos_of_ne_zero he0
    have hcSize : c.1.supp.ncard = c₀.supp.ncard :=
      (Finset.mem_filter.mp c.2).2
    have hcmin : ∀ l : C, c.1.supp.ncard ≤ l.supp.ncard := by
      intro l
      rw [hcSize]
      exact hc₀min l
    have heNot : e ∉ M := (Finset.mem_sdiff.mp he).2
    have hlt : c.1.supp.ncard < e.supp.ncard := by
      have hle := hcmin e
      have hneSize : e.supp.ncard ≠ c₀.supp.ncard := by
        intro hes
        exact heNot (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hes⟩)
      omega
    have hq2 : 2 ≤ Q c.1 e := by
      by_contra hq
      have hq1 : Q c.1 e = 1 := by omega
      have hs := secondOrder_minimumComponent_longer_edge_structure
        G hfree hd heven hmin hcard c.1 e hcmin hlt
          (by simpa [Q, D] using hepos)
      dsimp only [Q, D] at hq1
      rw [hq1, mul_one] at hs
      omega
    have hleSum : Q c.1 e ≤ L c.1 := by
      dsimp only [L]
      exact Finset.single_le_sum
        (fun x _ ↦ Nat.zero_le (Q c.1 x)) he
    omega
  have hsumI : ∑ c : I, L c.1 < Fintype.card I := by
    have hsumEq : (∑ c : I, L c.1) = ∑ c ∈ M, L c := by
      exact (Finset.sum_subtype M (fun _ ↦ Iff.rfl) L).symm
    rw [hsumEq]
    have hcardEq : Fintype.card I = M.card := by simp [I]
    rw [hcardEq]
    exact htotal
  obtain ⟨c, hc0⟩ := exists_zero_of_total_lt_card_of_pos_ge_two
    (fun c : I ↦ L c.1) hgap hsumI
  refine ⟨c.1, c.2, ?_⟩
  change L c.1 = 0
  exact hc0

/-- **Leakage collapse.**  If the coefficient-one minimum layer has at
least two components, then in fact every defect component has order `p`. -/
theorem secondOrder_square_unitLayer_all_equal_of_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s)
    (hNEq : N = d - s) (hs7 : 7 ≤ s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc₀unit : c₀.supp.ncard / p = 1)
    (hM2 : 2 ≤ (Finset.univ.filter
      (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        c.supp.ncard = c₀.supp.ncard)).card) :
    ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = p := by
  classical
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let Q := componentQuotientMatrix G D
  let M : Finset C := Finset.univ.filter
    (fun c ↦ c.supp.ncard = c₀.supp.ncard)
  let L : C → ℕ := fun c ↦ ∑ e ∈ Finset.univ \ M, Q c e
  have hc₀Size : c₀.supp.ncard = p := by
    calc
      c₀.supp.ncard = p * (c₀.supp.ncard / p) :=
        (Nat.mul_div_cancel' (hall c₀)).symm
      _ = p := by rw [hc₀unit, mul_one]
  obtain ⟨c, hcM, hcZero⟩ :=
    exists_secondOrder_square_unitComponent_zeroLeakage
      G hfree hd heven hmin hcard hp hboundary hdEq hpEq hNEq hs7 hall
        c₀ hc₀min hc₀unit (by simpa [M] using hM2)
  change c ∈ M at hcM
  change L c = 0 at hcZero
  have hrowQ : ∀ f : C, ∑ e, Q f e = d := by
    intro f
    simpa only [Q, D] using
      sum_secondOrder_componentQuotientMatrix_row_eq_degree
        G hfree hd heven hmin hcard f
  have hsqQ : ∀ e ∈ M, ∑ f, Q c f * Q f e =
      s * s * (if c = e then 1 else 0) + p := by
    intro e he
    have hsquare := secondOrder_componentQuotientMatrix_sq_apply
      G hfree hd heven hmin hcard c e
    have heSize : e.supp.ncard = p := by
      calc
        e.supp.ncard = c₀.supp.ncard := (Finset.mem_filter.mp he).2
        _ = p := hc₀Size
    simp only [Matrix.mul_apply, D] at hsquare
    rw [heSize] at hsquare
    have hd3 : d - 3 = s * s := by omega
    rw [hd3] at hsquare
    simpa [mul_assoc] using hsquare
  have hweightedIdentity := zeroLeakage_row_weighted_identity
    M Q L c d s p hcM hrowQ (fun _ ↦ rfl) hcZero hsqQ
  let S := ∑ f ∈ M, L f
  let W := ∑ f ∈ M, Q c f * L f
  change W + s * s + p * M.card = d * d at hweightedIdentity
  have hmass := secondOrder_square_unitLayer_totalLeakage_le_outsideWeight
    G hfree hd heven hmin hcard hp hboundary hall c₀ hc₀min hc₀unit
  change S ≤ N - M.card at hmass
  have hcoeffSum : ∑ f : C, f.supp.ncard / p = N := by
    have hsumSizes : (∑ f : C, f.supp.ncard) = N * p := by
      rw [sum_connectedComponent_supp_ncard D, hcard]
      exact hboundary
    have hmul : p * (∑ f : C, f.supp.ncard / p) = p * N := by
      calc
        _ = ∑ f : C, p * (f.supp.ncard / p) := by rw [Finset.mul_sum]
        _ = ∑ f : C, f.supp.ncard := by
          apply Finset.sum_congr rfl
          intro f hf
          exact Nat.mul_div_cancel' (hall f)
        _ = N * p := hsumSizes
        _ = p * N := Nat.mul_comm N p
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmul
  have hMle : M.card ≤ N := by
    calc
      M.card = ∑ _f ∈ M, 1 := by simp
      _ = ∑ f ∈ M, f.supp.ncard / p := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [(Finset.mem_filter.mp hf).2, hc₀unit]
      _ ≤ ∑ f : C, f.supp.ncard / p :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ M)
      _ = N := hcoeffSum
  have hQle : ∀ f : C, Q c f ≤ d := by
    intro f
    rw [← hrowQ c]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ f)
  have hWle : W ≤ d * S := by
    dsimp only [W, S]
    calc
      _ ≤ ∑ f ∈ M, d * L f := by
        apply Finset.sum_le_sum
        intro f hf
        exact Nat.mul_le_mul_right (L f) (hQle f)
      _ = d * ∑ f ∈ M, L f := by rw [Finset.mul_sum]
  have hfactor : d * d = s * s + p * N := by
    have hsd : s ≤ d := by rw [hdEq]; nlinarith
    have hNadd : N + s = d := by omega
    rw [hpEq]
    nlinarith
  have hW : W = p * (N - M.card) := by
    rw [hfactor] at hweightedIdentity
    have hpk : p * M.card ≤ p * N :=
      Nat.mul_le_mul_left p hMle
    calc
      W = p * N - p * M.card := by omega
      _ = p * (N - M.card) :=
        (Nat.mul_sub_left_distrib p N M.card).symm
  have hNM := outsideMass_eq_zero_of_zeroLeakage_row
    p d N M.card S W (by omega) hMle hmass hWle hW
  intro e
  by_contra heSize
  have heNot : e ∉ M := by
    intro heM
    have : e.supp.ncard = p :=
      (Finset.mem_filter.mp heM).2.trans hc₀Size
    exact heSize this
  have heWeightPos : 0 < e.supp.ncard / p :=
    Nat.div_pos (Nat.le_of_dvd e.nonempty_supp.ncard_pos (hall e)) hp.pos
  have houtsideLe : e.supp.ncard / p ≤
      ∑ f ∈ Finset.univ \ M, f.supp.ncard / p := by
    exact Finset.single_le_sum
      (f := fun f : C ↦ f.supp.ncard / p) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, heNot⟩)
  have hsplitCoeff := Finset.sum_sdiff
    (f := fun f : C ↦ f.supp.ncard / p) (Finset.subset_univ M)
  have hinsideCoeff : ∑ f ∈ M, f.supp.ncard / p = M.card := by
    calc
      _ = ∑ _f ∈ M, 1 := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [(Finset.mem_filter.mp hf).2, hc₀unit]
      _ = M.card := by simp
  rw [hcoeffSum, hinsideCoeff, hNM] at hsplitCoeff
  omega

/-- **Unit-layer dichotomy.**  Either there is at most one coefficient-one
component, or every defect component has the common order `p`. -/
theorem secondOrder_square_unitLayer_card_le_one_or_all_equal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s)
    (hNEq : N = d - s) (hs7 : 7 ≤ s)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hc₀unit : c₀.supp.ncard / p = 1) :
    (Finset.univ.filter
      (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        c.supp.ncard = c₀.supp.ncard)).card ≤ 1 ∨
      ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        c.supp.ncard = p := by
  by_cases htwo : 2 ≤ (Finset.univ.filter
      (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        c.supp.ncard = c₀.supp.ncard)).card
  · right
    exact secondOrder_square_unitLayer_all_equal_of_two
      G hfree hd heven hmin hcard hp hboundary hdEq hpEq hNEq hs7 hall
        c₀ hc₀min hc₀unit htwo
  · left
    omega

end

end Erdos85
