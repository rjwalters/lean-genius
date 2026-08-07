import Proofs.Erdos85MinimumLayerCrossPairIdentity

/-!
# The minimum-layer Gram matrix equation

Restricted to the minimum layer `M` of the second-order defect partition,
the component quotient matrix `R = Q|M` is symmetric (detailed balance
between equal orders), and its square satisfies the exact design equation

`(R²)(c,c') = w`  for `c ≠ c'`, and `(R²)(c,c) = (w - 3) + S(c)`,

where `w` is the minimum order and `S(c)` the row sum of `R`.  The
off-diagonal constancy follows from the weighted Gram identity: strictly
larger components see the minimum layer at most once, so they contribute
nothing to a product over two distinct minimum columns.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Equal orders give symmetric quotient entries.** -/
theorem componentQuotientMatrix_symm_of_ncard_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hsame : c.supp.ncard = e.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e =
      componentQuotientMatrix G (secondOrderDefectGraph G) e c := by
  have hreg : ∀ x : V, (secondOrderDefectGraph G).degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree hd heven hmin hcard
  have hbal := componentQuotientMatrix_balance
    G (secondOrderDefectGraph G) 2 hreg hcomm c e
  rw [hsame] at hbal
  have hpos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
  exact Nat.eq_of_mul_eq_mul_left hpos hbal

/-- **Off-diagonal quotient entries are strictly below the target order.**
If every vertex of one component were adjacent to all of another, any two
vertices of each would form a four-cycle. -/
theorem componentQuotientMatrix_lt_ncard_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) (hne : c ≠ c')
    (hc2 : 2 ≤ c.supp.ncard) (hc'2 : 2 ≤ c'.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c' <
      c'.supp.ncard := by
  classical
  have hreg : ∀ x : V, (secondOrderDefectGraph G).degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree hd heven hmin hcard
  have hsubset : ∀ x : V,
      componentNeighborFinset G (secondOrderDefectGraph G) c' x ⊆
        c'.supp.toFinset := by
    intro x y hy
    rw [Set.mem_toFinset]
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (Finset.mem_filter.mp hy).2
  have hle : componentQuotientMatrix G (secondOrderDefectGraph G) c c' ≤
      c'.supp.ncard := by
    rw [componentQuotientMatrix]
    calc
      (componentNeighborFinset G (secondOrderDefectGraph G) c'
          (componentRepresentative (secondOrderDefectGraph G) c)).card ≤
          c'.supp.toFinset.card :=
        Finset.card_le_card (hsubset _)
      _ = c'.supp.ncard := (Set.ncard_eq_toFinset_card' c'.supp).symm
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  exfalso
  -- Equality forces every vertex of `c` to see all of `c'`.
  have hall : ∀ x ∈ c.supp, ∀ y ∈ c'.supp, G.Adj x y := by
    intro x hx y hy
    have hxcard : (componentNeighborFinset G (secondOrderDefectGraph G)
        c' x).card = c'.supp.ncard := by
      rw [← componentQuotientMatrix_apply_eq G (secondOrderDefectGraph G)
        2 hreg hcomm c c' hx]
      exact heq
    have hfull : componentNeighborFinset G (secondOrderDefectGraph G)
        c' x = c'.supp.toFinset := by
      apply Finset.eq_of_subset_of_card_le (hsubset x)
      rw [hxcard, Set.ncard_eq_toFinset_card' c'.supp]
    have hymem : y ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c' x := by
      rw [hfull, Set.mem_toFinset]
      exact hy
    have := (Finset.mem_filter.mp hymem).1
    exact (SimpleGraph.mem_neighborFinset G x y).mp this
  -- Two vertices on each side give a four-cycle.
  have hcfin : c.supp.toFinset.card = c.supp.ncard :=
    (Set.ncard_eq_toFinset_card' c.supp).symm
  have hc'fin : c'.supp.toFinset.card = c'.supp.ncard :=
    (Set.ncard_eq_toFinset_card' c'.supp).symm
  obtain ⟨x, hx, x', hx', hxx⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < c.supp.toFinset.card)
  obtain ⟨y, hy, y', hy', hyy⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < c'.supp.toFinset.card)
  rw [Set.mem_toFinset] at hx hx'
  rw [Set.mem_toFinset] at hy hy' 
  exact hfree (containsC4_of_two_common hxx hyy
    (hall x hx y hy).symm (hall x' hx' y hy).symm
    (hall x hx y' hy').symm (hall x' hx' y' hy').symm)

/-- **The restricted Gram square is constant off the diagonal.**  For two
distinct minimum-layer components, the minimum-layer product sum equals the
minimum order. -/
theorem secondOrder_minimumLayer_gramSquare_offDiag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = c₀.supp.ncard)
    (hc' : c'.supp.ncard = c₀.supp.ncard) (hne : c ≠ c') :
    (∑ e ∈ Finset.univ.filter
        (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
          x.supp.ncard = c₀.supp.ncard),
      componentQuotientMatrix G (secondOrderDefectGraph G) e c *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c') =
      c₀.supp.ncard := by
  classical
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun x ↦ x.supp.ncard = c₀.supp.ncard) with hM
  set QM := componentQuotientMatrix G (secondOrderDefectGraph G) with hQM
  have hwpos : 0 < c₀.supp.ncard := c₀.nonempty_supp.ncard_pos
  -- The full weighted Gram identity.
  have hGram := sum_ncard_mul_componentQuotient_eq_of_ne
    G hfree hd heven hmin hcard c c' hne
  rw [← hQM, hc, hc'] at hGram
  -- Split off the strictly larger components; they contribute nothing.
  have hzero : ∀ e ∈ Finset.univ \ M,
      e.supp.ncard * (QM e c * QM e c') = 0 := by
    intro e he
    have heM : e ∉ M := (Finset.mem_sdiff.mp he).2
    have hlt : c₀.supp.ncard < e.supp.ncard := by
      have : e.supp.ncard ≠ c₀.supp.ncard := by
        intro h
        exact heM (by rw [hM]; simp [h])
      exact lt_of_le_of_ne (hc₀min e) (Ne.symm this)
    have hrow := secondOrder_largerComponent_minLayerRow_le_one
      G hfree hd heven hmin hcard c₀ hc₀min e hlt
    rw [← hQM, ← hM] at hrow
    have hcM : c ∈ M := by
      rw [hM]; simp [hc]
    have hc'M : c' ∈ M := by
      rw [hM]; simp [hc']
    -- The row hits at most one minimum column, so one factor vanishes.
    by_cases hcz : QM e c = 0
    · rw [hcz, zero_mul, mul_zero]
    · have hcpos : 1 ≤ QM e c := Nat.one_le_iff_ne_zero.mpr hcz
      have hc'z : QM e c' = 0 := by
        by_contra hc'z
        have hc'pos : 1 ≤ QM e c' := Nat.one_le_iff_ne_zero.mpr hc'z
        have hsum : 2 ≤ ∑ x ∈ M, QM e x := by
          have hpair : QM e c + QM e c' ≤ ∑ x ∈ M, QM e x := by
            have := Finset.add_sum_erase M (QM e) hcM
            have hmem' : c' ∈ M.erase c :=
              Finset.mem_erase.mpr ⟨Ne.symm hne, hc'M⟩
            calc
              QM e c + QM e c' ≤
                  QM e c + ∑ x ∈ M.erase c, QM e x := by
                have := Finset.single_le_sum
                  (fun x _ ↦ Nat.zero_le (QM e x)) hmem'
                omega
              _ = ∑ x ∈ M, QM e x :=
                Finset.add_sum_erase M (QM e) hcM
          omega
        omega
      rw [hc'z, mul_zero, mul_zero]
  have hsplit :
      (∑ e ∈ Finset.univ \ M, e.supp.ncard * (QM e c * QM e c')) +
        ∑ e ∈ M, e.supp.ncard * (QM e c * QM e c') =
        ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          e.supp.ncard * (QM e c * QM e c') :=
    Finset.sum_sdiff (Finset.subset_univ M)
  rw [Finset.sum_eq_zero hzero, zero_add] at hsplit
  rw [← hsplit] at hGram
  -- Inside the minimum layer every order is `w`.
  have hMsum :
      (∑ e ∈ M, e.supp.ncard * (QM e c * QM e c')) =
        c₀.supp.ncard * ∑ e ∈ M, QM e c * QM e c' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have := (Finset.mem_filter.mp (hM ▸ he)).2
    rw [this]
  rw [hMsum] at hGram
  exact Nat.eq_of_mul_eq_mul_left hwpos hGram

/-- **The restricted Gram square on the diagonal.**  For a minimum-layer
component `c`, the minimum-layer square sum is the equal-size excess plus
the restricted row sum. -/
theorem secondOrder_minimumLayer_gramSquare_diag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = c₀.supp.ncard) :
    (∑ e ∈ Finset.univ.filter
        (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
          x.supp.ncard = c₀.supp.ncard),
      ((componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ) *
        (componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ))) =
      ((c₀.supp.ncard : ℤ) - 3) +
        ∑ e ∈ Finset.univ.filter
          (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
            x.supp.ncard = c₀.supp.ncard),
          (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) := by
  classical
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun x ↦ x.supp.ncard = c₀.supp.ncard) with hM
  set QM := componentQuotientMatrix G (secondOrderDefectGraph G) with hQM
  have hmemSize : ∀ e ∈ M, e.supp.ncard = c₀.supp.ncard := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard := by
    intro l
    rw [hc]
    exact hc₀min l
  -- Symmetry inside the minimum layer.
  have hsymm : ∀ e ∈ M, QM e c = QM c e := by
    intro e he
    have := componentQuotientMatrix_symm_of_ncard_eq
      G hfree hd heven hmin hcard e c
        ((hmemSize e he).trans hc.symm)
    simpa [hQM] using this
  -- The equal-size excess identity for `c`.
  have hex := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hmin hcard c hcmin
  rw [← hQM] at hex
  have hcond : ∀ e' : (secondOrderDefectGraph G).ConnectedComponent,
      (e'.supp.ncard = c.supp.ncard) =
        (e'.supp.ncard = c₀.supp.ncard) := by
    intro e'
    rw [hc]
  simp only [hcond, hc] at hex
  have hfold :
      (∑ e' : (secondOrderDefectGraph G).ConnectedComponent,
        if e'.supp.ncard = c₀.supp.ncard then
          (QM c e' : ℤ) * ((QM c e' : ℤ) - 1) else 0) =
        ∑ e ∈ M, (QM c e : ℤ) * ((QM c e : ℤ) - 1) := by
    simp only [hM, Finset.sum_filter]
  rw [hfold] at hex
  calc
    (∑ e ∈ M, ((QM e c : ℤ) * (QM e c : ℤ))) =
        ∑ e ∈ M, ((QM c e : ℤ) * (QM c e : ℤ)) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hsymm e he]
    _ = (∑ e ∈ M, (QM c e : ℤ) * ((QM c e : ℤ) - 1)) +
          ∑ e ∈ M, (QM c e : ℤ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = ((c₀.supp.ncard : ℤ) - 3) + ∑ e ∈ M, (QM c e : ℤ) := by
      rw [hex]

/-- **The minimum-layer diagonal is at most two.**  Every minimum-layer
component is a minimum, has odd order, and carries a cyclic labeling, so
the odd-cycle diagonal bound applies. -/
theorem secondOrder_minimumLayer_diag_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = c₀.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c ≤ 2 := by
  classical
  have hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard := by
    intro l
    rw [hc]
    exact hc₀min l
  have hcOdd : Odd c.supp.ncard :=
    secondOrder_minimumComponent_order_odd
      G hfree hd heven hmin hcard c hcmin
  obtain ⟨u, hu, huRange, huD, hthree⟩ :=
    exists_mixed_cycle_labeling G hfree hd heven hmin hcard
  letI : NeZero c.supp.ncard := ⟨by have := hthree c; omega⟩
  exact secondOrder_equalOddCycleComponent_diagonal_le_two
    G hfree hd heven hmin hcard (hthree c) hcOdd c (u c) (hu c)
      (huRange c) (huD c)

/-- **The minimum-layer row excess.**  Each minimum-layer row of the
restricted quotient carries the equal-size excess `w - 3`. -/
theorem secondOrder_minimumLayer_row_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = c₀.supp.ncard) :
    (∑ e ∈ Finset.univ.filter
        (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
          x.supp.ncard = c₀.supp.ncard),
      (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
        ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) -
          1)) =
      (c₀.supp.ncard : ℤ) - 3 := by
  classical
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun x ↦ x.supp.ncard = c₀.supp.ncard) with hM
  set QM := componentQuotientMatrix G (secondOrderDefectGraph G) with hQM
  have hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard := by
    intro l
    rw [hc]
    exact hc₀min l
  have hex := secondOrder_minimumComponent_equalSize_excess
    G hfree hd heven hmin hcard c hcmin
  rw [← hQM] at hex
  have hcond : ∀ e' : (secondOrderDefectGraph G).ConnectedComponent,
      (e'.supp.ncard = c.supp.ncard) =
        (e'.supp.ncard = c₀.supp.ncard) := by
    intro e'
    rw [hc]
  simp only [hcond, hc] at hex
  have hfold :
      (∑ e' : (secondOrderDefectGraph G).ConnectedComponent,
        if e'.supp.ncard = c₀.supp.ncard then
          (QM c e' : ℤ) * ((QM c e' : ℤ) - 1) else 0) =
        ∑ e ∈ M, (QM c e : ℤ) * ((QM c e : ℤ) - 1) := by
    simp only [hM, Finset.sum_filter]
  rw [hfold] at hex
  exact hex

end

end Erdos85
