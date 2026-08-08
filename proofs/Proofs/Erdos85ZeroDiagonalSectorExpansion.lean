import Proofs.Erdos85ZeroDiagonalSectorGeometry

/-!
# Expansion forced by a zero-diagonal prime sector

The off-diagonal quotient-square equation prevents a covering edge between
two zero-diagonal components from being isolated.  A third component must
mediate a positive two-step quotient path; when the first component is
globally minimum, minimum-row closure keeps that mediator in the same prime
sector.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Any positive quotient edge from a globally minimum component to a
distinct zero-diagonal component forces a distinct third component on a
positive two-step path.  Every prime dividing the minimum order also divides
the mediator order. -/
theorem exists_third_pDivisibleComponent_of_zeroDiagonal_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (a : (secondOrderDefectGraph G).ConnectedComponent)
    (hamin : ∀ f : (secondOrderDefectGraph G).ConnectedComponent,
      a.supp.ncard ≤ f.supp.ncard)
    (hpa : p ∣ a.supp.ncard)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (hane : a ≠ e)
    (hdiagA : componentQuotientMatrix G
      (secondOrderDefectGraph G) a a = 0)
    (hdiagE : componentQuotientMatrix G
      (secondOrderDefectGraph G) e e = 0) :
    ∃ f : (secondOrderDefectGraph G).ConnectedComponent,
      f ≠ a ∧ f ≠ e ∧ p ∣ f.supp.ncard ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) a f ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) f e := by
  classical
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  have hsq := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard a e
  have hsum : (∑ f, Q a f * Q f e) = e.supp.ncard := by
    simpa only [Matrix.mul_apply, if_neg hane, mul_zero, zero_add, Q] using hsq
  have hsumne : (∑ f, Q a f * Q f e) ≠ 0 := by
    rw [hsum]
    exact Nat.ne_of_gt e.nonempty_supp.ncard_pos
  obtain ⟨f, _hfmem, hfprod⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hqaf : 0 < Q a f := Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hfprod).1
  have hqfe : 0 < Q f e := Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hfprod).2
  have hfa : f ≠ a := by
    intro h
    subst f
    simp only [hdiagA, Q, lt_self_iff_false] at hqaf
  have hfe : f ≠ e := by
    intro h
    subst f
    simp only [hdiagE, Q, lt_self_iff_false] at hqfe
  have hpf : p ∣ f.supp.ncard :=
    prime_dvd_neighbor_order_of_minimumComponent_quotient_pos
      G hfree hd heven hmin hcard a hamin hpa f hqaf
  exact ⟨f, hfa, hfe, hpf, hqaf, hqfe⟩

/-- Cover-edge specialization of
`exists_third_pDivisibleComponent_of_zeroDiagonal_edge`. -/
theorem exists_third_pDivisibleComponent_of_zeroDiagonal_cover_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (a : (secondOrderDefectGraph G).ConnectedComponent)
    (hamin : ∀ f : (secondOrderDefectGraph G).ConnectedComponent,
      a.supp.ncard ≤ f.supp.ncard)
    (hpa : p ∣ a.supp.ncard)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (hae : a.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) a e)
    (hdiagA : componentQuotientMatrix G
      (secondOrderDefectGraph G) a a = 0)
    (hdiagE : componentQuotientMatrix G
      (secondOrderDefectGraph G) e e = 0) :
    ∃ f : (secondOrderDefectGraph G).ConnectedComponent,
      f ≠ a ∧ f ≠ e ∧ p ∣ f.supp.ncard ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) a f ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) f e := by
  apply exists_third_pDivisibleComponent_of_zeroDiagonal_edge
    G hfree hd heven hmin hcard a hamin hpa e
  · intro h
    subst e
    omega
  · exact hdiagA
  · exact hdiagE

/-- A proper prime sector containing a global minimum and having zero
diagonal throughout contains at least three explicitly distinct components:
a minimum component, a larger component reached by a cyclic-cover edge, and
a third component mediating the off-diagonal quotient-square equation. -/
theorem exists_three_pDivisibleComponents_of_zeroDiagonal_minimum_sector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (t : (secondOrderDefectGraph G).ConnectedComponent)
    (hpt : ¬ p ∣ t.supp.ncard)
    (hdiag : ∀ x : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ x.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) x x = 0) :
    ∃ a e f : (secondOrderDefectGraph G).ConnectedComponent,
      a ≠ e ∧ f ≠ a ∧ f ≠ e ∧
      p ∣ a.supp.ncard ∧ p ∣ e.supp.ncard ∧ p ∣ f.supp.ncard ∧
      a.supp.ncard = c.supp.ncard ∧ c.supp.ncard < e.supp.ncard ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) a e ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) a f ∧
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) f e := by
  rcases exists_minimumToLarger_pDivisible_quotient_edge
    G hfree hd heven hmin hcard c hcmin hpc t hpt with
    ⟨a, e, hpa, hac, hpe, hce, hae, _hea, _hdvd, _hratio⟩
  have hamin : ∀ x : (secondOrderDefectGraph G).ConnectedComponent,
      a.supp.ncard ≤ x.supp.ncard := by
    intro x
    rw [hac]
    exact hcmin x
  have haelt : a.supp.ncard < e.supp.ncard := by simpa [hac] using hce
  rcases exists_third_pDivisibleComponent_of_zeroDiagonal_cover_edge
    G hfree hd heven hmin hcard a hamin hpa e haelt hae
      (hdiag a hpa) (hdiag e hpe) with
    ⟨f, hfa, hfe, hpf, haf, hfePos⟩
  have hane : a ≠ e := by
    intro h
    subst e
    omega
  exact ⟨a, e, f, hane, hfa, hfe, hpa, hpe, hpf, hac, hce,
    hae, haf, hfePos⟩

/-- Cardinal form of the three-component expansion theorem. -/
theorem three_le_pDivisible_filter_card_of_zeroDiagonal_minimum_sector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (t : (secondOrderDefectGraph G).ConnectedComponent)
    (hpt : ¬ p ∣ t.supp.ncard)
    (hdiag : ∀ x : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ x.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) x x = 0) :
    3 ≤ (Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card := by
  classical
  rcases exists_three_pDivisibleComponents_of_zeroDiagonal_minimum_sector
    G hfree hd heven hmin hcard c hcmin hpc t hpt hdiag with
    ⟨a, e, f, hae, hfa, hfe, hpa, hpe, hpf, _hac, _hce,
      _hQae, _hQaf, _hQfe⟩
  let S := Finset.univ.filter (fun x :
    (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ x.supp.ncard)
  have hsub : ({a, e, f} : Finset
      (secondOrderDefectGraph G).ConnectedComponent) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact hpa
    · exact hpe
    · exact hpf
  have hthree : ({a, e, f} : Finset
      (secondOrderDefectGraph G).ConnectedComponent).card = 3 := by
    simp [hae, hfa, hfe, Ne.symm]
  rw [← hthree]
  exact Finset.card_le_card hsub

/-- In particular, if arithmetic already forces the prime-sector cardinality
to be even (as in the nonresidue branch), zero diagonal and a proper sector
force at least four selected components. -/
theorem four_le_pDivisible_filter_card_of_even_zeroDiagonal_minimum_sector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (t : (secondOrderDefectGraph G).ConnectedComponent)
    (hpt : ¬ p ∣ t.supp.ncard)
    (hdiag : ∀ x : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ x.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) x x = 0)
    (hsectorEven : Even ((Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card)) :
    4 ≤ (Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card := by
  have hthree :=
    three_le_pDivisible_filter_card_of_zeroDiagonal_minimum_sector
      G hfree hd heven hmin hcard c hcmin hpc t hpt hdiag
  obtain ⟨k, hk⟩ := hsectorEven
  omega

/-- The complement hypothesis is unnecessary once the minimum component has
order at least four.  Local excess first forces a distinct equal-size
positive quotient neighbor; the off-diagonal square equation then forces a
third `p`-divisible component. -/
theorem three_le_pDivisible_filter_card_of_zeroDiagonal_minimum_order_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hc4 : 4 ≤ c.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (hdiag : ∀ x : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ x.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) x x = 0) :
    3 ≤ (Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card := by
  classical
  rcases exists_equalSize_quotient_ge_two_of_minimum_diagonal_zero
    G hfree hd heven hmin hcard c hcmin hc4 (hdiag c hpc) with
    ⟨e, hec, heq, _hQce⟩
  have hpe : p ∣ e.supp.ncard := by simpa [heq] using hpc
  rcases exists_third_pDivisibleComponent_of_zeroDiagonal_edge
    G hfree hd heven hmin hcard c hcmin hpc e hec.symm
      (hdiag c hpc) (hdiag e hpe) with
    ⟨f, hfc, hfe, hpf, _hQcf, _hQfe⟩
  let S := Finset.univ.filter (fun x :
    (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ x.supp.ncard)
  have hsub : ({c, e, f} : Finset
      (secondOrderDefectGraph G).ConnectedComponent) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact hpc
    · exact hpe
    · exact hpf
  have hthree : ({c, e, f} : Finset
      (secondOrderDefectGraph G).ConnectedComponent).card = 3 := by
    simp [hec, hfc, hfe, Ne.symm]
  rw [← hthree]
  exact Finset.card_le_card hsub

/-- Nonresidue-sector parity upgrades the preceding unconditional
three-component lower bound to four. -/
theorem four_le_pDivisible_filter_card_of_even_zeroDiagonal_minimum_order_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ e.supp.ncard)
    (hc4 : 4 ≤ c.supp.ncard)
    (hpc : p ∣ c.supp.ncard)
    (hdiag : ∀ x : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ x.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) x x = 0)
    (hsectorEven : Even ((Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card)) :
    4 ≤ (Finset.univ.filter (fun x :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ x.supp.ncard)).card := by
  have hthree :=
    three_le_pDivisible_filter_card_of_zeroDiagonal_minimum_order_four
      G hfree hd heven hmin hcard c hcmin hc4 hpc hdiag
  obtain ⟨k, hk⟩ := hsectorEven
  omega

end

end Erdos85
