import Proofs.Erdos85DegreeSixColorSectorSplit
import Proofs.Erdos85DegreeSixOddDiagonal

/-!
# Degree-six empty-sector assembly

Carrier lemmas for the empty color-sector branch of the degree-six exact
boundary.  The master contradiction is assembled here once the remaining
odd-diagonal discharge is available.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Common quotient data used by every odd diagonal-two exclusion at the
degree-six boundary. -/
theorem degreeSix_diagonal_two_quotient_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent) :
    let D := secondOrderDefectGraph G
    let Q := componentQuotientMatrix G D
    let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
    (∑ c, size c) = 33 ∧
    (∀ c, (∑ t, Q c t) = 6) ∧
    (∀ c t, size c * Q c t = size t * Q t c) ∧
    (∑ t, Q w t * Q t w) = size w + 3 ∧
    ∀ c t, Q c t ≤ 6 := by
  dsimp
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hrow : ∀ c : D.ConnectedComponent, (∑ t, Q c t) = 6 := by
    intro c
    exact sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hbal : ∀ c t, size c * Q c t = size t * Q t c := by
    intro c t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c t
  have hsq : (∑ t, Q w t * Q t w) = size w + 3 := by
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w w
    simpa [Q, size, D, Matrix.mul_apply, Nat.add_comm] using hs
  refine ⟨htotal, hrow, hbal, hsq, ?_⟩
  intro c t
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ t)).trans_eq (hrow c)

/-- The degree-six boundary order `33` is odd, so some defect component
has odd order. -/
theorem degreeSix_exists_odd_order_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hcard : Fintype.card V = 33) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard := by
  classical
  by_contra hnone
  push Not at hnone
  have hparts : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard) = Fintype.card V := by
    simpa using sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)
  have hdvd : 2 ∣ ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard := by
    apply Finset.dvd_sum
    intro c _
    exact (Nat.not_odd_iff_even.mp (hnone c)).two_dvd
  rw [hparts, hcard] at hdvd
  omega

/-- Once all odd components are zero-diagonal, the nonsquare trace six
must be carried by a positive-diagonal even component. -/
theorem degreeSix_exists_even_carrier_of_odd_zero_diagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hodd0 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      Even c.supp.ncard ∧
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  classical
  have htrace := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree (d := 6) (by norm_num) (by norm_num) hmin
      (by norm_num at hcard ⊢; exact hcard) (by norm_num)
  by_contra hnone
  push Not at hnone
  have hzero : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
    intro c
    by_cases hoddc : Odd c.supp.ncard
    · exact hodd0 c hoddc
    · have heven : Even c.supp.ncard := Nat.not_odd_iff_even.mp hoddc
      have := hnone c heven
      omega
  have hsum : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c c) = 0 :=
    Finset.sum_eq_zero fun c _ => hzero c
  rw [hsum] at htrace
  exact absurd htrace.symm (by norm_num)

/-- An order-thirteen component cannot have diagonal quotient two at the
degree-six boundary. -/
theorem false_of_degreeSix_orderThirteen_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw13 : w.supp.ncard = 13)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hsize : ∀ t, t ≠ w → size t ≤ 20 := by
    intro t htw
    have hle := two_distinct_terms_le_sum size htw
    rw [htotal] at hle
    dsimp [size] at hle ⊢
    rw [hw13] at hle
    omega
  have hrow (c : D.ConnectedComponent) : (∑ t, Q c t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6 := by
    intro t
    constructor
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ t)).trans_eq (hrow w)
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w)).trans_eq (hrow t)
  have hbal : ∀ t, size w * Q w t = size t * Q t w := by
    intro t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w t
  have hsq : (∑ t, Q w t * Q t w) = 16 := by
    have hs := secondOrder_componentQuotientMatrix_sq_apply
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w w
    simpa [Q, size, D, Matrix.mul_apply, hw13] using hs
  exact OddDiagonal.false_of_thirteen_diag_two
    Q size w hw13 hsize hrev hbal hdiag (hrow w) hsq

/-- A component of prime order at least seventeen cannot have diagonal
quotient two at the degree-six boundary. -/
theorem false_of_degreeSix_largePrime_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (w : (secondOrderDefectGraph G).ConnectedComponent) {o : ℕ}
    (hwo : w.supp.ncard = o) (hop : o.Prime) (ho17 : 17 ≤ o)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  have htotal : (∑ c : D.ConnectedComponent, size c) = 33 := by
    simpa [size, D, hcard] using sum_connectedComponent_supp_ncard D
  have hsize : ∀ t, t ≠ w → size t ≤ 33 - o := by
    intro t htw
    have hle := two_distinct_terms_le_sum size htw
    rw [htotal] at hle
    dsimp [size] at hle ⊢
    rw [hwo] at hle
    omega
  have hrow (c : D.ConnectedComponent) : (∑ t, Q c t) = 6 :=
    sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) c
  have hrev : ∀ t, Q w t ≤ 6 ∧ Q t w ≤ 6 := by
    intro t
    constructor
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ t)).trans_eq (hrow w)
    · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w)).trans_eq (hrow t)
  have hbal : ∀ t, size w * Q w t = size t * Q t w := by
    intro t
    exact secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) w t
  exact OddDiagonal.false_of_large_prime_diag_two
    Q size w hwo hop ho17 hsize hrev hbal hdiag (hrow w)

/-- Order twenty-seven has no admissible external quotient partner within
the remaining six vertices. -/
theorem false_of_degreeSix_orderTwentySeven_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw27 : w.supp.ncard = 27)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  obtain ⟨htotal, hrow, hbal, _, hle⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  change ∀ c t, size c * Q c t = size t * Q t c at hbal
  change ∀ c t, Q c t ≤ 6 at hle
  have hsw : size w = 27 := hw27
  have hdiagQ : Q w w = 2 := hdiag
  have hzero : ∀ t, t ≠ w → Q w t = 0 := by
    intro t htw
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal] at hpair
    have hst : size t ≤ 6 := by dsimp [size] at hpair ⊢; omega
    have hst3 : 3 ≤ size t := hr t
    have hb := hbal w t
    rw [hsw] at hb
    by_contra hq
    have hqpos : 0 < Q w t := Nat.pos_of_ne_zero hq
    have hrt := hle t w
    interval_cases (size t) <;> omega
  have hsum : (∑ t, Q w t) = Q w w := by
    rw [← Finset.sum_subset (Finset.subset_univ {w})]
    · simp
    · intro t _ ht
      exact hzero t (by simpa using ht)
  have hwrow := hrow w
  rw [hsum, hdiagQ] at hwrow
  omega

/-- For an order-twenty-five diagonal-two component, detailed balance
forces every external reverse quotient to be at most five.  The external
row mass four then contributes at most twenty to the square, short of the
required twenty-four. -/
theorem false_of_degreeSix_orderTwentyFive_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw25 : w.supp.ncard = 25)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  obtain ⟨htotal, hrow, hbal, hsq, hle⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  change ∀ c t, size c * Q c t = size t * Q t c at hbal
  change (∑ t, Q w t * Q t w) = size w + 3 at hsq
  change ∀ c t, Q c t ≤ 6 at hle
  have hsw : size w = 25 := hw25
  have hdiagQ : Q w w = 2 := hdiag
  have hrev5 : ∀ t, t ≠ w → Q t w ≤ 5 := by
    intro t htw
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal, hsw] at hpair
    have hst3 : 3 ≤ size t := hr t
    have hst8 : size t ≤ 8 := by omega
    have hb := hbal w t
    rw [hsw] at hb
    have hqt := hle w t
    have hrt := hle t w
    interval_cases (size t) <;> omega
  have hextRow : (∑ t ∈ Finset.univ.erase w, Q w t) = 4 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun t ↦ Q w t)
      (Finset.mem_univ w)
    have hwrow := hrow w
    change Q w w + (∑ t ∈ Finset.univ.erase w, Q w t) =
      ∑ t, Q w t at hadd
    rw [hdiagQ] at hadd
    omega
  have hextSqLe : (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) ≤ 20 := by
    calc
      (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) ≤
          ∑ t ∈ Finset.univ.erase w, Q w t * 5 := by
            apply Finset.sum_le_sum
            intro t ht
            exact Nat.mul_le_mul_left _ (hrev5 t (Finset.ne_of_mem_erase ht))
      _ = 5 * 4 := by rw [← Finset.sum_mul, hextRow]; omega
      _ = 20 := by omega
  have hextSq : (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) = 24 := by
    have hadd := Finset.add_sum_erase Finset.univ
      (fun t ↦ Q w t * Q t w) (Finset.mem_univ w)
    change Q w w * Q w w +
      (∑ t ∈ Finset.univ.erase w, Q w t * Q t w) =
        ∑ t, Q w t * Q t w at hadd
    rw [hdiagQ] at hadd
    rw [hsw] at hsq
    omega
  omega

/-- An order-thirty-three component exhausts the carrier, so diagonal two
cannot supply the degree-six row. -/
theorem false_of_degreeSix_orderThirtyThree_diagonal_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 33)
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (w : (secondOrderDefectGraph G).ConnectedComponent)
    (hw33 : w.supp.ncard = 33)
    (hdiag : componentQuotientMatrix G (secondOrderDefectGraph G) w w = 2) :
    False := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  obtain ⟨htotal, hrow, _, _, _⟩ :=
    degreeSix_diagonal_two_quotient_profile G hfree hmin hcard w
  change (∑ c, size c) = 33 at htotal
  change ∀ c, (∑ t, Q c t) = 6 at hrow
  have hsw : size w = 33 := hw33
  have hdiagQ : Q w w = 2 := hdiag
  have hall : ∀ t : D.ConnectedComponent, t = w := by
    intro t
    by_contra htw
    have hpair := two_distinct_terms_le_sum size htw
    rw [htotal] at hpair
    have hst3 : 3 ≤ size t := hr t
    rw [hsw] at hpair
    omega
  have huniv : (Finset.univ : Finset D.ConnectedComponent) = {w} := by
    ext t
    simp [hall t]
  have hwrow := hrow w
  rw [huniv] at hwrow
  simp at hwrow
  omega

/-- Once the empty-sector analysis supplies zero diagonal on every odd
component, the eight odd-to-even cover terminals give the boundary
contradiction immediately. -/
theorem false_of_degreeSix_of_odd_zero_diagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
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
    (hodd0 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      Odd c.supp.ncard →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    False := by
  obtain ⟨o, hoOdd⟩ := degreeSix_exists_odd_order_component G hcard
  obtain ⟨e, heEven, _⟩ :=
    degreeSix_exists_even_carrier_of_odd_zero_diagonal
      G hfree hmin hcard hodd0
  have hzero3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 3 →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
    intro c hc
    exact hodd0 c (by rw [hc]; norm_num)
  have hzero5 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 5 →
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 := by
    intro c hc
    exact hodd0 c (by rw [hc]; norm_num)
  obtain ⟨a, b, hba, h36 | h510 | h714 | h918 | h1122 | h312 | h520 | h318⟩ :=
    degreeSix_odd_to_even_cover_order_cases
      G hfree hmin hcard hr o e hoOdd heEven
  · exact false_of_degreeSix_oddEven_cover_three_six
      G hfree hmin hcard u hu huRange huD hr hzero3
        a b h36.1 h36.2 hba
  · exact false_of_degreeSix_oddEven_cover_five_ten
      G hfree hmin hcard hr hzero3 hzero5 a b h510.1 h510.2 hba
  · have haa := hodd0 a (by rw [h714.1]; norm_num)
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
    have hab : componentQuotientMatrix G (secondOrderDefectGraph G) a b = 2 := by
      rw [h714.1, h714.2, hba, mul_one] at hbal
      omega
    exact false_of_degreeSix_oddEven_cover_seven_fourteen
      G hfree hmin hcard hr a b h714.1 h714.2 haa hab
  · have haa := hodd0 a (by rw [h918.1]; norm_num)
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
    have hab : componentQuotientMatrix G (secondOrderDefectGraph G) a b = 2 := by
      rw [h918.1, h918.2, hba, mul_one] at hbal
      omega
    exact false_of_degreeSix_oddEven_cover_nine_eighteen
      G hfree hmin hcard hr a b h918.1 h918.2 haa hab
  · have haa := hodd0 a (by rw [h1122.1]; norm_num)
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 6) (by norm_num) (by norm_num) hmin
        (by norm_num at hcard ⊢; exact hcard) a b
    have hab : componentQuotientMatrix G (secondOrderDefectGraph G) a b = 2 := by
      rw [h1122.1, h1122.2, hba, mul_one] at hbal
      omega
    exact false_of_degreeSix_oddEven_cover_eleven_twentyTwo
      G hfree hmin hcard hr a b h1122.1 h1122.2 haa hab
  · exact false_of_degreeSix_oddEven_cover_three_twelve
      G hfree hmin hcard u hu huRange huD hr hzero3
        a b h312.1 h312.2 hba
  · exact false_of_degreeSix_oddEven_cover_five_twenty
      G hfree hmin hcard hr hzero3 hzero5 a b h520.1 h520.2 hba
  · exact false_of_degreeSix_oddEven_cover_three_eighteen
      G hfree hmin hcard u hu huRange huD hr
        a b h318.1 h318.2 (hzero3 a h318.1) hba

/-- The full color-sector split reduces the degree-six boundary to the one
remaining empty-sector odd-diagonal theorem: the singleton branch is already
impossible, and the empty branch is consumed by the eight-cover assembly. -/
theorem false_of_degreeSix_boundary_of_empty_odd_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent, NeZero c.supp.ncard]
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
    (hemptyOdd0 : triangleFreeCycleSector G u = ∅ →
      ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        Odd c.supp.ncard →
          componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0) :
    False := by
  rcases degreeSix_triangleFreeCycleSector_empty_or_singleton
      G hfree hmin (by norm_num at hcard ⊢; exact hcard)
        u hu huRange huD hr with hempty | ⟨c, hsingleton, _⟩
  · exact false_of_degreeSix_of_odd_zero_diagonal
      G hfree hmin hcard u hu huRange huD hr (hemptyOdd0 hempty)
  · exact false_of_degreeSix_triangleFreeCycleSector_singleton
      G hfree hmin hcard u hu huRange huD hr c hsingleton

end

end Erdos85
