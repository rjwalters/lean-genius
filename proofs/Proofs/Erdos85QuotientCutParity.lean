import Proofs.Erdos85BoundaryQuotientExcess

/-!
# Parity across a component-quotient cut

The mixed prime argument needs a parity statement about quotient edges
crossing from the `p`-divisible odd components to their complement.  The
finite combinatorics is isolated here before specializing it to the graph.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A finite matrix whose diagonal entries and symmetric off-diagonal pairs
are even has even total mass on every principal submatrix. -/
theorem even_principal_sum_of_pair_even
    {C : Type*} [DecidableEq C] (S : Finset C) (Q : C → C → ℕ)
    (hdiag : ∀ c ∈ S, Even (Q c c))
    (hpair : ∀ c ∈ S, ∀ e ∈ S, c ≠ e → Even (Q c e + Q e c)) :
    Even (∑ c ∈ S, ∑ e ∈ S, Q c e) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hdiagA : Even (Q a a) := hdiag a (by simp)
      have hpairs : Even (∑ e ∈ S, (Q a e + Q e a)) := by
        rw [even_iff_two_dvd]
        apply Finset.dvd_sum
        intro e he
        exact even_iff_two_dvd.mp
          (hpair a (by simp) e (by simp [he]) (by aesop))
      have hold : Even (∑ c ∈ S, ∑ e ∈ S, Q c e) := by
        apply ih
        · intro c hc
          exact hdiag c (by simp [hc])
        · intro c hc e he hce
          exact hpair c (by simp [hc]) e (by simp [he]) hce
      obtain ⟨x, hx⟩ := hdiagA
      obtain ⟨y, hy⟩ := hpairs
      obtain ⟨z, hz⟩ := hold
      refine ⟨x + y + z, ?_⟩
      simp only [Finset.sum_insert, ha, not_false_eq_true,
        Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib] at hy
      omega

/-- If every row has the same even mass and the principal mass on `S` is
even, then the mass crossing from `S` to its complement is even. -/
theorem even_cut_sum_of_even_rowSum
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (Q : C → C → ℕ) {d : ℕ} (hd : Even d)
    (hrow : ∀ c, ∑ e, Q c e = d)
    (hinternal : Even (∑ c ∈ S, ∑ e ∈ S, Q c e)) :
    Even (∑ c ∈ S, ∑ e ∈ Finset.univ.filter (fun e ↦ e ∉ S), Q c e) := by
  let T := Finset.univ.filter (fun e : C ↦ e ∉ S)
  have hsplit (c : C) :
      (∑ e ∈ S, Q c e) + (∑ e ∈ T, Q c e) = d := by
    rw [← hrow c]
    symm
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext e
        simp [T]
        tauto
      · intro e he
        rfl
    · exact Finset.disjoint_left.mpr (by
        intro e heS heT
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, T] at heT
        exact heT heS)
  have htotal : Even (∑ c ∈ S, ∑ e, Q c e) := by
    simp_rw [hrow]
    obtain ⟨k, hk⟩ := hd
    refine ⟨S.card * k, ?_⟩
    simp only [Finset.sum_const_nat]
    rw [hk, Nat.mul_add]
  have hdecomp :
      (∑ c ∈ S, ∑ e, Q c e) =
        (∑ c ∈ S, ∑ e ∈ S, Q c e) +
          (∑ c ∈ S, ∑ e ∈ T, Q c e) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    exact (hrow c).trans (hsplit c).symm
  obtain ⟨a, ha⟩ := htotal
  obtain ⟨b, hb⟩ := hinternal
  rw [hdecomp, hb] at ha
  have hba : b ≤ a := by omega
  have hcross : (∑ c ∈ S, ∑ e ∈ T, Q c e) =
      (a + a) - (b + b) := by omega
  refine ⟨a - b, ?_⟩
  rw [hcross]
  omega

/-- An odd defect component has even internal quotient degree, by the
handshake identity on the graph induced by that component. -/
theorem secondOrder_oddComponent_diagonal_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcOdd : Odd c.supp.ncard) :
    Even (componentQuotientMatrix G (secondOrderDefectGraph G) c c) := by
  have hprod := secondOrder_componentQuotientMatrix_diagonal_mul_even
    G hfree hd heven hmin hcard c
  exact (Nat.even_mul.mp hprod).resolve_left
    (Nat.not_even_iff_odd.mpr hcOdd)

/-- Detailed balance makes the two quotient entries between odd components
have the same parity. -/
theorem secondOrder_oddComponents_quotient_pair_add_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcOdd : Odd c.supp.ncard) (heOdd : Odd e.supp.ncard) :
    Even (componentQuotientMatrix G (secondOrderDefectGraph G) c e +
      componentQuotientMatrix G (secondOrderDefectGraph G) e c) := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hbalance := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  change c.supp.ncard * Q c e = e.supp.ncard * Q e c at hbalance
  rw [Nat.even_add]
  constructor
  · intro hce
    have hp : Even (c.supp.ncard * Q c e) :=
      (Nat.even_mul).2 (Or.inr hce)
    rw [hbalance] at hp
    exact (Nat.even_mul.mp hp).resolve_left
      (Nat.not_even_iff_odd.mpr heOdd)
  · intro hec
    have hp : Even (e.supp.ncard * Q e c) :=
      (Nat.even_mul).2 (Or.inr hec)
    rw [← hbalance] at hp
    exact (Nat.even_mul.mp hp).resolve_left
      (Nat.not_even_iff_odd.mpr hcOdd)

/-- **Prime-divisibility cut parity.** If every defect component whose order
is divisible by `p` has odd order, then the total quotient mass from those
components to the non-`p`-divisible components is even. -/
theorem secondOrder_pDivisible_quotient_cut_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard) :
    Even (∑ e ∈ Finset.univ.filter (fun e :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ e.supp.ncard),
      ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦ ¬p ∣ c.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) e c) := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset C := Finset.univ.filter (fun c ↦ p ∣ c.supp.ncard)
  have hinternal : Even (∑ c ∈ S, ∑ e ∈ S, Q c e) := by
    apply even_principal_sum_of_pair_even S Q
    · intro c hc
      have hpc : p ∣ c.supp.ncard := by simpa [S] using hc
      exact secondOrder_oddComponent_diagonal_even G hfree hd heven hmin
        hcard c (hodd c hpc)
    · intro c hc e he hce
      have hpc : p ∣ c.supp.ncard := by simpa [S] using hc
      have hpe : p ∣ e.supp.ncard := by simpa [S] using he
      exact secondOrder_oddComponents_quotient_pair_add_even G hfree hd
        heven hmin hcard c e (hodd c hpc) (hodd e hpe)
  have hcut := even_cut_sum_of_even_rowSum S Q heven
    (fun c ↦ sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hmin hcard c) hinternal
  simpa [S, Q] using hcut

/-- Across the prime-divisibility cut, every quotient entry is at most one.
Indeed `p ∣ |e|` and `p ∤ |c|` rule out `|e| ∣ |c|`, which is exactly the
one-neighbour criterion for the boundary quotient. -/
theorem secondOrder_pDivisible_cut_entry_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (e c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpe : p ∣ e.supp.ncard) (hpc : ¬p ∣ c.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e c ≤ 1 := by
  apply secondOrder_componentQuotientMatrix_le_one_of_not_dvd
    G hfree hd heven hmin hcard e c
  intro hec
  exact hpc (dvd_trans hpe hec)

/-- Consequently the even cut mass is literally the parity of the number of
positive quotient blocks crossing the cut. -/
theorem secondOrder_pDivisible_positive_cut_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard) :
    Even (((Finset.univ.filter (fun e :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ e.supp.ncard)) ×ˢ
      (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦ ¬p ∣ c.supp.ncard)))
      |>.filter (fun q ↦ 0 < componentQuotientMatrix G
        (secondOrderDefectGraph G) q.1 q.2)).card := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S : Finset C := Finset.univ.filter (fun e ↦ p ∣ e.supp.ncard)
  let T : Finset C := Finset.univ.filter (fun c ↦ ¬p ∣ c.supp.ncard)
  have hmass := secondOrder_pDivisible_quotient_cut_even G hfree hd heven
    hmin hcard hodd
  have hcardmass : ((S ×ˢ T).filter (fun q ↦ 0 < Q q.1 q.2)).card =
      ∑ e ∈ S, ∑ c ∈ T, Q e c := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro c hc
    have hpe : p ∣ e.supp.ncard := by simpa [S] using he
    have hpc : ¬p ∣ c.supp.ncard := by simpa [T] using hc
    have hle := secondOrder_pDivisible_cut_entry_le_one G hfree hd heven
      hmin hcard e c hpe hpc
    change Q e c ≤ 1 at hle
    change (if 0 < Q e c then 1 else 0) = Q e c
    split_ifs with hpos <;> omega
  rw [hcardmass]
  simpa [S, T, Q] using hmass

end

end Erdos85
