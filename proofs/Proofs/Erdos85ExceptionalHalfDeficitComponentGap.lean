import Proofs.Erdos85ExceptionalBalancedLeakageAggregate

/-!
# A component-order gap at half exceptional deficit

The balanced leakage inequality has a discrete endpoint that is useful before
any detailed component classification.  When the empty exceptional population
is exactly half the degree, a nonsaturated exceptional support cannot fit in a
defect component of the minimum possible order `q`.  Divisibility of component
orders therefore promotes the strict inequality to order at least `2q`.
-/

namespace Erdos85

/-- General arithmetic threshold for a component-order jump.  If the local
balanced-capacity coefficient is strictly smaller than the leakage generated
by one unit of nonsaturation, a component of order `q` cannot contain the
exceptional core and its leakage boundary. -/
theorem balancedLeakage_componentOrder_two_mul_le_of_coefficient_lt
    {q e f c m : ℕ}
    (hq : 0 < q)
    (hproper : c < q)
    (hcoefficient : q * q - q - f + e < 2 * q * e)
    (hleak :
      2 * q * e * (q - c) ≤ (q * q - q - f + e) * (m - c))
    (hdiv : q ∣ m) :
    2 * q ≤ m := by
  have hqc : 0 < q - c := Nat.sub_pos_of_lt hproper
  have hqe : 0 < 2 * q * e :=
    lt_of_le_of_lt (Nat.zero_le _) hcoefficient
  have hlhspos : 0 < 2 * q * e * (q - c) :=
    Nat.mul_pos hqe hqc
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    rw [hmzero] at hleak
    simp only [Nat.zero_sub, Nat.mul_zero] at hleak
    omega
  have hqm : q < m := by
    by_contra hnot
    have hmle : m ≤ q := Nat.le_of_not_gt hnot
    have hmc : m - c ≤ q - c := Nat.sub_le_sub_right hmle c
    have hprodle : (q * q - q - f + e) * (m - c) ≤
        (q * q - q - f + e) * (q - c) :=
      Nat.mul_le_mul_left _ hmc
    have hprodlt : (q * q - q - f + e) * (q - c) <
        (2 * q * e) * (q - c) :=
      Nat.mul_lt_mul_of_pos_right hcoefficient hqc
    omega
  obtain ⟨k, hk⟩ := hdiv
  subst m
  have hkTwo : 2 ≤ k :=
    (Nat.lt_mul_iff_one_lt_right hq).mp hqm
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left q hkTwo

/-- The coefficient threshold in displacement coordinates.  Here
`q - 2e` is the full-minus-empty imbalance and `c` is total exceptional
support. -/
theorem balancedLeakage_coefficient_lt_of_imbalance_mul_lt_support
    {q e f c : ℕ}
    (hq : 0 < q)
    (hc : c = f + e)
    (htwice : 2 * e ≤ q)
    (hproper : c < q)
    (himbalance : (q - 1) * (q - 2 * e) < c) :
    q * q - q - f + e < 2 * q * e := by
  have hqf : q + f ≤ q * q := by
    nlinarith
  have hleft : q * q - q - f + e + c = q * q - q + 2 * e := by
    omega
  have hright : 2 * q * e + (q - 1) * (q - 2 * e) =
      q * q - q + 2 * e := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le htwice
    have hqone : 1 ≤ q := hq
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hqone
    have hpred : q - 1 = r := by omega
    have hdiff : q - 2 * e = d := by omega
    have hqq : q * q - q = q * (q - 1) := by
      simpa using (Nat.mul_sub_left_distrib q q 1).symm
    rw [hpred, hdiff, hqq, hpred]
    nlinarith
  omega

/-- Arithmetic core of the half-deficit component jump.  The coefficient
`q*q-q-f+e` is the intrinsic form of the balanced outside capacity. -/
theorem halfDeficit_balancedLeakage_componentOrder_two_mul_le
    {q e f c m : ℕ}
    (hq : 0 < q)
    (hc : c = f + e)
    (hhalf : 2 * e = q)
    (hproper : c < q)
    (hleak :
      2 * q * e * (q - c) ≤ (q * q - q - f + e) * (m - c))
    (hdiv : q ∣ m) :
    2 * q ≤ m := by
  have he : 0 < e := by omega
  have hsubDefined : q + f ≤ q * q := by
    nlinarith
  have hcoef : q * q - q - f + e = q * q - c := by
    omega
  have hfactor : 2 * q * e = q * q := by
    nlinarith
  apply balancedLeakage_componentOrder_two_mul_le_of_coefficient_lt
    hq hproper _ hleak hdiv
  rw [hcoef, hfactor]
  exact Nat.sub_lt (by positivity) (by omega)

/-- Graph-facing threshold form: whenever the intrinsic balanced-capacity
coefficient is smaller than the empty-pole leakage coefficient, a proper
exceptional support forces a component-order jump. -/
theorem binarySquare_finalDyadic_exceptionalComponent_two_mul_degree_le_of_coefficient_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hproper :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card < q)
    (hcoefficient :
      q * q - q - (fullLineCenters G S q).card +
          (emptyLineCenters G S).card <
        2 * q * (emptyLineCenters G S).card)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    2 * q ≤
      ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  let E := emptyLineCenters G S
  let F := fullLineCenters G S q
  let C := F ∪ E
  let T := exceptionalEmptyLeakageBoundary G S q
  let component := (secondOrderDefectGraph G).connectedComponentMk pole
  let m := component.supp.ncard
  have hCcard : C.card = F.card + E.card := by
    exact Finset.card_union_of_disjoint
      (fullLineCenters_disjoint_emptyLineCenters G S (by omega))
  have hagg :=
    binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_intrinsic
      G hfree hq hqa hreg hcard S hdiv hemptyClique
  change 2 * q * (E.card * (q - C.card)) +
      (q * q + F.card + q) * T.card ≤
        (2 * q * q + E.card) * T.card at hagg
  have hqf : q + F.card ≤ q * q := by
    change C.card < q at hproper
    rw [hCcard] at hproper
    nlinarith
  have hsplit :
      (2 * q * q + E.card) * T.card =
        (q * q + F.card + q) * T.card +
          (q * q - q - F.card + E.card) * T.card := by
    have hscalar : 2 * q * q + E.card =
        q * q + F.card + q + (q * q - q - F.card + E.card) := by
      have hdouble : 2 * q * q = q * q + q * q := by ring
      rw [hdouble]
      rw [Nat.sub_sub]
      have hrecover := Nat.add_sub_of_le hqf
      omega
    rw [hscalar]
    ring
  rw [hsplit] at hagg
  have hboundaryLeak :
      2 * q * E.card * (q - C.card) ≤
        (q * q - q - F.card + E.card) * T.card := by
    apply Nat.le_of_add_le_add_right
      (b := (q * q + F.card + q) * T.card)
    simpa [Nat.mul_assoc, Nat.add_comm] using hagg
  have hcomponent := exceptional_card_add_leakageBoundary_card_le_component
    G hfree (by omega) hreg S hemptyClique pole hpole
  change C.card + T.card ≤ m at hcomponent
  have hTle : T.card ≤ m - C.card := by omega
  have hleak :
      2 * q * E.card * (q - C.card) ≤
        (q * q - q - F.card + E.card) * (m - C.card) :=
    hboundaryLeak.trans (Nat.mul_le_mul_left _ hTle)
  apply balancedLeakage_componentOrder_two_mul_le_of_coefficient_lt
    (q := q) (e := E.card) (f := F.card) (c := C.card) (m := m)
  · omega
  · exact hproper
  · exact hcoefficient
  · exact hleak
  · exact binarySquare_regular_dvd_defectComponent_card
      G hfree hq hreg hcard component

/-- Displacement-coordinate API for the component jump.  It applies directly
to the natural profile data `e`, `f`, and `c=e+f`. -/
theorem binarySquare_finalDyadic_exceptionalComponent_two_mul_degree_le_of_imbalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (htwice : 2 * (emptyLineCenters G S).card ≤ q)
    (hproper :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card < q)
    (himbalance :
      (q - 1) * (q - 2 * (emptyLineCenters G S).card) <
        (fullLineCenters G S q ∪ emptyLineCenters G S).card)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    2 * q ≤
      ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  apply
    binarySquare_finalDyadic_exceptionalComponent_two_mul_degree_le_of_coefficient_lt
      G hfree hq hqa hreg hcard S hdiv hemptyClique hproper _ pole hpole
  apply balancedLeakage_coefficient_lt_of_imbalance_mul_lt_support
    (q := q) (e := (emptyLineCenters G S).card)
    (f := (fullLineCenters G S q).card)
    (c := (fullLineCenters G S q ∪ emptyLineCenters G S).card)
  · omega
  · exact Finset.card_union_of_disjoint
      (fullLineCenters_disjoint_emptyLineCenters G S
        (show 0 < q by omega))
  · exact htwice
  · exact hproper
  · exact himbalance

/-- At half exceptional deficit the coefficient threshold is automatic, so
every empty pole lies in a defect component of normalized order at least two
whenever the exceptional support is not saturated. -/
theorem binarySquare_finalDyadic_halfEmpty_exceptionalComponent_two_mul_degree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (hhalf : 2 * (emptyLineCenters G S).card = q)
    (hproper :
      (fullLineCenters G S q ∪ emptyLineCenters G S).card < q)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    2 * q ≤
      ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  apply
    binarySquare_finalDyadic_exceptionalComponent_two_mul_degree_le_of_coefficient_lt
      G hfree hq hqa hreg hcard S hdiv hemptyClique hproper _ pole hpole
  have hCcard := Finset.card_union_of_disjoint
    (fullLineCenters_disjoint_emptyLineCenters G S
      (show 0 < q by omega))
  have hsubDefined : q + (fullLineCenters G S q).card ≤ q * q := by
    rw [hCcard] at hproper
    nlinarith
  have hcoef : q * q - q - (fullLineCenters G S q).card +
      (emptyLineCenters G S).card =
        q * q -
          (fullLineCenters G S q ∪ emptyLineCenters G S).card := by
    omega
  have hfactor : 2 * q * (emptyLineCenters G S).card = q * q := by
    nlinarith
  rw [hcoef, hfactor]
  exact Nat.sub_lt (by positivity) (by omega)

end Erdos85

#print axioms
  Erdos85.balancedLeakage_componentOrder_two_mul_le_of_coefficient_lt
#print axioms Erdos85.halfDeficit_balancedLeakage_componentOrder_two_mul_le
#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalComponent_two_mul_degree_le_of_coefficient_lt
#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalComponent_two_mul_degree_le_of_imbalance
#print axioms
  Erdos85.binarySquare_finalDyadic_halfEmpty_exceptionalComponent_two_mul_degree_le
