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
  have hqc : 0 < q - c := Nat.sub_pos_of_lt hproper
  have he : 0 < e := by omega
  have hcpos : 0 < c := by omega
  have hqTwo : 2 ≤ q := by omega
  have hsubDefined : q + f ≤ q * q := by
    nlinarith
  have hcoef : q * q - q - f + e = q * q - c := by
    omega
  have hfactor : 2 * q * e = q * q := by
    nlinarith
  have hlhspos : 0 < 2 * q * e * (q - c) := by positivity
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    rw [hmzero] at hleak
    simp only [Nat.zero_sub, Nat.mul_zero] at hleak
    omega
  have hqle : q ≤ m := by
    apply Nat.le_of_dvd
    · exact hmpos
    · exact hdiv
  have hqm : q < m := by
    by_contra hnot
    have hmle : m ≤ q := Nat.le_of_not_gt hnot
    have hmc : m - c ≤ q - c := Nat.sub_le_sub_right hmle c
    have hcoeflt : q * q - c < q * q :=
      Nat.sub_lt (by positivity) hcpos
    have hprodle : (q * q - c) * (m - c) ≤
        (q * q - c) * (q - c) :=
      Nat.mul_le_mul_left _ hmc
    have hprodlt : (q * q - c) * (q - c) <
        q * q * (q - c) :=
      Nat.mul_lt_mul_of_pos_right hcoeflt hqc
    rw [hcoef, hfactor] at hleak
    omega
  obtain ⟨k, hk⟩ := hdiv
  subst m
  have hkTwo : 2 ≤ k := by
    exact (Nat.lt_mul_iff_one_lt_right hq).mp hqm
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left q hkTwo

/-- Graph-facing form: at half exceptional deficit, every empty pole lies in
a defect component of normalized order at least two whenever the exceptional
support is not saturated. -/
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
  apply halfDeficit_balancedLeakage_componentOrder_two_mul_le
    (q := q) (e := E.card) (f := F.card) (c := C.card) (m := m)
  · omega
  · exact hCcard
  · exact hhalf
  · exact hproper
  · exact hleak
  · exact binarySquare_regular_dvd_defectComponent_card
      G hfree hq hreg hcard component

end Erdos85

#print axioms Erdos85.halfDeficit_balancedLeakage_componentOrder_two_mul_le
#print axioms
  Erdos85.binarySquare_finalDyadic_halfEmpty_exceptionalComponent_two_mul_degree_le
