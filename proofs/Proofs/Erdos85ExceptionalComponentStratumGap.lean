import Proofs.Erdos85ExceptionalHalfDeficitComponentGap

/-!
# Exceptional leakage forces jumps across defect-component strata

Defect-component orders are multiples of the ambient degree `q`.  The
balanced exceptional leakage inequality can therefore do more than give a
real-valued lower bound: whenever its required boundary mass does not fit in
an order-`kq` component, the component has order at least `(k+1)q`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic engine for jumping past an arbitrary normalized component
stratum. -/
theorem balancedLeakage_componentOrder_succ_mul_le_of_stratum_pressure
    {q e f c m k : ℕ}
    (hq : 0 < q) (hk : 1 ≤ k) (hproper : c < q)
    (hpressure :
      (q * q - q - f + e) * (k * q - c) <
        2 * q * e * (q - c))
    (hleak :
      2 * q * e * (q - c) ≤
        (q * q - q - f + e) * (m - c))
    (hdiv : q ∣ m) :
    (k + 1) * q ≤ m := by
  have hcKq : c ≤ k * q := by
    have hqKq : q ≤ k * q := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hk
    omega
  have hkqm : k * q < m := by
    by_contra hnot
    have hmle : m ≤ k * q := Nat.le_of_not_gt hnot
    have hmc : m - c ≤ k * q - c := Nat.sub_le_sub_right hmle c
    have hcap : (q * q - q - f + e) * (m - c) ≤
        (q * q - q - f + e) * (k * q - c) :=
      Nat.mul_le_mul_left _ hmc
    omega
  obtain ⟨t, rfl⟩ := hdiv
  have hkt : k < t := by
    have : q * k < q * t := by
      simpa [Nat.mul_comm] using hkqm
    exact (Nat.mul_lt_mul_left hq).mp this
  simpa [Nat.mul_comm, Nat.add_comm] using
    Nat.mul_le_mul_right q (show k + 1 ≤ t by omega)

/-- Graph-facing component-stratum jump from balanced exceptional leakage. -/
theorem binarySquare_finalDyadic_exceptionalComponent_succ_stratum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q j k : ℕ} (hq : 3 ≤ q) (hk : 1 ≤ k)
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
    (hpressure :
      (q * q - q - (fullLineCenters G S q).card +
          (emptyLineCenters G S).card) *
            (k * q -
              (fullLineCenters G S q ∪ emptyLineCenters G S).card) <
        2 * q * (emptyLineCenters G S).card *
          (q - (fullLineCenters G S q ∪ emptyLineCenters G S).card))
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    (k + 1) * q ≤
      ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  let E := emptyLineCenters G S
  let F := fullLineCenters G S q
  let C := F ∪ E
  let T := exceptionalEmptyLeakageBoundary G S q
  let component := (secondOrderDefectGraph G).connectedComponentMk pole
  let m := component.supp.ncard
  have hagg :=
    binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_intrinsic
      G hfree hq hqa hreg hcard S hdiv hemptyClique
  change 2 * q * (E.card * (q - C.card)) +
      (q * q + F.card + q) * T.card ≤
        (2 * q * q + E.card) * T.card at hagg
  have hqf : q + F.card ≤ q * q := by
    have hCcard : C.card = F.card + E.card :=
      Finset.card_union_of_disjoint
        (fullLineCenters_disjoint_emptyLineCenters G S
          (show 0 < q by omega))
    change C.card < q at hproper
    rw [hCcard] at hproper
    nlinarith
  have hsplit :
      (2 * q * q + E.card) * T.card =
        (q * q + F.card + q) * T.card +
          (q * q - q - F.card + E.card) * T.card := by
    have hdouble : 2 * q * q = q * q + q * q := by ring
    have hscalar : 2 * q * q + E.card =
        q * q + F.card + q + (q * q - q - F.card + E.card) := by
      rw [hdouble, Nat.sub_sub]
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
  exact balancedLeakage_componentOrder_succ_mul_le_of_stratum_pressure
    (q := q) (e := E.card) (f := F.card) (c := C.card) (m := m) (k := k)
    (by omega) hk hproper hpressure hleak
    (binarySquare_regular_dvd_defectComponent_card
      G hfree hq hreg hcard component)

end

end Erdos85

#print axioms
  Erdos85.balancedLeakage_componentOrder_succ_mul_le_of_stratum_pressure
#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalComponent_succ_stratum_le
