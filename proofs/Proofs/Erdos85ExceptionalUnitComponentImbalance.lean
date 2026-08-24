import Proofs.Erdos85ExceptionalHalfDeficitComponentGap

/-!
# Exceptional imbalance forced by a unit defect component

The balanced leakage component jump has a sharp contrapositive.  If an empty
pole lies in a minimum-order defect component (order `q`), a proper exceptional
support must have enough full-minus-empty imbalance to absorb its leakage.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An order-`q` component containing an empty pole forces the intrinsic
profile inequality `c ≤ (q-1)(q-2e)`. -/
theorem binarySquare_finalDyadic_unitExceptionalComponent_support_le_imbalance
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
    (pole : V) (hpole : pole ∈ emptyLineCenters G S)
    (hcomponent :
      ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard = q) :
    (fullLineCenters G S q ∪ emptyLineCenters G S).card ≤
      (q - 1) * (q - 2 * (emptyLineCenters G S).card) := by
  by_contra hnot
  have himbalance :
      (q - 1) * (q - 2 * (emptyLineCenters G S).card) <
        (fullLineCenters G S q ∪ emptyLineCenters G S).card := by
    omega
  have hjump :=
    binarySquare_finalDyadic_exceptionalComponent_two_mul_degree_le_of_imbalance
      G hfree hq hqa hreg hcard S hdiv hemptyClique htwice hproper
      himbalance pole hpole
  rw [hcomponent] at hjump
  omega

/-- In particular, half exceptional deficit is impossible inside an
order-`q` defect component. -/
theorem binarySquare_finalDyadic_unitExceptionalComponent_twice_empty_lt
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
    (pole : V) (hpole : pole ∈ emptyLineCenters G S)
    (hcomponent :
      ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard = q) :
    2 * (emptyLineCenters G S).card < q := by
  have himbalance :=
    binarySquare_finalDyadic_unitExceptionalComponent_support_le_imbalance
      G hfree hq hqa hreg hcard S hdiv hemptyClique htwice hproper
      pole hpole hcomponent
  have hsupportPos :
      0 < (fullLineCenters G S q ∪ emptyLineCenters G S).card := by
    apply Finset.card_pos.mpr
    exact ⟨pole, Finset.mem_union_right _ hpole⟩
  by_contra hnot
  have : 2 * (emptyLineCenters G S).card = q := by omega
  rw [this, Nat.sub_self, Nat.mul_zero] at himbalance
  omega

end

end Erdos85

#print axioms
  Erdos85.binarySquare_finalDyadic_unitExceptionalComponent_support_le_imbalance
#print axioms
  Erdos85.binarySquare_finalDyadic_unitExceptionalComponent_twice_empty_lt
