import Proofs.Erdos85FinalDyadicExceptionalParity
import Proofs.Erdos85PureLargeExceptionalGraphTerminal

/-!
# Exact range of the final dyadic exceptional population

Properness and parity give the lower endpoint two.  Empty-pole capacity plus
the four-class pure terminal give the upper endpoint `q`.  This packages the
three structural inputs into the range used by all remaining endpoint
analyses.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The final exceptional complement has positive even size at most the
regular degree. -/
theorem c4Free_binarySquare_compl_finalDyadicSupport_card_range
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    Even ((dyadicOccupancySupport G S j)ᶜ : Finset V).card ∧
      2 ≤ ((dyadicOccupancySupport G S j)ᶜ : Finset V).card ∧
      ((dyadicOccupancySupport G S j)ᶜ : Finset V).card ≤ q := by
  let B := dyadicOccupancySupport G S j
  have hVEven : Even (Fintype.card V) := by
    refine ⟨2 ^ j * q, ?_⟩
    rw [hcard, hqa]
    ring
  have heven : Even (Bᶜ : Finset V).card :=
    card_compl_finalDyadicSupport_even G hqa hreg hVEven S hdiv
  have hBupper : B.card ≤ q * q - 2 :=
    c4Free_binarySquare_finalDyadicSupport_card_le_sub_two
      G hfree (by omega) hqa hreg hcard hconn S hS hSc hdiv
  have hsplit : (Bᶜ : Finset V).card + B.card = q * q := by
    rw [Finset.card_compl_add_card, hcard]
  have htwo : 2 ≤ q * q := by nlinarith
  have hBadd : B.card + 2 ≤ q * q :=
    (Nat.le_sub_iff_add_le htwo).mp hBupper
  have hlower : 2 ≤ (Bᶜ : Finset V).card := by omega
  have hupper : (Bᶜ : Finset V).card ≤ q :=
    c4Free_binarySquare_compl_finalDyadicSupport_card_le_degree
      G hfree hq hqa hreg hcard S hS hSc hdiv hemptyClique
  exact ⟨heven, hlower, hupper⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_compl_finalDyadicSupport_card_range
