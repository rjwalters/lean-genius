import Mathlib

/-!
# Closed state-cycle transport of the two-pole owner carrier

On a closed H/V/S state cycle, the coboundary of the first-pole indicator
sums to zero.  Along every marked horizontal `10--10` edge that coboundary
is one, by pole alternation.  Splitting the remaining edges into the other
horizontal transitions and the vertical/switch transitions therefore
transports the whole `10--10` carrier to those complementary transitions.

This is the occurrence-level identity `(73rnz_cjibkzzg)`.  In particular it
does not replace physical edges by an endpoint-state multiset.
-/

namespace Erdos85

/-- Edges of the distinguished horizontal carrier inside an occurrence
census. -/
def closedStateCarrierEdges {E : Type*} [DecidableEq E]
    (edges : Finset E) (carrier : E → Bool) : Finset E :=
  edges.filter fun e => carrier e

/-- Horizontal edges outside the distinguished carrier. -/
def closedStateComplementaryHorizontalEdges {E : Type*} [DecidableEq E]
    (edges : Finset E) (horizontal carrier : E → Bool) : Finset E :=
  edges.filter fun e => horizontal e && !carrier e

/-- The vertical/switch part of the closed state cycle. -/
def closedStateNonHorizontalEdges {E : Type*} [DecidableEq E]
    (edges : Finset E) (horizontal : E → Bool) : Finset E :=
  edges.filter fun e => !horizontal e

/-- **Closed-state owner coboundary transport (`73rnz_cjibkzzg`).**

`edgeCoboundary e` is the sum of the first-pole indicator at the two
physical endpoint occurrences of `e`.  Closedness says its total is zero.
If the carrier consists of horizontal edges and its coboundary is one on
each carrier edge, then its parity is exactly the coboundary carried by the
complementary horizontal and non-horizontal transitions. -/
theorem closedStateCarrier_eq_complementary_coboundary
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (horizontal carrier : E → Bool)
    (edgeCoboundary : E → ZMod 2)
    (hcarrierHorizontal : ∀ e ∈ edges, carrier e = true → horizontal e = true)
    (hcarrierOne : ∀ e ∈ edges, carrier e = true → edgeCoboundary e = 1)
    (hclosed : ∑ e ∈ edges, edgeCoboundary e = 0) :
    (closedStateCarrierEdges edges carrier).card =
      (∑ e ∈ closedStateComplementaryHorizontalEdges edges horizontal carrier,
          edgeCoboundary e) +
        ∑ e ∈ closedStateNonHorizontalEdges edges horizontal, edgeCoboundary e := by
  classical
  have hcarrierFilter :
      (edges.filter fun e => horizontal e = true).filter (fun e => carrier e = true) =
        closedStateCarrierEdges edges carrier := by
    ext e
    simp only [Finset.mem_filter, closedStateCarrierEdges]
    constructor
    · rintro ⟨⟨he, _⟩, hc⟩
      exact ⟨he, hc⟩
    · rintro ⟨he, hc⟩
      exact ⟨⟨he, hcarrierHorizontal e he hc⟩, hc⟩
  have hcomplementaryFilter :
      (edges.filter fun e => horizontal e = true).filter (fun e => ¬ carrier e = true) =
        closedStateComplementaryHorizontalEdges edges horizontal carrier := by
    ext e
    simp only [Finset.mem_filter, closedStateComplementaryHorizontalEdges,
      Bool.and_eq_true, Bool.not_eq_true]
    aesop
  have hnonHorizontalFilter :
      edges.filter (fun e => ¬ horizontal e = true) =
        closedStateNonHorizontalEdges edges horizontal := by
    ext e
    simp [closedStateNonHorizontalEdges]
  have hpartition :
      (∑ e ∈ edges, edgeCoboundary e) =
        (∑ e ∈ closedStateCarrierEdges edges carrier, edgeCoboundary e) +
          (∑ e ∈ closedStateComplementaryHorizontalEdges edges horizontal carrier,
            edgeCoboundary e) +
            ∑ e ∈ closedStateNonHorizontalEdges edges horizontal, edgeCoboundary e := by
    rw [← Finset.sum_filter_add_sum_filter_not edges (fun e => horizontal e = true)]
    rw [← Finset.sum_filter_add_sum_filter_not
      (edges.filter fun e => horizontal e = true) (fun e => carrier e = true)]
    rw [hcarrierFilter, hcomplementaryFilter, hnonHorizontalFilter, add_assoc]
  have hcarrierSum :
      (∑ e ∈ closedStateCarrierEdges edges carrier, edgeCoboundary e) =
        (closedStateCarrierEdges edges carrier).card := by
    calc
      _ = ∑ _e ∈ closedStateCarrierEdges edges carrier, (1 : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [closedStateCarrierEdges, Finset.mem_filter] at he
        exact hcarrierOne e he.1 he.2
      _ = (closedStateCarrierEdges edges carrier).card := by simp
  rw [hclosed, hcarrierSum] at hpartition
  have hsum :
      (closedStateCarrierEdges edges carrier).card +
          ((∑ e ∈ closedStateComplementaryHorizontalEdges edges horizontal carrier,
              edgeCoboundary e) +
            ∑ e ∈ closedStateNonHorizontalEdges edges horizontal, edgeCoboundary e) = 0 := by
    simpa [add_assoc] using hpartition.symm
  apply (eq_neg_of_add_eq_zero_left hsum).trans
  have hnegOne : -(1 : ZMod 2) = 1 := by decide
  have hneg (x : ZMod 2) : -x = x := by
    calc
      -x = (-1) * x := by rw [neg_one_mul]
      _ = 1 * x := by rw [hnegOne]
      _ = x := one_mul x
  exact hneg _

end Erdos85

#print axioms Erdos85.closedStateCarrier_eq_complementary_coboundary
