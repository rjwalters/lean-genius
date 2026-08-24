import Proofs.Erdos85CanonicalExceptionalMassBalance
import Proofs.Erdos85FinalDyadicExceptionalSupportBridge
import Proofs.Erdos85FinalDyadicSupportProper

/-!
# Parity of the final dyadic exceptional population

The full-plus-empty population has the same parity as its signed mass.
At square order and even degree, that mass is even.  Consequently a proper
final dyadic support misses at least two vertices, not merely one.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If the difference of two populations is even, then their sum is even. -/
theorem even_add_of_int_sub_eq_even
    {f e n s : ℕ} (hn : Even n)
    (h : (f : ℤ) - e = 2 * (s : ℤ) - n) : Even (f + e) := by
  obtain ⟨k, rfl⟩ := hn
  refine ⟨?_, ?_⟩
  · exact (f + e) / 2
  · omega

/-- In an even-order regular graph, a tri-valued occupancy profile has an
even number of exceptional (full or empty) line centers. -/
theorem exceptionalSignedSupport_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 0 < q) (hreg : ∀ v, G.degree v = q)
    (hV : Even (Fintype.card V)) (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q) :
    Even (exceptionalSignedSupport G S q).card := by
  rw [exceptionalSignedSupport_card_eq_full_add_empty G S hq]
  apply even_add_of_int_sub_eq_even hV
  exact fullLineCenters_card_sub_emptyLineCenters_card_eq_cutDisplacement
    G hq hreg S htri

/-- Final-scale form: divisibility and `q=2·2^j` force the complement of
the dyadic support to have even cardinality. -/
theorem card_compl_finalDyadicSupport_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hV : Even (Fintype.card V)) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    Even ((dyadicOccupancySupport G S j)ᶜ : Finset V).card := by
  rw [card_compl_dyadicOccupancySupport_eq_exceptionalSignedSupport
    G hqa hreg S hdiv]
  apply exceptionalSignedSupport_card_even G (by rw [hqa]; positivity) hreg hV S
  intro v
  let n := (G.neighborFinset v ∩ S).card
  have hnle : n ≤ q := by
    calc
      n ≤ (G.neighborFinset v).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  obtain ⟨t, ht⟩ := hdiv v
  have ha : 0 < 2 ^ j := by positivity
  have htLe : t ≤ 2 := by
    change n = 2 ^ j * t at ht
    rw [ht, hqa] at hnle
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ j) (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnle) ha
  change n = 2 ^ j * t at ht
  change n = 0 ∨ 2 * n = q ∨ n = q
  interval_cases t <;> omega

/-- Quantitative properness: at square order the final dyadic support omits
at least two vertices. -/
theorem c4Free_binarySquare_finalDyadicSupport_card_le_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hq3 : 3 ≤ q) (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    (dyadicOccupancySupport G S j).card ≤ q * q - 2 := by
  have hproper := c4Free_binarySquare_finalDyadicSupport_ne_univ
    G hfree (by omega) hq3 (by positivity) hqa hreg hcard hconn
      S hS hSc hdiv
  have hcompNonempty :
      ((dyadicOccupancySupport G S j)ᶜ : Finset V).Nonempty := by
    by_contra hn
    have hempty : ((dyadicOccupancySupport G S j)ᶜ : Finset V) = ∅ := by
      simpa using hn
    apply hproper
    ext x
    simp only [Finset.mem_univ, iff_true]
    by_contra hx
    have hxc : x ∈ ((dyadicOccupancySupport G S j)ᶜ : Finset V) :=
      Finset.mem_compl.mpr hx
    rw [hempty] at hxc
    simpa using hxc
  have hcompPos : 0 < ((dyadicOccupancySupport G S j)ᶜ : Finset V).card :=
    Finset.card_pos.mpr hcompNonempty
  have hVEven : Even (Fintype.card V) := by
    refine ⟨2 ^ j * q, ?_⟩
    rw [hcard, hqa]
    ring
  have hcompEven := card_compl_finalDyadicSupport_even
    G hqa hreg hVEven S hdiv
  obtain ⟨k, hk⟩ := hcompEven
  have hcompTwo : 2 ≤ ((dyadicOccupancySupport G S j)ᶜ : Finset V).card := by
    omega
  rw [← hcard, ← Finset.card_compl_add_card
    (dyadicOccupancySupport G S j)]
  omega

end

end Erdos85

#print axioms Erdos85.exceptionalSignedSupport_card_even
#print axioms Erdos85.card_compl_finalDyadicSupport_even
#print axioms Erdos85.c4Free_binarySquare_finalDyadicSupport_card_le_sub_two
