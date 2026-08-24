import Proofs.Erdos85ConnectedIncidenceBottleneckSixthMoment
import Proofs.Erdos85ConnectedIncidenceBottleneckDyadicStrict
import Proofs.Erdos85RegularCubicTraceModFour

/-!
# Dyadic sixth-moment sharpening modulo four

The regular sixth trace is congruent modulo four to twice the number of
triangles.  Combining this with the strict connected lower bounds sharpens
the threshold in the parity-compatible branches.
-/

open Finset BigOperators SimpleGraph Matrix

namespace Erdos85

noncomputable section

private theorem four_dvd_dyadic_of_four_le {q k : ℕ} (hq : 4 ≤ q)
    (hqpow : q = 2 ^ k) : 4 ∣ q := by
  have hk : 2 ≤ k := by
    by_contra hnot
    have hk' : k ≤ 1 := by omega
    interval_cases k <;> norm_num at hqpow <;> omega
  rw [hqpow]
  change 2 ^ 2 ∣ 2 ^ k
  exact pow_dvd_pow 2 hk

private theorem four_dvd_dyadic_sixth_baseline {q k : ℕ} (hq : 4 ≤ q)
    (hqpow : q = 2 ^ k) :
    (4 : ℤ) ∣ (q : ℤ) ^ 6 + (q : ℤ) ^ 5 -
      (q : ℤ) ^ 4 + (q : ℤ) ^ 3 := by
  obtain ⟨a, ha⟩ := four_dvd_dyadic_of_four_le hq hqpow
  use (q : ℤ) ^ 5 * a + (q : ℤ) ^ 4 * a -
    (q : ℤ) ^ 3 * a + (q : ℤ) ^ 2 * a
  have haZ : (q : ℤ) = 4 * (a : ℤ) := by exact_mod_cast ha
  rw [haZ]
  ring

private theorem sixthTrace_mod_four_by_triangleParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (hq : 4 ≤ q)
    (hfour : 4 ∣ q) :
    (Even (adjacencyTriangleMinorFinset G).card →
      (4 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6)) ∧
    (Odd (adjacencyTriangleMinorFinset G).card →
      ∃ z : ℤ, Matrix.trace ((G.adjMatrix ℤ) ^ 6) = 4 * z + 2) := by
  have hmod := regular_trace_pow_six_mod_four G q hreg (by rw [hcard]; nlinarith)
  rw [hcard] at hmod
  constructor
  · intro htri
    obtain ⟨a, ha⟩ := htri
    obtain ⟨b, hb⟩ := hmod
    obtain ⟨c, hc⟩ := hfour
    use b + (c : ℤ) * (q : ℤ) ^ 4 - 3 * a
    have haZraw : ((adjacencyTriangleMinorFinset G).card : ℤ) =
        (a : ℤ) + a := by exact_mod_cast ha
    have haZ : ((adjacencyTriangleMinorFinset G).card : ℤ) =
        2 * (a : ℤ) := by linarith
    have hcZ : (q : ℤ) = 4 * (c : ℤ) := by exact_mod_cast hc
    push_cast at hb
    rw [haZ, hcZ] at hb
    rw [hcZ]
    ring_nf at hb ⊢
    linarith
  · intro htri
    obtain ⟨a, ha⟩ := htri
    obtain ⟨b, hb⟩ := hmod
    obtain ⟨c, hc⟩ := hfour
    use b + (c : ℤ) * (q : ℤ) ^ 4 - 3 * a - 2
    have haZ : ((adjacencyTriangleMinorFinset G).card : ℤ) =
        2 * (a : ℤ) + 1 := by exact_mod_cast ha
    have hcZ : (q : ℤ) = 4 * (c : ℤ) := by exact_mod_cast hc
    push_cast at hb
    rw [haZ, hcZ] at hb
    rw [hcZ]
    ring_nf at hb ⊢
    linarith

/-- With even exponent and an even triangle count, mod-four congruence rounds
the connected strict bound from baseline plus two to baseline plus four. -/
theorem connected_binarySquare_evenDyadic_evenTriangles_sixthMoment_ge_baseline_add_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 4 ≤ q)
    (hqpow : q = 2 ^ k) (hkEven : Even k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected)
    (htriEven : Even (adjacencyTriangleMinorFinset G).card) :
    (q : ℤ) ^ 6 + (q : ℤ) ^ 5 - (q : ℤ) ^ 4 + (q : ℤ) ^ 3 + 4 ≤
      Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have hmodq : q % 3 = 1 := by
    simpa [hqpow] using (two_pow_mod_three_eq_of_parity k).1 hkEven
  have hlower := connected_binarySquare_sixthMoment_ge_baseline_add_two
    G hfree (by omega : 3 ≤ q)
      (even_of_three_le_of_eq_two_pow (by omega) hqpow) hmodq
      hreg hcard hDconn
  have htrace4 :=
    (sixthTrace_mod_four_by_triangleParity G hreg hcard hq
      (four_dvd_dyadic_of_four_le hq hqpow)).1 htriEven
  have hbase4 := four_dvd_dyadic_sixth_baseline hq hqpow
  obtain ⟨a, ha⟩ := htrace4
  obtain ⟨b, hb⟩ := hbase4
  have hlowerPow :
      (q : ℤ) ^ 6 + (q : ℤ) ^ 5 - (q : ℤ) ^ 4 +
          (q : ℤ) ^ 3 + 2 ≤ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    simpa [pow_succ, Matrix.mul_assoc] using hlower
  omega

/-- With odd exponent and an odd triangle count, the trace residue is two
modulo four, rounding baseline plus four to baseline plus six. -/
theorem connected_binarySquare_oddDyadic_oddTriangles_sixthMoment_ge_baseline_add_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 4 ≤ q)
    (hqpow : q = 2 ^ k) (hkOdd : Odd k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hDconn : (secondOrderDefectGraph G).Connected)
    (htriOdd : Odd (adjacencyTriangleMinorFinset G).card) :
    (q : ℤ) ^ 6 + (q : ℤ) ^ 5 - (q : ℤ) ^ 4 + (q : ℤ) ^ 3 + 6 ≤
      Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have hmodq : q % 3 = 2 := by
    simpa [hqpow] using (two_pow_mod_three_eq_of_parity k).2 hkOdd
  have hlower := connected_binarySquare_sixthMoment_ge_baseline_add_four
    G hfree (by omega : 3 ≤ q)
      (even_of_three_le_of_eq_two_pow (by omega) hqpow) hmodq
      hreg hcard hDconn
  obtain ⟨a, ha⟩ :=
    (sixthTrace_mod_four_by_triangleParity G hreg hcard hq
      (four_dvd_dyadic_of_four_le hq hqpow)).2 htriOdd
  obtain ⟨b, hb⟩ := four_dvd_dyadic_sixth_baseline hq hqpow
  have hlowerPow :
      (q : ℤ) ^ 6 + (q : ℤ) ^ 5 - (q : ℤ) ^ 4 +
          (q : ℤ) ^ 3 + 4 ≤ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    simpa [pow_succ, Matrix.mul_assoc] using hlower
  omega

end

end Erdos85

#print axioms Erdos85.connected_binarySquare_evenDyadic_evenTriangles_sixthMoment_ge_baseline_add_four
#print axioms Erdos85.connected_binarySquare_oddDyadic_oddTriangles_sixthMoment_ge_baseline_add_six
