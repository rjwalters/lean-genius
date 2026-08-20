import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Proofs.Erdos85CubicTraceHistogramExcess
import Proofs.Erdos85TriangleFreeCommutatorGap

/-! # Divisibility of the service sixth trace -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- If the second trace of an integer matrix is divisible by three, then so
is its sixth trace.  This is Frobenius for traces over `ZMod 3`, applied to
the square of the matrix. -/
theorem three_dvd_trace_pow_six_of_three_dvd_trace_pow_two
    {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℤ)
    (h2 : (3 : ℤ) ∣ Matrix.trace (A ^ 2)) :
    (3 : ℤ) ∣ Matrix.trace (A ^ 6) := by
  let f := Int.castRingHom (ZMod 3)
  let A3 : Matrix X X (ZMod 3) := A.map f
  have hmapTrace (n : ℕ) :
      ((Matrix.trace (A ^ n) : ℤ) : ZMod 3) =
        Matrix.trace (A3 ^ n) := by
    rw [Matrix.trace, Matrix.trace]
    push_cast
    change (∑ x, f ((A ^ n) x x)) = ∑ x, ((A.map f) ^ n) x x
    rw [← Matrix.map_pow]
    rfl
  have h2zero : ((Matrix.trace (A ^ 2) : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h2
  have hfrob := ZMod.trace_pow_card (p := 3) (A3 ^ 2)
  have h6zero : Matrix.trace (A3 ^ 6) = 0 := by
    rw [show (A3 ^ 2) ^ 3 = A3 ^ 6 by simp [← pow_mul]] at hfrob
    rw [← hmapTrace 2, h2zero] at hfrob
    simpa using hfrob
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  rw [hmapTrace 6]
  exact h6zero

/-- The sixth trace of a six-regular graph on 48 vertices is divisible by
three, because its second trace is `48*6=288`. -/
theorem three_dvd_sixRegular_fortyEight_trace_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    (3 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  apply three_dvd_trace_pow_six_of_three_dvd_trace_pow_two
  have h2 := trace_adjMatrix_sq_eq_sum_degrees G
  have h2' : Matrix.trace ((G.adjMatrix ℤ) ^ 2) = 288 := by
    rw [pow_two, h2]
    simp [hreg, hcard]
  rw [h2']
  norm_num

/-- Combining mod three with the previously established parity gives full
divisibility by six. -/
theorem six_dvd_sixRegular_fortyEight_trace_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    (6 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have htwo : (2 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) :=
    by
      rcases even_trace_adjMatrix_pow_six G with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
  have hthree := three_dvd_sixRegular_fortyEight_trace_pow_six
    G hcard hreg
  exact IsCoprime.mul_dvd (by norm_num : IsCoprime (2 : ℤ) 3)
    htwo hthree

/-- Consequently a strict h305 sixth moment is at least `61254`, the next
multiple of six after `61248`. -/
theorem sixRegular_fortyEight_strict_trace_six_ge_61254
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6)) :
    61254 ≤ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  rcases six_dvd_sixRegular_fortyEight_trace_pow_six G hcard hreg with
    ⟨k, hk⟩
  omega

/-- The exact global histogram excess itself is a multiple of six, since
the constant baseline `61056` is divisible by six. -/
theorem six_dvd_sixRegular_fortyEight_histogramExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    (6 : ℤ) ∣ ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4)) := by
  dsimp only
  rcases six_dvd_sixRegular_fortyEight_trace_pow_six G hcard hreg with
    ⟨k, hk⟩
  rw [sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
    G hfree hcard hreg] at hk
  refine ⟨k - 10176, ?_⟩
  omega

/-- In exact histogram coordinates, strictness therefore forces at least
`198` units of excess rather than merely `194`. -/
theorem sixRegular_fortyEight_histogramExcess_ge_198
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6)) :
    let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
    198 ≤ ∑ a, ((A3 a a) ^ 2 - 7 * A3 a a + 12 +
      ∑ b ∈ cubicNonneighborFinset G a,
        (A3 a b - 3) * (A3 a b - 4)) := by
  dsimp only
  have htrace := sixRegular_fortyEight_strict_trace_six_ge_61254
    G hcard hreg hstrict
  rw [sixRegular_fortyEight_trace_six_eq_baseline_add_histogramExcess
    G hfree hcard hreg] at htrace
  omega

end

end Erdos85

#print axioms Erdos85.three_dvd_trace_pow_six_of_three_dvd_trace_pow_two
#print axioms Erdos85.three_dvd_sixRegular_fortyEight_trace_pow_six
#print axioms Erdos85.six_dvd_sixRegular_fortyEight_trace_pow_six
#print axioms Erdos85.sixRegular_fortyEight_strict_trace_six_ge_61254
#print axioms Erdos85.six_dvd_sixRegular_fortyEight_histogramExcess
#print axioms Erdos85.sixRegular_fortyEight_histogramExcess_ge_198
