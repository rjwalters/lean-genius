import Proofs.Erdos85ServiceSixthTraceDivisibility

/-! # Arbitrary-parameter sixth-trace divisibility

Node: F.3 GENERALIZATION.  For a regular graph, the mod-three input is the
single arithmetic condition `3 ∣ |V|d`; parity then upgrades this to mod six.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A finite `d`-regular graph has sixth adjacency trace divisible by three
whenever its degree sum `|V|d` is divisible by three. -/
theorem three_dvd_regular_trace_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ x, G.degree x = d)
    (hcardDegree : (3 : ℤ) ∣ (Fintype.card V : ℤ) * d) :
    (3 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  apply three_dvd_trace_pow_six_of_three_dvd_trace_pow_two
  have h2 := trace_adjMatrix_sq_eq_sum_degrees G
  have h2' : Matrix.trace ((G.adjMatrix ℤ) ^ 2) =
      (Fintype.card V : ℤ) * d := by
    rw [pow_two, h2]
    simp [hreg]
  rw [h2']
  exact hcardDegree

/-- Under the same degree-sum condition, the universal evenness of the sixth
trace combines with mod three to give divisibility by six. -/
theorem six_dvd_regular_trace_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ x, G.degree x = d)
    (hcardDegree : (3 : ℤ) ∣ (Fintype.card V : ℤ) * d) :
    (6 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have htwo : (2 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    rcases even_trace_adjMatrix_pow_six G with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  have hthree := three_dvd_regular_trace_pow_six
    G d hreg hcardDegree
  exact IsCoprime.mul_dvd (by norm_num : IsCoprime (2 : ℤ) 3)
    htwo hthree

/-- The former degree-six/order-48 theorem follows from the generic
degree-sum criterion. -/
theorem six_dvd_sixRegular_fortyEight_trace_pow_six_of_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6) :
    (6 : ℤ) ∣ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  apply six_dvd_regular_trace_pow_six G 6 hreg
  norm_num [hcard]

end


end Erdos85

#print axioms Erdos85.three_dvd_regular_trace_pow_six
#print axioms Erdos85.six_dvd_regular_trace_pow_six
#print axioms Erdos85.six_dvd_sixRegular_fortyEight_trace_pow_six_of_general
