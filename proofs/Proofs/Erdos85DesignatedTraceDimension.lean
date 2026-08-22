import Mathlib

/-!
# A growing dimension requirement for designated trace sectors

If all residual sign-paired sectors cancel, the designated adjacency roots
must sum to the negative principal trace.  Cauchy--Schwarz turns a uniform
strict square bound on those roots into a strict lower bound on their total
multiplicity.  At binary square order the spectral input is
`theta² < 2(q-1)`, giving `q² < 2(q-1)m²`.
-/

namespace Erdos85

/-- A family of `m` real numbers, each of square strictly below `B`, cannot
have a sum of magnitude `q` unless `q² < Bm²`. -/
theorem traceMultiplicity_sq_growth
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (θ : ι → ℝ) {q B : ℝ}
    (hq : 0 < q) (hsum : ∑ i ∈ s, θ i = -q)
    (hbound : ∀ i ∈ s, (θ i) ^ 2 < B) :
    q ^ 2 < B * (s.card : ℝ) ^ 2 := by
  have hs : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hsum
    simp only [Finset.sum_empty] at hsum
    linarith
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsquares : (∑ i ∈ s, (θ i) ^ 2) < (s.card : ℝ) * B := by
    calc
      (∑ i ∈ s, (θ i) ^ 2) < ∑ _i ∈ s, B :=
        Finset.sum_lt_sum_of_nonempty hs hbound
      _ = (s.card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcauchy : (∑ i ∈ s, θ i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, (θ i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    q ^ 2 = (∑ i ∈ s, θ i) ^ 2 := by rw [hsum]; ring
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (θ i) ^ 2 := hcauchy
    _ < (s.card : ℝ) * ((s.card : ℝ) * B) :=
      mul_lt_mul_of_pos_left hsquares hcard
    _ = B * (s.card : ℝ) ^ 2 := by ring

/-- **Binary-square designated-sector growth.**  If designated real roots
sum to `-q` and every one satisfies `theta² < 2(q-1)`, their multiplicity
`m` obeys the division-free growing lower bound
`q² < 2(q-1)m²`. -/
theorem binarySquare_designatedTrace_card_sq_growth
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (θ : ι → ℝ) {q : ℕ} (hq : 1 < q)
    (hsum : ∑ i ∈ s, θ i = -(q : ℝ))
    (hbound : ∀ i ∈ s, (θ i) ^ 2 < 2 * ((q : ℝ) - 1)) :
    (q : ℝ) ^ 2 < 2 * ((q : ℝ) - 1) * (s.card : ℝ) ^ 2 := by
  exact traceMultiplicity_sq_growth s θ (by positivity) hsum hbound

end Erdos85

#print axioms Erdos85.traceMultiplicity_sq_growth
#print axioms Erdos85.binarySquare_designatedTrace_card_sq_growth
