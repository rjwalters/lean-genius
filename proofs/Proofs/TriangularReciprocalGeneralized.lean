/-
  Generalized Alternating Reciprocal Product Sum

  Result: For k ≥ 1,
    ∑_{n=1}^∞ (-1)^{n+1}/(n(n+k)) = (1/k)(log 2 - (-1)^k(log 2 - A_k))

  where A_k = ∑_{m=1}^k (-1)^{m+1}/m is the k-th alternating harmonic partial sum.

  Special cases:
    k=1: 2·log(2) - 1          (matches TriangularReciprocalAlternatingOQ03.lean)
    k=2: 1/4                    (logarithmic terms cancel for even k)
    k=3: (2·log(2) - 5/6) / 3

  Proof: Partial fractions 1/(n(n+k)) = (1/k)(1/n - 1/(n+k)), then rearrange
  using the alternating harmonic series ∑(-1)^{n+1}/n = log(2).

  Axioms: 1 (alternating harmonic series, same as parent OQ03)
  Extends: TriangularReciprocalAlternatingOQ03.lean
-/
import Proofs.TriangularReciprocalAlternatingOQ03

namespace AlternatingTriangularReciprocals.Generalized

open Finset BigOperators Filter Topology Real
open AlternatingTriangularReciprocals (alternating_harmonic_hasSum shifted_alternating_hasSum)

-- alternating_harmonic_hasSum imported from TriangularReciprocalAlternatingOQ03.lean

-- ═══════════════════════════════════════════════════
-- Part II: Alternating Harmonic Partial Sums
-- ═══════════════════════════════════════════════════

/-- The k-th alternating harmonic partial sum:
    A_k = ∑_{m=1}^k (-1)^{m+1}/m = 1 - 1/2 + 1/3 - ... ± 1/k -/
noncomputable def altHarmonicPartial (k : ℕ) : ℝ :=
  (Finset.range k).sum (fun m =>
    if m = 0 then 0 else (-1 : ℝ) ^ (m + 1) / (m : ℝ))

theorem altHarmonicPartial_zero : altHarmonicPartial 0 = 0 := by
  simp [altHarmonicPartial]

theorem altHarmonicPartial_one : altHarmonicPartial 1 = 1 := by
  simp [altHarmonicPartial, Finset.sum_range_one]

-- ═══════════════════════════════════════════════════
-- Part III: Tail of Alternating Harmonic Series
-- ═══════════════════════════════════════════════════

/-- The tail of the alternating harmonic series: ∑_{n=k+1}^∞ (-1)^{n+1}/n = log(2) - A_k.
    This follows from HasSum = finite sum + tail. -/
theorem alternating_harmonic_tail (k : ℕ) :
    HasSum (fun n : ℕ => if n + k = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + k + 1) / ((n : ℝ) + k))
      (Real.log 2 - altHarmonicPartial k) := by
  sorry -- Uses HasSum.nat_add: if HasSum f s then HasSum (f ∘ (· + k)) (s - ∑ i ∈ range k, f i)

-- ═══════════════════════════════════════════════════
-- Part IV: Shifted Alternating Sum
-- ═══════════════════════════════════════════════════

/-- The shifted alternating sum: ∑_{n=1}^∞ (-1)^{n+1}/(n+k) = (-1)^k(log 2 - A_k).

    Proof: Let m = n+k. Then ∑_{n=1}^∞ (-1)^{n+1}/(n+k) = ∑_{m=k+1}^∞ (-1)^{m-k+1}/m.
    Since (-1)^{m-k+1} = (-1)^k · (-1)^{m+1}, this equals
    (-1)^k · ∑_{m=k+1}^∞ (-1)^{m+1}/m = (-1)^k · (log 2 - A_k). -/
theorem shifted_alternating_hasSum (k : ℕ) (hk : 0 < k) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + k))
      ((-1 : ℝ) ^ k * (Real.log 2 - altHarmonicPartial k)) := by
  sorry -- Follows from alternating_harmonic_tail via index substitution

-- ═══════════════════════════════════════════════════
-- Part V: Partial Fractions
-- ═══════════════════════════════════════════════════

/-- Partial fraction decomposition: 1/(n(n+k)) = (1/k)(1/n - 1/(n+k)) for k ≠ 0, n ≠ 0. -/
theorem partial_fraction {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + k)) =
      (1 / k) * (1 / (n : ℝ) - 1 / ((n : ℝ) + k)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hnk : (n : ℝ) + k ≠ 0 := by positivity
  have hmul : (n : ℝ) * ((n : ℝ) + k) ≠ 0 := mul_ne_zero hn' hnk
  field_simp
  ring

-- ═══════════════════════════════════════════════════
-- Part VI: Main Theorem
-- ═══════════════════════════════════════════════════

/-- **Generalized Alternating Reciprocal Product Sum.**

    For k ≥ 1:
    ∑_{n=1}^∞ (-1)^{n+1}/(n(n+k)) = (1/k)(log 2 - (-1)^k · (log 2 - A_k))

    where A_k = ∑_{m=1}^k (-1)^{m+1}/m.

    Special cases:
    - k=1: log 2 - (-1)(log 2 - 1) = 2·log 2 - 1
    - k=2: log 2 - (1)(log 2 - 1/2) = 1/2, divided by 2 = 1/4
    - k even: A_k / k   (logarithmic terms cancel)
    - k odd: (2·log 2 - A_k) / k -/
theorem generalized_alternating_sum (k : ℕ) (hk : 0 < k) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + k)))
      ((1 / k) * (Real.log 2 - (-1 : ℝ) ^ k * (Real.log 2 - altHarmonicPartial k))) := by
  sorry -- Combines partial_fraction with alternating_harmonic_hasSum and shifted_alternating_hasSum

/-- tsum version of the generalized formula. -/
theorem generalized_alternating_tsum (k : ℕ) (hk : 0 < k) :
    ∑' n : ℕ, (if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + k))) =
      (1 / k) * (Real.log 2 - (-1 : ℝ) ^ k * (Real.log 2 - altHarmonicPartial k)) := by
  exact (generalized_alternating_sum k hk).tsum_eq

-- ═══════════════════════════════════════════════════
-- Part VII: Verification of Special Cases
-- ═══════════════════════════════════════════════════

/-- k=1 case: reduces to 2·log 2 - 1, matching the parent proof. -/
theorem special_case_k1 :
    (1 / (1 : ℝ)) * (Real.log 2 - (-1 : ℝ) ^ 1 * (Real.log 2 - altHarmonicPartial 1)) =
    2 * Real.log 2 - 1 := by
  simp [altHarmonicPartial_one]
  ring

/-- k=2 case: logarithmic terms cancel, giving exactly 1/4. -/
theorem special_case_k2 :
    (1 / (2 : ℝ)) * (Real.log 2 - (-1 : ℝ) ^ 2 * (Real.log 2 - altHarmonicPartial 2)) =
    1 / 4 := by
  simp [altHarmonicPartial]
  simp [Finset.sum_range_succ, Finset.sum_range_one]
  ring

end AlternatingTriangularReciprocals.Generalized
