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

  Axioms: 1 (alternating_harmonic_hasSum: Mercator series ∑(-1)^{n+1}/n = log 2)
  Previously extended TriangularReciprocalAlternatingOQ03.lean; now self-contained.
-/
import Mathlib

namespace AlternatingTriangularReciprocals.Generalized

open Finset BigOperators Filter Topology Real

/-- The alternating harmonic series: ∑_{n=1}^∞ (-1)^{n+1}/n = log(2).
    Mercator (1668). Boundary convergence of the power series for log(1+x)
    requires Abel's theorem, not yet formalized in Mathlib. -/
axiom alternating_harmonic_hasSum :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / (n : ℝ))
      (Real.log 2)

-- ═══════════════════════════════════════════════════
-- Part II: Alternating Harmonic Partial Sums
-- ═══════════════════════════════════════════════════

/-- The k-th alternating harmonic partial sum:
    A_k = ∑_{m=1}^k (-1)^{m+1}/m = 1 - 1/2 + 1/3 - ... ± 1/k

    Implementation: 0-indexed range with shift to avoid m=0 division:
    A_k = ∑_{m=0}^{k-1} (-1)^{m+2}/(m+1) = ∑_{j=1}^k (-1)^{j+1}/j -/
noncomputable def altHarmonicPartial (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range k, (-1 : ℝ) ^ (m + 2) / ((m : ℝ) + 1)

theorem altHarmonicPartial_zero : altHarmonicPartial 0 = 0 := by
  simp [altHarmonicPartial]

theorem altHarmonicPartial_one : altHarmonicPartial 1 = 1 := by
  simp [altHarmonicPartial, Finset.sum_range_one]
  norm_num

/-- altHarmonicPartial k equals the partial sum of the alternating harmonic function
    over range (k+1). This connects our definition to hasSum_nat_add_iff. -/
private lemma partialSum_eq (k : ℕ) :
    ∑ i in Finset.range (k + 1),
      (fun n : ℕ => if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / (n : ℝ)) i =
    altHarmonicPartial k := by
  rw [Finset.sum_range_succ']
  simp only [↓reduceIte, zero_add]
  unfold altHarmonicPartial
  congr 1
  ext i
  rw [if_neg (Nat.succ_ne_zero i)]
  have h1 : (i + 1) + 1 = i + 2 := by omega
  have h2 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [h1, h2]

-- ═══════════════════════════════════════════════════
-- Part III: Tail of Alternating Harmonic Series
-- ═══════════════════════════════════════════════════

/-- The tail of the alternating harmonic series starting from index k+1:
    ∑_{n=0}^∞ (-1)^{n+k+2}/(n+k+1) = log(2) - A_k.

    Proof: By hasSum_nat_add_iff, shifting the alternating harmonic series
    by (k+1) gives the tail. Since n+k+1 ≥ 1, all terms are well-defined. -/
theorem alternating_harmonic_tail (k : ℕ) :
    HasSum (fun n : ℕ =>
      (-1 : ℝ) ^ (n + k + 2) / ((n : ℝ) + ↑k + 1))
      (Real.log 2 - altHarmonicPartial k) := by
  have h_shifted := (hasSum_nat_add_iff (k + 1)).mpr (by
    rw [partialSum_eq, sub_add_cancel]
    exact alternating_harmonic_hasSum)
  exact h_shifted.congr fun n => by
    rw [if_neg (show n + (k + 1) ≠ 0 from by omega)]
    have h1 : n + (k + 1) + 1 = n + k + 2 := by omega
    have h2 : ((n + (k + 1) : ℕ) : ℝ) = (n : ℝ) + ↑k + 1 := by push_cast; ring
    rw [h1, h2]

-- ═══════════════════════════════════════════════════
-- Part IV: Shifted Alternating Sum
-- ═══════════════════════════════════════════════════

/-- The shifted alternating sum: ∑_{n=1}^∞ (-1)^{n+1}/(n+k) = (-1)^k(log 2 - A_k).

    Proof: The tail from index k+1 gives ∑ (-1)^{n+k+2}/(n+k+1) = log 2 - A_k.
    Factor: (-1)^{n+k+2} = (-1)^k · (-1)^{n+2}, and n+k+1 = (n+1)+k.
    So the tail = (-1)^k · ∑ g(n+1) where g(n) = (-1)^{n+1}/(n+k).
    Factor out (-1)^k using its self-inverse property, then remove the +1 shift. -/
theorem shifted_alternating_hasSum (k : ℕ) (hk : 0 < k) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + ↑k))
      ((-1 : ℝ) ^ k * (Real.log 2 - altHarmonicPartial k)) := by
  let g : ℕ → ℝ := fun n => if n = 0 then 0 else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + ↑k)
  -- Step 1: Rewrite tail as (-1)^k * g(n+1)
  have h_factor : HasSum (fun n : ℕ => (-1 : ℝ) ^ k * g (n + 1))
      (Real.log 2 - altHarmonicPartial k) :=
    (alternating_harmonic_tail k).congr fun n => by
      show (-1 : ℝ) ^ (n + k + 2) / ((n : ℝ) + ↑k + 1) = (-1 : ℝ) ^ k * g (n + 1)
      simp only [g, show (n + 1 : ℕ) ≠ 0 from Nat.succ_ne_zero n, ↓reduceIte]
      rw [show n + k + 2 = k + (n + 2) from by omega, pow_add,
          show (n : ℝ) + ↑k + 1 = ↑(n + 1 : ℕ) + ↑k from by push_cast; ring,
          mul_div_assoc]
  -- Step 2: Factor out (-1)^k using (-1)^k * (-1)^k = 1
  have h_unfactor : HasSum (fun n => g (n + 1))
      ((-1 : ℝ) ^ k * (Real.log 2 - altHarmonicPartial k)) :=
    (h_factor.mul_left ((-1 : ℝ) ^ k)).congr fun n => by
      show (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * g (n + 1)) = g (n + 1)
      rw [← mul_assoc,
          show (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 from by
            rw [← pow_add, show k + k = 2 * k from by omega, pow_mul, neg_one_sq, one_pow],
          one_mul]
  -- Step 3: Remove +1 shift via hasSum_nat_add_iff 1 (g(0) = 0)
  have h_final := (hasSum_nat_add_iff 1).mp h_unfactor
  simp only [Finset.sum_range_one, show g 0 = 0 from if_pos rfl, add_zero] at h_final
  exact h_final

-- ═══════════════════════════════════════════════════
-- Part V: Partial Fractions
-- ═══════════════════════════════════════════════════

/-- Partial fraction decomposition: 1/(n(n+k)) = (1/k)(1/n - 1/(n+k)) for k ≠ 0, n ≠ 0. -/
theorem partial_fraction {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + ↑k)) =
      (1 / ↑k) * (1 / (n : ℝ) - 1 / ((n : ℝ) + ↑k)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk' : (↑k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hnk : (n : ℝ) + ↑k ≠ 0 := by positivity
  field_simp
  ring

-- ═══════════════════════════════════════════════════
-- Part VI: Main Theorem
-- ═══════════════════════════════════════════════════

/-- **Generalized Alternating Reciprocal Product Sum.**

    For k ≥ 1:
    ∑_{n=1}^∞ (-1)^{n+1}/(n(n+k)) = (1/k)(log 2 - (-1)^k · (log 2 - A_k))

    where A_k = ∑_{m=1}^k (-1)^{m+1}/m.

    Proof: By partial fractions, (-1)^{n+1}/(n(n+k)) = (1/k)((-1)^{n+1}/n - (-1)^{n+1}/(n+k)).
    Summing: (1/k)(log 2 - (-1)^k(log 2 - A_k)). -/
theorem generalized_alternating_sum (k : ℕ) (hk : 0 < k) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + ↑k)))
      ((1 / ↑k) * (Real.log 2 - (-1 : ℝ) ^ k * (Real.log 2 - altHarmonicPartial k))) := by
  have h_feq : (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + ↑k))) =
    (fun n : ℕ => (1 / (↑k : ℝ)) *
      ((if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / (n : ℝ)) -
       (if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + ↑k)))) := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hk' : (↑k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hnk : (n : ℝ) + ↑k ≠ 0 := by positivity
      field_simp
      ring
  rw [h_feq]
  exact (alternating_harmonic_hasSum.sub (shifted_alternating_hasSum k hk)).mul_left (1 / ↑k)

/-- tsum version of the generalized formula. -/
theorem generalized_alternating_tsum (k : ℕ) (hk : 0 < k) :
    ∑' n : ℕ, (if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + ↑k))) =
      (1 / ↑k) * (Real.log 2 - (-1 : ℝ) ^ k * (Real.log 2 - altHarmonicPartial k)) := by
  exact (generalized_alternating_sum k hk).tsum_eq

-- ═══════════════════════════════════════════════════
-- Part VII: Verification of Special Cases
-- ═══════════════════════════════════════════════════

/-- k=1 case: reduces to 2·log 2 - 1, matching the parent proof. -/
theorem special_case_k1 :
    (1 / (1 : ℝ)) * (Real.log 2 - (-1 : ℝ) ^ 1 * (Real.log 2 - altHarmonicPartial 1)) =
    2 * Real.log 2 - 1 := by
  rw [altHarmonicPartial_one]
  ring

/-- k=2 case: logarithmic terms cancel, giving exactly 1/4.
    A_2 = 1 - 1/2 = 1/2, so (1/2)(log 2 - 1·(log 2 - 1/2)) = (1/2)(1/2) = 1/4. -/
theorem special_case_k2 :
    (1 / (2 : ℝ)) * (Real.log 2 - (-1 : ℝ) ^ 2 * (Real.log 2 - altHarmonicPartial 2)) =
    1 / 4 := by
  simp only [altHarmonicPartial, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

end AlternatingTriangularReciprocals.Generalized
