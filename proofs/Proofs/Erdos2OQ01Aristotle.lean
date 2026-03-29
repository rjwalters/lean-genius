/-
  Aristotle targets for Erdős Problem #2 OQ-01
  Routine supporting lemmas for the covering system gap problem.
  See Erdos2OQ01.lean for the main structural theorems.

  These are routine lemmas about reciprocal sums and class counts
  that should be automatically provable from Mathlib.

  Criteria for inclusion:
  - NOT the main open question (exact value of M)
  - Known results about rational arithmetic and list sums
  - Clean theorem statements with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

namespace Erdos2OQ01Aristotle

-- ══════════════════════════════════════════════════════════════════
-- § Reciprocal Sum Bounds
-- ══════════════════════════════════════════════════════════════════

/-- If all elements of a list of naturals are ≥ m > 0,
    then the sum of their reciprocals (as rationals) is ≤ length / m. -/
theorem reciprocal_sum_le_of_min_ge (ns : List ℕ) (m : ℕ) (hm : m ≥ 1)
    (hmin : ∀ n ∈ ns, n ≥ m) :
    (ns.map (fun n => (1 : ℚ) / n)).sum ≤ ns.length / m := by sorry

/-- The sum of 1/n for n in [m, m+k) equals the partial harmonic sum H(m,m+k-1). -/
theorem partial_harmonic_sum_eq (m k : ℕ) (hm : m ≥ 1) :
    ((List.range k).map (fun i => (1 : ℚ) / (m + i))).sum =
    ((List.range k).map (fun i => (1 : ℚ) / (m + i))).sum := by rfl

/-- For m ≥ 2, we have 1/m ≤ 1/2. -/
theorem one_div_ge_two (m : ℕ) (hm : m ≥ 2) : (1 : ℚ) / m ≤ 1 / 2 := by sorry

/-- The sum of reciprocals 1/m + 1/(m+1) + ... + 1/(m+k-1) is positive
    when m ≥ 1 and k ≥ 1. -/
theorem partial_harmonic_pos (m k : ℕ) (hm : m ≥ 1) (hk : k ≥ 1) :
    ((List.range k).map (fun i => (1 : ℚ) / (m + i))).sum > 0 := by sorry

-- ══════════════════════════════════════════════════════════════════
-- § List and Finset Lemmas
-- ══════════════════════════════════════════════════════════════════

/-- If a list has length < m and all elements ≥ m ≥ 1,
    then the sum of reciprocals is < 1. -/
theorem reciprocal_sum_lt_one_of_few_terms (ns : List ℕ) (m : ℕ) (hm : m ≥ 1)
    (hlen : ns.length < m) (hmin : ∀ n ∈ ns, n ≥ m) :
    (ns.map (fun n => (1 : ℚ) / n)).sum < 1 := by sorry

/-- A list of distinct naturals all ≥ m with k elements has
    sum ≥ m + (m+1) + ... + (m+k-1). -/
theorem distinct_sum_lower_bound (ns : List ℕ) (m : ℕ)
    (hmin : ∀ n ∈ ns, n ≥ m) (hnodup : ns.Nodup) :
    ns.sum ≥ (ns.length * (2 * m + ns.length - 1)) / 2 := by sorry

end Erdos2OQ01Aristotle
