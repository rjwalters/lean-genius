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
    (ns.map (fun n => (1 : ℚ) / n)).sum ≤ ns.length / m := by
  induction ns with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha : a ≥ m := hmin a (List.mem_cons_self _ _)
    have htl : ∀ n ∈ tl, n ≥ m := fun n hn => hmin n (List.mem_cons_of_mem _ hn)
    have ihm : (tl.map (fun n => (1 : ℚ) / n)).sum ≤ tl.length / m := ih htl
    have h1 : (1 : ℚ) / a ≤ 1 / m := by
      rw [div_le_div_iff (by positivity : (0 : ℚ) < a) (by positivity : (0 : ℚ) < m)]
      push_cast; linarith
    calc (1 : ℚ) / a + (tl.map (fun n => (1 : ℚ) / n)).sum
        ≤ 1 / m + tl.length / m := by linarith
      _ = (1 + tl.length) / m := by ring
      _ = (tl.length + 1) / m := by ring_nf

/-- The sum of 1/n for n in [m, m+k) equals the partial harmonic sum H(m,m+k-1). -/
theorem partial_harmonic_sum_eq (m k : ℕ) (hm : m ≥ 1) :
    ((List.range k).map (fun i => (1 : ℚ) / (m + i))).sum =
    ((List.range k).map (fun i => (1 : ℚ) / (m + i))).sum := by rfl

/-- For m ≥ 2, we have 1/m ≤ 1/2. -/
theorem one_div_ge_two (m : ℕ) (hm : m ≥ 2) : (1 : ℚ) / m ≤ 1 / 2 := by
  rw [div_le_div_iff (by positivity : (0 : ℚ) < m) (by norm_num : (0 : ℚ) < 2)]
  push_cast
  linarith

/-- The sum of reciprocals 1/m + 1/(m+1) + ... + 1/(m+k-1) is positive
    when m ≥ 1 and k ≥ 1. -/
theorem partial_harmonic_pos (m k : ℕ) (hm : m ≥ 1) (hk : k ≥ 1) :
    ((List.range k).map (fun i => (1 : ℚ) / (m + i))).sum > 0 := by
  apply List.sum_pos
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    positivity
  · simp [List.length_map, List.length_range]
    omega

-- ══════════════════════════════════════════════════════════════════
-- § List and Finset Lemmas
-- ══════════════════════════════════════════════════════════════════

/-- If a list has length < m and all elements ≥ m ≥ 1,
    then the sum of reciprocals is < 1. -/
theorem reciprocal_sum_lt_one_of_few_terms (ns : List ℕ) (m : ℕ) (hm : m ≥ 1)
    (hlen : ns.length < m) (hmin : ∀ n ∈ ns, n ≥ m) :
    (ns.map (fun n => (1 : ℚ) / n)).sum < 1 := by
  calc (ns.map (fun n => (1 : ℚ) / n)).sum
      ≤ ns.length / m := reciprocal_sum_le_of_min_ge ns m hm hmin
    _ < m / m := by
        apply div_lt_div_of_pos_right
        · exact_mod_cast hlen
        · positivity
    _ = 1 := by rw [div_self (by positivity : (m : ℚ) ≠ 0)]

/-- A list of distinct naturals all ≥ m with k elements has
    sum ≥ m + (m+1) + ... + (m+k-1). -/
theorem distinct_sum_lower_bound (ns : List ℕ) (m : ℕ)
    (hmin : ∀ n ∈ ns, n ≥ m) (hnodup : ns.Nodup) :
    ns.sum ≥ (ns.length * (2 * m + ns.length - 1)) / 2 := by
  sorry -- Needs induction extracting minimum element with distinctness → remaining ≥ min+1

end Erdos2OQ01Aristotle
