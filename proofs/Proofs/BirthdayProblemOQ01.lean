import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-
# Expected Number of Shared Birthday Pairs (OQ-01)

## What This Proves
Extends the Birthday Problem by analyzing the expected number of shared
birthday pairs in a group of n people with d equally likely birthdays.

**Key Results:**
1. Basic properties: nonnegativity, values at n=0,1,2
2. Monotonicity: E[pairs] is increasing in n
3. Additivity: each new person adds n/d to the expected pairs
4. Sum formula: E[pairs] = sum_{i<n} i/d (telescoping from additivity)
5. Rational formula: 2*d*E[pairs] = n*(n-1)
6. Variance formula and variance <= expected
7. Threshold computations: n=28 is first to exceed 1 expected pair (d=365)
8. General d: formulas work for any number of days d >= 1
9. Positivity: E[pairs] > 0 when n >= 2 and d > 0
10. General threshold criterion: E[pairs] > k when C(n,2) > k*d
-/

namespace BirthdayProblemOQ01

/-- Expected number of shared birthday pairs among n people with d possible
    birthdays. By linearity of expectation, E[pairs] = C(n,2) / d. -/
noncomputable def expectedPairs (n d : ℕ) : ℚ :=
  (n.choose 2 : ℚ) / (d : ℚ)

/-- Variance of the number of shared birthday pairs. Each pair indicator is
    Bernoulli(1/d), with variance (1/d)(1 - 1/d) = (d-1)/d^2.
    Var = C(n,2) * (d-1) / d^2. -/
noncomputable def variancePairs (n d : ℕ) : ℚ :=
  (n.choose 2 : ℚ) * ((d : ℚ) - 1) / ((d : ℚ) ^ 2)

-- ## Part I: Basic Properties

/-- Expected pairs is nonneg. -/
theorem expectedPairs_nonneg (n d : ℕ) : 0 ≤ expectedPairs n d := by
  unfold expectedPairs
  apply div_nonneg <;> positivity

/-- With 0 people, expected pairs is 0. -/
theorem expectedPairs_zero (d : ℕ) : expectedPairs 0 d = 0 := by
  simp [expectedPairs, Nat.choose]

/-- With 1 person, expected pairs is 0. -/
theorem expectedPairs_one (d : ℕ) : expectedPairs 1 d = 0 := by
  simp [expectedPairs, Nat.choose]

/-- With 2 people, expected pairs is 1/d. -/
theorem expectedPairs_two (d : ℕ) : expectedPairs 2 d = 1 / d := by
  unfold expectedPairs
  norm_num [Nat.choose]

-- ## Part II: Monotonicity

/-- C(n, 2) <= C(m, 2) when n <= m. -/
theorem choose_two_mono {n m : ℕ} (h : n ≤ m) : n.choose 2 ≤ m.choose 2 :=
  Nat.choose_mono 2 h

/-- Expected pairs is monotone in n. -/
theorem expectedPairs_mono {n m : ℕ} (h : n ≤ m) (d : ℕ) :
    expectedPairs n d ≤ expectedPairs m d := by
  unfold expectedPairs
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℚ) ≤ d)
  exact_mod_cast choose_two_mono h

-- ## Part III: Additivity

/-- Key identity: C(n+1, 2) = C(n, 2) + n. -/
theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  -- Use the recurrence for choose: C(n+1, k+1) = C(n, k+1) + C(n, k)
  -- Specifically: C(n+1, 2) = C(n, 2) + C(n, 1) = C(n, 2) + n
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- Additivity: expectedPairs (n+1) d = expectedPairs n d + n/d.
    Each new person adds n new potential pairs. -/
theorem expectedPairs_succ (n d : ℕ) :
    expectedPairs (n + 1) d = expectedPairs n d + (n : ℚ) / d := by
  unfold expectedPairs
  rw [choose_two_succ, Nat.cast_add, add_div]

/-- The sum formula: E[pairs for n people] equals the sum of i/d for i from 0 to n-1.
    This follows from telescoping via expectedPairs_succ. -/
theorem expectedPairs_sum (n d : ℕ) :
    expectedPairs n d = (∑ i ∈ Finset.range n, (i : ℚ)) / d := by
  induction n with
  | zero => simp [expectedPairs_zero]
  | succ k ih =>
    rw [expectedPairs_succ]
    rw [ih]
    rw [Finset.sum_range_succ]
    ring

-- ## Part IV: The Rational Formula

/-- C(n, 2) = n * (n - 1) / 2 (natural number division). -/
theorem choose_two_eq (n : ℕ) : n.choose 2 = n * (n - 1) / 2 :=
  Nat.choose_two_right n

/-- 2 * C(n, 2) = n * (n - 1). -/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  have heven : 2 ∣ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (n - 1), by rw [hk]; ring⟩
    · have : n - 1 = 2 * k := by omega
      exact ⟨n * k, by rw [this]; ring⟩
  omega

/-- In Q: C(n,2) = n * (n-1) / 2. -/
theorem choose_two_cast (n : ℕ) :
    (n.choose 2 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  have key := two_mul_choose_two n
  -- key : 2 * n.choose 2 = n * (n - 1) in ℕ
  rcases n with _ | m
  · simp [Nat.choose]
  · -- n = m + 1, so n - 1 = m
    have hsub : (m + 1 - 1 : ℕ) = m := Nat.succ_sub_one m
    rw [hsub] at key
    -- key : 2 * (m + 1).choose 2 = (m + 1) * m
    have hcast : (2 : ℚ) * ((m + 1).choose 2 : ℚ) = ((m + 1 : ℕ) : ℚ) * ((m : ℕ) : ℚ) := by
      exact_mod_cast key
    -- Goal: ↑((m + 1).choose 2) = ↑(m + 1) * (↑(m + 1) - 1) / 2
    -- Since ↑(m + 1) - 1 = ↑m (in ℚ):
    have hmcast : ((m + 1 : ℕ) : ℚ) - 1 = (m : ℚ) := by push_cast; ring
    rw [hmcast]
    linarith

/-- Expected pairs as a rational: E[pairs] = n(n-1) / (2d). -/
theorem expectedPairs_eq_rational (n d : ℕ) :
    expectedPairs n d = (n : ℚ) * ((n : ℚ) - 1) / (2 * d) := by
  unfold expectedPairs
  rw [choose_two_cast]
  ring

-- ## Part V: Variance

/-- Variance is nonneg for d >= 1. -/
theorem variancePairs_nonneg (n d : ℕ) (hd : 1 ≤ d) : 0 ≤ variancePairs n d := by
  unfold variancePairs
  apply div_nonneg
  · apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · have : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
      linarith
  · positivity

/-- Variance is 0 with fewer than 2 people. -/
theorem variancePairs_zero (d : ℕ) : variancePairs 0 d = 0 := by
  simp [variancePairs, Nat.choose]

theorem variancePairs_one (d : ℕ) : variancePairs 1 d = 0 := by
  simp [variancePairs, Nat.choose]

/-- Variance <= Expected (since (d-1)/d <= 1). -/
theorem variancePairs_le_expected (n d : ℕ) (hd : 1 ≤ d) :
    variancePairs n d ≤ expectedPairs n d := by
  unfold variancePairs expectedPairs
  have hd_pos : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd2 : (0 : ℚ) < (d : ℚ) ^ 2 := by positivity
  rw [div_le_div_iff₀ hd2 hd_pos]
  have : (d : ℚ) - 1 ≤ d := by linarith
  nlinarith [Nat.zero_le (n.choose 2)]

-- ## Part VI: Threshold Computations (d = 365)

abbrev stdDays : ℕ := 365

/-- E[pairs] for the standard birthday problem. -/
noncomputable def stdExpectedPairs (n : ℕ) : ℚ := expectedPairs n stdDays

/-- With 23 people: E[pairs] = 253/365. -/
theorem std_expected_23 : stdExpectedPairs 23 = 253 / 365 := by
  unfold stdExpectedPairs expectedPairs stdDays
  norm_num [Nat.choose]

/-- The n=28 threshold: first n where E[pairs] > 1. -/
theorem std_expected_28_gt_one : stdExpectedPairs 28 > 1 := by
  unfold stdExpectedPairs expectedPairs stdDays
  norm_num [Nat.choose]

/-- n=27 gives E[pairs] < 1. -/
theorem std_expected_27_lt_one : stdExpectedPairs 27 < 1 := by
  unfold stdExpectedPairs expectedPairs stdDays
  norm_num [Nat.choose]

/-- The exact value at n=28: E[pairs] = 378/365. -/
theorem std_expected_28_exact : stdExpectedPairs 28 = 378 / 365 := by
  unfold stdExpectedPairs expectedPairs stdDays
  norm_num [Nat.choose]

/-- n=40: C(40,2) = 780 > 2*365 = 730, so E[pairs] > 2. -/
theorem std_expected_40_gt_two : stdExpectedPairs 40 > 2 := by
  show expectedPairs 40 365 > 2
  unfold expectedPairs
  have : Nat.choose 40 2 = 780 := by native_decide
  rw [this]; norm_num

/-- n=39 threshold: E[pairs] > 2 (since C(39,2) = 741 > 730 = 2*365). -/
theorem std_expected_39_gt_two : stdExpectedPairs 39 > 2 := by
  show expectedPairs 39 365 > 2
  unfold expectedPairs
  have : Nat.choose 39 2 = 741 := by native_decide
  rw [this]; norm_num

/-- n=38: C(38,2) = 703 < 730 = 2*365, so E[pairs] < 2. -/
theorem std_expected_38_lt_two : stdExpectedPairs 38 < 2 := by
  show expectedPairs 38 365 < 2
  unfold expectedPairs
  have : Nat.choose 38 2 = 703 := by native_decide
  rw [this]; norm_num

-- ## Part VII: Positivity

/-- If n >= 2 and d > 0, then the expected pairs is positive. -/
theorem expectedPairs_pos (n d : ℕ) (hd : 0 < d) (hn : 2 ≤ n) :
    0 < expectedPairs n d := by
  unfold expectedPairs
  apply div_pos
  · have : 0 < n.choose 2 := by
      have h2 := choose_two_succ (n - 1)
      have : n - 1 + 1 = n := by omega
      rw [this] at h2
      -- h2 : n.choose 2 = (n-1).choose 2 + (n-1)
      -- Since n >= 2, n-1 >= 1 > 0
      omega
    exact_mod_cast this
  · exact_mod_cast hd

-- ## Part VIII: General Threshold Criterion

/-- The expected pairs exceeds k when C(n,2) > k*d.
    This gives the threshold: n is approximately sqrt(2kd) for k expected pairs. -/
theorem expectedPairs_gt_of_choose_gt (n d k : ℕ) (hd : 0 < d)
    (h : k * d < n.choose 2) :
    (k : ℚ) < expectedPairs n d := by
  unfold expectedPairs
  have hd_pos : (0 : ℚ) < d := by exact_mod_cast hd
  rw [lt_div_iff₀ hd_pos]
  exact_mod_cast h

-- ## Part IX: General Day Count

/-- With d = 7 (days of the week), the threshold is much lower.
    C(4, 2) = 6 < 7, but C(5, 2) = 10 > 7. -/
theorem weekly_expected_5_gt_one : expectedPairs 5 7 > 1 := by
  unfold expectedPairs; norm_num [Nat.choose]

theorem weekly_expected_4_lt_one : expectedPairs 4 7 < 1 := by
  unfold expectedPairs; norm_num [Nat.choose]

/-- With d = 12 (months), threshold is between 5 and 6.
    C(5, 2) = 10 < 12, but C(6, 2) = 15 > 12. -/
theorem monthly_expected_6_gt_one : expectedPairs 6 12 > 1 := by
  unfold expectedPairs; norm_num [Nat.choose]

theorem monthly_expected_5_lt_one : expectedPairs 5 12 < 1 := by
  unfold expectedPairs; norm_num [Nat.choose]

-- ## Part X: Expected k-Tuples (Generalized Collisions)

/-- Expected number of k-tuples sharing a birthday among n people with d
    possible birthdays. By linearity of expectation over indicator variables
    for each k-subset of people:
    E[k-tuples] = C(n,k) / d^(k-1)

    Each k-subset of people has probability 1/d^(k-1) of all sharing
    the same birthday (the first person picks any day, the remaining k-1
    must match, each with probability 1/d). -/
noncomputable def expectedKTuples (n d k : ℕ) : ℚ :=
  (n.choose k : ℚ) / ((d : ℚ) ^ (k - 1))

/-- Specialization: expectedKTuples with k=2 equals expectedPairs. -/
theorem expectedKTuples_two (n d : ℕ) :
    expectedKTuples n d 2 = expectedPairs n d := by
  unfold expectedKTuples expectedPairs
  simp

/-- Expected k-tuples is nonneg. -/
theorem expectedKTuples_nonneg (n d k : ℕ) : 0 ≤ expectedKTuples n d k := by
  unfold expectedKTuples
  apply div_nonneg <;> positivity

/-- With fewer than k people, expected k-tuples is 0. -/
theorem expectedKTuples_lt (n d k : ℕ) (h : n < k) :
    expectedKTuples n d k = 0 := by
  unfold expectedKTuples
  rw [Nat.choose_eq_zero_of_lt h]
  simp

/-- Expected k-tuples is monotone in n. -/
theorem expectedKTuples_mono {n m : ℕ} (h : n ≤ m) (d k : ℕ) :
    expectedKTuples n d k ≤ expectedKTuples m d k := by
  unfold expectedKTuples
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_mono k h

-- ## Part XI: Expected Birthday Triples

/-- Expected number of birthday triples: E[triples] = C(n,3) / d^2. -/
noncomputable def expectedTriples (n d : ℕ) : ℚ := expectedKTuples n d 3

/-- expectedTriples is the specialization of expectedKTuples at k=3. -/
theorem expectedTriples_def (n d : ℕ) :
    expectedTriples n d = (n.choose 3 : ℚ) / ((d : ℚ) ^ 2) := by
  unfold expectedTriples expectedKTuples
  simp

/-- Expected triples is nonneg. -/
theorem expectedTriples_nonneg (n d : ℕ) : 0 ≤ expectedTriples n d :=
  expectedKTuples_nonneg n d 3

/-- With 0, 1, or 2 people, expected triples is 0. -/
theorem expectedTriples_zero (d : ℕ) : expectedTriples 0 d = 0 := by
  unfold expectedTriples; exact expectedKTuples_lt 0 d 3 (by omega)

theorem expectedTriples_one (d : ℕ) : expectedTriples 1 d = 0 := by
  unfold expectedTriples; exact expectedKTuples_lt 1 d 3 (by omega)

theorem expectedTriples_two (d : ℕ) : expectedTriples 2 d = 0 := by
  unfold expectedTriples; exact expectedKTuples_lt 2 d 3 (by omega)

/-- With 3 people, expected triples is 1/d^2. -/
theorem expectedTriples_three (d : ℕ) : expectedTriples 3 d = 1 / ((d : ℚ) ^ 2) := by
  rw [expectedTriples_def]
  norm_num [Nat.choose]

/-- Expected triples is monotone in n. -/
theorem expectedTriples_mono {n m : ℕ} (h : n ≤ m) (d : ℕ) :
    expectedTriples n d ≤ expectedTriples m d :=
  expectedKTuples_mono h d 3

/-- If n >= 3 and d > 0, expected triples is positive. -/
theorem expectedTriples_pos (n d : ℕ) (hd : 0 < d) (hn : 3 ≤ n) :
    0 < expectedTriples n d := by
  rw [expectedTriples_def]
  apply div_pos
  · have : 0 < n.choose 3 := Nat.choose_pos hn
    exact_mod_cast this
  · positivity

-- ## Part XII: Triple Threshold for d = 365

/-- E[triples] for the standard birthday problem. -/
noncomputable def stdExpectedTriples (n : ℕ) : ℚ := expectedTriples n stdDays

/-- The triple threshold exceeds 1 when C(n,3) > 365^2 = 133225.
    C(94,3) = 134044 > 133225. -/
theorem std_expected_triples_94_gt_one : stdExpectedTriples 94 > 1 := by
  show expectedTriples 94 365 > 1
  rw [expectedTriples_def]
  have h1 : Nat.choose 94 3 = 134044 := by native_decide
  rw [h1]; norm_num

/-- C(93,3) = 129766 < 133225 = 365^2, so E[triples] < 1. -/
theorem std_expected_triples_93_lt_one : stdExpectedTriples 93 < 1 := by
  show expectedTriples 93 365 < 1
  rw [expectedTriples_def]
  have h1 : Nat.choose 93 3 = 129766 := by native_decide
  rw [h1]; norm_num

/-- The general threshold criterion for k-tuples:
    E[k-tuples] > t when C(n,k) > t * d^(k-1). -/
theorem expectedKTuples_gt_of_choose_gt (n d k : ℕ) (t : ℕ) (hd : 0 < d) (hk : 1 ≤ k)
    (h : t * d ^ (k - 1) < n.choose k) :
    (t : ℚ) < expectedKTuples n d k := by
  unfold expectedKTuples
  have hd_pos : (0 : ℚ) < (d : ℚ) ^ (k - 1) := by positivity
  rw [lt_div_iff₀ hd_pos]
  exact_mod_cast h

-- ## Part XIII: Comparing Pairs vs Triples

/-- Key combinatorial identity in ℕ: 3 * C(n,3) = C(n,2) * (n-2).
    Both sides equal n*(n-1)*(n-2)/2. -/
theorem three_mul_choose_three (n : ℕ) (hn : 2 ≤ n) :
    3 * n.choose 3 = n.choose 2 * (n - 2) := by
  rcases n with _ | _ | m
  · omega
  · omega
  · -- n = m + 2, so n - 2 = m, n ≥ 2
    simp only [show m + 2 - 2 = m from by omega]
    -- C(m+2, 3) = C(m+1, 2) + C(m+1, 3) but let's use the factorial formula
    -- C(m+2, 3) = (m+2)*(m+1)*m/6 and C(m+2, 2) = (m+2)*(m+1)/2
    -- So 3 * C(m+2, 3) = 3*(m+2)*(m+1)*m/6 = (m+2)*(m+1)*m/2
    -- and C(m+2, 2) * m = (m+2)*(m+1)/2 * m = (m+2)*(m+1)*m/2 ✓
    have h2 := two_mul_choose_two (m + 2)
    -- h2 : 2 * (m+2).choose 2 = (m+2) * (m+1)
    -- Use: 6 * C(n,3) = n*(n-1)*(n-2) for n ≥ 2
    -- We know 2 * C(m+2, 2) = (m+2)*(m+1)
    -- We need 3 * C(m+2, 3) = C(m+2, 2) * m
    -- Equivalently: 6 * C(m+2, 3) = 2 * C(m+2, 2) * m = (m+2)*(m+1)*m
    -- And 6 * C(m+2, 3) = (m+2)!/(m-1)! when m ≥ 1, but ℕ arithmetic is messy.
    -- Use Nat.choose_succ_succ repeatedly:
    -- C(m+2, 3) = C(m+1, 2) + C(m+1, 3)
    -- For the base relation, use omega after reducing to known identities
    rw [Nat.choose_two_right]
    -- Goal: 3 * (m+2).choose 3 = (m+2) * (m+1) / 2 * m
    -- Use the identity: (m+2).choose 3 = (m+2) * (m+1) * m / 6
    -- which follows from Nat.choose applied to a product
    have six_choose : 6 * (m + 2).choose 3 = (m + 2) * (m + 1) * m := by
      have := Nat.choose_three_right (m + 2)
      -- Nat.choose_three_right gives: C(n, 3) = n * (n-1) * (n-2) / 6
      omega
    -- Now: 3 * C(m+2, 3) = (m+2)*(m+1)*m/2
    -- And: (m+2)*(m+1)/2 * m = (m+2)*(m+1)*m/2
    have even_prod : 2 ∣ (m + 2) * (m + 1) := by
      rcases Nat.even_or_odd (m + 2) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (m + 1), by rw [hk]; ring⟩
      · have : m + 1 = 2 * k := by omega
        exact ⟨(m + 2) * k, by rw [this]; ring⟩
    omega

/-- Triples relate to pairs: E[triples] = E[pairs] * (n-2)/(3d)
    when n ≥ 2. This follows from 3 * C(n,3) = C(n,2) * (n-2). -/
theorem triples_from_pairs (n d : ℕ) (hd : 1 ≤ d) (hn : 3 ≤ n) :
    expectedTriples n d = expectedPairs n d * ((n : ℚ) - 2) / (3 * d) := by
  rw [expectedTriples_def]
  unfold expectedPairs
  have hd_pos : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have h3 := three_mul_choose_three n (by omega : 2 ≤ n)
  -- h3 : 3 * n.choose 3 = n.choose 2 * (n - 2) in ℕ
  -- Goal: ↑(n.choose 3) / d^2 = (↑(n.choose 2) / d) * (↑n - 2) / (3 * d)
  -- RHS = ↑(n.choose 2) * (↑n - 2) / (3 * d^2)
  -- So need: ↑(n.choose 3) * 3 = ↑(n.choose 2) * (↑n - 2)
  have hcast : (3 : ℚ) * (n.choose 3 : ℚ) = (n.choose 2 : ℚ) * ((n : ℚ) - 2) := by
    have := h3
    rcases n with _ | _ | m
    · omega
    · omega
    · simp only [show m + 2 - 2 = m from by omega] at this
      have : (3 : ℚ) * ((m + 2).choose 3 : ℚ) = ((m + 2).choose 2 : ℚ) * (m : ℚ) := by
        exact_mod_cast this
      push_cast at this ⊢
      linarith
  field_simp
  linarith

/-- For the standard problem (d=365), E[triples] grows much slower than E[pairs].
    At n=23: E[pairs] ≈ 0.693, E[triples] ≈ 0.00439.
    Triples are roughly (n-2)/(3d) ≈ 21/1095 ≈ 0.019 times as frequent. -/
theorem std_triples_23_value : stdExpectedTriples 23 = 1771 / 133225 := by
  show expectedTriples 23 365 = 1771 / 133225
  rw [expectedTriples_def]
  have h1 : Nat.choose 23 3 = 1771 := by native_decide
  rw [h1]; norm_num

-- ## Part XIV: Expected Quadruples

/-- Expected birthday quadruples: E[quads] = C(n,4) / d^3. -/
noncomputable def expectedQuads (n d : ℕ) : ℚ := expectedKTuples n d 4

/-- expectedQuads is the specialization at k=4. -/
theorem expectedQuads_def (n d : ℕ) :
    expectedQuads n d = (n.choose 4 : ℚ) / ((d : ℚ) ^ 3) := by
  unfold expectedQuads expectedKTuples
  simp

/-- With fewer than 4 people, expected quads is 0. -/
theorem expectedQuads_lt_four (n d : ℕ) (h : n < 4) : expectedQuads n d = 0 := by
  unfold expectedQuads; exact expectedKTuples_lt n d 4 h

/-- Quad threshold (d=365): need C(n,4) > 365^3 = 48627125.
    C(188,4) = 51,895,981 > 48,627,125. -/
theorem std_expected_quads_188_gt_one :
    expectedQuads 188 stdDays > 1 := by
  rw [expectedQuads_def]
  have h1 : Nat.choose 188 4 = 51895981 := by native_decide
  rw [h1]; simp [stdDays]; norm_num

/-- C(187,4) = 47,791,135 < 48,627,125 = 365^3, so E[quads] < 1. -/
theorem std_expected_quads_187_lt_one :
    expectedQuads 187 stdDays < 1 := by
  rw [expectedQuads_def]
  have h1 : Nat.choose 187 4 = 47791135 := by native_decide
  rw [h1]; simp [stdDays]; norm_num

-- ## Part XV: Summary of Thresholds

/-- Summary: the first n where E[k-tuples] > 1 for the standard birthday problem.
    - k=2 (pairs): n=28 (first where C(n,2) > 365)
    - k=3 (triples): n=94 (first where C(n,3) > 365^2)
    - k=4 (quads): n=188 (first where C(n,4) > 365^3)

    The threshold grows roughly as (k! * 365^(k-1))^(1/k) ≈ 365^(1-1/k) * k!^(1/k). -/
theorem thresholds_summary :
    (28 : ℕ).choose 2 > 365 ∧ (27 : ℕ).choose 2 ≤ 365 ∧
    (94 : ℕ).choose 3 > 365 ^ 2 ∧ (93 : ℕ).choose 3 ≤ 365 ^ 2 ∧
    (188 : ℕ).choose 4 > 365 ^ 3 ∧ (187 : ℕ).choose 4 ≤ 365 ^ 3 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

-- ## Verification Examples

example : Nat.choose 23 2 = 253 := by native_decide
example : Nat.choose 28 2 = 378 := by native_decide
example : Nat.choose 39 2 = 741 := by native_decide
example : 365 < Nat.choose 28 2 := by native_decide
example : Nat.choose 27 2 < 365 := by native_decide
example : Nat.choose 94 3 = 134044 := by native_decide
example : Nat.choose 93 3 = 129766 := by native_decide
example : Nat.choose 188 4 = 51895981 := by native_decide
example : Nat.choose 187 4 = 47791135 := by native_decide

end BirthdayProblemOQ01
