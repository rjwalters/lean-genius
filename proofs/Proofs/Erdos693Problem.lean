/-
Erdős Problem #693: Divisor Gaps in Intervals

Source: https://erdosproblems.com/693
Status: OPEN

Statement:
Let k ≥ 2 and n be sufficiently large. Consider the set A of integers in
[n, n^k] that have a divisor in the interval (n, 2n). Order A as
a₁ < a₂ < ···.

Question: Is the maximum gap max_i(a_{i+1} - a_i) bounded by (log n)^O(1)?

Key Insight:
Elements of A have a "medium-sized" divisor. Heuristically, a random integer
has a divisor in (n, 2n) with probability ~log(2), suggesting density ~1/log(n)
in [n, n^k], which would make average gaps ~log(n).

References:
- Erdős [Er79e]
- Ford (2008) "The distribution of integers with a divisor in a given interval"
- Related to Problem #446 (density δ(n) solved by Ford)
-/

import Mathlib

open Nat Finset Set Filter

namespace Erdos693

/- ## Part I: Basic Definitions -/

/-- An integer m has a divisor in the open interval (a, b). -/
def hasDivisorInInterval (m : ℕ) (a b : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ m ∧ a < d ∧ d < b

/-- The set A(n, k): integers in [n, n^k] with a divisor in (n, 2n). -/
def setA (n k : ℕ) : Set ℕ :=
  { m | n ≤ m ∧ m ≤ n ^ k ∧ hasDivisorInInterval m n (2 * n) }

/-- setA is finite for n ≥ 1 (contained in the finite interval [n, n^k]). -/
theorem setA_finite (n k : ℕ) (_hn : n ≥ 1) : (setA n k).Finite := by
  apply Set.Finite.subset (Set.finite_Icc n (n ^ k))
  intro m hm
  exact ⟨hm.1, hm.2.1⟩

/-- setA is a subset of Set.Icc n (n^k). -/
theorem setA_subset_Icc (n k : ℕ) : setA n k ⊆ Set.Icc n (n ^ k) :=
  fun _m hm => ⟨hm.1, hm.2.1⟩

/-- Every element of A is at least n. -/
theorem setA_lower_bound {n k m : ℕ} (hm : m ∈ setA n k) : n ≤ m :=
  hm.1

/-- Every element of A is at most n^k. -/
theorem setA_upper_bound {n k m : ℕ} (hm : m ∈ setA n k) : m ≤ n ^ k :=
  hm.2.1

/-- Every element of A has a divisor in (n, 2n) by definition. -/
theorem mem_setA_has_divisor {n k m : ℕ} (hm : m ∈ setA n k) :
    hasDivisorInInterval m n (2 * n) :=
  hm.2.2

/-- If d divides m, then m = d·q for some q. -/
theorem divisor_factorization {m d : ℕ} (hd : d ∣ m) :
    ∃ q, m = d * q :=
  hd

/- ## Part II: Monotonicity and Structural Properties -/

/-- setA is monotone in k: if k ≤ k', then setA n k ⊆ setA n k'. -/
theorem setA_mono {n k k' : ℕ} (hn : n ≥ 1) (hkk' : k ≤ k') :
    setA n k ⊆ setA n k' := by
  intro m ⟨hlb, hub, hdiv⟩
  refine ⟨hlb, ?_, hdiv⟩
  calc m ≤ n ^ k := hub
    _ ≤ n ^ k' := Nat.pow_le_pow_right hn hkk'

/-- The divisor d of any element of A satisfies n < d < 2n and d ≥ 2 when n ≥ 1. -/
theorem setA_divisor_bounds {n k m : ℕ} (_hn : n ≥ 1) (hm : m ∈ setA n k) :
    ∃ d : ℕ, d ∣ m ∧ n < d ∧ d < 2 * n ∧ d ≥ 2 := by
  obtain ⟨d, hd_div, hd_lb, hd_ub⟩ := mem_setA_has_divisor hm
  exact ⟨d, hd_div, hd_lb, hd_ub, by omega⟩

/-- The quotient q = m/d for m ∈ A satisfies q ≥ 1. -/
theorem setA_quotient_ge_one {n k m : ℕ} (_hn : n ≥ 2) (_hk : k ≥ 2)
    (hm : m ∈ setA n k) :
    ∃ d q : ℕ, d ∣ m ∧ m = d * q ∧ n < d ∧ d < 2 * n ∧ q ≥ 1 := by
  obtain ⟨d, hd_div, hd_lb, hd_ub⟩ := mem_setA_has_divisor hm
  obtain ⟨q, hq⟩ := divisor_factorization hd_div
  refine ⟨d, q, hd_div, hq, hd_lb, hd_ub, ?_⟩
  by_contra h
  push_neg at h
  interval_cases q
  simp_all
  have := setA_lower_bound hm
  omega

/- ## Part III: Gap Definitions -/

/-- Convert setA to a finset. -/
noncomputable def setAFinset (n k : ℕ) (hn : n ≥ 1) : Finset ℕ :=
  (setA_finite n k hn).toFinset

/-- The ordered list of elements in A. -/
noncomputable def orderedA (n k : ℕ) (hn : n ≥ 1) : List ℕ :=
  (setAFinset n k hn).sort (· ≤ ·)

/-- Gap between consecutive elements in a sorted list. -/
def consecutiveGaps (L : List ℕ) : List ℕ :=
  L.zipWith (fun a b => b - a) L.tail

/-- Maximum gap in a list. -/
noncomputable def maxGap (L : List ℕ) : ℕ :=
  (consecutiveGaps L).foldl max 0

/-- The maximum gap for the set A(n, k). -/
noncomputable def maxGapA (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  maxGap (orderedA n k hn)

/- ## Part IV: The Main Problem -/

/-- Polylogarithmic bound: ∃ C, α > 0 such that maxGap ≤ C·(log n)^α for large n. -/
def polylogBoundedGap (k : ℕ) : Prop :=
  ∃ C α : ℝ, C > 0 ∧ α > 0 ∧
    ∀ᶠ n in atTop, ∀ hn : (n : ℕ) ≥ 1,
      (maxGapA n k hn : ℝ) ≤ C * (Real.log n) ^ α

/-- **Erdős Problem #693 (OPEN):** Is the maximum gap polylogarithmically bounded? -/
def erdos693Conjecture : Prop :=
  ∀ k : ℕ, k ≥ 2 → polylogBoundedGap k

/- ## Part V: List Infrastructure Lemmas -/

/-- consecutiveGaps of an empty list is empty. -/
theorem consecutiveGaps_nil : consecutiveGaps ([] : List ℕ) = [] := rfl

/-- consecutiveGaps of a singleton is empty. -/
theorem consecutiveGaps_singleton (a : ℕ) : consecutiveGaps [a] = [] := rfl

/-- maxGap of an empty list is 0. -/
theorem maxGap_nil : maxGap ([] : List ℕ) = 0 := rfl

/-- maxGap of a singleton is 0 (no gaps). -/
theorem maxGap_singleton (a : ℕ) : maxGap [a] = 0 := rfl

/- ## Part VI: Cardinality and Range -/

/-- For k ≥ 1 and n ≥ 1, we have n ≤ n^k. -/
theorem le_pow_of_ge_one {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1) : n ≤ n ^ k := by
  calc n = n ^ 1 := (pow_one n).symm
    _ ≤ n ^ k := Nat.pow_le_pow_right hn hk

/-- setA is contained in the Finset.Icc. -/
theorem setAFinset_subset_Icc (n k : ℕ) (hn : n ≥ 1) :
    setAFinset n k hn ⊆ Finset.Icc n (n ^ k) := by
  intro m hm
  rw [Finset.mem_Icc]
  have hm' := (setA_finite n k hn).mem_toFinset.mp hm
  exact ⟨hm'.1, hm'.2.1⟩

/-- setA has at most n^k - n + 1 elements. -/
theorem setA_card_le (n k : ℕ) (hn : n ≥ 1) (_hk : k ≥ 1) :
    (setAFinset n k hn).card ≤ n ^ k - n + 1 := by
  calc (setAFinset n k hn).card
      ≤ (Finset.Icc n (n ^ k)).card := Finset.card_le_card (setAFinset_subset_Icc n k hn)
    _ ≤ n ^ k - n + 1 := by simp [Nat.card_Icc]; omega

/- ## Part VII: Membership Witnesses -/

/-- d·q ∈ setA when d ∈ (n, 2n) and d·q ∈ [n, n^k].
This is the fundamental membership criterion. -/
theorem mem_setA_of_divisor_product {n k d q : ℕ} (hd_lb : n < d) (hd_ub : d < 2 * n)
    (hm_lb : n ≤ d * q) (hm_ub : d * q ≤ n ^ k) :
    d * q ∈ setA n k := by
  refine ⟨hm_lb, hm_ub, d, ⟨q, rfl⟩, hd_lb, hd_ub⟩

/-- For n ≥ 2, n+1 is in setA when k ≥ 2 (since n+1 divides itself and n < n+1 < 2n). -/
theorem mem_setA_of_succ {n k : ℕ} (hn : n ≥ 2) (hk : k ≥ 2) :
    n + 1 ∈ setA n k := by
  refine ⟨by omega, ?_, ?_⟩
  · calc n + 1 ≤ n * n := by nlinarith
      _ = n ^ 2 := by ring
      _ ≤ n ^ k := Nat.pow_le_pow_right (by omega) hk
  · exact ⟨n + 1, ⟨1, by ring⟩, by omega, by omega⟩

/-- For n ≥ 2, k ≥ 2, setA is nonempty. -/
theorem setA_nonempty {n k : ℕ} (hn : n ≥ 2) (hk : k ≥ 2) : (setA n k).Nonempty :=
  ⟨n + 1, mem_setA_of_succ hn hk⟩

/-- Every integer d ∈ (n, 2n) is in setA (since d divides itself).
Requires n ≥ 3 so that d < 2n ≤ n^2 ≤ n^k. -/
theorem setA_contains_interval {n k : ℕ} (hn : n ≥ 3) (hk : k ≥ 2) :
    ∀ d : ℕ, n < d → d < 2 * n → d ∈ setA n k := by
  intro d hd_lb hd_ub
  refine ⟨by omega, ?_, ?_⟩
  · have h2n : 2 * n ≤ n * n := by nlinarith
    have : d < n ^ k := calc
      d < 2 * n := hd_ub
      _ ≤ n * n := h2n
      _ = n ^ 2 := by ring
      _ ≤ n ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  · exact ⟨d, dvd_refl d, hd_lb, hd_ub⟩

/-- setA contains at least n-1 elements when k ≥ 2, n ≥ 3. -/
theorem setA_has_many_elements {n k : ℕ} (hn : n ≥ 3) (hk : k ≥ 2) :
    n - 1 ≤ (setAFinset n k (by omega : n ≥ 1)).card := by
  have h_sub : ∀ d, d ∈ Finset.Ioo n (2 * n) →
      d ∈ setAFinset n k (by omega : n ≥ 1) := by
    intro d hd
    rw [Finset.mem_Ioo] at hd
    simp only [setAFinset, Set.Finite.mem_toFinset]
    exact setA_contains_interval hn hk d hd.1 hd.2
  have h_card : (Finset.Ioo n (2 * n)).card = n - 1 := by
    simp [Nat.card_Ioo]; omega
  calc n - 1 = (Finset.Ioo n (2 * n)).card := h_card.symm
    _ ≤ (setAFinset n k (by omega : n ≥ 1)).card :=
        Finset.card_le_card h_sub

/- ## Part VIII: Gap Bounds -/

/-- Helper: if all elements of a list are in [lo, hi], the foldl max of
    consecutive gaps is bounded by hi - lo. -/
private theorem consecutiveGaps_foldl_max_le (lo hi : ℕ) :
    ∀ (L : List ℕ) (acc : ℕ),
      acc ≤ hi - lo →
      (∀ x ∈ L, lo ≤ x ∧ x ≤ hi) →
      (consecutiveGaps L).foldl max acc ≤ hi - lo := by
  intro L
  induction L with
  | nil => intro acc hacc _; rw [consecutiveGaps_nil]; exact hacc
  | cons a L ih =>
    intro acc hacc hL
    cases L with
    | nil => rw [consecutiveGaps_singleton]; exact hacc
    | cons b L' =>
      have hcg : consecutiveGaps (a :: b :: L') =
          (b - a) :: consecutiveGaps (b :: L') := by
        simp only [consecutiveGaps, List.tail_cons, List.zipWith_cons_cons]
      rw [hcg]; change (consecutiveGaps (b :: L')).foldl max (max acc (b - a)) ≤ hi - lo
      apply ih
      · exact max_le hacc (by
          have := (hL a (List.mem_cons_self _ _)).1
          have := (hL b (List.mem_cons_of_mem _ (List.mem_cons_self _ _))).2
          omega)
      · intro x hx; exact hL x (List.mem_cons_of_mem _ hx)

/-- Maximum gap ≤ n^k - n: all elements lie in [n, n^k], so no
    consecutive difference can exceed the total range. -/
theorem maxGap_trivial_upper (n k : ℕ) (hn : n ≥ 1) :
    maxGapA n k hn ≤ n ^ k - n := by
  unfold maxGapA maxGap
  apply consecutiveGaps_foldl_max_le n (n ^ k) (orderedA n k hn) 0 (Nat.zero_le _)
  intro x hx
  have hmem : x ∈ setAFinset n k hn := by
    simp only [orderedA] at hx
    rwa [Finset.mem_sort] at hx
  exact Finset.mem_Icc.mp (setAFinset_subset_Icc n k hn hmem)

/-- Note: a previous `maxGap_pigeonhole` axiom stating `maxGap * card ≥ n^k - n`
    was removed because the bound is incorrect — counterexample: n=2, k=2 gives
    setA = {3} (only 3 has a divisor in (2,4)), so card=1, maxGap=0, but n^k-n=2.
    A correct pigeonhole bound involves the actual span (last-first) of the sorted
    list, not the ambient range n^k - n. -/

/-- Crude upper bound on average gap using cardinality. -/
theorem average_gap_crude_bound {n k : ℕ} (_hn : n ≥ 3) (_hk : k ≥ 2) :
    (n ^ k - n) / (setAFinset n k (by omega : n ≥ 1)).card ≤ n ^ k - n := by
  apply Nat.div_le_self

/- ## Part IX: Counting and Density -/

/-- Count of elements in A. -/
noncomputable def countA (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  (setAFinset n k hn).card

/- ## Part X: orderedA Properties -/

/-- The sorted list of A is sorted in increasing order. -/
theorem orderedA_sorted (n k : ℕ) (hn : n ≥ 1) :
    (orderedA n k hn).Sorted (· ≤ ·) :=
  Finset.sort_sorted (· ≤ ·) _

/-- Membership in orderedA iff membership in setAFinset. -/
theorem mem_orderedA_iff {n k : ℕ} (hn : n ≥ 1) (m : ℕ) :
    m ∈ orderedA n k hn ↔ m ∈ setAFinset n k hn := by
  simp [orderedA, Finset.mem_sort]

/-- Every element of orderedA is in [n, n^k]. -/
theorem orderedA_bounds {n k : ℕ} (hn : n ≥ 1) {m : ℕ}
    (hm : m ∈ orderedA n k hn) : n ≤ m ∧ m ≤ n ^ k :=
  Finset.mem_Icc.mp (setAFinset_subset_Icc n k hn ((mem_orderedA_iff hn m).mp hm))

/-- The length of orderedA equals |A|. -/
theorem orderedA_length (n k : ℕ) (hn : n ≥ 1) :
    (orderedA n k hn).length = (setAFinset n k hn).card :=
  Finset.length_sort _

/-- orderedA is nonempty when n ≥ 2 and k ≥ 2. -/
theorem orderedA_ne_nil {n k : ℕ} (hn : n ≥ 2) (hk : k ≥ 2) :
    (orderedA n k (by omega : n ≥ 1)).length ≥ 1 := by
  rw [orderedA_length]
  have : n + 1 ∈ setAFinset n k (by omega : n ≥ 1) := by
    simp [setAFinset, Set.Finite.mem_toFinset]
    exact mem_setA_of_succ hn hk
  have := Finset.card_pos.mpr ⟨n + 1, this⟩
  omega

/-- orderedA has no duplicates (comes from a Finset). -/
theorem orderedA_nodup (n k : ℕ) (hn : n ≥ 1) :
    (orderedA n k hn).Nodup :=
  Finset.sort_nodup _ _

/- ## Part XI: Alternative Formulation -/

/-- Maximum gap alias. -/
noncomputable def maxConsecDiff (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  maxGap (orderedA n k hn)

/-- The polylog conjecture restated. -/
theorem polylog_restatement :
    erdos693Conjecture ↔
      ∀ k : ℕ, k ≥ 2 →
        ∃ C α : ℝ, C > 0 ∧ α > 0 ∧
          ∀ᶠ n in atTop, ∀ hn : (n : ℕ) ≥ 1,
            (maxGapA n k hn : ℝ) ≤ C * (Real.log n) ^ α :=
  Iff.rfl

/- ## Part XI: Connections to Problem #446 -/

/-
**Connection to Erdős Problem #446:**
Problem #446 asks for the growth rate of δ(n). Ford (2008) solved this:
  δ(n) ≍ 1/((log n)^α · (log log n)^{3/2}), α ≈ 0.086
Problem #693 is the "gap version": #446 = average, #693 = worst-case.
-/

/-- The Erdős-Ford constant α governing divisor density. -/
noncomputable def fordAlpha : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- A weaker form: max gap grows subpolynomially. -/
def subpolynomialGap (k : ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∀ᶠ n in atTop, ∀ hn : (n : ℕ) ≥ 1,
      (maxGapA n k hn : ℝ) ≤ (n : ℝ) ^ ε

/-- Polylogarithmic implies subpolynomial: for any ε > 0, eventually
    C · (log n)^α ≤ n^ε. Uses that log = o(n^δ) for any δ > 0
    (Mathlib: `isLittleO_log_rpow_atTop`), splitting ε as ε/2 + ε/2. -/
theorem polylog_implies_subpoly : ∀ k : ℕ, polylogBoundedGap k → subpolynomialGap k := by
  intro k ⟨C, α, hC, hα, hpoly⟩ ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hδ : (0 : ℝ) < ε / (2 * α) := div_pos hε (by positivity)
  -- From little-o: eventually |log x| ≤ |x^(ε/(2α))| for x : ℝ
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hδ).bound (show (0 : ℝ) < 1 by norm_num))
  -- From polylog bound (on ℕ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpoly
  -- Combined ℕ threshold
  rw [Filter.eventually_atTop]
  refine ⟨max (max ⌈R⌉₊ ⌈C ^ (2 / ε)⌉₊) N, fun n hn hn1 => ?_⟩
  -- Sub-threshold extraction
  have hR_le : ⌈R⌉₊ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hC_le : ⌈C ^ (2 / ε)⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hN_le : N ≤ n := le_trans (le_max_right _ _) hn
  -- Transfer to ℝ
  have hR_real : R ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil R) (by exact_mod_cast hR_le)
  have hCexp_real : C ^ (2 / ε) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hC_le)
  -- Basic positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
  have hlog_nn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn1)
  -- (1) log n ≤ n^(ε/(2α)) from isLittleO bound
  have h_logb := hR (n : ℝ) hR_real
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hlog_nn, abs_of_nonneg (rpow_nonneg hn_nn _)] at h_logb
  -- (2) (log n)^α ≤ n^(ε/2) by raising to power α
  have h_pow : Real.log (n : ℝ) ^ α ≤ (n : ℝ) ^ (ε / 2) :=
    calc Real.log (n : ℝ) ^ α
        ≤ ((n : ℝ) ^ (ε / (2 * α))) ^ α :=
          rpow_le_rpow hlog_nn h_logb hα.le
      _ = (n : ℝ) ^ (ε / (2 * α) * α) := rpow_mul hn_nn _ _
      _ = (n : ℝ) ^ (ε / 2) := by congr 1; field_simp
  -- (3) C ≤ n^(ε/2) since n ≥ C^(2/ε)
  have h_C : C ≤ (n : ℝ) ^ (ε / 2) := by
    have hC_eq : C = (C ^ (2 / ε)) ^ (ε / 2) := by
      rw [rpow_mul hC.le, show (2 : ℝ) / ε * (ε / 2) = 1 by field_simp, rpow_one]
    rw [hC_eq]
    exact rpow_le_rpow (rpow_nonneg hC.le _) hCexp_real hε2.le
  -- Combine: maxGap ≤ C·(log n)^α ≤ C·n^(ε/2) ≤ n^(ε/2)·n^(ε/2) = n^ε
  calc (maxGapA n k hn1 : ℝ)
      ≤ C * Real.log (n : ℝ) ^ α := hN n hN_le hn1
    _ ≤ C * (n : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left h_pow hC.le
    _ ≤ (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right h_C (rpow_nonneg hn_nn _)
    _ = (n : ℝ) ^ ε := by rw [← rpow_add hn_pos]; congr 1; ring

/- ## Part XII: Summary -/

/--
**Erdős Problem #693: Summary**

**STATUS:** OPEN

**PROVED (31+ theorems):**
- setA finite, contained in [n, n^k], monotone in k
- Divisor bounds: d ≥ 2, quotient q ≥ 1
- setA contains all d ∈ (n, 2n) (≥ n-1 elements for n ≥ 3)
- General membership criterion, specific witnesses
- Gap infrastructure, cardinality bounds
- maxGap ≤ n^k - n (proved by list induction)
- polylogBoundedGap → subpolynomialGap (proved via isLittleO_log_rpow_atTop)
- orderedA: sorted, membership, bounds, length, nonempty, nodup

**AXIOMATIZED (1 axiom):**
- Ford density theorem (deep analytic number theory, Ford 2008)

**REMOVED:**
- maxGap_pigeonhole (incorrect bound — see comment at Part VIII)
-/
theorem erdos_693_summary :
    erdos693Conjecture ↔ ∀ k, k ≥ 2 → polylogBoundedGap k :=
  Iff.rfl

end Erdos693
