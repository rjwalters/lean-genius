/-
  Erdős Problem #771: Subsets Avoiding a Given Sum

  Source: https://erdosproblems.com/771
  Status: SOLVED (Alon-Freiman)

  Statement:
  Let f(n) be maximal such that, for every m ≥ 1, there exists some
  S ⊆ {1, ..., n} with |S| = f(n) such that m ≠ ∑_{a ∈ A} a for all A ⊆ S.

  Is it true that f(n) = (1/2 + o(1)) · n / log n?

  Answer: YES

  Key Results:
  - Erdős-Graham: Lower bound f(n) ≥ (1/2 + o(1)) · n / log n
    Proof: Take S = multiples of smallest prime not dividing m
  - Alon-Freiman: Upper bound f(n) ≤ (1/2 + o(1)) · n / log n
    Proof: Uses LCM of {1, ..., s} argument

  The problem combines additive combinatorics with number theory.

  The deep asymptotics (both the Erdős–Graham lower bound and the Alon–Freiman
  upper bound) are external results and are recorded here as `axiom`s. Everything
  else in this file is machine-checked: the elementary construction behind the
  lower bound (`prime_multiples_size`, `prime_multiples_avoid`) is verified, and
  the two axiomatic bounds are combined into the asymptotic statement
  (`erdos_graham_conjecture_true`, `leading_constant`). The fully verified,
  self-contained construction lives in `Erdos771Construction.lean`.

  References:
  - Erdős-Graham, "Old and new problems and results..."
  - Alon-Freiman (upper bound)
-/

import Mathlib

open Finset BigOperators Real Nat

namespace Erdos771

/-
## Part I: Basic Definitions
-/

/-- The set {1, ..., n}. -/
def Icc_n (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- The set of all subset sums of S. -/
noncomputable def subsetSums (S : Finset ℕ) : Finset ℕ :=
  (S.powerset.image (fun A => ∑ a ∈ A, a)).filter (· > 0)

/-- A set S avoids sum m if no nonempty subset of S sums to m. -/
def AvoidSum (S : Finset ℕ) (m : ℕ) : Prop :=
  m ∉ subsetSums S

/-- An m-avoiding set is a set that avoids sum m. -/
def IsMAvoidingSet (S : Finset ℕ) (n m : ℕ) : Prop :=
  S ⊆ Icc_n n ∧ AvoidSum S m

/-
## Part II: The Function f(n)
-/

open Classical in
/-- The maximum size of an m-avoiding set in {1, ..., n}.
    `AvoidSum · m` is a `Prop` whose decidability we supply classically (this
    definition is `noncomputable`, so no executable code is generated for it). -/
noncomputable def maxAvoidingSize (n m : ℕ) : ℕ :=
  (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S m)
    |>.sup (fun S => S.card)

/-- f(n) is the maximum k such that for all m, there exists an
    m-avoiding set of size at least k. -/
noncomputable def f (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    (Finset.Icc 1 (n * n)).inf'
      (Finset.nonempty_Icc.mpr (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h h)))
      (fun m => maxAvoidingSize n m)

/-- Alternative definition: f(n) is max k such that for every m,
    some S ⊆ {1,...,n} with |S| ≥ k avoids m. -/
def f_property (n k : ℕ) : Prop :=
  ∀ m ≥ 1, ∃ S : Finset ℕ, S ⊆ Icc_n n ∧ S.card ≥ k ∧ AvoidSum S m

/-- If every element of `S` is strictly larger than `m`, then `S` avoids `m`:
    every nonempty subset sum is at least its (single) minimum element `> m`, and
    the empty subset sums to `0`, which is filtered out of `subsetSums`. -/
theorem avoid_of_forall_lt (S : Finset ℕ) (m : ℕ) (hlb : ∀ a ∈ S, m < a) :
    AvoidSum S m := by
  intro hmem
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
  obtain ⟨⟨A, hA, hAsum⟩, hpos⟩ := hmem
  rw [Finset.mem_powerset] at hA
  rcases A.eq_empty_or_nonempty with hA0 | hA1
  · rw [hA0, Finset.sum_empty] at hAsum; omega
  · obtain ⟨a₀, ha₀⟩ := hA1
    have hle : a₀ ≤ ∑ a ∈ A, a := Finset.single_le_sum (fun i _ => Nat.zero_le i) ha₀
    have hlt : m < a₀ := hlb a₀ (hA ha₀)
    rw [hAsum] at hle
    omega

/-- A positive element of `S`, taken as the singleton `{a}`, is one of its subset
    sums. Hence a set containing a positive `m` cannot avoid `m`. -/
theorem self_mem_subsetSums (S : Finset ℕ) (a : ℕ) (ha : a ∈ S) (hpos : 0 < a) :
    a ∈ subsetSums S := by
  rw [subsetSums, Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨{a}, ?_, ?_⟩, hpos⟩
  · rw [Finset.mem_powerset]; simpa using ha
  · simp

/-- Every avoiding subset of `{1,…,n}` has size at most `n`. -/
theorem maxAvoidingSize_le (n m : ℕ) : maxAvoidingSize n m ≤ n := by
  classical
  unfold maxAvoidingSize
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  have hcard : S.card ≤ (Icc_n n).card := Finset.card_le_card hS.1
  rw [Icc_n, Nat.card_Icc] at hcard
  omega

/-- **Monotonicity in the range `n`.** For a fixed target `m`, enlarging the
    ambient box `{1,…,n}` can only enlarge the family of `m`-avoiding subsets, so
    the maximum avoiding size is non-decreasing in `n`: `maxAvoidingSize n m ≤
    maxAvoidingSize (n+1) m`. Every `m`-avoiding `S ⊆ {1,…,n}` is still an
    `m`-avoiding subset of `{1,…,n+1}` (the `AvoidSum S m` predicate depends only
    on `S` and `m`, not on the box), so the filtered powerset for `n` embeds into
    that for `n+1` and `Finset.sup_mono` transfers the bound. This is the analogue
    for `maxAvoidingSize` of the counting-function monotonicity used elsewhere in
    the gallery, and complements the lower bounds `interval_avoiding_lower` /
    `primeMultiples_avoiding_lower` and the upper bound `maxAvoidingSize_le`. -/
theorem maxAvoidingSize_le_succ (n m : ℕ) :
    maxAvoidingSize n m ≤ maxAvoidingSize (n + 1) m := by
  classical
  unfold maxAvoidingSize
  -- Reduce to nestedness of the two filtered avoiding families; working on the
  -- unfolded goal directly keeps the `filter`'s decidability instances aligned
  -- with the `open Classical`-based definition (a fresh `filter` term would not).
  apply Finset.sup_mono
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  -- `AvoidSum S m` is unchanged; only the box `{1,…,n} ⊆ {1,…,n+1}` grows.
  refine ⟨hS.1.trans ?_, hS.2⟩
  rw [Icc_n, Icc_n]
  exact Finset.Icc_subset_Icc (le_refl 1) (Nat.le_succ n)

/-- **`maxAvoidingSize` is monotone in `n`** (packaged form of
    `maxAvoidingSize_le_succ`). -/
theorem maxAvoidingSize_monotone (m : ℕ) : Monotone (fun n => maxAvoidingSize n m) :=
  monotone_nat_of_le_succ (fun n => maxAvoidingSize_le_succ n m)

/-- For `m > n²` the whole set `{1,…,n}` avoids `m`: every subset sum is at most
    `|A|·n ≤ n·n < m`, so `m` is never realised. -/
theorem avoid_full (n m : ℕ) (h : n * n < m) : AvoidSum (Icc_n n) m := by
  intro hmem
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
  obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
  rw [Finset.mem_powerset] at hA
  have hbound : ∑ a ∈ A, a ≤ A.card * n := by
    have hle := Finset.sum_le_card_nsmul A id n (fun a ha => by
      have haI : a ∈ Icc_n n := hA ha
      rw [Icc_n, Finset.mem_Icc] at haI; simpa using haI.2)
    simpa [smul_eq_mul] using hle
  have hcard : A.card ≤ n := by
    have hc := Finset.card_le_card hA
    rw [Icc_n, Nat.card_Icc] at hc; omega
  have hfin : ∑ a ∈ A, a ≤ n * n :=
    le_trans hbound (Nat.mul_le_mul hcard (le_refl n))
  rw [hAsum] at hfin
  omega

/-- Key bridge: an avoiding subset of size ≥ k exists iff `maxAvoidingSize n m ≥ k`. -/
theorem maxAvoidingSize_ge_iff (n m k : ℕ) :
    (∃ S : Finset ℕ, S ⊆ Icc_n n ∧ S.card ≥ k ∧ AvoidSum S m)
      ↔ k ≤ maxAvoidingSize n m := by
  classical
  constructor
  · rintro ⟨S, hSsub, hScard, hSavoid⟩
    have hmem : S ∈ (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S m) := by
      rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hSsub, hSavoid⟩
    calc k ≤ S.card := hScard
      _ ≤ maxAvoidingSize n m := by unfold maxAvoidingSize; exact Finset.le_sup hmem
  · intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact ⟨∅, Finset.empty_subset _, by rw [hk0]; exact Nat.zero_le _,
        avoid_of_forall_lt ∅ m (fun a ha => absurd ha (Finset.notMem_empty a))⟩
    · unfold maxAvoidingSize at hk
      rw [Finset.le_sup_iff (show (⊥ : ℕ) < k from hkpos)] at hk
      obtain ⟨S, hSmem, hScard⟩ := hk
      rw [Finset.mem_filter, Finset.mem_powerset] at hSmem
      exact ⟨S, hSmem.1, hScard, hSmem.2⟩

/-- f(n) is the largest k satisfying f_property. -/
theorem f_characterization (n : ℕ) (hn : n ≥ 1) :
    f_property n (f n) ∧ ∀ k > f n, ¬f_property n k := by
  classical
  have hn0 : n ≠ 0 := by omega
  have H : (Finset.Icc 1 (n * n)).Nonempty :=
    Finset.nonempty_Icc.mpr (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn0 hn0))
  have hf : f n = (Finset.Icc 1 (n * n)).inf' H (fun m => maxAvoidingSize n m) := by
    unfold f; rw [dif_neg hn0]
  have hfn_le : f n ≤ n := by
    rw [hf]
    calc (Finset.Icc 1 (n * n)).inf' H (fun m => maxAvoidingSize n m)
        ≤ maxAvoidingSize n 1 :=
          Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨le_refl 1, by nlinarith [hn]⟩)
      _ ≤ n := maxAvoidingSize_le n 1
  refine ⟨?_, ?_⟩
  · -- f_property n (f n)
    intro m hm
    rw [maxAvoidingSize_ge_iff]
    rcases le_or_lt m (n * n) with hmle | hmgt
    · rw [hf]; exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hm, hmle⟩)
    · have hfull : n ≤ maxAvoidingSize n m := by
        have hmemfull : Icc_n n ∈
            (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S m) := by
          rw [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.Subset.refl _, avoid_full n m hmgt⟩
        calc n = (Icc_n n).card := by rw [Icc_n, Nat.card_Icc]; omega
          _ ≤ maxAvoidingSize n m := by unfold maxAvoidingSize; exact Finset.le_sup hmemfull
      omega
  · -- maximality
    intro k hk hprop
    obtain ⟨m₀, hm₀mem, hm₀eq⟩ :=
      Finset.exists_mem_eq_inf' H (fun m => maxAvoidingSize n m)
    rw [Finset.mem_Icc] at hm₀mem
    obtain ⟨S, hSsub, hScard, hSavoid⟩ := hprop m₀ hm₀mem.1
    have hle : k ≤ maxAvoidingSize n m₀ :=
      (maxAvoidingSize_ge_iff n m₀ k).mp ⟨S, hSsub, hScard, hSavoid⟩
    have hfm0 : f n = maxAvoidingSize n m₀ := by rw [hf, hm₀eq]
    omega

/-
## Part III: The Erdős-Graham Conjecture
-/

/-- The conjectured asymptotic value: (1/2) · n / log n. -/
noncomputable def expectedValue (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else (1/2) * n / Real.log n

/-- Erdős-Graham Conjecture: f(n) = (1/2 + o(1)) · n / log n. -/
def ErdosGrahamConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |((f n : ℝ) / (n / Real.log n)) - 1/2| < ε

/-- Alternative formulation with explicit bounds. -/
def ErdosGrahamConjecture' : Prop :=
  ∃ g : ℕ → ℝ, (∀ n, g n > 0) ∧
    (Filter.Tendsto g Filter.atTop (nhds 0)) ∧
    ∀ n ≥ 2, (f n : ℝ) = (1/2 + g n) * n / Real.log n

/-
## Part IV: Erdős-Graham Lower Bound
-/

/-- **Erdős-Graham Lower Bound:**
    f(n) ≥ (1/2 + o(1)) · n / log n.
    Proof idea: Take S = multiples of the smallest prime p not dividing m.
    Then S avoids m (since all subset sums are multiples of p).

    This is a deep external result (Erdős–Graham) recorded here as an axiom.
    The elementary construction underneath it is fully verified below
    (`prime_multiples_size`, `prime_multiples_avoid`) and, self-contained, in
    `Erdos771Construction.lean`. -/
axiom erdos_graham_lower_bound :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (f n : ℝ) ≥ (1/2 - ε) * n / Real.log n

/-- The construction: multiples of a prime p in {1,...,n}. -/
def primeMutliples (p n : ℕ) : Finset ℕ :=
  (Icc_n n).filter (fun k => p ∣ k)

/-- Size of prime multiples: ⌊n/p⌋. -/
theorem prime_multiples_size (p n : ℕ) (_hp : p > 0) :
    (primeMutliples p n).card = n / p := by
  have hIcc : Icc_n n = Finset.Ioc 0 n := by
    unfold Icc_n; ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  unfold primeMutliples
  rw [hIcc]
  exact Nat.Ioc_filter_dvd_card_eq_div n p

/-- For prime p not dividing m, multiples of p avoid m.
    Every subset sum of multiples of `p` is divisible by `p`, but `m` is not. -/
theorem prime_multiples_avoid (p m n : ℕ) (_hp : Nat.Prime p) (hpm : ¬p ∣ m) :
    AvoidSum (primeMutliples p n) m := by
  intro hmem
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
  obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
  rw [Finset.mem_powerset] at hA
  have hdvd : p ∣ ∑ a ∈ A, a := by
    refine Finset.dvd_sum (fun a ha => ?_)
    have ha' : a ∈ primeMutliples p n := hA ha
    rw [primeMutliples, Finset.mem_filter] at ha'
    exact ha'.2
  rw [hAsum] at hdvd
  exact hpm hdvd

/-
## Part V: Alon-Freiman Upper Bound
-/

/-- **Alon-Freiman Upper Bound:**
    f(n) ≤ (1/2 + o(1)) · n / log n.
    Proof uses LCM argument. This is a deep external result recorded as an axiom. -/
axiom alon_freiman_upper_bound :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (f n : ℝ) ≤ (1/2 + ε) * n / Real.log n

/-- The LCM of {1, ..., s}. -/
noncomputable def lcm_up_to (s : ℕ) : ℕ :=
  (Icc_n s).lcm id

/-
## Part VI: The Complete Answer
-/

/-- **The Answer: The conjecture is TRUE.**
    f(n) = (1/2 + o(1)) · n / log n.

    Combining the two axiomatic bounds: for `n ≥ 2` the quantity
    `L = n / log n` is positive, and the lower/upper bounds squeeze
    `f n / L` into `[1/2 - ε/2, 1/2 + ε/2]`, so `|f n / L - 1/2| ≤ ε/2 < ε`. -/
theorem erdos_graham_conjecture_true : ErdosGrahamConjecture := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := erdos_graham_lower_bound (ε/2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := alon_freiman_upper_bound (ε/2) (by linarith)
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have h1 : n ≥ N₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have h2 : n ≥ N₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hlow := hN₁ n h1
  have hupp := hN₂ n h2
  have h1n : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogpos : 0 < Real.log n := Real.log_pos h1n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < (n : ℝ) / Real.log n := div_pos hnpos hlogpos
  rw [abs_lt]
  have hUB : (f n : ℝ) / ((n : ℝ) / Real.log n) ≤ 1/2 + ε/2 := by
    rw [div_le_iff₀ hLpos]
    have hrw : (1/2 + ε/2 : ℝ) * ((n : ℝ) / Real.log n)
        = (1/2 + ε/2) * n / Real.log n := by ring
    rw [hrw]; exact hupp
  have hLB : (1/2 - ε/2 : ℝ) ≤ (f n : ℝ) / ((n : ℝ) / Real.log n) := by
    rw [le_div_iff₀ hLpos]
    have hrw : (1/2 - ε/2 : ℝ) * ((n : ℝ) / Real.log n)
        = (1/2 - ε/2) * n / Real.log n := by ring
    rw [hrw]; exact hlow
  constructor <;> linarith

/-- The asymptotic formula. -/
theorem f_asymptotic : ErdosGrahamConjecture := erdos_graham_conjecture_true

/-
## Part VII: Explicit Bounds
-/

/-- For large n, we have explicit bounds. -/
def explicitBounds (n : ℕ) : Prop :=
  n ≥ 10 →
    (0.4 : ℝ) * n / Real.log n ≤ (f n : ℝ) ∧
    (f n : ℝ) ≤ (0.6 : ℝ) * n / Real.log n

/-- The leading constant is exactly 1/2. This is the limit form of
    `erdos_graham_conjecture_true`. -/
theorem leading_constant :
    Filter.Tendsto (fun n => (f n : ℝ) / (n / Real.log n)) Filter.atTop (nhds (1/2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := erdos_graham_conjecture_true ε hε
  exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n hn⟩

/-
## Part VIII: Special Cases
-/

/-- For m = 1, we can't include 1 in S, so the largest 1-avoiding subset of
    `{1,…,n}` is `{2,…,n}`, of size `n − 1`. -/
theorem m_eq_one_case (n : ℕ) (hn : n ≥ 1) :
    maxAvoidingSize n 1 = n - 1 := by
  classical
  unfold maxAvoidingSize
  apply le_antisymm
  · -- every 1-avoiding S omits 1, so |S| ≤ n − 1
    apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSavoid⟩ := hS
    have h1notin : 1 ∉ S := fun h1 => hSavoid (self_mem_subsetSums S 1 h1 one_pos)
    have hsub2 : S ⊆ Finset.Icc 2 n := by
      intro x hx
      have hxI : x ∈ Icc_n n := hSsub hx
      rw [Icc_n, Finset.mem_Icc] at hxI
      rw [Finset.mem_Icc]
      rcases Nat.lt_or_ge x 2 with hlt | hge
      · interval_cases x
        · omega
        · exact absurd hx h1notin
      · exact ⟨hge, hxI.2⟩
    calc S.card ≤ (Finset.Icc 2 n).card := Finset.card_le_card hsub2
      _ = n - 1 := by rw [Nat.card_Icc]; omega
  · -- {2,…,n} is 1-avoiding with size n − 1
    have hmem : Finset.Icc 2 n ∈
        (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S 1) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun x hx => by rw [Finset.mem_Icc] at hx; rw [Icc_n, Finset.mem_Icc]; omega,
        avoid_of_forall_lt _ 1 (fun a ha => by rw [Finset.mem_Icc] at ha; omega)⟩
    calc n - 1 = (Finset.Icc 2 n).card := by rw [Nat.card_Icc]; omega
      _ ≤ _ := Finset.le_sup hmem

/-- For m = 2, the set `{3,…,n}` is 2-avoiding and has size `n − 2`, so the
    largest 2-avoiding subset has size at least `n − 2`. -/
theorem m_eq_two_case (n : ℕ) (hn : n ≥ 2) :
    maxAvoidingSize n 2 ≥ n - 2 := by
  classical
  unfold maxAvoidingSize
  have hmem : Finset.Icc 3 n ∈
      (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S 2) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun x hx => by rw [Finset.mem_Icc] at hx; rw [Icc_n, Finset.mem_Icc]; omega,
      avoid_of_forall_lt _ 2 (fun a ha => by rw [Finset.mem_Icc] at ha; omega)⟩
  calc n - 2 = (Finset.Icc 3 n).card := by rw [Nat.card_Icc]; omega
    _ ≤ _ := Finset.le_sup hmem

/-- **General interval lower bound.** The interval `{m+1,…,n}` avoids `m` (all of
    its elements exceed `m`, so no nonempty subset sum can equal `m`) and has
    `n - m` elements, hence `maxAvoidingSize n m ≥ n - m`. This unifies the `m = 1`
    and `m = 2` special cases (they are the instances `m = 1, 2`). -/
theorem interval_avoiding_lower (n m : ℕ) : maxAvoidingSize n m ≥ n - m := by
  classical
  unfold maxAvoidingSize
  have hmem : Finset.Icc (m + 1) n ∈
      (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S m) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun x hx => by rw [Finset.mem_Icc] at hx; rw [Icc_n, Finset.mem_Icc]; omega,
      avoid_of_forall_lt _ m (fun a ha => by rw [Finset.mem_Icc] at ha; omega)⟩
  calc n - m = (Finset.Icc (m + 1) n).card := by rw [Nat.card_Icc]; omega
    _ ≤ _ := Finset.le_sup hmem

/-- **Prime-multiples lower bound.** For any prime `p ∤ m`, the multiples of `p`
    in `{1,…,n}` form an `m`-avoiding subset of size `⌊n/p⌋` (every subset sum is
    a multiple of `p`, but `m` is not), hence `maxAvoidingSize n m ≥ ⌊n/p⌋`. This
    feeds the verified construction lemmas `prime_multiples_avoid` /
    `prime_multiples_size` directly into a lower bound on the `f`-defining
    function `maxAvoidingSize`. -/
theorem primeMultiples_avoiding_lower (p m n : ℕ) (hp : Nat.Prime p) (hpm : ¬p ∣ m) :
    maxAvoidingSize n m ≥ n / p := by
  classical
  unfold maxAvoidingSize
  have hsub : primeMutliples p n ⊆ Icc_n n := by
    intro x hx; rw [primeMutliples, Finset.mem_filter] at hx; exact hx.1
  have hmem : primeMutliples p n ∈
      (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S m) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, prime_multiples_avoid p m n hp hpm⟩
  calc n / p = (primeMutliples p n).card := (prime_multiples_size p n hp.pos).symm
    _ ≤ _ := Finset.le_sup hmem

/-- **Bertrand-quantitative lower bound.** For every `m ≥ 1` there is a prime
    `m < p ≤ 2m` (Bertrand's postulate); it cannot divide `m` (a divisor of a
    positive `m` is at most `m`), so the prime-multiples bound and Nat-division
    antitonicity give `maxAvoidingSize n m ≥ ⌊n/(2m)⌋`. Unlike the interval bound,
    this stays useful as `m` grows relative to `n`. -/
theorem maxAvoidingSize_ge_div_two_mul (n m : ℕ) (hm : 1 ≤ m) :
    maxAvoidingSize n m ≥ n / (2 * m) := by
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have hpm : ¬p ∣ m := fun hdvd => by
    have := Nat.le_of_dvd (by omega) hdvd; omega
  calc n / (2 * m) ≤ n / p := Nat.div_le_div_left hp2m hp.pos
    _ ≤ maxAvoidingSize n m := primeMultiples_avoiding_lower p m n hp hpm

/-- Small primes give good constructions. -/
def smallPrimeConstruction (m n : ℕ) : Finset ℕ :=
  let p := Nat.minFac (m + 1)  -- A prime not dividing m
  primeMutliples p n

/-
## Part IX: Connection to Sum-Free Sets
-/

/-- A set is sum-free if no two elements sum to a third. -/
def IsSumFree (S : Finset ℕ) : Prop :=
  ∀ a b c, a ∈ S → b ∈ S → c ∈ S → a + b ≠ c

/-- m-avoiding is weaker than sum-free in some sense: m-avoiding sets can be
    larger than sum-free sets (`n/(2 log n)` vs `n/3`). -/
def avoiding_vs_sumfree : Prop :=
  True

/-
## Part X: Summary
-/

/-- **Erdős Problem #771: SOLVED**

Question: Is f(n) = (1/2 + o(1)) · n / log n?

Answer: YES

Where f(n) is the maximum k such that for every m ≥ 1, there exists
S ⊆ {1,...,n} with |S| = k such that no nonempty subset of S sums to m.

- Erdős-Graham: Lower bound using prime multiples
- Alon-Freiman: Upper bound using LCM argument
- The constant 1/2 is exact
-/
theorem erdos_771 : ErdosGrahamConjecture := erdos_graham_conjecture_true

/-- Main result: the asymptotic is (1/2) · n / log n. -/
theorem erdos_771_main :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((f n : ℝ) / (n / Real.log n)) - 1/2| < ε :=
  erdos_771

/-- The problem is completely solved. -/
theorem erdos_771_solved : ErdosGrahamConjecture := erdos_771

end Erdos771
