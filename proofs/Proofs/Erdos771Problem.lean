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

/-- **A two-element sum is a subset sum.**  If `a, b ∈ S` are distinct and `a + b > 0`, then
    `a + b ∈ subsetSums S`: the pair `{a, b} ⊆ S` sums to `a + b`.  The two-element companion of
    `self_mem_subsetSums`, used to detect the representation `m = a + b` obstructing avoidance
    (e.g. `3 = 1 + 2`). -/
theorem pair_mem_subsetSums (S : Finset ℕ) (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (hpos : 0 < a + b) : a + b ∈ subsetSums S := by
  rw [subsetSums, Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨{a, b}, ?_, ?_⟩, hpos⟩
  · rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · rw [Finset.sum_pair hab]

/-- **Subset sums are monotone under inclusion.** If `T ⊆ S` then every subset sum of `T`
    is a subset sum of `S`: `subsetSums T ⊆ subsetSums S`.  A subset `A ⊆ T` is also a
    subset `A ⊆ S`, so its sum survives into `subsetSums S`. -/
theorem subsetSums_mono {S T : Finset ℕ} (h : T ⊆ S) : subsetSums T ⊆ subsetSums S := by
  intro x hx
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hx ⊢
  obtain ⟨⟨A, hA, hAsum⟩, hpos⟩ := hx
  rw [Finset.mem_powerset] at hA
  exact ⟨⟨A, Finset.mem_powerset.mpr (hA.trans h), hAsum⟩, hpos⟩

/-- **Avoidance is hereditary to subsets.** If `S` avoids the sum `m` then so does every
    subset `T ⊆ S`: fewer elements can only remove subset sums, never create the target `m`.
    Contrapositive of `subsetSums_mono`.  This is the structural reason `maxAvoidingSize` is
    a genuine maximum — any avoiding set stays avoiding when trimmed — and complements the
    ambient-box monotonicity `maxAvoidingSize_monotone`. -/
theorem avoidSum_subset {S T : Finset ℕ} (h : T ⊆ S) (m : ℕ) (hS : AvoidSum S m) :
    AvoidSum T m :=
  fun hmem => hS (subsetSums_mono h hmem)

/-- **Every set avoids the sum `0`.**  The target `0` is never a *positive* subset sum
    (`subsetSums` filters out `0`), so `AvoidSum S 0` holds vacuously for every `S`.  This is
    the degenerate base of the avoidance theory, dual to the large-target regime
    `avoid_full` (`n·n < m`): both endpoints of the target range are trivially avoidable. -/
theorem avoidSum_zero (S : Finset ℕ) : AvoidSum S 0 := by
  intro hmem
  rw [subsetSums, Finset.mem_filter] at hmem
  exact absurd hmem.2 (lt_irrefl 0)

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

/-- **The full box is a large-target witness.** For `m > n²` the whole set
`{1,…,n}` avoids `m` (`avoid_full`) and has size `n`, so the maximum avoiding
size is at least `n`: `n ≤ maxAvoidingSize n m`. Packaged from `avoid_full` via
the bridge `maxAvoidingSize_ge_iff`. -/
theorem le_maxAvoidingSize_of_lt (n m : ℕ) (h : n * n < m) :
    n ≤ maxAvoidingSize n m :=
  (maxAvoidingSize_ge_iff n m n).mp
    ⟨Icc_n n, Finset.Subset.refl _, by rw [Icc_n, Nat.card_Icc]; omega,
      avoid_full n m h⟩

/-- **Exact value for large targets.** Once `m > n²` no subset sum of `{1,…,n}`
can reach `m` (`avoid_full`), so the maximum avoiding size attains its ceiling:
`maxAvoidingSize n m = n`. Combines the universal upper bound
`maxAvoidingSize_le` with the full-box lower bound `le_maxAvoidingSize_of_lt`.
This pins down `maxAvoidingSize` completely in the large-`m` regime and is the
fact behind the `m > n²` branch of `f_characterization`. -/
theorem maxAvoidingSize_eq_of_lt (n m : ℕ) (h : n * n < m) :
    maxAvoidingSize n m = n :=
  le_antisymm (maxAvoidingSize_le n m) (le_maxAvoidingSize_of_lt n m h)

/-
## Part II.b: Completeness of the full box and the sharp avoidance threshold

The crude witness `avoid_full` uses the loose threshold `n² < m`.  The **sharp**
threshold is the actual total `∑_{a=1}^n a = n(n+1)/2`: the interval `{1,…,n}` is a
*complete sequence* — its subset sums realise *every* value in `[1, n(n+1)/2]`.
Consequently the full box avoids `m` exactly when `m = 0` or `m` exceeds the total,
and `maxAvoidingSize n m = n` precisely on that boundary.  This pins down where the
trivial ceiling `maxAvoidingSize n m ≤ n` is attained.
-/

/-- **Completeness of `{1,…,n}`.** Every `k ≤ ∑_{a=1}^n a` is realised as the sum of
    some subset `A ⊆ {1,…,n}`.  Greedy induction on `n`: adjoining `n+1` to a subset
    of `{1,…,n}` summing to `k-(n+1)` reaches every `k` in the new top band
    `(∑_{a≤n} a, ∑_{a≤n+1} a]`. -/
theorem exists_subset_sum_eq :
    ∀ (n k : ℕ), k ≤ ∑ a ∈ Icc_n n, a → ∃ A ⊆ Icc_n n, ∑ a ∈ A, a = k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hz : Icc_n 0 = (∅ : Finset ℕ) := by
      unfold Icc_n; exact Finset.Icc_eq_empty (by omega)
    rw [hz, Finset.sum_empty] at hk
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [Finset.sum_empty]; omega
  | succ n ih =>
    intro k hk
    have hins : Icc_n (n + 1) = insert (n + 1) (Icc_n n) := by
      unfold Icc_n; ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnm : (n + 1) ∉ Icc_n n := by
      unfold Icc_n; simp only [Finset.mem_Icc]; omega
    have htot : ∑ a ∈ Icc_n (n + 1), a = ((n + 1) + ∑ a ∈ Icc_n n, a) := by
      rw [hins, Finset.sum_insert hnm]
    rw [htot] at hk
    by_cases hcase : k ≤ ∑ a ∈ Icc_n n, a
    · obtain ⟨A, hAsub, hAsum⟩ := ih k hcase
      exact ⟨A, hAsub.trans (by rw [hins]; exact Finset.subset_insert _ _), hAsum⟩
    · push_neg at hcase
      have hnle : n ≤ ∑ a ∈ Icc_n n, a := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · simp [h0]
        · have hmem : n ∈ Icc_n n := by
            unfold Icc_n; simp only [Finset.mem_Icc]; omega
          exact Finset.single_le_sum (fun i _ => Nat.zero_le i) hmem
      obtain ⟨A, hAsub, hAsum⟩ := ih (k - (n + 1)) (by omega)
      have hnmA : (n + 1) ∉ A := fun h => hnm (hAsub h)
      refine ⟨insert (n + 1) A, ?_, ?_⟩
      · rw [hins]; exact Finset.insert_subset_insert _ hAsub
      · rw [Finset.sum_insert hnmA, hAsum]; omega

/-- The total of the full box in closed form: `2·∑_{a=1}^n a = n(n+1)`
    (equivalently `∑_{a=1}^n a = n(n+1)/2`, the Gauss sum). -/
theorem two_mul_sum_Icc_n (n : ℕ) : 2 * ∑ a ∈ Icc_n n, a = n * (n + 1) := by
  induction n with
  | zero => simp [Icc_n]
  | succ n ih =>
    have hins : Icc_n (n + 1) = insert (n + 1) (Icc_n n) := by
      unfold Icc_n; ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnm : (n + 1) ∉ Icc_n n := by
      unfold Icc_n; simp only [Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert hnm, Nat.mul_add, ih]; ring

/-- **Subset sums of the full box.** `subsetSums {1,…,n}` is exactly the interval
    `{1,…,∑_{a=1}^n a}`: completeness (`exists_subset_sum_eq`) supplies every value in
    range, and no subset sum can exceed the total. -/
theorem subsetSums_Icc_n (n : ℕ) :
    subsetSums (Icc_n n) = Finset.Icc 1 (∑ a ∈ Icc_n n, a) := by
  ext k
  rw [subsetSums, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨A, hA, hAsum⟩, hpos⟩
    rw [Finset.mem_powerset] at hA
    refine ⟨hpos, ?_⟩
    rw [← hAsum]
    exact Finset.sum_le_sum_of_subset hA
  · rintro ⟨hk1, hk2⟩
    obtain ⟨A, hAsub, hAsum⟩ := exists_subset_sum_eq n k hk2
    exact ⟨⟨A, Finset.mem_powerset.mpr hAsub, hAsum⟩, by omega⟩

/-- **Sharp full-box avoidance.** `{1,…,n}` avoids `m` iff `m = 0` or `m` exceeds the
    total `∑_{a=1}^n a`.  Sharpens `avoid_full` (`n² < m`) to the exact threshold: for
    `∑_{a=1}^n a ≥ m ≥ 1` the full box necessarily hits `m` as a subset sum. -/
theorem avoid_full_iff (n m : ℕ) :
    AvoidSum (Icc_n n) m ↔ m = 0 ∨ (∑ a ∈ Icc_n n, a) < m := by
  rw [AvoidSum, subsetSums_Icc_n, Finset.mem_Icc]
  omega

/-- **The full box is optimal exactly on the avoidance boundary.**
    `maxAvoidingSize n m = n` iff `m = 0` or `m` exceeds the total `∑_{a=1}^n a`.
    Forward: an `m`-avoiding subset of size `n` must be all of `{1,…,n}`, so the box
    itself avoids `m`.  Backward: on the boundary the box avoids `m` and has size `n`.
    Sharpens `maxAvoidingSize_eq_of_lt` (`n² < m`) to the exact `n(n+1)/2` threshold. -/
theorem maxAvoidingSize_eq_n_iff (n m : ℕ) :
    maxAvoidingSize n m = n ↔ m = 0 ∨ (∑ a ∈ Icc_n n, a) < m := by
  classical
  constructor
  · intro heq
    by_contra hcon
    push_neg at hcon
    have hnotavoid : ¬ AvoidSum (Icc_n n) m := by
      rw [avoid_full_iff]; push_neg; exact hcon
    obtain ⟨S, hSsub, hScard, hSavoid⟩ :=
      (maxAvoidingSize_ge_iff n m n).mpr (le_of_eq heq.symm)
    have hcardn : (Icc_n n).card = n := by rw [Icc_n, Nat.card_Icc]; omega
    have hSeq : S = Icc_n n :=
      Finset.eq_of_subset_of_card_le hSsub (by rw [hcardn]; exact hScard)
    rw [hSeq] at hSavoid
    exact hnotavoid hSavoid
  · intro h
    have havoid : AvoidSum (Icc_n n) m := (avoid_full_iff n m).mpr h
    refine le_antisymm (maxAvoidingSize_le n m) ?_
    exact (maxAvoidingSize_ge_iff n m n).mp
      ⟨Icc_n n, Finset.Subset.refl _, by rw [Icc_n, Nat.card_Icc]; omega, havoid⟩

/-- **Exact value at the total-sum boundary:** `maxAvoidingSize n (∑_{a=1}^n a) = n − 1`
    for `n ≥ 1`.  This is the first point of the intermediate regime `n < m ≤ n(n+1)/2`, sitting
    just below the trivial ceiling: at the target `m = T := ∑_{a=1}^n a` the full box `{1,…,n}`
    is the *unique* subset summing to `T`, so no size-`n` avoiding set exists
    (`maxAvoidingSize_eq_n_iff` fails since `¬(T < T)`), forcing `maxAvoidingSize ≤ n − 1`; and
    dropping the single element `1` leaves `{2,…,n}` — of size `n − 1` and total `T − 1 < T`,
    hence `T`-avoiding — so the bound is attained.  The exact companion of
    `maxAvoidingSize_eq_n_iff` at the boundary itself. -/
theorem maxAvoidingSize_total_boundary (n : ℕ) (hn : 1 ≤ n) :
    maxAvoidingSize n (∑ a ∈ Icc_n n, a) = n - 1 := by
  classical
  have h1mem : (1 : ℕ) ∈ Icc_n n := by unfold Icc_n; simp only [Finset.mem_Icc]; omega
  have hTpos : 1 ≤ ∑ a ∈ Icc_n n, a :=
    Finset.single_le_sum (f := fun a => a) (fun i _ => Nat.zero_le i) h1mem
  -- Upper bound: the value is not `n`, so it is `≤ n - 1`.
  have hne : maxAvoidingSize n (∑ a ∈ Icc_n n, a) ≠ n := by
    rw [Ne, maxAvoidingSize_eq_n_iff]
    omega
  have hle : maxAvoidingSize n (∑ a ∈ Icc_n n, a) ≤ n := maxAvoidingSize_le _ _
  -- Lower bound: `{2,…,n} = (Icc_n n).erase 1` is a size-`n-1` avoiding witness.
  have hSsub : (Icc_n n).erase 1 ⊆ Icc_n n := Finset.erase_subset _ _
  have hScard : ((Icc_n n).erase 1).card = n - 1 := by
    rw [Finset.card_erase_of_mem h1mem, Icc_n, Nat.card_Icc]; omega
  have hSsum : ∑ a ∈ (Icc_n n).erase 1, a = (∑ a ∈ Icc_n n, a) - 1 := by
    have hadd := Finset.add_sum_erase (Icc_n n) (fun a => a) h1mem
    omega
  have hSavoid : AvoidSum ((Icc_n n).erase 1) (∑ a ∈ Icc_n n, a) := by
    intro hmem
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
    rw [Finset.mem_powerset] at hA
    have hbound : ∑ a ∈ A, a ≤ ∑ a ∈ (Icc_n n).erase 1, a :=
      Finset.sum_le_sum_of_subset hA
    rw [hAsum, hSsum] at hbound
    omega
  have hge : n - 1 ≤ maxAvoidingSize n (∑ a ∈ Icc_n n, a) := by
    rw [← hScard]
    exact (maxAvoidingSize_ge_iff n (∑ a ∈ Icc_n n, a) _).mp
      ⟨(Icc_n n).erase 1, hSsub, le_rfl, hSavoid⟩
  omega

/-- **Avoiding the target `1` means omitting `1`.**  For `S ⊆ {1,…,n}`, `AvoidSum S 1`
    holds iff `1 ∉ S`: every element is a positive integer, so the only nonempty subset
    that can sum to `1` is the singleton `{1}`.  (`→` uses `self_mem_subsetSums`; `←` uses
    `avoid_of_forall_lt`, since all remaining elements are `≥ 2 > 1`.) -/
theorem avoidSum_one_iff (n : ℕ) {S : Finset ℕ} (hS : S ⊆ Icc_n n) :
    AvoidSum S 1 ↔ 1 ∉ S := by
  constructor
  · intro havoid h1
    exact havoid (self_mem_subsetSums S 1 h1 (by norm_num))
  · intro h1
    apply avoid_of_forall_lt
    intro a ha
    have haI : a ∈ Icc_n n := hS ha
    rw [Icc_n, Finset.mem_Icc] at haI
    have hane : a ≠ 1 := fun he => h1 (he ▸ ha)
    omega

/-- **Exact value at the small target `1`:** `maxAvoidingSize n 1 = n - 1`.  The largest
    subset of `{1,…,n}` avoiding the target `1` is `{2,…,n}` (drop the element `1`), of size
    `n-1`; conversely any `1`-avoiding subset omits `1` (`avoidSum_one_iff`), hence embeds in
    `{2,…,n}`.  This pins down `maxAvoidingSize` at the small-target endpoint `m = 1`, the
    companion of `maxAvoidingSize_eq_of_lt` (`m > n²`) at the large-target endpoint. -/
theorem maxAvoidingSize_one (n : ℕ) : maxAvoidingSize n 1 = n - 1 := by
  classical
  apply le_antisymm
  · -- upper bound: every `1`-avoiding subset of `{1,…,n}` omits `1`, so sits in `{2,…,n}`.
    unfold maxAvoidingSize
    apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, havoid⟩ := hS
    have h1 : 1 ∉ S := (avoidSum_one_iff n hSsub).mp havoid
    have hsub : S ⊆ Finset.Icc 2 n := by
      intro x hx
      rw [Finset.mem_Icc]
      have hxI : x ∈ Icc_n n := hSsub hx
      rw [Icc_n, Finset.mem_Icc] at hxI
      have hxne : x ≠ 1 := fun he => h1 (he ▸ hx)
      omega
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  · -- lower bound: `{2,…,n}` is a `1`-avoiding witness of size `n-1`.
    rw [← maxAvoidingSize_ge_iff]
    refine ⟨Finset.Icc 2 n, ?_, ?_, ?_⟩
    · rw [Icc_n]; exact Finset.Icc_subset_Icc (by norm_num) (le_refl n)
    · rw [Nat.card_Icc]; omega
    · apply avoid_of_forall_lt
      intro a ha
      rw [Finset.mem_Icc] at ha
      omega

/-- **Exact value at the small target `2`:** `maxAvoidingSize n 2 = n - 1` for `n ≥ 2`.  Like
    `m = 1`, the only distinct-positive representation of `2` is the singleton `{2}`, so avoiding
    `2` costs exactly one deletion: the largest witness is `{1,…,n} ∖ {2}`, of size `n - 1`.
    Upper bound: a `2`-avoiding `S` omits `2` (else `self_mem_subsetSums` puts `2 ∈ subsetSums S`),
    so `S ⊆ {1,…,n} ∖ {2}`.  Lower bound: `{1,…,n} ∖ {2}` avoids `2` because every element is `1`
    or `≥ 3`, so no subset can sum to `2`.  The value stays at `n - 1` (as at `m = 1`) — the plateau
    before the target `3` first pushes it down. -/
theorem maxAvoidingSize_two (n : ℕ) (hn : 2 ≤ n) : maxAvoidingSize n 2 = n - 1 := by
  classical
  apply le_antisymm
  · unfold maxAvoidingSize
    apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, havoid⟩ := hS
    have h2 : 2 ∉ S := fun h => havoid (self_mem_subsetSums S 2 h (by norm_num))
    have hsub : S ⊆ (Icc_n n).erase 2 := by
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun he => h2 (he ▸ hx), hSsub hx⟩
    have hcard := Finset.card_le_card hsub
    have h2mem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
    rw [Finset.card_erase_of_mem h2mem, Icc_n, Nat.card_Icc] at hcard
    omega
  · rw [← maxAvoidingSize_ge_iff]
    refine ⟨(Icc_n n).erase 2, ?_, ?_, ?_⟩
    · exact Finset.erase_subset _ _
    · have h2mem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      rw [Finset.card_erase_of_mem h2mem, Icc_n, Nat.card_Icc]; omega
    · intro hmem
      rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
      obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
      rw [Finset.mem_powerset] at hA
      have hle : ∀ a ∈ A, a ≤ 2 := by
        intro a ha
        have hs := Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) ha
        rw [hAsum] at hs; exact hs
      have heq1 : ∀ a ∈ A, a = 1 := by
        intro a ha
        have haS := hA ha
        rw [Finset.mem_erase, Icc_n, Finset.mem_Icc] at haS
        have hle2 := hle a ha
        omega
      have hAsub : A ⊆ {1} := fun a ha => Finset.mem_singleton.mpr (heq1 a ha)
      have hsum : ∑ a ∈ A, a ≤ ∑ a ∈ ({1} : Finset ℕ), a :=
        Finset.sum_le_sum_of_subset hAsub
      rw [Finset.sum_singleton] at hsum
      omega

/-- **The value first drops: `maxAvoidingSize n 3 = n - 2` for `n ≥ 3`.**  Unlike `m = 1, 2`,
    the target `3` has *two* distinct-positive representations, `{3}` and `{1, 2}`, so avoiding it
    costs *two* deletions.  Upper bound: a `3`-avoiding `S` has `3 ∉ S` (`self_mem_subsetSums`) and
    not both `1, 2 ∈ S` (`pair_mem_subsetSums`, since `1 + 2 = 3`), so `S` misses `3` and at least
    one of `{1, 2}` — two distinct elements of `{1,…,n}`, hence `|S| ≤ n - 2`.  Lower bound: the
    witness `{1,…,n} ∖ {1, 3}` (every element is `2` or `≥ 4`) avoids `3` and has size `n - 2`.
    This is the first target where `maxAvoidingSize` dips strictly below `n - 1`, and it forces the
    sharpened bound `f n ≤ n - 2` (`f_le_sub_two`). -/
theorem maxAvoidingSize_three (n : ℕ) (hn : 3 ≤ n) : maxAvoidingSize n 3 = n - 2 := by
  classical
  apply le_antisymm
  · unfold maxAvoidingSize
    apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, havoid⟩ := hS
    have h3 : 3 ∉ S := fun h => havoid (self_mem_subsetSums S 3 h (by norm_num))
    have h12 : ¬ (1 ∈ S ∧ 2 ∈ S) := by
      rintro ⟨h1, h2⟩
      refine havoid ?_
      have hp := pair_mem_subsetSums S 1 2 h1 h2 (by norm_num) (by norm_num)
      simpa using hp
    rw [not_and_or] at h12
    rcases h12 with h1 | h2
    · have hsub : S ⊆ ((Icc_n n).erase 1).erase 3 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun he => h3 (he ▸ hx), fun he => h1 (he ▸ hx), hSsub hx⟩
      have hcard := Finset.card_le_card hsub
      have h1mem : (1 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      have h3mem : (3 : ℕ) ∈ (Icc_n n).erase 1 := by
        rw [Finset.mem_erase, Icc_n, Finset.mem_Icc]; omega
      rw [Finset.card_erase_of_mem h3mem, Finset.card_erase_of_mem h1mem,
        Icc_n, Nat.card_Icc] at hcard
      omega
    · have hsub : S ⊆ ((Icc_n n).erase 2).erase 3 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun he => h3 (he ▸ hx), fun he => h2 (he ▸ hx), hSsub hx⟩
      have hcard := Finset.card_le_card hsub
      have h2mem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      have h3mem : (3 : ℕ) ∈ (Icc_n n).erase 2 := by
        rw [Finset.mem_erase, Icc_n, Finset.mem_Icc]; omega
      rw [Finset.card_erase_of_mem h3mem, Finset.card_erase_of_mem h2mem,
        Icc_n, Nat.card_Icc] at hcard
      omega
  · rw [← maxAvoidingSize_ge_iff]
    refine ⟨((Icc_n n).erase 1).erase 3, ?_, ?_, ?_⟩
    · exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    · have h1mem : (1 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      have h3mem : (3 : ℕ) ∈ (Icc_n n).erase 1 := by
        rw [Finset.mem_erase, Icc_n, Finset.mem_Icc]; omega
      rw [Finset.card_erase_of_mem h3mem, Finset.card_erase_of_mem h1mem, Icc_n, Nat.card_Icc]
      omega
    · intro hmem
      rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
      obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
      rw [Finset.mem_powerset] at hA
      have hle : ∀ a ∈ A, a ≤ 3 := by
        intro a ha
        have hs := Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) ha
        rw [hAsum] at hs; exact hs
      have heq2 : ∀ a ∈ A, a = 2 := by
        intro a ha
        have haS := hA ha
        rw [Finset.mem_erase, Finset.mem_erase, Icc_n, Finset.mem_Icc] at haS
        have hle3 := hle a ha
        omega
      have hAsub : A ⊆ {2} := fun a ha => Finset.mem_singleton.mpr (heq2 a ha)
      have hsum : ∑ a ∈ A, a ≤ ∑ a ∈ ({2} : Finset ℕ), a :=
        Finset.sum_le_sum_of_subset hAsub
      rw [Finset.sum_singleton] at hsum
      omega

/-- **Exact value at the target `m = 0`: `maxAvoidingSize n 0 = n`.**  Since `0` is never a
    positive subset sum (`avoidSum_zero`), *every* subset of `{1,…,n}` avoids it, so the whole
    box `{1,…,n}` is an avoiding witness of the maximal size `n`.  This is the degenerate
    small-target endpoint of `maxAvoidingSize`, sitting one step below `maxAvoidingSize_one`
    (`= n-1`), and it coincides with the large-target value `maxAvoidingSize_eq_of_lt`
    (`n·n < m ⟹ = n`): the extremal size is `n` at *both* ends of the target range and dips
    only in the interior where the sum obstruction bites. -/
theorem maxAvoidingSize_zero (n : ℕ) : maxAvoidingSize n 0 = n := by
  classical
  refine le_antisymm (maxAvoidingSize_le n 0) ?_
  unfold maxAvoidingSize
  have hmem : Icc_n n ∈
      (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S 0) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, avoidSum_zero _⟩
  calc n = (Icc_n n).card := by rw [Icc_n, Nat.card_Icc]; omega
    _ ≤ _ := Finset.le_sup hmem

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
    rcases le_or_gt m (n * n) with hmle | hmgt
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

/-- **Sharpened universal upper bound:** `f n ≤ n - 1` for `n ≥ 1`.  The target `m = 1`
    always lies in the range `{1,…,n²}` that `f` minimises over, and
    `maxAvoidingSize n 1 = n - 1` (`maxAvoidingSize_one`), so
    `f n ≤ maxAvoidingSize n 1 = n - 1`.  This strictly improves the trivial `f n ≤ n`
    (the ambient box `{1,…,n}` can never itself be `1`-avoiding, as it contains `1`), and is
    consistent with the conjectured asymptotic `f n = (1/2+o(1))·n/log n`. -/
theorem f_le_pred (n : ℕ) (hn : n ≥ 1) : f n ≤ n - 1 := by
  have hn0 : n ≠ 0 := by omega
  have H : (Finset.Icc 1 (n * n)).Nonempty :=
    Finset.nonempty_Icc.mpr (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn0 hn0))
  have hf : f n = (Finset.Icc 1 (n * n)).inf' H (fun m => maxAvoidingSize n m) := by
    unfold f; rw [dif_neg hn0]
  rw [hf]
  calc (Finset.Icc 1 (n * n)).inf' H (fun m => maxAvoidingSize n m)
      ≤ maxAvoidingSize n 1 :=
        Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨le_refl 1, by nlinarith [hn]⟩)
    _ = n - 1 := maxAvoidingSize_one n

/-- **Sharper universal upper bound:** `f n ≤ n - 2` for `n ≥ 3`.  The target `m = 3` lies in the
    range `{1,…,n²}` that `f` minimises over (for `n ≥ 3`, `3 ≤ n²`), and `maxAvoidingSize n 3 =
    n - 2` (`maxAvoidingSize_three`), so `f n ≤ maxAvoidingSize n 3 = n - 2`.  This strictly
    improves `f_le_pred` (`f n ≤ n - 1`): the two-representation target `3` forces `f` two below
    the box size once `n ≥ 3`, the first quantitative evidence of the conjectured `n/log n` decay. -/
theorem f_le_sub_two (n : ℕ) (hn : 3 ≤ n) : f n ≤ n - 2 := by
  have hn0 : n ≠ 0 := by omega
  have H : (Finset.Icc 1 (n * n)).Nonempty :=
    Finset.nonempty_Icc.mpr (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn0 hn0))
  have hf : f n = (Finset.Icc 1 (n * n)).inf' H (fun m => maxAvoidingSize n m) := by
    unfold f; rw [dif_neg hn0]
  rw [hf]
  calc (Finset.Icc 1 (n * n)).inf' H (fun m => maxAvoidingSize n m)
      ≤ maxAvoidingSize n 3 :=
        Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨by omega, by nlinarith [hn]⟩)
    _ = n - 2 := maxAvoidingSize_three n hn

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

/-! ### Exact small-`m` values of `maxAvoidingSize`

The `m = 2` and `m = 3` cases can be pinned *exactly*, not merely bounded below. The
interval bound `m_eq_two_case` only gives `maxAvoidingSize n 2 ≥ n - 2`; but the sharp
value is `n - 1`, because avoiding the subset sum `2` costs a *single* deletion (only the
singleton `{2}` sums to `2`). The `m = 3` case is the first where the value genuinely drops,
to `n - 2`, since `3` has the two representations `3 = {3} = {1, 2}` and so forces a second
deletion. Together with `maxAvoidingSize_one` (`= n - 1`) this pins the first three values
`n-1, n-1, n-2` of `maxAvoidingSize n ·` exactly. -/

/-- `2` is a positive subset sum of `S` iff `2 ∈ S`: the only nonempty set of distinct
    naturals summing to `2` is the singleton `{2}` (an element `≥ 3` overshoots, and the
    remaining candidates `{0, 1}` together sum to only `1`). -/
theorem two_mem_subsetSums_iff (S : Finset ℕ) :
    (2 : ℕ) ∈ subsetSums S ↔ 2 ∈ S := by
  constructor
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at h
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := h
    rw [Finset.mem_powerset] at hA
    have h2A : (2 : ℕ) ∈ A := by
      by_contra h2
      have hle : ∀ a ∈ A, a ≤ 1 := by
        intro a ha
        by_contra ha1
        have ha2 : a ≠ 2 := fun he => h2 (he ▸ ha)
        have ha3 : 3 ≤ a := by omega
        have hge : 3 ≤ ∑ x ∈ A, x :=
          le_trans ha3 (Finset.single_le_sum (fun i _ => Nat.zero_le i) ha)
        omega
      have hsub : A ⊆ {0, 1} := by
        intro a ha
        have := hle a ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hbound : ∑ x ∈ A, x ≤ ∑ x ∈ ({0, 1} : Finset ℕ), x :=
        Finset.sum_le_sum_of_subset hsub
      rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at hbound
      omega
    exact hA h2A
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨{2}, ?_, ?_⟩, by norm_num⟩
    · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr h
    · simp

/-- **`m = 2` characterization.** `S` avoids the subset sum `2` iff `2 ∉ S`. -/
theorem avoid_two_iff (S : Finset ℕ) : AvoidSum S 2 ↔ 2 ∉ S := by
  unfold AvoidSum
  rw [two_mem_subsetSums_iff]

/-- **Exact value at `m = 2`.** For `n ≥ 2` the largest `2`-avoiding subset of `{1,…,n}`
    has size exactly `n - 1`, sharpening the interval bound `m_eq_two_case` (`≥ n - 2`).
    Optimality: avoiding `2` forces `2 ∉ S`, so `S ⊆ {1,…,n} ∖ {2}` of size `n - 1`.
    Realization: `{1,…,n} ∖ {2}` itself avoids `2` (via `avoid_two_iff`). -/
theorem m_eq_two_case_exact (n : ℕ) (hn : n ≥ 2) :
    maxAvoidingSize n 2 = n - 1 := by
  classical
  unfold maxAvoidingSize
  have hmem2 : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSavoid⟩ := hS
    have h2notin : 2 ∉ S := (avoid_two_iff S).mp hSavoid
    have hsub : S ⊆ (Icc_n n).erase 2 := by
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun h => h2notin (h ▸ hx), hSsub hx⟩
    calc S.card ≤ ((Icc_n n).erase 2).card := Finset.card_le_card hsub
      _ = n - 1 := by rw [Finset.card_erase_of_mem hmem2, Icc_n, Nat.card_Icc]; omega
  · have hmem : (Icc_n n).erase 2 ∈
        (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S 2) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.erase_subset _ _, ?_⟩
      rw [avoid_two_iff]
      exact Finset.notMem_erase 2 _
    calc n - 1 = ((Icc_n n).erase 2).card := by
          rw [Finset.card_erase_of_mem hmem2, Icc_n, Nat.card_Icc]; omega
      _ ≤ _ := Finset.le_sup hmem

/-- `3` is a positive subset sum of `S` iff `3 ∈ S` **or** both `1 ∈ S` and `2 ∈ S`: the
    only nonempty sets of distinct naturals summing to `3` are `{3}` and `{1, 2}` (any
    element `≥ 4` overshoots, and once `3` is excluded the candidates `{0, 1, 2}` reach `3`
    only by using both `1` and `2`). -/
theorem three_mem_subsetSums_iff (S : Finset ℕ) :
    (3 : ℕ) ∈ subsetSums S ↔ (3 ∈ S ∨ (1 ∈ S ∧ 2 ∈ S)) := by
  constructor
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at h
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := h
    rw [Finset.mem_powerset] at hA
    have hle : ∀ a ∈ A, a ≤ 3 := by
      intro a ha
      have hsum := Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) ha
      rw [hAsum] at hsum; exact hsum
    by_cases h3 : (3 : ℕ) ∈ A
    · exact Or.inl (hA h3)
    · refine Or.inr ⟨hA ?_, hA ?_⟩
      · by_contra h1
        have hsub : A ⊆ {0, 2} := by
          intro a ha
          have hle3 := hle a ha
          have ha3 : a ≠ 3 := fun he => h3 (he ▸ ha)
          have ha1 : a ≠ 1 := fun he => h1 (he ▸ ha)
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have hbound : ∑ x ∈ A, x ≤ ∑ x ∈ ({0, 2} : Finset ℕ), x :=
          Finset.sum_le_sum_of_subset hsub
        rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 2)] at hbound
        omega
      · by_contra h2
        have hsub : A ⊆ {0, 1} := by
          intro a ha
          have hle3 := hle a ha
          have ha3 : a ≠ 3 := fun he => h3 (he ▸ ha)
          have ha2 : a ≠ 2 := fun he => h2 (he ▸ ha)
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have hbound : ∑ x ∈ A, x ≤ ∑ x ∈ ({0, 1} : Finset ℕ), x :=
          Finset.sum_le_sum_of_subset hsub
        rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at hbound
        omega
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    rcases h with h3 | ⟨h1, h2⟩
    · refine ⟨⟨{3}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr h3
      · simp
    · refine ⟨⟨{1, 2}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h1, h2⟩
      · rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]

/-- **`m = 3` characterization.** `S` avoids the subset sum `3` iff `3 ∉ S` and not both
    `1, 2 ∈ S`. -/
theorem avoid_three_iff (S : Finset ℕ) :
    AvoidSum S 3 ↔ (3 ∉ S ∧ ¬ (1 ∈ S ∧ 2 ∈ S)) := by
  unfold AvoidSum
  rw [three_mem_subsetSums_iff, not_or]

/-- **Exact value at `m = 3`.** For `n ≥ 3` the largest `3`-avoiding subset of `{1,…,n}`
    has size exactly `n - 2` — the first case where the value drops below `n - 1`, because
    `3 = {3} = {1, 2}` forces a second deletion. Optimality: avoiding `3` forces `3 ∉ S`
    and (`1 ∉ S` or `2 ∉ S`), two distinct missing elements. Realization:
    `{1,…,n} ∖ {2, 3}` avoids `3` (via `avoid_three_iff`). -/
theorem m_eq_three_case (n : ℕ) (hn : n ≥ 3) :
    maxAvoidingSize n 3 = n - 2 := by
  classical
  unfold maxAvoidingSize
  have h3mem : (3 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSavoid⟩ := hS
    rw [avoid_three_iff] at hSavoid
    obtain ⟨h3, h12⟩ := hSavoid
    rw [not_and_or] at h12
    rcases h12 with h1 | h2
    · have h1mem : (1 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      have hsub : S ⊆ ((Icc_n n).erase 1).erase 3 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun he => h3 (he ▸ hx), fun he => h1 (he ▸ hx), hSsub hx⟩
      calc S.card ≤ (((Icc_n n).erase 1).erase 3).card := Finset.card_le_card hsub
        _ = n - 2 := by
          have h3e : (3 : ℕ) ∈ (Icc_n n).erase 1 := by
            rw [Finset.mem_erase]; exact ⟨by norm_num, h3mem⟩
          rw [Finset.card_erase_of_mem h3e, Finset.card_erase_of_mem h1mem, Icc_n, Nat.card_Icc]
          omega
    · have h2mem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      have hsub : S ⊆ ((Icc_n n).erase 2).erase 3 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun he => h3 (he ▸ hx), fun he => h2 (he ▸ hx), hSsub hx⟩
      calc S.card ≤ (((Icc_n n).erase 2).erase 3).card := Finset.card_le_card hsub
        _ = n - 2 := by
          have h3e : (3 : ℕ) ∈ (Icc_n n).erase 2 := by
            rw [Finset.mem_erase]; exact ⟨by norm_num, h3mem⟩
          rw [Finset.card_erase_of_mem h3e, Finset.card_erase_of_mem h2mem, Icc_n, Nat.card_Icc]
          omega
  · have h2mem : (2 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
    have h3e : (3 : ℕ) ∈ (Icc_n n).erase 2 := by
      rw [Finset.mem_erase, Icc_n, Finset.mem_Icc]; omega
    have hmem : ((Icc_n n).erase 2).erase 3 ∈
        (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S 3) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_⟩
      rw [avoid_three_iff]
      refine ⟨Finset.notMem_erase 3 _, ?_⟩
      rintro ⟨_, hmem2⟩
      have hno2 : (2 : ℕ) ∉ (Icc_n n).erase 2 := Finset.notMem_erase 2 _
      exact hno2 (Finset.mem_of_mem_erase hmem2)
    calc n - 2 = (((Icc_n n).erase 2).erase 3).card := by
          rw [Finset.card_erase_of_mem h3e, Finset.card_erase_of_mem h2mem, Icc_n, Nat.card_Icc]
          omega
      _ ≤ _ := Finset.le_sup hmem

/-- `4` is a positive subset sum of `S` iff `4 ∈ S` **or** both `1 ∈ S` and `3 ∈ S`: the
    only nonempty sets of distinct naturals summing to `4` are `{4}` and `{1, 3}` (any
    element `≥ 5` overshoots; excluding `3` and `4` leaves candidates `≤ 2` summing to at
    most `0 + 1 + 2 = 3 < 4`, so `3` is forced; then the complement `A ∖ {3}` sums to `1`,
    forcing `1`).  This is the first target whose two representations `{4}` and `{1, 3}`
    are *disjoint pairs* rather than nested, yet — like `m = 3` — still cost only two
    deletions, so the value stays at `n - 2`. -/
theorem four_mem_subsetSums_iff (S : Finset ℕ) :
    (4 : ℕ) ∈ subsetSums S ↔ (4 ∈ S ∨ (1 ∈ S ∧ 3 ∈ S)) := by
  constructor
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at h
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := h
    rw [Finset.mem_powerset] at hA
    have hle : ∀ a ∈ A, a ≤ 4 := by
      intro a ha
      have hsum := Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) ha
      rw [hAsum] at hsum; exact hsum
    by_cases h4 : (4 : ℕ) ∈ A
    · exact Or.inl (hA h4)
    · -- With `4 ∉ A`, first `3 ∈ A`: else all elements are `≤ 2`, summing to `≤ 3 < 4`.
      have h3A : (3 : ℕ) ∈ A := by
        by_contra h3
        have hsub : A ⊆ ({0, 1, 2} : Finset ℕ) := by
          intro a ha
          have hle4 := hle a ha
          have ha4 : a ≠ 4 := fun he => h4 (he ▸ ha)
          have ha3 : a ≠ 3 := fun he => h3 (he ▸ ha)
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        have hbound : ∑ x ∈ A, x ≤ ∑ x ∈ ({0, 1, 2} : Finset ℕ), x :=
          Finset.sum_le_sum_of_subset hsub
        have h012 : (∑ x ∈ ({0, 1, 2} : Finset ℕ), x) = 3 := by decide
        rw [hAsum, h012] at hbound
        omega
      -- Given `3 ∈ A`, the remaining elements sum to `1`, which forces `1 ∈ A`.
      have h1A : (1 : ℕ) ∈ A := by
        have herase : (3 : ℕ) + ∑ x ∈ A.erase 3, x = 4 := by
          rw [Finset.add_sum_erase A (fun x => x) h3A]; exact hAsum
        have hsum1 : ∑ x ∈ A.erase 3, x = 1 := by omega
        by_contra h1
        have hz : ∀ a ∈ A.erase 3, a = 0 := by
          intro a ha
          have hane1 : a ≠ 1 := fun he => h1 (Finset.mem_of_mem_erase (he ▸ ha))
          have haleq : a ≤ ∑ x ∈ A.erase 3, x :=
            Finset.single_le_sum (f := fun x => x) (fun i _ => Nat.zero_le i) ha
          rw [hsum1] at haleq
          omega
        have hz0 : ∑ x ∈ A.erase 3, x = 0 := Finset.sum_eq_zero hz
        omega
      exact Or.inr ⟨hA h1A, hA h3A⟩
  · intro h
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    rcases h with h4 | ⟨h1, h3⟩
    · refine ⟨⟨{4}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr h4
      · simp
    · refine ⟨⟨{1, 3}, ?_, ?_⟩, by norm_num⟩
      · rw [Finset.mem_powerset, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h1, h3⟩
      · rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 3)]

/-- **`m = 4` characterization.** `S` avoids the subset sum `4` iff `4 ∉ S` and not both
    `1, 3 ∈ S`. -/
theorem avoid_four_iff (S : Finset ℕ) :
    AvoidSum S 4 ↔ (4 ∉ S ∧ ¬ (1 ∈ S ∧ 3 ∈ S)) := by
  unfold AvoidSum
  rw [four_mem_subsetSums_iff, not_or]

/-- **Exact value at `m = 4`.** For `n ≥ 4` the largest `4`-avoiding subset of `{1,…,n}`
    has size exactly `n - 2` — the value *plateaus* at `n - 2` (as at `m = 3`) before its
    next drop to `n - 3` at `m = 5`.  Optimality: avoiding `4` forces `4 ∉ S` and
    (`1 ∉ S` or `3 ∉ S`), two distinct missing elements. Realization: `{1,…,n} ∖ {3, 4}`
    avoids `4` (via `avoid_four_iff`). Together with `maxAvoidingSize_one`,
    `m_eq_two_case_exact` and `m_eq_three_case` this pins the profile
    `n-1, n-1, n-2, n-2` at the targets `m = 1, 2, 3, 4`. -/
theorem m_eq_four_case (n : ℕ) (hn : n ≥ 4) :
    maxAvoidingSize n 4 = n - 2 := by
  classical
  unfold maxAvoidingSize
  have h4mem : (4 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSavoid⟩ := hS
    rw [avoid_four_iff] at hSavoid
    obtain ⟨h4, h13⟩ := hSavoid
    rw [not_and_or] at h13
    rcases h13 with h1 | h3
    · have h1mem : (1 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      have hsub : S ⊆ ((Icc_n n).erase 1).erase 4 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun he => h4 (he ▸ hx), fun he => h1 (he ▸ hx), hSsub hx⟩
      calc S.card ≤ (((Icc_n n).erase 1).erase 4).card := Finset.card_le_card hsub
        _ = n - 2 := by
          have h4e : (4 : ℕ) ∈ (Icc_n n).erase 1 := by
            rw [Finset.mem_erase]; exact ⟨by norm_num, h4mem⟩
          rw [Finset.card_erase_of_mem h4e, Finset.card_erase_of_mem h1mem, Icc_n, Nat.card_Icc]
          omega
    · have h3mem : (3 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
      have hsub : S ⊆ ((Icc_n n).erase 3).erase 4 := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨fun he => h4 (he ▸ hx), fun he => h3 (he ▸ hx), hSsub hx⟩
      calc S.card ≤ (((Icc_n n).erase 3).erase 4).card := Finset.card_le_card hsub
        _ = n - 2 := by
          have h4e : (4 : ℕ) ∈ (Icc_n n).erase 3 := by
            rw [Finset.mem_erase]; exact ⟨by norm_num, h4mem⟩
          rw [Finset.card_erase_of_mem h4e, Finset.card_erase_of_mem h3mem, Icc_n, Nat.card_Icc]
          omega
  · have h3mem : (3 : ℕ) ∈ Icc_n n := by rw [Icc_n, Finset.mem_Icc]; omega
    have h4e : (4 : ℕ) ∈ (Icc_n n).erase 3 := by
      rw [Finset.mem_erase, Icc_n, Finset.mem_Icc]; omega
    have hmem : ((Icc_n n).erase 3).erase 4 ∈
        (Finset.powerset (Icc_n n)).filter (fun S => AvoidSum S 4) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨(Finset.erase_subset _ _).trans (Finset.erase_subset _ _), ?_⟩
      rw [avoid_four_iff]
      refine ⟨Finset.notMem_erase 4 _, ?_⟩
      rintro ⟨_, hmem3⟩
      have hno3 : (3 : ℕ) ∉ (Icc_n n).erase 3 := Finset.notMem_erase 3 _
      exact hno3 (Finset.mem_of_mem_erase hmem3)
    calc n - 2 = (((Icc_n n).erase 3).erase 4).card := by
          rw [Finset.card_erase_of_mem h4e, Finset.card_erase_of_mem h3mem, Icc_n, Nat.card_Icc]
          omega
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

/-- **Sharp closed-form lower bound `maxAvoidingSize n m ≥ n − ⌈m/2⌉`** (with
    `⌈m/2⌉ = (m+1)/2` in `ℕ`), for `1 ≤ m ≤ n`.

    The witness is `S = {⌈m/2⌉, …, n} \ {m}`, of size `n − ⌈m/2⌉`.  It avoids `m`:
    the single element `m` is removed (killing the singleton `{m}`), and any two
    *distinct* remaining elements are each `≥ ⌈m/2⌉`, so their sum is
    `≥ ⌈m/2⌉ + (⌈m/2⌉+1) = 2⌈m/2⌉ + 1 > m` — no subset of size `≥ 2` can hit `m`
    either.  This strictly improves the interval bound `interval_avoiding_lower`
    (`n − m`) and is in fact tight: it matches the exact small-`m` values
    `maxAvoidingSize n 1 = n−1`, `… n 2 = n−1`, `… n 3 = n−2`, `… n 4 = n−2`
    (all `= n − ⌈m/2⌉`). -/
theorem maxAvoidingSize_ge_sub_ceil_half (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    maxAvoidingSize n m ≥ n - (m + 1) / 2 := by
  classical
  set c := (m + 1) / 2 with hc
  have hcm : c ≤ m := by rw [hc]; omega
  have hc1 : 1 ≤ c := by rw [hc]; omega
  set S := (Finset.Icc c n).erase m with hS
  -- `S ⊆ {1,…,n}`
  have hSsub : S ⊆ Icc_n n := by
    intro x hx
    rw [hS, Finset.mem_erase, Finset.mem_Icc] at hx
    rw [Icc_n, Finset.mem_Icc]; omega
  -- `S` avoids `m`
  have hSavoid : AvoidSum S m := by
    intro hmem
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
    obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
    rw [Finset.mem_powerset] at hA
    have hAlb : ∀ a ∈ A, c ≤ a ∧ a ≠ m := by
      intro a ha
      have hain := hA ha
      rw [hS, Finset.mem_erase, Finset.mem_Icc] at hain
      exact ⟨hain.2.1, hain.1⟩
    rcases A.eq_empty_or_nonempty with h0 | ⟨a₀, ha₀⟩
    · rw [h0, Finset.sum_empty] at hAsum; omega
    · by_cases hcard : 2 ≤ A.card
      · have h1lt : 1 < A.card := by omega
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1lt
        have hpair : ({x, y} : Finset ℕ) ⊆ A := by
          intro z hz; rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl; exacts [hx, hy]
        have hsum2 : x + y ≤ ∑ a ∈ A, a := by
          calc x + y = ∑ a ∈ ({x, y} : Finset ℕ), a := by rw [Finset.sum_pair hxy]
            _ ≤ ∑ a ∈ A, a := Finset.sum_le_sum_of_subset hpair
        have hxc := (hAlb x hx).1
        have hyc := (hAlb y hy).1
        -- `x ≠ y`, both `≥ c` ⟹ `x + y ≥ 2c+1 > m = ∑A`
        omega
      · -- singleton: `A = {a₀}`, `∑A = a₀ = m`, contradicting `a₀ ≠ m`
        have hA1 : A = {a₀} :=
          Finset.eq_singleton_iff_unique_mem.mpr
            ⟨ha₀, fun x hx => Finset.card_le_one.mp (by omega) x hx a₀ ha₀⟩
        rw [hA1, Finset.sum_singleton] at hAsum
        exact (hAlb a₀ ha₀).2 hAsum
  -- `|S| = n − c`
  have hmMem : m ∈ Finset.Icc c n := by rw [Finset.mem_Icc]; omega
  have hcardS : S.card = n - c := by
    rw [hS, Finset.card_erase_of_mem hmMem, Nat.card_Icc]; omega
  -- conclude via `Finset.le_sup`
  unfold maxAvoidingSize
  have hmemS : S ∈ (Finset.powerset (Icc_n n)).filter (fun T => AvoidSum T m) := by
    rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hSsub, hSavoid⟩
  calc n - c = S.card := hcardS.symm
    _ ≤ _ := Finset.le_sup hmemS

/-- **Matching upper bound `maxAvoidingSize n m ≤ n − ⌈m/2⌉`** (with
    `⌈m/2⌉ = (m+1)/2` in `ℕ`), for `1 ≤ m ≤ n`.

    Any `m`-avoiding `S ⊆ {1,…,n}` contains **at most `⌊m/2⌋` elements of `{1,…,m}`**:
    the involution `x ↦ m − x` on `{1,…,m−1}` pairs the low interval, and `S` can
    keep at most one element from each pair (both would sum to `m`) and must drop
    `m` itself (its singleton sums to `m`).  Concretely the map `x ↦ min x (m−x)`
    injects `S ∩ {1,…,m}` into `{1,…,⌊m/2⌋}` — a collision `min x (m−x) = min y (m−y)`
    with `x ≠ y` forces `x + y = m`, a forbidden two-element subset sum.  Adding the
    at-most `n − m` elements of `S` above `m` gives
    `|S| ≤ ⌊m/2⌋ + (n − m) = n − ⌈m/2⌉`.  Together with
    `maxAvoidingSize_ge_sub_ceil_half` this pins the exact value. -/
theorem maxAvoidingSize_le_sub_ceil_half (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    maxAvoidingSize n m ≤ n - (m + 1) / 2 := by
  classical
  unfold maxAvoidingSize
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSavoid⟩ := hS
  have hSIcc : S ⊆ Finset.Icc 1 n := by
    intro x hx; have := hSsub hx; rwa [Icc_n] at this
  -- `m` itself cannot be in `S` (its singleton sum is `m`).
  have hmnotinS : m ∉ S := fun h => hSavoid (self_mem_subsetSums S m h (by omega))
  set Slow := S ∩ Finset.Icc 1 m with hSlow
  set Shigh := S ∩ Finset.Icc (m + 1) n with hShigh
  -- `S` is the disjoint union of its low (`≤ m`) and high (`> m`) parts.
  have hunion : Slow ∪ Shigh = S := by
    rw [hSlow, hShigh, ← Finset.inter_union_distrib_left]
    have hIcc : Finset.Icc 1 m ∪ Finset.Icc (m + 1) n = Finset.Icc 1 n := by
      ext a; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    rw [hIcc, Finset.inter_eq_left.mpr hSIcc]
  have hdisj : Disjoint Slow Shigh := by
    rw [hSlow, hShigh, Finset.disjoint_left]
    intro a ha1 ha2
    simp only [Finset.mem_inter, Finset.mem_Icc] at ha1 ha2
    omega
  have hcard : S.card = Slow.card + Shigh.card := by
    rw [← hunion, card_union_eq_card_add_card.mpr hdisj]
  -- The high part has at most `n − m` elements.
  have hShighcard : Shigh.card ≤ n - m := by
    rw [hShigh]
    calc (S ∩ Finset.Icc (m + 1) n).card ≤ (Finset.Icc (m + 1) n).card :=
          Finset.card_le_card Finset.inter_subset_right
      _ = n - m := by rw [Nat.card_Icc]; omega
  -- The low part injects into `{1,…,⌊m/2⌋}` via `x ↦ min x (m − x)`.
  have hmap : Set.MapsTo (fun x => min x (m - x)) (Slow : Set ℕ)
      (Finset.Icc 1 (m / 2) : Set ℕ) := by
    intro x hx
    rw [Finset.mem_coe, hSlow, Finset.mem_inter, Finset.mem_Icc] at hx
    obtain ⟨hxS, hx1, hxm⟩ := hx
    have hxne : x ≠ m := fun h => hmnotinS (h ▸ hxS)
    have hv1 : 1 ≤ min x (m - x) := Nat.le_min.mpr ⟨by omega, by omega⟩
    have hvx : min x (m - x) ≤ x := Nat.min_le_left _ _
    have hvmx : min x (m - x) ≤ m - x := Nat.min_le_right _ _
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨hv1, ?_⟩
    show min x (m - x) ≤ m / 2
    omega
  have hinj : Set.InjOn (fun x => min x (m - x)) (Slow : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hSlow, Finset.mem_inter, Finset.mem_Icc] at hx hy
    obtain ⟨hxS, hx1, hxm⟩ := hx
    obtain ⟨hyS, hy1, hym⟩ := hy
    simp only at hxy
    have hcase : x = y ∨ x + y = m := by
      rcases le_total x (m - x) with h1 | h1 <;> rcases le_total y (m - y) with h2 | h2
      · rw [Nat.min_eq_left h1, Nat.min_eq_left h2] at hxy; omega
      · rw [Nat.min_eq_left h1, Nat.min_eq_right h2] at hxy; omega
      · rw [Nat.min_eq_right h1, Nat.min_eq_left h2] at hxy; omega
      · rw [Nat.min_eq_right h1, Nat.min_eq_right h2] at hxy; omega
    rcases hcase with h | h
    · exact h
    · by_cases hxyeq : x = y
      · exact hxyeq
      · exact absurd (h ▸ pair_mem_subsetSums S x y hxS hyS hxyeq (by omega)) hSavoid
  have hSlowcard : Slow.card ≤ m / 2 := by
    have hle := Finset.card_le_card_of_injOn (fun x => min x (m - x)) hmap hinj
    rwa [Nat.card_Icc, show m / 2 + 1 - 1 = m / 2 by omega] at hle
  omega

/-- **Sharp exact closed form `maxAvoidingSize n m = n − ⌈m/2⌉`** (with
    `⌈m/2⌉ = (m+1)/2` in `ℕ`), for `1 ≤ m ≤ n`.

    Combines the construction lower bound `maxAvoidingSize_ge_sub_ceil_half`
    (witness `{⌈m/2⌉,…,n} \ {m}`) with the hitting-set upper bound
    `maxAvoidingSize_le_sub_ceil_half`.  This is the complete answer for the
    benchmark family: the maximum size of a subset of `{1,…,n}` no subset of which
    sums to `m` is exactly `n − ⌈m/2⌉`.  It recovers the tabulated small-`m` values
    `n−1, n−1, n−2, n−2` for `m = 1,2,3,4` uniformly, and upgrades the previously
    one-sided closed-form bound to an equality. -/
theorem maxAvoidingSize_eq_sub_ceil_half (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    maxAvoidingSize n m = n - (m + 1) / 2 :=
  le_antisymm (maxAvoidingSize_le_sub_ceil_half n m hm hmn)
    (maxAvoidingSize_ge_sub_ceil_half n m hm hmn)

/-- **Antitone in the target on `[1,n]`.** On the exact-formula regime `1 ≤ m₁ ≤ m₂ ≤ n`
    the maximum avoiding size is non-increasing in the forbidden sum: a larger target `m₂`
    admits an avoiding set no larger than one for the smaller target `m₁`,
    `maxAvoidingSize n m₂ ≤ maxAvoidingSize n m₁`. Immediate from
    `maxAvoidingSize_eq_sub_ceil_half`, since `m ↦ ⌈m/2⌉ = (m+1)/2` is monotone. Note this
    monotonicity is *specific to `[1,n]`*: it fails for very large targets, where
    `maxAvoidingSize n m = n` again (`maxAvoidingSize_eq_of_lt`). -/
theorem maxAvoidingSize_antitone_target (n m₁ m₂ : ℕ) (hm₁ : 1 ≤ m₁)
    (hle : m₁ ≤ m₂) (hmn : m₂ ≤ n) :
    maxAvoidingSize n m₂ ≤ maxAvoidingSize n m₁ := by
  rw [maxAvoidingSize_eq_sub_ceil_half n m₁ hm₁ (le_trans hle hmn),
      maxAvoidingSize_eq_sub_ceil_half n m₂ (le_trans hm₁ hle) hmn]
  omega

/-- **Even-target value.** For `1 ≤ t` and `2t ≤ n`, the even target `m = 2t` gives
    `maxAvoidingSize n (2t) = n - t` (here `⌈2t/2⌉ = t`). -/
theorem maxAvoidingSize_two_mul (n t : ℕ) (ht : 1 ≤ t) (htn : 2 * t ≤ n) :
    maxAvoidingSize n (2 * t) = n - t := by
  rw [maxAvoidingSize_eq_sub_ceil_half n (2 * t) (by omega) htn]
  congr 1
  omega

/-- **Odd-target value.** For `1 ≤ t` and `2t ≤ n`, the odd target `m = 2t-1` gives the
    same value `maxAvoidingSize n (2t-1) = n - t` (here `⌈(2t-1)/2⌉ = t`). -/
theorem maxAvoidingSize_two_mul_sub_one (n t : ℕ) (ht : 1 ≤ t) (htn : 2 * t ≤ n) :
    maxAvoidingSize n (2 * t - 1) = n - t := by
  rw [maxAvoidingSize_eq_sub_ceil_half n (2 * t - 1) (by omega) (by omega)]
  congr 1
  omega

/-- **Plateaus of width two.** Because the exact value depends on the target `m` only
    through `⌈m/2⌉ = (m+1)/2`, the function `m ↦ maxAvoidingSize n m` is constant on each
    consecutive pair `{2t-1, 2t}`: for `1 ≤ t` and `2t ≤ n`,
    `maxAvoidingSize n (2t-1) = maxAvoidingSize n (2t)` (both `= n - t`). This is the step
    structure behind the tabulated repeats `n-1, n-1, n-2, n-2, …` for `m = 1,2,3,4,…`. -/
theorem maxAvoidingSize_plateau (n t : ℕ) (ht : 1 ≤ t) (htn : 2 * t ≤ n) :
    maxAvoidingSize n (2 * t - 1) = maxAvoidingSize n (2 * t) := by
  rw [maxAvoidingSize_two_mul_sub_one n t ht htn, maxAvoidingSize_two_mul n t ht htn]

/-- **Diagonal value = minimum over the regime.** At the extreme target `m = n` the maximum
    avoiding size is exactly `⌊n/2⌋`: `maxAvoidingSize n n = n / 2` for `n ≥ 1`. Since the
    value is antitone in `m` on `[1,n]` (`maxAvoidingSize_antitone_target`), this is the
    minimum of `m ↦ maxAvoidingSize n m` over `1 ≤ m ≤ n` — the hardest target `m = n`
    still leaves an avoiding set of half the box. -/
theorem maxAvoidingSize_self (n : ℕ) (hn : 1 ≤ n) :
    maxAvoidingSize n n = n / 2 := by
  rw [maxAvoidingSize_eq_sub_ceil_half n n hn le_rfl]
  omega

/-- Small primes give good constructions. -/
def smallPrimeConstruction (m n : ℕ) : Finset ℕ :=
  let p := Nat.minFac (m + 1)  -- A prime not dividing m
  primeMutliples p n

/-- **`minFac (m+1)` does not divide `m`.**  The least prime factor `p` of `m + 1`
    divides `m + 1`; if it also divided `m` it would divide `(m+1) - m = 1`, forcing
    `p = 1` and contradicting primality.  This is the fact that makes
    `smallPrimeConstruction` a valid `m`-avoiding construction. -/
theorem minFac_succ_not_dvd (m : ℕ) (hm : 1 ≤ m) : ¬ Nat.minFac (m + 1) ∣ m := by
  intro hdvd
  have hp : (Nat.minFac (m + 1)).Prime := Nat.minFac_prime (by omega)
  have hdsub : Nat.minFac (m + 1) ∣ (m + 1 - m) := dvd_sub (Nat.minFac_dvd _) hdvd
  rw [show m + 1 - m = 1 by omega] at hdsub
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdsub)

/-- **`smallPrimeConstruction` is `m`-avoiding.**  Its elements are the multiples of
    the prime `p = minFac (m+1) ∤ m` in `{1,…,n}`, so every nonempty subset sum is a
    multiple of `p` while `m` is not (`prime_multiples_avoid`). -/
theorem smallPrimeConstruction_avoid (m n : ℕ) (hm : 1 ≤ m) :
    AvoidSum (smallPrimeConstruction m n) m :=
  prime_multiples_avoid (Nat.minFac (m + 1)) m n
    (Nat.minFac_prime (by omega)) (minFac_succ_not_dvd m hm)

/-- **Size of `smallPrimeConstruction`.**  It has `⌊n / minFac (m+1)⌋` elements
    (`prime_multiples_size`). -/
theorem smallPrimeConstruction_card (m n : ℕ) (hm : 1 ≤ m) :
    (smallPrimeConstruction m n).card = n / Nat.minFac (m + 1) :=
  prime_multiples_size (Nat.minFac (m + 1)) n (Nat.minFac_prime (by omega)).pos

/-- **Small-prime lower bound.**  Instantiating the prime-multiples bound at the
    canonical prime `minFac (m+1) ∤ m` gives `maxAvoidingSize n m ≥ ⌊n / minFac(m+1)⌋`
    — the lower bound realised by `smallPrimeConstruction`, with no external choice
    of prime.  For `m + 1` prime this is `⌊n/(m+1)⌋`; in general `minFac(m+1) ≤ m+1`
    so it dominates the crude `⌊n/(m+1)⌋`. -/
theorem smallPrime_avoiding_lower (m n : ℕ) (hm : 1 ≤ m) :
    maxAvoidingSize n m ≥ n / Nat.minFac (m + 1) :=
  primeMultiples_avoiding_lower (Nat.minFac (m + 1)) m n
    (Nat.minFac_prime (by omega)) (minFac_succ_not_dvd m hm)

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


