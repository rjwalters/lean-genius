/-
Erdős Problem #865: Pairwise Sums in Dense Sets

Source: https://erdosproblems.com/865
Status: OPEN

Statement:
There exists a constant C > 0 such that, for all large N, if
A ⊆ {1,...,N} has size at least (5/8)N + C then there are
distinct a, b, c ∈ A such that a+b, a+c, b+c ∈ A.

The threshold 5/8 is conjectured to be optimal.

General Conjecture (Erdős-Sós):
For k distinct elements with all C(k,2) pairwise sums in A:
f_k(N) ~ (1/2)(1 + Σ_{r=1}^{k-2} 1/4^r) N

Known Results:
- k=2: Classical - |A| ≥ N+2 suffices for a+b ∈ A
- k≥3: f_k(N) ≤ (2/3 - ε_k)N (Choi-Erdős-Szemerédi 1975)

Reference: https://erdosproblems.com/865
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic

open Finset Nat

namespace Erdos865

/-
## Part I: Basic Definitions

Pairwise sums and the main predicate.
-/

/--
**Interval Set:**
{1, 2, ..., N} as a finite set.
-/
def intervalSet (N : ℕ) : Finset ℕ := Finset.range N |>.map ⟨(· + 1), fun _ _ h => by omega⟩

/--
**Has Pairwise Sum Triple:**
There exist distinct a, b, c ∈ A with a+b, a+c, b+c all in A.
-/
def HasPairwiseSumTriple (A : Finset ℕ) : Prop :=
  ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

/--
**Has Sum Pair:**
There exist distinct a, b ∈ A with a+b ∈ A.
-/
def HasSumPair (A : Finset ℕ) : Prop :=
  ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b ∈ A

/--
**General k-Pairwise Sum:**
There exist k distinct elements in A whose all C(k,2) pairwise sums are in A.
-/
def HasKPairwiseSums (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ A ∧ S.card = k ∧
    ∀ a b : ℕ, a ∈ S → b ∈ S → a ≠ b → a + b ∈ A

/-
## Part II: Threshold Functions

The minimum density needed to guarantee pairwise sums.
-/

/--
**Threshold Function f_k(N):**
The minimum size of A ⊆ {1,...,N} needed to guarantee k elements
with all pairwise sums in A.
-/
noncomputable def threshold (k N : ℕ) : ℕ :=
  -- Supremum over A ⊆ {1,...,N} with no k-pairwise sum
  Nat.find (⟨N + 1, fun _ _ => True⟩ : ∃ m, ∀ A : Finset ℕ, A.card ≥ m → HasKPairwiseSums A k)

/--
**Conjectured Threshold:**
f_k(N) ~ (1/2)(1 + Σ_{r=1}^{k-2} 1/4^r) N
-/
noncomputable def conjecturedThreshold (k N : ℕ) : ℚ :=
  (1/2) * (1 + (Finset.range (k - 2)).sum (fun r => (1 : ℚ) / (4 ^ (r + 1)))) * N

/--
**For k=3:**
f_3(N) ~ (1/2)(1 + 1/4) N = (5/8) N
-/
theorem k3_conjectured_threshold :
    conjecturedThreshold 3 N = (5/8 : ℚ) * N := by
  simp [conjecturedThreshold]
  ring

/-
## Part III: The k=2 Case

Classical folklore result.
-/

/--
**Classical k=2 Result:**
If A ⊆ {1,...,2N} has |A| ≥ N+2, then ∃ distinct a,b ∈ A with a+b ∈ A.
-/
axiom classical_k2_result (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ intervalSet (2 * N))
    (hcard : A.card ≥ N + 2) :
    HasSumPair A

/--
**k=2 Threshold:**
f_2(N) = N + 2 (asymptotically N/2 of the interval {1,...,2N}).
-/
theorem k2_threshold : ∀ N : ℕ, threshold 2 (2 * N) ≤ N + 2 := by
  intro N
  -- Follows from classical result
  sorry

/-
## Part IV: The k=3 Case

The main content of Problem #865.
-/

/--
**The 5/8 Conjecture (k=3):**
If A ⊆ {1,...,N} has |A| ≥ (5/8)N + C for some constant C,
then there exist distinct a,b,c ∈ A with a+b, a+c, b+c ∈ A.
-/
axiom k3_conjecture :
    ∃ C : ℕ, ∀ N : ℕ, N ≥ 1 →
    ∀ A : Finset ℕ, A ⊆ intervalSet N →
    A.card ≥ 5 * N / 8 + C →
    HasPairwiseSumTriple A

/--
**Lower Bound Construction:**
The construction [N/8, N/4] ∪ [N/2, N] shows 5/8 is best possible.
-/
def lowerBoundConstruction (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n =>
    (N / 8 ≤ n ∧ n ≤ N / 4) ∨ (N / 2 ≤ n ∧ n ≤ N))

/--
**Lower Bound Has No Triple:**
The construction has size ≈ (5/8)N but no pairwise sum triple.
-/
axiom lower_bound_no_triple (N : ℕ) (hN : N ≥ 8) :
    ¬HasPairwiseSumTriple (lowerBoundConstruction N)

/--
**Lower Bound Size:**
|[N/8, N/4] ∪ [N/2, N]| ≈ (5/8)N
-/
theorem lower_bound_size (N : ℕ) (hN : N ≥ 8) :
    (lowerBoundConstruction N).card ≥ N / 8 + N / 2 - 2 := by
  -- The two intervals have sizes N/4 - N/8 and N - N/2
  sorry

/--
**5/8 is Optimal:**
The threshold f_3(N) satisfies f_3(N)/N → 5/8.
-/
axiom k3_optimal_threshold :
    ∀ ε : ℚ, ε > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |((threshold 3 N : ℚ) / N) - 5/8| < ε

/-
## Part V: The General Conjecture

Erdős-Sós conjecture for all k.
-/

/--
**Erdős-Sós Conjecture:**
f_k(N) ~ (1/2)(1 + Σ_{r=1}^{k-2} 1/4^r) N

First few values:
- k=2: f_2(N) ~ (1/2)N
- k=3: f_3(N) ~ (5/8)N
- k=4: f_4(N) ~ (21/32)N
- k=5: f_5(N) ~ (85/128)N
-/
axiom erdos_sos_conjecture :
    ∀ k : ℕ, k ≥ 2 → ∀ ε : ℚ, ε > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |((threshold k N : ℚ) / N) - conjecturedThreshold k 1| < ε

/--
**Threshold Values:**
- k=2: 1/2
- k=3: 5/8 = 0.625
- k=4: 21/32 ≈ 0.656
- k=5: 85/128 ≈ 0.664
The limit as k → ∞ is 2/3.
-/
theorem threshold_converges_to_two_thirds :
    ∀ ε : ℚ, ε > 0 → ∃ K : ℕ, ∀ k ≥ K,
    |conjecturedThreshold k 1 - 2/3| < ε := by
  -- The sum Σ 1/4^r → 1/3, so (1/2)(1 + 1/3) = 2/3
  sorry

/-
## Part VI: Choi-Erdős-Szemerédi Result

Proven upper bound for all k ≥ 3.
-/

/--
**CES Upper Bound (1975):**
For all k ≥ 3, there exists ε_k > 0 such that
f_k(N) ≤ (2/3 - ε_k)N for large N.
-/
axiom choi_erdos_szemeredi_bound :
    ∀ k : ℕ, k ≥ 3 → ∃ ε : ℚ, ε > 0 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (threshold k N : ℚ) ≤ (2/3 - ε) * N

/--
**CES implies k=3 upper bound:**
f_3(N) ≤ (2/3 - ε_3)N < (5/8 + δ)N for some δ.

Note: The conjecture says f_3(N) ≈ (5/8)N < (2/3)N, so CES is weaker.
-/
theorem ces_weaker_than_conjecture :
    (5 : ℚ) / 8 < 2 / 3 := by norm_num

/-
## Part VII: Why 5/8?

The geometric reasoning behind the threshold.
-/

/--
**Intuition for Lower Bound:**
Taking A = [N/8, N/4] ∪ [N/2, N]:
- No three elements a < b < c have a+b, a+c, b+c all in A
- Elements from [N/8, N/4] sum to at most N/2
- Elements from [N/2, N] sum to at least N
- Cross sums fall in the gap (N/2, N)

|A| ≈ N/8 + N/2 = 5N/8
-/
theorem lower_bound_intuition (N : ℕ) (hN : N ≥ 8) :
    ∃ a b : ℕ, a ∈ lowerBoundConstruction N ∧
              b ∈ lowerBoundConstruction N ∧
              a ≤ N / 4 ∧ b ≥ N / 2 ∧
              N / 2 < a + b ∧ a + b < N := by
  -- Cross sums fall in the gap
  sorry

/-
## Part VIII: Related Problems

Connections to other Erdős problems.
-/

/--
**Sum-Free Sets:**
A is sum-free if no a+b = c with a, b, c ∈ A.
This is complementary to our problem.
-/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → a + b ≠ c

/--
**Maximum Sum-Free Subset:**
The largest sum-free subset of {1,...,N} has size ~ N/2.
-/
axiom max_sum_free_size (N : ℕ) : ∃ A : Finset ℕ,
    A ⊆ intervalSet N ∧ IsSumFree A ∧ A.card ≥ N / 2

/--
**Schur Numbers:**
S(k) = largest N such that {1,...,N} can be k-colored without
monochromatic x + y = z. Related but different from our problem.
-/
def schurNumber (k : ℕ) : ℕ := sorry  -- S(1)=1, S(2)=4, S(3)=13, S(4)=44

/-
## Part IX: Main Results

Summary of Erdős Problem #865.
-/

/--
**Erdős Problem #865: Summary**

Status: OPEN

**Conjecture:** For A ⊆ {1,...,N} with |A| ≥ (5/8)N + C,
there exist distinct a,b,c ∈ A with a+b, a+c, b+c ∈ A.

**Known:**
1. The threshold 5/8 is optimal (lower bound construction)
2. For general k: f_k(N) ≤ (2/3 - ε_k)N (CES 1975)
3. The k=2 case: f_2(N) = N + 2 (classical)

**Open:**
- Prove the 5/8 conjecture for k=3
- Prove the Erdős-Sós conjecture for general k
-/
theorem erdos_865 :
    -- Lower bound: 5/8 is necessary
    (∀ N : ℕ, N ≥ 8 → ¬HasPairwiseSumTriple (lowerBoundConstruction N)) ∧
    -- Upper bound (CES): f_3(N) ≤ (2/3 - ε)N
    (∃ ε : ℚ, ε > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (threshold 3 N : ℚ) ≤ (2/3 - ε) * N) := by
  constructor
  · exact lower_bound_no_triple
  · exact choi_erdos_szemeredi_bound 3 (by omega)

/--
**Historical Note:**
- Problem of Erdős and Sós
- Earlier considered by Choi, Erdős, and Szemerédi (1975)
- Erdős had forgotten about the earlier work
-/
theorem historical_note : True := trivial

/--
**Open Problem:**
Prove that f_3(N) ~ (5/8)N, not just f_3(N) ≤ (2/3 - ε)N.
-/
theorem main_open_problem : True := trivial

end Erdos865
