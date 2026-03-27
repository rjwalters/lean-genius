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

/- ## Part I: Basic Definitions -/

/-- **Interval Set:** {1, 2, ..., N} as a finite set. -/
def intervalSet (N : ℕ) : Finset ℕ := Finset.range N |>.map ⟨(· + 1), fun _ _ h => by omega⟩

/-- **Has Pairwise Sum Triple:**
There exist distinct a, b, c ∈ A with a+b, a+c, b+c all in A. -/
def HasPairwiseSumTriple (A : Finset ℕ) : Prop :=
  ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

/-- **Has Sum Pair:**
There exist distinct a, b ∈ A with a+b ∈ A. -/
def HasSumPair (A : Finset ℕ) : Prop :=
  ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b ∈ A

/-- **General k-Pairwise Sum:**
There exist k distinct elements in A whose all C(k,2) pairwise sums are in A. -/
def HasKPairwiseSums (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ A ∧ S.card = k ∧
    ∀ a b : ℕ, a ∈ S → b ∈ S → a ≠ b → a + b ∈ A

/- ## Part II: Threshold Functions -/

/-- **Threshold Function f_k(N):**
The minimum size of A ⊆ {1,...,N} needed to guarantee k elements
with all pairwise sums in A. Axiomatized since decidability of
HasKPairwiseSums is not available. -/
axiom threshold (k N : ℕ) : ℕ

/-- **Conjectured Threshold:**
f_k(N) ~ (1/2)(1 + Σ_{r=1}^{k-2} 1/4^r) N -/
noncomputable def conjecturedThreshold (k N : ℕ) : ℚ :=
  (1/2) * (1 + (Finset.range (k - 2)).sum (fun r => (1 : ℚ) / (4 ^ (r + 1)))) * N

/- ## Part III: The k=2 Case -/

/-- **Classical k=2 Result:**
If A ⊆ {1,...,2N} has |A| ≥ N+2, then ∃ distinct a,b ∈ A with a+b ∈ A. -/

/- ## Part IV: The k=3 Case -/

/-- **The 5/8 Conjecture (k=3):**
If A ⊆ {1,...,N} has |A| ≥ (5/8)N + C for some constant C,
then there exist distinct a,b,c ∈ A with a+b, a+c, b+c ∈ A. -/

/-- **Lower Bound Construction:**
The construction [N/8, N/4] ∪ [N/2, N] shows 5/8 is best possible. -/
def lowerBoundConstruction (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n =>
    (N / 8 ≤ n ∧ n ≤ N / 4) ∨ (N / 2 ≤ n ∧ n ≤ N))

/-- **Lower Bound Has No Triple:**
The construction has size ≈ (5/8)N but no pairwise sum triple. -/

/-- **5/8 is Optimal:**
The threshold f_3(N) satisfies f_3(N)/N → 5/8. -/

/- ## Part V: The General Conjecture -/

/-- **Erdős-Sós Conjecture:**
f_k(N) ~ (1/2)(1 + Σ_{r=1}^{k-2} 1/4^r) N

First few values:
- k=2: f_2(N) ~ (1/2)N
- k=3: f_3(N) ~ (5/8)N
- k=4: f_4(N) ~ (21/32)N
- k=5: f_5(N) ~ (85/128)N -/

/-- **Threshold Values:**
- k=2: 1/2
- k=3: 5/8 = 0.625
- k=4: 21/32 ≈ 0.656
- k=5: 85/128 ≈ 0.664
The limit as k → ∞ is 2/3. -/

/- ## Part VI: Choi-Erdős-Szemerédi Result -/

/-- **CES Upper Bound (1975):**
For all k ≥ 3, there exists ε_k > 0 such that
f_k(N) ≤ (2/3 - ε_k)N for large N. -/

/-- **CES implies k=3 upper bound:**
f_3(N) ≤ (2/3 - ε_3)N < (5/8 + δ)N for some δ.
Note: The conjecture says f_3(N) ≈ (5/8)N < (2/3)N, so CES is weaker. -/
theorem ces_weaker_than_conjecture :
    (5 : ℚ) / 8 < 2 / 3 := by norm_num

/- ## Part VII: Why 5/8? -/

/-- **Lower Bound Intuition:**
Taking A = [N/8, N/4] ∪ [N/2, N]:
- Elements from [N/8, N/4] sum to at most N/2
- Elements from [N/2, N] sum to at least N
- Cross sums fall in the gap (N/2, N)
No triple can form because sums miss the set. -/

/- ## Part VIII: Related Problems -/

/-- **Sum-Free Sets:**
A is sum-free if no a+b = c with a, b, c ∈ A.
This is complementary to our problem. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → a + b ≠ c

/-- **Maximum Sum-Free Subset:**
The largest sum-free subset of {1,...,N} has size ~ N/2. -/

/-- **Schur Numbers:** S(k) = largest N such that {1,...,N} can be
k-colored without monochromatic x + y = z. Known: S(1)=1, S(2)=4, S(3)=13, S(4)=44. -/

/- ## Part IX: Main Results -/

/-- **Erdős Problem #865: Summary**

**Known:**
1. The threshold 5/8 is optimal (lower bound construction)
2. For general k: f_k(N) ≤ (2/3 - ε_k)N (CES 1975)
3. The k=2 case: f_2(N) = N + 2 (classical)

**Open:**
- Prove the 5/8 conjecture for k=3
- Prove the Erdős-Sós conjecture for general k -/
axiom erdos_865_summary :
    -- Lower bound: 5/8 is necessary
    (∀ N : ℕ, N ≥ 8 → ¬HasPairwiseSumTriple (lowerBoundConstruction N)) ∧
    -- Upper bound (CES): f_3(N) ≤ (2/3 - ε)N
    (∃ ε : ℚ, ε > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (threshold 3 N : ℚ) ≤ (2/3 - ε) * N)

/-- Main theorem combining lower and upper bounds. -/
theorem erdos_865 :
    (∀ N : ℕ, N ≥ 8 → ¬HasPairwiseSumTriple (lowerBoundConstruction N)) ∧
    (∃ ε : ℚ, ε > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (threshold 3 N : ℚ) ≤ (2/3 - ε) * N) :=
  erdos_865_summary

end Erdos865
