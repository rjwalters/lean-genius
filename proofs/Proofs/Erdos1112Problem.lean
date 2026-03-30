/-
Erdős Problem #1112: k-fold Sumsets Avoiding Lacunary Sequences

Source: https://erdosproblems.com/1112
Status: PARTIALLY RESOLVED

Statement:
Let 1 ≤ d₁ < d₂ and k ≥ 3. Does there exist an integer r such that if B = {b₁ < b₂ < ⋯}
is a lacunary sequence with b_{i+1} ≥ r·b_i, then there exists a sequence
A = {a₁ < a₂ < ⋯} with d₁ ≤ a_{i+1} - a_i ≤ d₂ such that (kA) ∩ B = ∅?

Partial Answer:
- r₂(2,3) = 2 (Erdős-Graham 1980, Bollobás-Hegyvári-Jin 1997)
- r₃(2,3) does not exist (Bollobás-Hegyvári-Jin 1997)
- r₂(a,b) ≤ 2 for b ≠ 2a (Chen 2000)
- The general existence of r_k(a,b) for k ≥ 3 remains OPEN

The problem explores the tension between lacunary sequences (very sparse, exponentially growing)
and arithmetic progressions with bounded gaps. For 2-fold sumsets (A + A), one can always
avoid lacunary sequences with sufficient growth. For 3-fold sumsets (A + A + A), this
becomes impossible.

References:
- Erdős-Graham [ErGr80]: Old and New Problems in Combinatorial Number Theory
- Bollobás-Hegyvári-Jin [BHJ97]: Negative answer for k = 3
- Chen [Ch00]: Generalization for r₂(a,b)
- Tang-Yang [TaYa21]: Further non-existence results
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite

open Set Nat

namespace Erdos1112

/- ##Part I: Lacunary Sequences

A lacunary sequence is one that grows at least exponentially.
-/

/-- **Lacunary Sequence:**
A strictly increasing sequence B = {b₁ < b₂ < ⋯} is r-lacunary if
b_{i+1} ≥ r · b_i for all i ≥ 1. -/
def IsLacunary (r : ℕ) (B : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, B i < B (i + 1)) ∧ (∀ i : ℕ, B (i + 1) ≥ r * B i)

/-- **Bounded Gap Sequence:**
A sequence A = {a₁ < a₂ < ⋯} has gaps bounded by [d₁, d₂] if
d₁ ≤ a_{i+1} - a_i ≤ d₂ for all i. -/
def HasBoundedGaps (d₁ d₂ : ℕ) (A : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, A i < A (i + 1)) ∧
  (∀ i : ℕ, d₁ ≤ A (i + 1) - A i) ∧
  (∀ i : ℕ, A (i + 1) - A i ≤ d₂)

/- ##Part II: k-fold Sumsets

The k-fold sumset kA consists of all sums a₁ + a₂ + ⋯ + a_k
where a_i ∈ A (not necessarily distinct).
-/

/-- **Range of a Sequence:** The set of values taken by sequence A. -/
def SeqRange (A : ℕ → ℕ) : Set ℕ := {n : ℕ | ∃ i : ℕ, A i = n}

/-- **2-fold Sumset:** A + A = {a + a' | a, a' ∈ A}. -/
def TwoFoldSumset (A : Set ℕ) : Set ℕ :=
  {s : ℕ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ s = a + b}

/-- **3-fold Sumset:** A + A + A = {a + a' + a'' | a, a', a'' ∈ A}. -/
def ThreeFoldSumset (A : Set ℕ) : Set ℕ :=
  {s : ℕ | ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ s = a + b + c}

/-- **k-fold Sumset (general):** kA = {a₁ + ⋯ + a_k | a_i ∈ A}. -/
def KFoldSumset (k : ℕ) (A : Set ℕ) : Set ℕ :=
  match k with
  | 0 => {0}
  | 1 => A
  | n + 1 => {s : ℕ | ∃ a t : ℕ, a ∈ A ∧ t ∈ KFoldSumset n A ∧ s = a + t}

/- ##Part III: The Avoidance Problem

Can we find A with bounded gaps such that kA avoids a lacunary B?
-/

/-- **Avoidance Possible:**
For given k, r, d₁, d₂: every r-lacunary B can be avoided by some
A with gaps in [d₁, d₂], meaning (kA) ∩ B = ∅. -/
def AvoidancePossible (k r d₁ d₂ : ℕ) : Prop :=
  ∀ B : ℕ → ℕ, IsLacunary r B →
    ∃ A : ℕ → ℕ, HasBoundedGaps d₁ d₂ A ∧
      (KFoldSumset k (SeqRange A)) ∩ (SeqRange B) = ∅

/-- **r_k(d₁, d₂) Exists:** There is some r making avoidance possible. -/
def RkExists (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℕ, r ≥ 2 ∧ AvoidancePossible k r d₁ d₂

/- ##Part IV: Erdős-Graham Result (1980)

For k = 2 and gaps [2, 3], r = 2 suffices.
-/

/-- **Erdős-Graham Theorem (1980):**
If B is 2-lacunary starting from b₁ ≥ 5, then there exists A
with gaps in [2, 3] such that (A + A) ∩ B = ∅.
This shows r₂(2, 3) = 2. -/
axiom erdos_graham_1980 :
    ∀ B : ℕ → ℕ, IsLacunary 2 B → B 0 ≥ 5 →
      ∃ A : ℕ → ℕ, HasBoundedGaps 2 3 A ∧
        (TwoFoldSumset (SeqRange A)) ∩ (SeqRange B) = ∅

/-- The 2-fold sumset equals KFoldSumset 2 for avoidance purposes. -/
axiom twofold_eq_kfold (A : Set ℕ) :
    TwoFoldSumset A = KFoldSumset 2 A

/-- **r₂(2, 3) = 2:**
The minimal lacunary ratio for 2-fold avoidance with gaps [2,3]. -/
theorem r2_23_equals_2 : RkExists 2 2 3 := by
  use 2
  constructor
  · omega
  · intro B hB
    have h := erdos_graham_1980 B hB
    by_cases hB0 : B 0 ≥ 5
    · obtain ⟨A, hA, hDisj⟩ := h hB0
      use A
      constructor
      · exact hA
      · rw [← twofold_eq_kfold]
        exact hDisj
    · exact ⟨fun n => 2 * n + 1, ⟨by intro i; omega, by intro i; omega, by intro i; omega⟩, by simp [KFoldSumset, SeqRange]; ext; constructor <;> intro h <;> simp_all⟩

/- ##Part V: Bollobás-Hegyvári-Jin Result (1997)

The situation changes dramatically for k = 3.
-/

/-- **Bollobás-Hegyvári-Jin Theorem (1997):**
For any sequence of integers r₁ < r₂ < ⋯, there exists a sequence B
with b_{i+1} ≥ r_i · b_i such that (A + A + A) ∩ B ≠ ∅
for any A with gaps in [2, 3].
This shows r₃(2, 3) does NOT exist! -/
/-- ThreeFold equals KFoldSumset 3. -/
axiom threefold_eq_kfold (A : Set ℕ) :
    ThreeFoldSumset A = KFoldSumset 3 A

/-- BHJ r-lacunary version: for any r ≥ 2, there exists an r-lacunary B
that defeats all A with gaps [2,3]. -/
axiom bhj_r_lacunary (r : ℕ) (hr : r ≥ 2) :
    ∃ B : ℕ → ℕ, IsLacunary r B ∧
      ∀ A : ℕ → ℕ, HasBoundedGaps 2 3 A →
        (ThreeFoldSumset (SeqRange A)) ∩ (SeqRange B) ≠ ∅

/-- **r₃(2, 3) Does Not Exist:**
No matter how lacunary B is, 3-fold sumsets cannot avoid it. -/
theorem r3_23_not_exists : ¬RkExists 3 2 3 := by
  intro ⟨r, hr, hAvoid⟩
  obtain ⟨B, hBLac, hBDefeats⟩ := bhj_r_lacunary r hr
  obtain ⟨A, hA, hDisj⟩ := hAvoid B hBLac
  have hIntersect := hBDefeats A hA
  rw [threefold_eq_kfold] at hIntersect
  exact hIntersect hDisj

/- ##Part VI: Chen's Generalization (2000) -/

/-- **Chen's Theorem (2000):**
For any integers a < b with b ≠ 2a, we have r₂(a, b) ≤ 2.
When b = 2a, a different behavior occurs. -/
axiom chen_r2_bound :
    ∀ a b : ℕ, a ≥ 1 → b > a → b ≠ 2 * a → RkExists 2 a b

/- ##Part VII: Tang-Yang Results (2021)

Further non-existence results for k ≥ 3.
-/

/-- **Tang-Yang (2021):**
Additional non-existence results for specific parameter combinations with k ≥ 3. -/
/- ##Part VIII: Summary

**Erdős Problem #1112: PARTIALLY RESOLVED**

| k | Gap [d₁,d₂] | r_k exists? | Reference |
|---|-------------|-------------|-----------|
| 2 | [2,3]       | Yes, r=2    | ErGr80    |
| 2 | [a,b], b≠2a | Yes, r≤2    | Ch00      |
| 3 | [2,3]       | No          | BHJ97     |
| ≥3| various     | No (many)   | TaYa21    |

The problem represents a phase transition at k = 3.
-/

/-- **Erdős Problem #1112: PARTIALLY RESOLVED**

The essential dichotomy: 2-fold sumsets can avoid lacunary sequences,
but 3-fold sumsets cannot. -/
theorem erdos_1112 :
    (∀ a b : ℕ, a ≥ 1 → b > a → b ≠ 2 * a → RkExists 2 a b) ∧
    (¬RkExists 3 2 3) :=
  ⟨chen_r2_bound, r3_23_not_exists⟩

/-- Summary: the k=2 vs k=3 dichotomy for gaps [2,3]. -/
theorem erdos_1112_summary :
    (RkExists 2 2 3) ∧ (¬RkExists 3 2 3) :=
  ⟨r2_23_equals_2, r3_23_not_exists⟩

end Erdos1112
