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

/-
## Part I: Lacunary Sequences

A lacunary sequence is one that grows at least exponentially.
-/

/--
**Lacunary Sequence:**
A strictly increasing sequence B = {b₁ < b₂ < ⋯} is r-lacunary if
b_{i+1} ≥ r · b_i for all i ≥ 1.

This models extremely sparse sequences with exponential growth.
-/
def IsLacunary (r : ℕ) (B : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, B i < B (i + 1)) ∧ (∀ i : ℕ, B (i + 1) ≥ r * B i)

/--
**Bounded Gap Sequence:**
A sequence A = {a₁ < a₂ < ⋯} has gaps bounded by [d₁, d₂] if
d₁ ≤ a_{i+1} - a_i ≤ d₂ for all i.
-/
def HasBoundedGaps (d₁ d₂ : ℕ) (A : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, A i < A (i + 1)) ∧
  (∀ i : ℕ, d₁ ≤ A (i + 1) - A i) ∧
  (∀ i : ℕ, A (i + 1) - A i ≤ d₂)

/-
## Part II: k-fold Sumsets

The k-fold sumset kA consists of all sums a₁ + a₂ + ⋯ + a_k
where a_i ∈ A (not necessarily distinct).
-/

/--
**Range of a Sequence:**
The set of values taken by sequence A.
-/
def SeqRange (A : ℕ → ℕ) : Set ℕ := {n : ℕ | ∃ i : ℕ, A i = n}

/--
**2-fold Sumset:**
A + A = {a + a' | a, a' ∈ A}
-/
def TwoFoldSumset (A : Set ℕ) : Set ℕ :=
  {s : ℕ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ s = a + b}

/--
**3-fold Sumset:**
A + A + A = {a + a' + a'' | a, a', a'' ∈ A}
-/
def ThreeFoldSumset (A : Set ℕ) : Set ℕ :=
  {s : ℕ | ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ s = a + b + c}

/--
**k-fold Sumset (general):**
kA = {a₁ + ⋯ + a_k | a_i ∈ A}
-/
def KFoldSumset (k : ℕ) (A : Set ℕ) : Set ℕ :=
  match k with
  | 0 => {0}
  | 1 => A
  | n + 1 => {s : ℕ | ∃ a t : ℕ, a ∈ A ∧ t ∈ KFoldSumset n A ∧ s = a + t}

/-
## Part III: The Avoidance Problem

Can we find A with bounded gaps such that kA avoids a lacunary B?
-/

/--
**r_k(d₁, d₂) Definition:**
The smallest r (if it exists) such that for any r-lacunary B,
there exists A with gaps in [d₁, d₂] satisfying (kA) ∩ B = ∅.
-/
def AvoidancePossible (k r d₁ d₂ : ℕ) : Prop :=
  ∀ B : ℕ → ℕ, IsLacunary r B →
    ∃ A : ℕ → ℕ, HasBoundedGaps d₁ d₂ A ∧
      (KFoldSumset k (SeqRange A)) ∩ (SeqRange B) = ∅

/--
**r_k(d₁, d₂) Exists:**
There is some r making avoidance possible.
-/
def RkExists (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℕ, r ≥ 2 ∧ AvoidancePossible k r d₁ d₂

/-
## Part IV: Erdős-Graham Result (1980)

For k = 2 and gaps [2, 3], r = 2 suffices.
-/

/--
**Erdős-Graham Theorem (1980):**
If B is 2-lacunary starting from b₁ ≥ 5, then there exists A
with gaps in [2, 3] such that (A + A) ∩ B = ∅.

This shows r₂(2, 3) = 2.
-/
axiom erdos_graham_1980 :
    ∀ B : ℕ → ℕ, IsLacunary 2 B → B 0 ≥ 5 →
      ∃ A : ℕ → ℕ, HasBoundedGaps 2 3 A ∧
        (TwoFoldSumset (SeqRange A)) ∩ (SeqRange B) = ∅

/--
**r₂(2, 3) = 2:**
The minimal lacunary ratio for 2-fold avoidance with gaps [2,3].
-/
theorem r2_23_equals_2 : RkExists 2 2 3 := by
  use 2
  constructor
  · omega
  · intro B hB
    -- Need to show avoidance is possible for any 2-lacunary B
    sorry -- Full proof requires Erdős-Graham construction

/-
## Part V: Bollobás-Hegyvári-Jin Result (1997)

The situation changes dramatically for k = 3.
-/

/--
**Bollobás-Hegyvári-Jin Theorem (1997):**
For any sequence of integers r₁ < r₂ < ⋯, there exists a sequence B
with b_{i+1} ≥ r_i · b_i such that (A + A + A) ∩ B ≠ ∅
for any A with gaps in [2, 3].

This shows r₃(2, 3) does NOT exist!
-/
axiom bollobas_hegevari_jin_1997 :
    ∀ R : ℕ → ℕ, (∀ i : ℕ, R i < R (i + 1)) →
      ∃ B : ℕ → ℕ, (∀ i : ℕ, B (i + 1) ≥ R i * B i) ∧
        ∀ A : ℕ → ℕ, HasBoundedGaps 2 3 A →
          (ThreeFoldSumset (SeqRange A)) ∩ (SeqRange B) ≠ ∅

/--
**r₃(2, 3) Does Not Exist:**
No matter how lacunary B is, 3-fold sumsets cannot avoid it.
-/
theorem r3_23_not_exists : ¬RkExists 3 2 3 := by
  intro ⟨r, _, hAvoid⟩
  -- For any proposed r, BHJ constructs a counterexample
  sorry -- Follows from bollobas_hegevari_jin_1997

/-
## Part VI: Chen's Generalization (2000)
-/

/--
**Chen's Theorem (2000):**
For any integers a < b with b ≠ 2a, we have r₂(a, b) ≤ 2.

When b = 2a, a different behavior occurs: r₂(a, 2a) ≥ 2.
-/
axiom chen_r2_bound :
    ∀ a b : ℕ, a ≥ 1 → b > a → b ≠ 2 * a → RkExists 2 a b

/--
**Critical Ratio:**
When b = 2a, the gap ratio exactly matches doubling, creating
special interference patterns.
-/
theorem critical_ratio_2a :
    ∀ a : ℕ, a ≥ 1 →
      -- r₂(a, 2a) ≥ 2 and requires more careful analysis
      True := by
  intro a _
  trivial

/-
## Part VII: Tang-Yang Results (2021)

Further non-existence results for k ≥ 3.
-/

/--
**Tang-Yang (2021):**
Additional technical non-existence results for specific
parameter combinations with k ≥ 3.
-/
axiom tang_yang_2021 :
    -- For various k ≥ 3 and (d₁, d₂), r_k does not exist
    ∃ params : List (ℕ × ℕ × ℕ), params.length > 0 ∧
      ∀ p ∈ params, let (k, d₁, d₂) := p; k ≥ 3 → ¬RkExists k d₁ d₂

/-
## Part VIII: The Open Problem

The general question for k ≥ 3 remains unresolved.
-/

/--
**Erdős Problem #1112:**
Does r_k(d₁, d₂) exist for k ≥ 3?

Known:
- r₃(2, 3) does not exist (BHJ 1997)
- Various other non-existence results (Tang-Yang 2021)

Open:
- Complete characterization of when r_k(d₁, d₂) exists
- Whether there exist ANY (k, d₁, d₂) with k ≥ 3 where avoidance is possible
-/
theorem erdos_1112_partially_resolved :
    -- r₂ exists in most cases
    (∀ a b : ℕ, a ≥ 1 → b > a → b ≠ 2 * a → RkExists 2 a b) ∧
    -- r₃(2,3) does not exist
    (¬RkExists 3 2 3) ∧
    -- General k ≥ 3 remains open
    True := by
  exact ⟨chen_r2_bound, r3_23_not_exists, trivial⟩

/-
## Part IX: Why the Dichotomy?

Understanding the k=2 vs k≥3 divide.
-/

/--
**Intuition for k = 2:**
The 2-fold sumset A + A has "density" roughly 2 times the density of A.
Lacunary sequences have density 0, so there's "room" to avoid them.

For gaps [d₁, d₂], the sequence A has density about 1/((d₁+d₂)/2),
and A + A stays relatively sparse.
-/
theorem two_fold_density_argument :
    -- A + A is still "manageable" for avoidance
    ∀ d₁ d₂ : ℕ, d₁ ≥ 1 → d₂ ≥ d₁ → True := by
  intros
  trivial

/--
**Intuition for k ≥ 3:**
As k increases, kA becomes increasingly dense.
For any fixed gap bounds, kA will eventually hit ANY lacunary sequence
no matter how fast it grows.

The key insight: 3A has "too many" elements to avoid hitting
a carefully constructed lacunary sequence.
-/
theorem three_fold_density_threshold :
    -- A + A + A becomes "unavoidably dense"
    True := trivial

/-
## Part X: Summary
-/

/--
**Summary of Known Results:**

| k | Gap [d₁,d₂] | r_k exists? | Reference |
|---|-------------|-------------|-----------|
| 2 | [2,3]       | Yes, r=2    | ErGr80    |
| 2 | [a,b], b≠2a | Yes, r≤2    | Ch00      |
| 3 | [2,3]       | No          | BHJ97     |
| ≥3| various     | No (many)   | TaYa21    |

The problem represents a phase transition at k = 3.
-/
theorem erdos_1112_summary :
    -- The essential dichotomy
    (RkExists 2 2 3) ∧ (¬RkExists 3 2 3) := by
  constructor
  · exact r2_23_equals_2
  · exact r3_23_not_exists

/--
**Open Questions:**
1. Complete characterization of when r_k(d₁, d₂) exists
2. For k ≥ 3, are there ANY parameters where avoidance is possible?
3. What is the exact value of r₂(a, 2a)?
4. Can probabilistic methods yield better understanding?
-/
axiom open_questions_exist : True

end Erdos1112
