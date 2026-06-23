/-
Erdős Problem #819: Sumsets of √N-Sized Sets

Source: https://erdosproblems.com/819
Status: OPEN

Statement:
Let f(N) be maximal such that there exists A ⊆ {1,...,N} with |A| = ⌊√N⌋
such that |(A+A) ∩ [1,N]| = f(N). Estimate f(N).

In other words: For a set of ~√N integers from [1,N], what is the maximum
possible size of the sumset A+A restricted to [1,N]?

Background:
This is a fundamental question in additive combinatorics about the trade-off
between set size and sumset structure. A set of size √N is "critically sized" -
small enough that A+A might not fill [1,N], but large enough to be interesting.

Known Results (Erdős-Freud 1991):
  (3/8 - o(1))N ≤ f(N) ≤ (1/2 + o(1))N

The gap between 0.375N and 0.5N remains OPEN.

References:
- [ErFr91] Erdős-Freud (1991): Original bounds
- See also Problem #840 (quasi-Sidon sets)

Tags: additive-combinatorics, sumsets
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

namespace Erdos819

/-
## Part I: Sumsets
-/

/--
**Sumset A + A:**
The set of all pairwise sums {a + b : a, b ∈ A}.
-/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/--
**Restricted sumset:**
(A + A) ∩ [1, N]
-/
def restrictedSumset (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (sumset A).filter (fun x => x ≥ 1 ∧ x ≤ N)

/-
## Part II: The Function f(N)
-/

/--
**Set from [1,N]:**
A ⊆ {1, ..., N}.
-/
def IsSubsetInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, a ≥ 1 ∧ a ≤ N

/--
**√N-sized set:**
|A| = ⌊√N⌋.
-/
def HasSqrtSize (A : Finset ℕ) (N : ℕ) : Prop :=
  A.card = Nat.sqrt N

/--
**Admissible set:**
A ⊆ [1,N] with |A| = ⌊√N⌋.
-/
def IsAdmissible (A : Finset ℕ) (N : ℕ) : Prop :=
  IsSubsetInterval A N ∧ HasSqrtSize A N

/--
**f(N):**
The maximum size of (A+A) ∩ [1,N] over all admissible A.
-/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {(restrictedSumset A N).card | A : Finset ℕ, IsAdmissible A N}

/--
The supremum defining f(N) is attained because we optimize over a finite
collection of finite sets. Axiomatized since the proof requires finiteness
arguments about the space of admissible sets.
-/
/-
## Part III: Trivial Bounds
-/

/--
**Upper bound: f(N) ≤ N**
The restricted sumset is a subset of [1,N], so has at most N elements.
-/
/--
**Trivial lower bound:**
Any admissible set gives |(A+A) ∩ [1,N]| ≥ |A| = √N, since
at minimum the elements of A themselves appear as sums (a + 0 is not valid,
but various small sums land in [1,N]).
-/
/-
## Part IV: Erdős-Freud Bounds (1991)
-/

/--
**Erdős-Freud Lower Bound:**
f(N) ≥ (3/8 - o(1))N

There exist √N-sized sets with sumset covering at least 3N/8.
-/
axiom erdos_freud_lower :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (f N : ℝ) ≥ (3/8 - ε) * N

/--
**Erdős-Freud Upper Bound:**
f(N) ≤ (1/2 + o(1))N

No √N-sized set can have sumset covering more than N/2.
-/
axiom erdos_freud_upper :
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (f N : ℝ) ≤ (1/2 + ε) * N

/--
**Combined bounds:**
(3/8 - o(1))N ≤ f(N) ≤ (1/2 + o(1))N
-/
theorem erdos_freud_bounds (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (3/8 - ε) * N ≤ f N ∧ (f N : ℝ) ≤ (1/2 + ε) * N := by
  obtain ⟨N₁, hN₁⟩ := erdos_freud_lower ε hε
  obtain ⟨N₂, hN₂⟩ := erdos_freud_upper ε hε
  use max N₁ N₂
  intro N hN
  constructor
  · exact hN₁ N (le_of_max_le_left hN)
  · exact hN₂ N (le_of_max_le_right hN)

/--
The asymptotic constants bounding f(N)/N.
Lower coefficient: 3/8 = 0.375
Upper coefficient: 1/2 = 0.5
-/
def lowerCoefficient : ℚ := 3 / 8
def upperCoefficient : ℚ := 1 / 2

theorem coefficients_gap : upperCoefficient - lowerCoefficient = 1 / 8 := by
  unfold upperCoefficient lowerCoefficient
  norm_num

/-
## Part V: Lower Bound Construction
-/

/--
**Lower bound construction (Erdős-Freud 1991):**
To achieve 3N/8, one constructs sets where sums are well-distributed
using arithmetic progressions with carefully chosen common difference.
The construction avoids too much additive structure while still generating
many distinct sums landing in [1,N].
-/
/--
**Upper bound argument (Erdős-Freud 1991):**
If |A| = √N, then |A+A| ≤ |A|² = N in general.
But (A+A) ∩ [1,N] has additional constraints: sums a+b with
a,b ∈ [1,N] range from 2 to 2N, and roughly half exceed N.
This geometric constraint limits coverage to at most N/2.
-/
/-
## Part VI: Connection to Quasi-Sidon Sets
-/

/--
**Quasi-Sidon set:**
A set where the number of representation pairs a+b = n is bounded.
Sidon sets have at most one representation per sum; quasi-Sidon allows
a bounded number. The maximum quasi-Sidon set size in [1,N] is related
to the sumset coverage achievable by √N-sized sets.
-/
def IsQuasiSidon (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ((A ×ˢ A).filter (fun p => p.1 + p.2 = n ∧ p.1 ≤ p.2)).card ≤ k

/--
**Problem #840 connection:**
The size of the largest quasi-Sidon set in [1,N] is related to f(N).
If A is quasi-Sidon with parameter k, then |A+A| ≥ |A|²/(2k),
so better quasi-Sidon sets yield larger sumsets.
-/
/-
## Part VII: Extremal Examples
-/

/--
**Arithmetic progression sumset:**
A = {0, 1, ..., k-1} has |A+A| = 2k-1.
For k = √N: only ~2√N sums, far from the optimal ~0.375N.
APs have too much additive structure - their sums overlap heavily.
-/
/-
## Part VIII: The Gap
-/

/--
**The gap between bounds:**
We know 3N/8 ≤ f(N) ≤ N/2.
The gap is N/8 (12.5% of N).

**Open question:** What is the true asymptotic constant c where f(N) ~ cN?
-/
def boundGap : ℚ := upperCoefficient - lowerCoefficient  -- = 1/8

theorem gap_is_eighth : boundGap = 1 / 8 := by
  unfold boundGap upperCoefficient lowerCoefficient
  norm_num

/-
## Part IX: Summary
-/

/--
**Erdős Problem #819: OPEN**

**QUESTION:** For A ⊆ [1,N] with |A| = √N, estimate
max |(A+A) ∩ [1,N]| = f(N).

**KNOWN (Erdős-Freud 1991):**
  (3/8 - o(1))N ≤ f(N) ≤ (1/2 + o(1))N
  0.375N ≤ f(N) ≤ 0.5N

**THE GAP:** N/8 between bounds (12.5% of N)

**CONNECTIONS:**
- Quasi-Sidon sets (Problem #840)
- Sumset structure in additive combinatorics
- Trade-off between set size and sumset coverage

**KEY INSIGHT:** √N is a critical threshold - large enough for
interesting additive structure, small enough that sumsets don't
automatically fill [1,N].
-/
theorem erdos_819_summary :
    -- Lower bound
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (f N : ℝ) ≥ (3/8 - ε) * N) ∧
    -- Upper bound
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (f N : ℝ) ≤ (1/2 + ε) * N) :=
  ⟨erdos_freud_lower, erdos_freud_upper⟩

end Erdos819
