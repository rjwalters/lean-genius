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
**f(N) is well-defined:**
The supremum exists because we're maximizing over a finite family.
-/
theorem f_exists (N : ℕ) (hN : N ≥ 4) :
    ∃ A : Finset ℕ, IsAdmissible A N ∧ (restrictedSumset A N).card = f N := by
  sorry

/-
## Part III: Trivial Bounds
-/

/--
**Upper bound: f(N) ≤ N**
The restricted sumset is a subset of [1,N].
-/
theorem f_le_N (N : ℕ) : f N ≤ N := by
  sorry

/--
**Trivial lower bound:**
Any admissible set gives |(A+A) ∩ [1,N]| ≥ |A| = √N.
-/
theorem f_ge_sqrt_N (N : ℕ) (hN : N ≥ 1) : f N ≥ Nat.sqrt N := by
  sorry

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
**The asymptotic constants:**
Lower coefficient: 3/8 = 0.375
Upper coefficient: 1/2 = 0.5
-/
def lowerCoefficient : ℚ := 3 / 8
def upperCoefficient : ℚ := 1 / 2

theorem coefficients_gap : upperCoefficient - lowerCoefficient = 1 / 8 := by
  unfold upperCoefficient lowerCoefficient
  norm_num

/-
## Part V: Why These Bounds?
-/

/--
**Lower bound construction:**
To achieve 3N/8, Erdős-Freud construct sets where sums are well-distributed.
Roughly: use arithmetic progressions with carefully chosen common difference.
-/
axiom lower_bound_construction :
  -- The construction uses sets that avoid too much additive structure
  -- while still generating many distinct sums in [1,N]
  True

/--
**Upper bound argument:**
If |A| = √N, then |A+A| ≤ |A|² = N in general.
But (A+A) ∩ [1,N] has additional constraints from the interval.
The 1/2 bound uses counting arguments on where sums can land.
-/
axiom upper_bound_argument :
  -- Sums a+b with a,b ∈ [1,N] range from 2 to 2N
  -- Only half of these are in [1,N]
  True

/-
## Part VI: Connection to Quasi-Sidon Sets
-/

/--
**Quasi-Sidon set:**
A set where sums a+b = c+d (with {a,b} ≠ {c,d}) are rare.
Sidon sets have no such coincidences; quasi-Sidon allows few.
-/
def IsQuasiSidon (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ (a b c d : ℕ), a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → a ≤ b → c ≤ d → (a, b) ≠ (c, d) →
    -- At most k such coincidences (rough definition)
    True

/--
**Problem #840 connection:**
The size of the largest quasi-Sidon set in [1,N] is related to f(N).
If A is quasi-Sidon, then |A+A| is close to |A|²/2.
-/
axiom problem_840_connection :
  -- See Problem #840 for details on quasi-Sidon sets
  True

/-
## Part VII: Extremal Examples
-/

/--
**Arithmetic progression:**
A = {1, 2, ..., k} for k = √N has |A+A| = {2, 3, ..., 2k} = 2k-1 distinct sums.
Only ~2√N sums, far from optimal.
-/
theorem arithmetic_progression_sumset (k : ℕ) :
    let A := Finset.range k
    (sumset A).card = 2 * k - 1 := by
  sorry

/--
**Random-like sets:**
Sets with "random-like" structure tend to have |A+A| ≈ |A|²/2 ≈ N/2.
This motivates the 1/2 upper bound.
-/
axiom random_like_heuristic : True

/--
**Sidon set limitation:**
A Sidon set in [1,N] has size O(√N), and |A+A| = |A|·(|A|+1)/2 ≈ N/2.
But Sidon sets in [1,N] are quite constrained.
-/
axiom sidon_set_bound : True

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

/--
**Possible true value:**
Is f(N) ~ (3/8)N? Or ~ (1/2)N? Or something in between?
This is the core open question.
-/
def trueConstant : ℝ := sorry  -- Unknown!

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
      (f N : ℝ) ≤ (1/2 + ε) * N) := by
  exact ⟨erdos_freud_lower, erdos_freud_upper⟩

/--
**Problem status:**
Erdős Problem #819 remains OPEN.
-/
theorem erdos_819_status : True := trivial

end Erdos819
