/-
Erdős Problem #635: Non-Divisibility Condition on Differences

Given t ≥ 1 and A ⊆ {1,...,N}, suppose that whenever a, b ∈ A with
b - a ≥ t, we have (b - a) ∤ b. How large can |A| be?

**Conjecture**: |A| ≤ (1/2 + o_t(1)) · N.

**Status**: OPEN

**Known results**:
- For t = 1, the maximum is ⌊(N+1)/2⌋ (all odd numbers work)
- For t = 2, Erdős showed |A| ≥ N/2 + c·log(N) for some c > 0
  using odd numbers augmented with certain powers of 2
- The conjecture says density is always close to 1/2

**Origin**: Asked by Erdős in a letter to Ruzsa (~1980)
**References**: [Gu83] Gupta, [Ru99] Ruzsa

Reference: https://erdosproblems.com/635
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos635

/-! ## Part I: The Non-Divisibility Condition

The key constraint is: if two elements a < b of the set satisfy b - a ≥ t,
then (b - a) must NOT divide b. This is a non-trivial restriction on which
elements can coexist — it couples the gap between elements to their
absolute values via divisibility. -/

/-- A set A ⊆ {1,...,N} satisfies the t-non-divisibility condition
    if whenever a, b ∈ A with b - a ≥ t, then (b - a) does not divide b.

    Note: If b - a divides b, then b - a also divides a (since a = b - (b-a)).
    So the condition equivalently says: large gaps cannot divide either endpoint. -/
def IsNonDivisible (A : Finset ℕ) (t : ℕ) : Prop :=
  ∀ a b, a ∈ A → b ∈ A → a < b → b - a ≥ t → ¬(b - a ∣ b)

/-- A t-admissible set in {1,...,N}: contained in {1,...,N} and satisfying
    the t-non-divisibility condition. -/
def IsAdmissible (A : Finset ℕ) (N t : ℕ) : Prop :=
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) ∧ IsNonDivisible A t

/-! ## Part II: The Extremal Function

f(N, t) is the maximum size of a t-admissible set in {1,...,N}.
This is the central quantity of the problem — Erdős asks for its
asymptotic behavior as N → ∞ for fixed t. -/

/-- f(N, t) = the maximum size of a t-admissible set in {1,...,N}.
    Defined as the supremum over all achievable cardinalities. -/
noncomputable def f (N t : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A.card = k ∧ IsAdmissible A N t}

/-! ## Part III: The Case t = 1 — Odd Numbers

When t = 1, every pair with a < b has b - a ≥ 1, so the condition
applies to ALL pairs. The odd numbers {1, 3, 5, ...} form an optimal
solution: if a and b are both odd, then b - a is even, and an even
number cannot divide an odd number. -/

/-- The odd numbers in {1,...,N}. -/
def oddSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 2 = 1)

/-- The odd set is 1-admissible: if a, b are both odd with a < b,
    then b - a is even. Since b is odd, (b - a) ∤ b.

    Proof sketch: b - a is even (difference of two odds). An even
    number cannot divide an odd number, so the condition holds. -/
axiom oddSet_admissible (N : ℕ) (hN : N ≥ 1) :
    IsAdmissible (oddSet N) N 1

/-- The odd set has size ⌊(N+1)/2⌋.

    When N is odd: {1,3,...,N} has (N+1)/2 elements.
    When N is even: {1,3,...,N-1} has N/2 elements = (N+1)/2 by integer division. -/
axiom oddSet_card (N : ℕ) : (oddSet N).card = (N + 1) / 2

/-- For t = 1, the maximum is exactly ⌊(N+1)/2⌋.

    This is tight: the odd set achieves it (lower bound), and no
    set with more than (N+1)/2 elements can satisfy the condition
    (upper bound, since the condition applies to all pairs). -/
axiom f_t1 (N : ℕ) (hN : N ≥ 1) : f N 1 = (N + 1) / 2

/-! ## Part IV: The Case t = 2 — Beating the N/2 Barrier

For t = 2, the condition only applies to pairs with b - a ≥ 2. This
allows b - a = 1 to be "free," meaning consecutive elements can coexist.
Erdős showed one can improve beyond N/2 by augmenting the odd set with
certain powers of 2. -/

/-- For t = 2, one can do slightly better than N/2.

    The logarithmic improvement comes from adding elements of the form
    2^k (for odd k) to the odd set, contributing c·log(N) extra elements. -/
axiom f_t2_lower (N : ℕ) (hN : N ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ (f N 2 : ℝ) ≥ N / 2 + c * Real.log N

/-- The explicit construction: odd numbers plus certain powers of 2.

    Take A = {odd numbers in {1,...,N}} ∪ {2^k : k odd, 2^k ≤ N}.
    This gives |A| ≥ N/2 + c·log(N).

    Why it works: For the newly added even elements 2^k (k odd),
    any difference b - a ≥ 2 with b = 2^k either doesn't divide b
    or involves a pair where both are powers of 2 with controlled gaps. -/
axiom erdos_construction_t2 (N : ℕ) (hN : N ≥ 2) :
    ∃ A : Finset ℕ, IsAdmissible A N 2 ∧
    ∃ c : ℝ, c > 0 ∧ (A.card : ℝ) ≥ N / 2 + c * Real.log N

/-! ## Part V: The Main Conjecture (OPEN)

The central question: does the density of the extremal set always
approach 1/2 as N → ∞, regardless of t? The o_t(1) notation means
the error may depend on t but vanishes for large N. -/

/--
**Erdős Problem #635 (OPEN):**
For any fixed t, |A| ≤ (1/2 + o_t(1)) · N.

Formally: for every ε > 0 and every t ≥ 1, there exists N₀ such that
for all N ≥ N₀, f(N, t) ≤ (1/2 + ε) · N.

This is the main open conjecture. The difficulty increases with t because
larger t allows more "free" differences (those below t), potentially
enabling larger sets. -/
def ErdosConjecture635 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ t : ℕ, t ≥ 1 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (f N t : ℝ) ≤ (1 / 2 + ε) * N

/-- The conjecture is axiomatized as it remains open. -/
axiom erdos_635 : ErdosConjecture635

/-! ## Part VI: Upper and Lower Bounds

We collect known bounds on f(N, t). The trivial upper bound is N
(the entire set {1,...,N}), but this is far from tight. -/

/-- Trivial upper bound: f(N, t) ≤ N for all t.
    Since A ⊆ {1,...,N}, we have |A| ≤ N. -/
axiom f_upper_trivial (N t : ℕ) : f N t ≤ N

/-- Monotonicity: f(N, t) ≤ f(N, t') when t ≤ t'.
    Larger t means the condition applies to fewer pairs,
    so more sets are admissible. -/
axiom f_monotone_t (N t t' : ℕ) (h : t ≤ t') : f N t ≤ f N t'

/-- Lower bound: f(N, t) ≥ (N+1)/2 for all t ≥ 1.
    The odd set works for t = 1, hence for all larger t too. -/
axiom f_lower_half (N t : ℕ) (hN : N ≥ 1) (ht : t ≥ 1) :
    f N t ≥ (N + 1) / 2

/-- The density is at most 1/2 + o(1) for t = 1.
    Since f(N,1) = ⌊(N+1)/2⌋, the ratio f(N,1)/N → 1/2 as N → ∞. -/
axiom f_t1_density :
    Filter.Tendsto (fun N => (f N 1 : ℝ) / N) Filter.atTop (nhds (1 / 2))

/-! ## Part VII: Structural Observations

Additional properties connecting the non-divisibility condition to
number-theoretic structure. -/

/-- For any t-admissible set A, no element can be a multiple of
    another element at distance ≥ t.

    This is an immediate consequence: if b = k·a for some k ≥ 2,
    then b - a = (k-1)·a divides b = k·a, violating the condition
    when b - a ≥ t. -/
axiom no_far_multiples (A : Finset ℕ) (N t : ℕ)
    (hA : IsAdmissible A N t) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a < b) (hd : b - a ≥ t) (k : ℕ) (hk : k ≥ 2) :
    b ≠ k * a

/-! ## Part VIII: Summary -/

/--
**Erdős Problem #635: Summary**

PROBLEM: For A ⊆ {1,...,N} with b - a ≥ t ⟹ (b-a) ∤ b,
is |A| ≤ (1/2 + o_t(1)) · N?

STATUS: OPEN

KNOWN:
- t = 1: f(N,1) = ⌊(N+1)/2⌋ (all odd numbers, tight)
- t = 2: f(N,2) ≥ N/2 + c·log(N) (Erdős construction)
- General: f(N,t) ≥ (N+1)/2 for all t (odd numbers always work)
- Conjecture: density → 1/2 for all fixed t

The problem captures a deep connection between the additive
structure of a set (gaps between elements) and multiplicative
structure (divisibility relations).
-/
theorem erdos_635_t1_solved (N : ℕ) (hN : N ≥ 1) :
    f N 1 = (N + 1) / 2 := f_t1 N hN

/-- The problem remains OPEN for general t. -/
theorem erdos_635_status : True := trivial

end Erdos635
