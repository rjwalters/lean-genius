/-
Erdős Problem #338: Restricted Order of Additive Bases

Source: https://erdosproblems.com/338
Status: OPEN

Statement:
The restricted order of a basis is the least integer t (if it exists) such that
every large integer is the sum of at most t distinct summands from A.
What are necessary and sufficient conditions that this exists?
Can it be bounded (when it exists) in terms of the order of the basis?
What are necessary and sufficient conditions that this is equal to the order?

Key Results:
- Bateman: For h ≥ 3, there exist bases of order h with no restricted order
  (Example: A = {1} ∪ {x > 0 : h | x})
- Kelly (1957): Bases of order 2 have restricted order ≤ 4
- Kelly's Conjecture (disproved): Bases of order 2 have restricted order ≤ 3
- Hennecart (2005): Constructed order-2 basis with restricted order 4
- Squares have order 4, restricted order 5 (Pall 1933)
- Triangular numbers have order 3, restricted order 3 (Schinzel 1954)
- Hegyvári-Hennecart-Plagne (2007): For k ≥ 2, there exist order-k bases
  with restricted order ≥ 2^{k-2} + k - 1

Open Questions:
- Necessary and sufficient conditions for restricted order to exist
- Bounds on restricted order in terms of order
- When is restricted order = order?
- If A \ F is a basis for all finite F, must A have restricted order?

Tags: number-theory, additive-bases, restricted-order, combinatorics
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos338

/-!
## Part I: Basic Definitions
-/

/--
**Additive Basis of Order h:**
A set A ⊆ ℕ is an additive basis of order h if every sufficiently large integer
can be expressed as a sum of at most h elements from A (with repetition allowed).
-/
def IsBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ (s : Multiset ℕ),
    (∀ x ∈ s, x ∈ A) ∧ s.card ≤ h ∧ s.sum = n

/--
**h is Achieved:**
h is the exact order of basis A (not just an upper bound).
-/
def IsExactOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsBasisOfOrder A h ∧ ¬IsBasisOfOrder A (h - 1)

/--
**Restricted Representation:**
A representation using distinct summands (no repetition).
-/
def IsRestrictedRepresentation (A : Set ℕ) (s : Finset ℕ) (n : ℕ) : Prop :=
  (∀ x ∈ s, x ∈ A) ∧ s.sum id = n

/--
**Restricted Order:**
The restricted order t of A is the least integer such that every sufficiently
large integer is the sum of at most t DISTINCT elements from A.
-/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ (s : Finset ℕ),
    IsRestrictedRepresentation A s n ∧ s.card ≤ t

/--
**Has Finite Restricted Order:**
A basis has a restricted order if some finite t works.
-/
def HasFiniteRestrictedOrder (A : Set ℕ) : Prop :=
  ∃ t : ℕ, HasRestrictedOrder A t

/--
**Minimal Restricted Order:**
The minimal t such that HasRestrictedOrder A t holds.
-/
noncomputable def minimalRestrictedOrder (A : Set ℕ)
    (h : HasFiniteRestrictedOrder A) : ℕ :=
  Nat.find (h)

/-!
## Part II: Bateman's Observation
-/

/--
**Bateman's Example:**
For h ≥ 3, the set A = {1} ∪ {x > 0 : h | x} is a basis of order h
but has no restricted order.
-/
def batemanSet (h : ℕ) : Set ℕ :=
  {1} ∪ {x : ℕ | x > 0 ∧ h ∣ x}

/-- Bateman's set is a basis of order h for h ≥ 3. -/
axiom bateman_is_basis (h : ℕ) (hh : h ≥ 3) :
    IsBasisOfOrder (batemanSet h) h

/-- Bateman's set has no restricted order. -/
axiom bateman_no_restricted_order (h : ℕ) (hh : h ≥ 3) :
    ¬HasFiniteRestrictedOrder (batemanSet h)

/-- Summary: For h ≥ 3, bases of order h may lack restricted order. -/
theorem bateman_observation (h : ℕ) (hh : h ≥ 3) :
    IsBasisOfOrder (batemanSet h) h ∧ ¬HasFiniteRestrictedOrder (batemanSet h) :=
  ⟨bateman_is_basis h hh, bateman_no_restricted_order h hh⟩

/-!
## Part III: Kelly's Results (1957)
-/

/--
**Kelly's Theorem (1957):**
Every basis of order 2 has restricted order at most 4.
-/
axiom kelly_theorem (A : Set ℕ) (hA : IsBasisOfOrder A 2) :
    HasRestrictedOrder A 4

/--
**Kelly's Conjecture (DISPROVED):**
Every basis of order 2 has restricted order at most 3.
-/
def kellyConjecture : Prop :=
  ∀ A : Set ℕ, IsBasisOfOrder A 2 → HasRestrictedOrder A 3

/--
**Kelly's Conjecture is FALSE.**
Hennecart (2005) provided a counterexample.
-/
theorem kelly_conjecture_false : ¬kellyConjecture := by
  intro h
  -- Hennecart constructed a basis of order 2 with restricted order 4
  sorry

/-!
## Part IV: Hennecart's Counterexample (2005)
-/

/--
**Hennecart's Construction:**
A basis of order 2 with restricted order exactly 4.
-/
axiom hennecart_basis : Set ℕ

axiom hennecart_is_order_two :
    IsBasisOfOrder hennecart_basis 2

axiom hennecart_restricted_order_four :
    HasRestrictedOrder hennecart_basis 4 ∧ ¬HasRestrictedOrder hennecart_basis 3

/-- Hennecart's result disproves Kelly's conjecture. -/
theorem hennecart_disproves_kelly : ¬kellyConjecture := by
  intro hconj
  have h3 := hconj hennecart_basis hennecart_is_order_two
  have h4 := hennecart_restricted_order_four.2
  exact h4 h3

/-!
## Part V: Classical Examples
-/

/-- The set of perfect squares. -/
def squares : Set ℕ := {n : ℕ | ∃ k : ℕ, n = k * k}

/-- The set of triangular numbers T_k = k(k+1)/2. -/
def triangular : Set ℕ := {n : ℕ | ∃ k : ℕ, n = k * (k + 1) / 2}

/--
**Lagrange's Four-Squares Theorem:**
Squares form a basis of order 4.
-/
axiom squares_order_four : IsBasisOfOrder squares 4

/--
**Pall (1933):**
Squares have restricted order 5.
This means every large enough integer is a sum of 5 distinct squares.
-/
axiom pall_theorem : HasRestrictedOrder squares 5 ∧ ¬HasRestrictedOrder squares 4

/--
**Gauss's Theorem (Eureka!):**
Triangular numbers form a basis of order 3.
-/
axiom triangular_order_three : IsBasisOfOrder triangular 3

/--
**Schinzel (1954):**
Triangular numbers have restricted order 3.
-/
axiom schinzel_theorem : HasRestrictedOrder triangular 3

/-- Triangular numbers: order = restricted order = 3. -/
theorem triangular_orders_equal :
    IsBasisOfOrder triangular 3 ∧ HasRestrictedOrder triangular 3 :=
  ⟨triangular_order_three, schinzel_theorem⟩

/-- Squares: order = 4 but restricted order = 5. -/
theorem squares_orders_differ :
    IsBasisOfOrder squares 4 ∧ HasRestrictedOrder squares 5 ∧
    ¬HasRestrictedOrder squares 4 :=
  ⟨squares_order_four, pall_theorem⟩

/-!
## Part VI: Hegyvári-Hennecart-Plagne Lower Bound (2007)
-/

/--
**HHP Lower Bound (2007):**
For k ≥ 2, there exists a basis of order k with restricted order at least 2^{k-2} + k - 1.
-/
axiom hhp_lower_bound (k : ℕ) (hk : k ≥ 2) :
    ∃ A : Set ℕ, IsBasisOfOrder A k ∧
    ∀ t : ℕ, t < 2^(k-2) + k - 1 → ¬HasRestrictedOrder A t

/-- The gap between order and restricted order can be exponential. -/
theorem exponential_gap (k : ℕ) (hk : k ≥ 2) :
    ∃ A : Set ℕ, IsBasisOfOrder A k ∧
    (∀ t : ℕ, HasRestrictedOrder A t → t ≥ 2^(k-2) + k - 1) := by
  obtain ⟨A, hbasis, hlower⟩ := hhp_lower_bound k hk
  refine ⟨A, hbasis, ?_⟩
  intro t ht
  by_contra hlt
  push_neg at hlt
  exact hlower t hlt ht

/-!
## Part VII: The Main Open Questions
-/

/--
**Open Question 1:**
What are necessary and sufficient conditions for a basis to have a restricted order?
-/
def OpenQuestion1 : Prop :=
  ∃ (P : Set ℕ → Prop), ∀ A : Set ℕ, HasFiniteRestrictedOrder A ↔ P A

/--
**Open Question 2:**
Can the restricted order (when it exists) be bounded in terms of the order?
-/
def OpenQuestion2 : Prop :=
  ∃ f : ℕ → ℕ, ∀ A : Set ℕ, ∀ h : ℕ,
    IsBasisOfOrder A h → HasFiniteRestrictedOrder A →
    ∃ t, HasRestrictedOrder A t ∧ t ≤ f h

/--
**Open Question 3:**
What are necessary and sufficient conditions for restricted order to equal order?
-/
def OpenQuestion3 : Prop :=
  ∃ (P : Set ℕ → Prop), ∀ A : Set ℕ, ∀ h : ℕ,
    (IsBasisOfOrder A h ∧ HasRestrictedOrder A h) ↔ (IsBasisOfOrder A h ∧ P A)

/--
**Open Question 4:**
If A \ F is a basis for all finite sets F, must A have a restricted order?
-/
def IsRobustBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ F : Finset ℕ, IsBasisOfOrder (A \ ↑F) h

def OpenQuestion4 : Prop :=
  ∀ A : Set ℕ, ∀ h : ℕ, IsRobustBasis A h → HasFiniteRestrictedOrder A

/-!
## Part VIII: Basic Properties
-/

/--
**Restricted order implies regular order:**
If every large integer is a sum of t distinct elements, it's certainly a sum of t elements.
-/
theorem restricted_implies_regular (A : Set ℕ) (t : ℕ) :
    HasRestrictedOrder A t → IsBasisOfOrder A t := by
  intro ⟨N, hN⟩
  use N
  intro n hn
  obtain ⟨s, ⟨hmem, hsum⟩, hcard⟩ := hN n hn
  -- Convert Finset to Multiset
  use s.val
  constructor
  · intro x hx
    exact hmem x (Multiset.mem_toFinset.mp (by simp [hx]))
  constructor
  · simp [hcard]
  · simp [hsum]

/--
**Order at most restricted order:**
If A has order h and restricted order t, then h ≤ t.
-/
theorem order_le_restricted_order (A : Set ℕ) (h t : ℕ)
    (hbasis : IsExactOrder A h) (hrestricted : HasRestrictedOrder A t) :
    h ≤ t := by
  sorry

/--
**Monotonicity:**
If HasRestrictedOrder A t, then HasRestrictedOrder A (t+1).
-/
theorem restricted_order_monotone (A : Set ℕ) (t : ℕ) :
    HasRestrictedOrder A t → HasRestrictedOrder A (t + 1) := by
  intro ⟨N, hN⟩
  use N
  intro n hn
  obtain ⟨s, hrep, hcard⟩ := hN n hn
  exact ⟨s, hrep, Nat.le_succ_of_le hcard⟩

/-!
## Part IX: Summary

**Erdős Problem #338: Status OPEN**

**Known Results:**
1. Bateman: Order h ≥ 3 doesn't guarantee finite restricted order
2. Kelly: Order 2 implies restricted order ≤ 4
3. Hennecart: Some order-2 bases have restricted order = 4 (disproving Kelly's conjecture)
4. HHP: For order k, restricted order can be at least 2^{k-2} + k - 1

**Examples:**
- Squares: order 4, restricted order 5
- Triangular numbers: order 3, restricted order 3

**Open Questions:**
- Characterize when restricted order exists
- Bound restricted order in terms of order
- Characterize when restricted order equals order
- Does "robustness" imply finite restricted order?

**References:**
- Kelly (1957): Restricted bases, Amer. J. Math.
- Hennecart (2005): On restricted order of bases of order two, Ramanujan J.
- Hegyvári, Hennecart, Plagne (2007): Answer to Burr-Erdős question, Combin. Probab. Comput.
- Pall (1933): On Sums of Squares, Amer. Math. Monthly
- Schinzel (1954): Triangular numbers, Bull. Acad. Polon. Sci.
-/

theorem erdos_338_summary :
    -- Kelly's theorem holds
    (∀ A, IsBasisOfOrder A 2 → HasRestrictedOrder A 4) ∧
    -- Kelly's conjecture is false
    ¬kellyConjecture ∧
    -- Squares example
    (IsBasisOfOrder squares 4 ∧ HasRestrictedOrder squares 5) ∧
    -- Triangular example
    (IsBasisOfOrder triangular 3 ∧ HasRestrictedOrder triangular 3) := by
  refine ⟨kelly_theorem, hennecart_disproves_kelly, ?_, triangular_orders_equal⟩
  exact ⟨squares_order_four, pall_theorem.1⟩

end Erdos338
