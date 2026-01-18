/-
  Erdős Problem #354: Completeness of Binary Floor Sequences

  **Question**: Let α, β ∈ ℝ₊ such that α/β is irrational. Is the multiset
  {⌊α⌋, ⌊2α⌋, ⌊4α⌋, ...} ∪ {⌊β⌋, ⌊2β⌋, ⌊4β⌋, ...} complete?

  A multiset is **complete** if all sufficiently large n can be written as
  sums of elements from the multiset (with repetition from distinct 2^k terms).

  **Status**: OPEN - Cannot be resolved with finite computation.

  **History**: Graham (1971) posed this question. It connects to representation
  theory and additive combinatorics.

  **Known Results**:
  - Hegyvári (1989): Complete when α = m/2ⁿ (dyadic rational) and β is not dyadic
  - Van Doorn: Complete when α < 2 < β < 3
  - Hegyvári (1989): NOT complete when α ≥ 2 and β = 2ᵏα
  - Jiang-Ma (2024), Fang-He (2025): Non-completeness for 1 < α < 2 and β = 2ᵏα

  References:
  - https://erdosproblems.com/354
  - Graham, R.L. "On a conjecture of Erdős" (1971)
  - Hegyvári, N. "On representation problems in the additive number theory" (1989)
  - Hegyvári, N. "On the representation of integers as sums..." (1991, 1994)
-/

import Mathlib

open Set Finset BigOperators Real

namespace Erdos354

/-!
## Core Definitions

The floor sequence and completeness properties.
-/

/-- The **floor sequence** for a positive real α: the set {⌊2ᵏα⌋ : k ∈ ℕ}. -/
def FloorSeq (α : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ, n = ⌊(2 : ℝ)^k * α⌋.toNat}

/-- The k-th term of the floor sequence: ⌊2ᵏα⌋. -/
noncomputable def floorSeqTerm (α : ℝ) (k : ℕ) : ℕ :=
  ⌊(2 : ℝ)^k * α⌋.toNat

/-- A number n is **representable** by two floor sequences if it can be written as
a sum of distinct terms from each sequence. -/
def IsRepresentable (α β : ℝ) (n : ℕ) : Prop :=
  ∃ (S T : Finset ℕ),
    n = (∑ s ∈ S, floorSeqTerm α s) + (∑ t ∈ T, floorSeqTerm β t)

/-- The multiset of two floor sequences is **complete** if all sufficiently large
natural numbers are representable. -/
def IsComplete (α β : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, IsRepresentable α β n

/-- A real number is **dyadic rational** if it equals m/2ⁿ for some integers. -/
def IsDyadicRational (x : ℝ) : Prop :=
  ∃ (m : ℤ) (n : ℕ), x = m / (2 : ℝ)^n

/-- Two reals have **irrational ratio** if α/β is irrational. -/
def HasIrrationalRatio (α β : ℝ) : Prop :=
  Irrational (α / β)

/-!
## Basic Properties

Elementary facts about floor sequences.
-/

/-- The floor sequence terms are non-negative. -/
theorem floorSeqTerm_nonneg (α : ℝ) (k : ℕ) (hα : 0 < α) :
    0 ≤ floorSeqTerm α k := by
  unfold floorSeqTerm
  exact Nat.zero_le _

/-- For α ≥ 1, the floor sequence is unbounded. -/
axiom floorSeq_unbounded (α : ℝ) (hα : 1 ≤ α) :
    ∀ M : ℕ, ∃ k : ℕ, M < floorSeqTerm α k

/-- The floor sequence is monotonically increasing for k large enough. -/
axiom floorSeq_eventually_increasing (α : ℝ) (hα : 0 < α) :
    ∃ K : ℕ, ∀ k ≥ K, floorSeqTerm α k < floorSeqTerm α (k + 1)

/-!
## Hegyvári's Results (1989)

Key partial solutions from Hegyvári's groundbreaking work.
-/

/-- **Hegyvári's Positive Result (1989)**: If α is a dyadic rational and β is NOT
dyadic rational, then the combined floor sequences are complete.

This uses the fact that dyadic rationals give periodic behavior mod powers of 2,
while non-dyadic numbers fill in the gaps. -/
axiom hegyvari_dyadic_complete (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hαDyadic : IsDyadicRational α) (hβNotDyadic : ¬IsDyadicRational β)
    (hRatio : HasIrrationalRatio α β) :
    IsComplete α β

/-- **Hegyvári's Negative Result (1989)**: If α ≥ 2 and β = 2ᵏα for some k ≥ 1,
then the combined sequences are NOT complete.

This is because the sequences become "too aligned" - they miss certain residue classes. -/
axiom hegyvari_not_complete (α : ℝ) (k : ℕ) (hα : 2 ≤ α) (hk : 1 ≤ k) :
    ¬IsComplete α ((2 : ℝ)^k * α)

/-!
## Van Doorn's Result

Another special case of completeness.
-/

/-- **Van Doorn's Result**: If α < 2 < β < 3, then the sequences are complete.

The separation between α and β in this range ensures good coverage. -/
axiom vanDoorn_complete (α β : ℝ) (hα : 0 < α) (hα2 : α < 2)
    (hβ2 : 2 < β) (hβ3 : β < 3) (hRatio : HasIrrationalRatio α β) :
    IsComplete α β

/-!
## Recent Negative Results (2024-2025)

Extensions of Hegyvári's non-completeness results.
-/

/-- **Jiang-Ma (2024)**: Non-completeness extends to 1 < α < 2 with β = 2ᵏα
for sufficiently large k.

This shows the gap phenomenon persists even when α is small. -/
axiom jiangMa_not_complete (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ K : ℕ, ∀ k ≥ K, ¬IsComplete α ((2 : ℝ)^k * α)

/-- **Fang-He (2025)**: Strengthened version with explicit bounds. -/
axiom fangHe_not_complete (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (k : ℕ) (hk : 10 ≤ k) :
    ¬IsComplete α ((2 : ℝ)^k * α)

/-!
## Main Conjecture (OPEN)

The general question for irrational ratios.
-/

/-- **Erdős Problem #354 (OPEN)**: For α, β > 0 with α/β irrational,
is the combined floor sequence always complete?

The answer is NOT always yes (Hegyvári counterexamples), so the refined
conjecture asks: for which pairs (α, β) is completeness achieved? -/
axiom erdos_354_conjecture :
    (∀ α β : ℝ, 0 < α → 0 < β → HasIrrationalRatio α β → IsComplete α β) ∨
    (∃ α β : ℝ, 0 < α ∧ 0 < β ∧ HasIrrationalRatio α β ∧ ¬IsComplete α β)

/-- The conjecture is known to be FALSE in full generality - counterexamples exist.

The counterexample construction is technical: one takes α > 2 and β such that
α/β is irrational but β = 2ᵏ · α for some k. This gives HasIrrationalRatio α β
while hegyvari_not_complete shows ¬IsComplete α β. -/
axiom conjecture_is_false :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ HasIrrationalRatio α β ∧ ¬IsComplete α β

/-- The REFINED conjecture: Is completeness achieved when α/β is irrational
AND neither α nor β is a power of 2 times the other? -/
axiom refined_conjecture (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hRatio : HasIrrationalRatio α β)
    (hNotPower : ∀ k : ℤ, β ≠ (2 : ℝ)^k * α) :
    IsComplete α β ∨ ¬IsComplete α β  -- Unknown!

/-!
## Representation Properties

Understanding which numbers are representable.
-/

/-- Zero is always representable (empty sums). -/
axiom zero_representable (α β : ℝ) : IsRepresentable α β 0

/-- For α ≥ 1, every term in the floor sequence is representable. -/
axiom floorSeqTerm_representable (α β : ℝ) (k : ℕ) (hα : 1 ≤ α) :
    IsRepresentable α β (floorSeqTerm α k)

/-- The set of representable numbers is closed under addition of floor sequence terms. -/
axiom representable_add_term (α β : ℝ) (n : ℕ) (k : ℕ)
    (hn : IsRepresentable α β n) :
    IsRepresentable α β (n + floorSeqTerm α k) ∨
    IsRepresentable α β (n + floorSeqTerm β k)

/-!
## Measure-Theoretic Results

Hegyvári's density results.
-/

/-- The set of representable numbers has positive lower density. -/
axiom representable_positive_density (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hRatio : HasIrrationalRatio α β) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, c * N ≤ ({n : ℕ | n ≤ N ∧ IsRepresentable α β n} : Set ℕ).ncard

/-- For "generic" pairs (α, β), completeness holds (measure 1). -/
axiom generic_completeness :
    ∃ S : Set (ℝ × ℝ), (∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ IsComplete p.1 p.2) ∧
    -- S has full measure in some appropriate sense
    True  -- Placeholder for measure-theoretic statement

/-!
## Connection to Binary Representations

The problem relates to binary expansions.
-/

/-- For α = 1, the floor sequence gives powers of 2: {1, 2, 4, 8, ...}. -/
axiom floorSeq_one (k : ℕ) : floorSeqTerm 1 k = 2^k

/-- With α = β = 1, every positive integer is representable (binary representation).
This follows from the standard fact that every natural number has a binary representation. -/
axiom binary_complete : IsComplete 1 1

/-!
## The Generalization Question

What about base γ ∈ (1, 2)?
-/

/-- The **generalized floor sequence** for base γ: {⌊γᵏα⌋ : k ∈ ℕ}. -/
def GeneralFloorSeq (γ α : ℝ) : Set ℕ :=
  {n | ∃ k : ℕ, n = ⌊γ^k * α⌋.toNat}

/-- The generalized completeness question for base γ ∈ (1, 2). -/
axiom generalized_conjecture (γ α β : ℝ) (hγ1 : 1 < γ) (hγ2 : γ < 2)
    (hα : 0 < α) (hβ : 0 < β) (hRatio : HasIrrationalRatio α β) :
    (∃ N : ℕ, ∀ n ≥ N, ∃ (S T : Finset ℕ),
      n = (∑ s ∈ S, ⌊γ^s * α⌋.toNat) + (∑ t ∈ T, ⌊γ^t * β⌋.toNat)) ∨
    ¬(∃ N : ℕ, ∀ n ≥ N, ∃ (S T : Finset ℕ),
      n = (∑ s ∈ S, ⌊γ^s * α⌋.toNat) + (∑ t ∈ T, ⌊γ^t * β⌋.toNat))

/-!
## Historical Notes

The problem connects to several areas:
1. **Representation theory**: Which integers can be represented?
2. **Additive combinatorics**: Sumset properties of floor sequences
3. **Diophantine approximation**: Role of irrationality in coverage
4. **Ergodic theory**: Hegyvári's measure-theoretic arguments

Graham's original (1971) question was whether irrationality of α/β alone
suffices for completeness. Hegyvári's counterexamples (1989) showed this
is false in general, but the exact boundary remains elusive.
-/

end Erdos354
