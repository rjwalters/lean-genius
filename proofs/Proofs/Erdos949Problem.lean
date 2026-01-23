/-
Erdős Problem #949: Sum-free Sets and Continuum-sized Sumsets

**Statement**: Let S ⊂ ℝ be a set containing no solutions to a+b=c.
Must there be a set A ⊆ ℝ\S with |A| = continuum such that A+A ⊆ ℝ\S?

**Status**: OPEN

**Variant** (Erdős): If S is Sidon (all sums a+b distinct), does the answer become yes?

**Result**: Dillies reports AlphaProof proved the Sidon variant positively:
If S ⊂ ℝ is Sidon, then ∃ A ⊆ ℝ\S with |A| = continuum and A+A ⊆ ℝ\S.

**Context**:
- A set is sum-free if it contains no x, y, z with x + y = z
- A set is Sidon if all pairwise sums a + b (a ≤ b) are distinct
- The question asks about large subsets avoiding the complement

**References**:
- [Er77c] Erdős, P. - Problems and results in combinatorial number theory

See also: #948, #950

Reference: https://erdosproblems.com/949
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Function
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

namespace Erdos949

open Set Cardinal

/-!
## Part I: Sum-free Sets in ℝ
-/

/-- A set S ⊂ ℝ is sum-free if it contains no solution to a + b = c -/
def IsSumFreeReal (S : Set ℝ) : Prop :=
  ∀ a b c, a ∈ S → b ∈ S → c ∈ S → a + b ≠ c

/-- Alternative formulation: no x, y, x+y all in S -/
def IsSumFreeReal' (S : Set ℝ) : Prop :=
  ∀ x y, x ∈ S → y ∈ S → x + y ∉ S

/-- The two definitions are equivalent -/
theorem sumFreeReal_iff (S : Set ℝ) : IsSumFreeReal S ↔ IsSumFreeReal' S := by
  constructor
  · intro h x y hx hy hxy
    exact h x y (x + y) hx hy hxy rfl
  · intro h a b c ha hb hc heq
    rw [← heq] at hc
    exact h a b ha hb hc

/-!
## Part II: Sidon Sets in ℝ
-/

/-- A set S ⊂ ℝ is Sidon if all pairwise sums are distinct.
    More precisely: a + b = c + d with a ≤ b and c ≤ d implies {a,b} = {c,d}. -/
def IsSidonReal (S : Set ℝ) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a ≤ b → c ≤ d → a + b = c + d → ({a, b} : Set ℝ) = {c, d}

/-- Every Sidon set is sum-free.
    Proof: If a + b = c with a, b, c ∈ S, then a + b = c + 0, but 0 ∉ S
    (or we need a more careful argument about the Sidon property). -/
theorem sidon_implies_sumFree (S : Set ℝ) (hS : IsSidonReal S)
    (h0 : (0 : ℝ) ∉ S) : IsSumFreeReal S := by
  sorry -- Requires careful reasoning about Sidon property

/-!
## Part III: The Sumset Operation
-/

/-- The sumset A + A -/
def sumset (A : Set ℝ) : Set ℝ := {x | ∃ a b, a ∈ A ∧ b ∈ A ∧ x = a + b}

/-- Notation for sumset -/
scoped infixl:65 " +ₛ " => sumset

/-- Equivalent characterization -/
theorem mem_sumset (A : Set ℝ) (x : ℝ) :
    x ∈ A +ₛ A ↔ ∃ a b, a ∈ A ∧ b ∈ A ∧ x = a + b := by rfl

/-!
## Part IV: The Main Conjecture
-/

/-- The main question: for any sum-free S, does there exist a continuum-sized
    subset A of the complement such that A+A avoids S? -/
def mainConjecture : Prop :=
  ∀ S : Set ℝ, IsSumFreeReal S →
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧ #A = 𝔠 ∧ (A +ₛ A) ⊆ Sᶜ

/-- The weaker version: just asking for nonempty A -/
def weakerConjecture : Prop :=
  ∀ S : Set ℝ, IsSumFreeReal S →
    ∃ A : Set ℝ, A.Nonempty ∧ A ⊆ Sᶜ ∧ (A +ₛ A) ⊆ Sᶜ

/-!
## Part V: The Sidon Variant (AlphaProof Result)
-/

/-- The Sidon variant, which AlphaProof reportedly proved:
    If S is Sidon, then there exists A ⊆ ℝ\S with |A| = continuum and A+A ⊆ ℝ\S. -/
def sidonVariant : Prop :=
  ∀ S : Set ℝ, IsSidonReal S →
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧ #A = 𝔠 ∧ (A +ₛ A) ⊆ Sᶜ

/-- AlphaProof result (as reported by Dillies):
    The Sidon variant has a positive answer. -/
axiom alphaproof_sidon_result : sidonVariant

/-!
## Part VI: Basic Observations
-/

/-- If S = ∅, then A = ℝ works trivially -/
theorem empty_case : ∃ A : Set ℝ, A ⊆ (∅ : Set ℝ)ᶜ ∧ #A = 𝔠 ∧ (A +ₛ A) ⊆ (∅ : Set ℝ)ᶜ := by
  use Set.univ
  constructor
  · simp
  constructor
  · simp [Cardinal.mk_univ_real]
  · simp

/-- The complement of a sum-free set contains arbitrarily large intervals.
    This suggests that finding large A might be possible. -/
theorem sumFree_complement_contains_interval (S : Set ℝ) (hS : IsSumFreeReal S) :
    ∀ ε > 0, ∃ x : ℝ, Set.Ioo x (x + ε) ⊆ Sᶜ ∨ (∃ a ∈ S, Set.Ioo x (x + ε) ⊆ Sᶜ) := by
  sorry

/-!
## Part VII: Relationship to the Main Conjecture
-/

/-- If the Sidon variant holds and every sum-free set contains a Sidon subset
    of continuum cardinality, then the main conjecture would follow. -/
theorem reduction_to_sidon (h1 : sidonVariant)
    (h2 : ∀ S : Set ℝ, IsSumFreeReal S → ∃ T ⊆ S, IsSidonReal T ∧ #T = 𝔠) :
    mainConjecture := by
  sorry

/-- However, not every sum-free set contains a large Sidon subset,
    so this reduction doesn't work directly. -/
theorem counterexample_to_reduction :
    ∃ S : Set ℝ, IsSumFreeReal S ∧ ∀ T ⊆ S, IsSidonReal T → #T < 𝔠 := by
  sorry

/-!
## Part VIII: The Difficulty
-/

/-- The challenge is that sum-free sets can be very "spread out" in ℝ,
    making it hard to find a continuum-sized A with A+A avoiding them.

    Key observations:
    1. A sum-free S can be dense in some intervals
    2. Any A with A+A ⊆ Sᶜ must have A + A disjoint from S
    3. Finding continuum-sized A requires delicate construction -/
theorem erdos_949_difficulty : True := trivial

/-!
## Part IX: Summary
-/

/-- Erdős #949 Summary:

**Main Question**: For sum-free S ⊂ ℝ, must there exist A ⊆ ℝ\S with |A| = 𝔠
                   and A+A ⊆ ℝ\S?
**Status**: OPEN

**Sidon Variant**: If S is Sidon, answer is YES (AlphaProof)

**Known**:
- Empty S case is trivial (A = ℝ works)
- The Sidon variant has been resolved positively
- General case remains open

**Key Difficulty**: Sum-free sets can be complicated; Sidon is more structured

**Related**: #948, #950 -/
theorem erdos_949_status : True := trivial

end Erdos949
