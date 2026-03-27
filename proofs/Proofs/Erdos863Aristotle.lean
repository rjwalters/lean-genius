/-
  Aristotle targets for Erdős Problem #863
  Routine supporting lemmas for automated proof search.
  See Erdos863Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable via Mathlib combinatorics
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos863Aristotle

/-- The number of representations of n as a + b with a ≤ b, a, b ∈ A -/
noncomputable def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card

/-- A is a B₂[r] set if every integer has at most r sum representations -/
def IsB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℕ, sumRepCount A n ≤ r

/-- A ⊆ {1,...,N} -/
def InRange (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- The number of representations of n as a - b with a, b ∈ A -/
noncomputable def diffRepCount (A : Finset ℕ) (n : ℤ) : ℕ :=
  (A.product A).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card

/-- A is a difference B₂[r] set if every nonzero integer has at most r
    difference representations -/
def IsDiffB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → diffRepCount A n ≤ r

/-- A singleton is B₂[r] for any r ≥ 1: the only sum representation
    of 2a from {a} is (a, a), giving sumRepCount {a} (2a) = 1 -/
theorem isB2r_singleton (a : ℕ) (r : ℕ) (hr : 1 ≤ r) : IsB2r {a} r := by sorry

/-- A singleton is a difference B₂[r] set for any r ≥ 1 -/
theorem isDiffB2r_singleton (a : ℕ) (r : ℕ) (hr : 1 ≤ r) : IsDiffB2r {a} r := by sorry

/-- Subset preserves B₂[r]: if A is B₂[r] and B ⊆ A, then B is B₂[r] -/
theorem isB2r_subset {A B : Finset ℕ} {r : ℕ} (h : IsB2r A r) (hsub : B ⊆ A) :
    IsB2r B r := by sorry

/-- Subset preserves difference B₂[r] -/
theorem isDiffB2r_subset {A B : Finset ℕ} {r : ℕ} (h : IsDiffB2r A r) (hsub : B ⊆ A) :
    IsDiffB2r B r := by sorry

/-- Counting argument: for a B₂[1] set A in {1,...,N}, the number of
    ordered pairs (a,b) with a ≤ b gives |A|(|A|+1)/2 distinct sums
    in {2,...,2N}, so |A|² ≤ 4N -/
theorem sidon_counting_bound (A : Finset ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hB : IsB2r A 1) (hR : InRange A N) :
    A.card * A.card ≤ 4 * N := by sorry

end Erdos863Aristotle
