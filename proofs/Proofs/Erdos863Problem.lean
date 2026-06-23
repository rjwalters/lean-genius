/-
# Erdős Problem #863 — B₂[r] Sum Sets vs Difference Sets

For r ≥ 2, let A ⊆ {1,...,N} be a maximal-size set where every integer
has at most r representations as a+b with a ≤ b (a B₂[r] set), and let
B ⊆ {1,...,N} be maximal where every integer has at most r representations
as a-b (a difference B₂[r] set).

If |A| ~ cᵣ √N and |B| ~ c'ᵣ √N, is cᵣ ≠ c'ᵣ for r ≥ 2?
Is c'ᵣ < cᵣ?

Known: For r = 1, c₁ = c'₁ = 1 (classical Sidon set bound).

A problem of Erdős (with Berend, and independently Freud) [Er92c].

Reference: https://erdosproblems.com/863
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/- ## B₂[r] Sets -/

/-- The number of representations of n as a + b with a ≤ b, a, b ∈ A -/
noncomputable def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card

/-- A is a B₂[r] set if every integer has at most r sum representations -/
def IsB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℕ, sumRepCount A n ≤ r

/-- The number of representations of n as a - b with a, b ∈ A -/
noncomputable def diffRepCount (A : Finset ℕ) (n : ℤ) : ℕ :=
  (A.product A).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card

/-- A is a difference B₂[r] set if every nonzero integer has at most r
    difference representations -/
def IsDiffB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → diffRepCount A n ≤ r

/- ## Containment in {1,...,N} -/

/-- A ⊆ {1,...,N} -/
def InRange (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/- ## The Constants cᵣ and c'ᵣ -/

/-- Maximum size of a B₂[r] set in {1,...,N} -/
noncomputable def maxB2rSize (r N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter (fun A => IsB2r A r ∧ InRange A N))
    Finset.card

/-- Maximum size of a difference B₂[r] set in {1,...,N} -/
noncomputable def maxDiffB2rSize (r N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter (fun A => IsDiffB2r A r ∧ InRange A N))
    Finset.card

/- ## Classical Sidon Case (r = 1) -/

/-- For r = 1 (Sidon sets), both constants equal 1:
    |A| ~ √N for both sum and difference versions -/
/- ## The Erdős Problem -/

/-- Erdős Problem 863: For r ≥ 2, do the asymptotic constants for
    B₂[r] sets and difference B₂[r] sets differ?
    The conjecture is c'ᵣ < cᵣ, meaning difference sets are smaller. -/
/-- Weaker version: just prove cᵣ ≠ c'ᵣ for some r ≥ 2 -/
/- ## Part II: Basic Properties of B₂[r] Sets -/

/-- B₂[r] property is monotone in r: B₂[r] implies B₂[r'] for r ≤ r' -/
theorem isB2r_mono {A : Finset ℕ} {r r' : ℕ} (h : IsB2r A r) (hrr : r ≤ r') :
    IsB2r A r' :=
  fun n => le_trans (h n) hrr

/-- Difference B₂[r] property is monotone in r -/
theorem isDiffB2r_mono {A : Finset ℕ} {r r' : ℕ} (h : IsDiffB2r A r)
    (hrr : r ≤ r') : IsDiffB2r A r' :=
  fun n hn => le_trans (h n hn) hrr

/-- InRange is monotone in N: A ⊆ {1,...,N} implies A ⊆ {1,...,N'} for N ≤ N' -/
theorem inRange_mono {A : Finset ℕ} {N N' : ℕ} (h : InRange A N)
    (hNN : N ≤ N') : InRange A N' :=
  fun a ha => ⟨(h a ha).1, le_trans (h a ha).2 hNN⟩

/-- Empty set is in range for any N -/
theorem inRange_empty (N : ℕ) : InRange ∅ N :=
  fun _ ha => absurd ha (Finset.not_mem_empty _)

/-- The empty set is B₂[r] for any r -/
theorem isB2r_empty (r : ℕ) : IsB2r ∅ r := by
  intro n; simp [sumRepCount]

/-- The empty set is a difference B₂[r] set for any r -/
theorem isDiffB2r_empty (r : ℕ) : IsDiffB2r ∅ r := by
  intro n _; simp [diffRepCount]

/-- Sum representation count is at most |A|²: filtering a product
    can only decrease cardinality -/
theorem sumRepCount_le_card_sq (A : Finset ℕ) (n : ℕ) :
    sumRepCount A n ≤ A.card * A.card := by
  unfold sumRepCount
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_product A A))

/-- Difference representation count is at most |A|² -/
theorem diffRepCount_le_card_sq (A : Finset ℕ) (n : ℤ) :
    diffRepCount A n ≤ A.card * A.card := by
  unfold diffRepCount
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_product A A))

/-- B₂[r] property is preserved by subsets: if A is B₂[r] and A' ⊆ A, then A' is B₂[r].

**Proof**: For any n, the pairs (a,b) ∈ A'×A' with a ≤ b, a+b = n form a subset
of the corresponding pairs in A×A, so sumRepCount A' n ≤ sumRepCount A n ≤ r. -/
theorem isB2r_subset {A A' : Finset ℕ} {r : ℕ} (h : IsB2r A r) (hsub : A' ⊆ A) :
    IsB2r A' r := by
  intro n
  calc sumRepCount A' n
      ≤ sumRepCount A n := by
        unfold sumRepCount
        exact Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.product_subset_product hsub hsub))
    _ ≤ r := h n

/-- Difference B₂[r] property is preserved by subsets. -/
theorem isDiffB2r_subset {A A' : Finset ℕ} {r : ℕ} (h : IsDiffB2r A r) (hsub : A' ⊆ A) :
    IsDiffB2r A' r := by
  intro n hn
  calc diffRepCount A' n
      ≤ diffRepCount A n := by
        unfold diffRepCount
        exact Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.product_subset_product hsub hsub))
    _ ≤ r := h n hn

/- ## Connection to Sidon Sets (Erdős #340)

A B₂[1] set is exactly a Sidon set: all pairwise sums a + b (a ≤ b) are distinct.
This connects Erdős #863 (r = 1 case) to the Sidon set formalization in Erdős #340. -/

/-- Sidon set property: all ordered sums are distinct.
    Matches IsSidonSet from Erdos340Problem.lean. -/
def IsSidonSetLocal (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- B₂[1] is equivalent to the Sidon set property.

**Forward** (B₂[1] → Sidon): If sumRepCount A n ≤ 1 for all n, then any two pairs
(a,b) and (c,d) with a+b = c+d are in the same singleton filter set, hence equal.

**Backward** (Sidon → B₂[1]): If all sums are distinct, then for each n the filter
set has at most one element, giving sumRepCount A n ≤ 1. -/
theorem isB2r_one_iff_sidon (A : Finset ℕ) : IsB2r A 1 ↔ IsSidonSetLocal A := by
  constructor
  · -- B₂[1] → Sidon: unique representation implies distinct sums
    intro h a ha b hb c hc d hd hab hcd hsum
    have h1 := h (a + b)
    unfold sumRepCount at h1
    have hmem1 : (a, b) ∈ (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a + b) := by
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha, hb⟩, hab, rfl⟩
    have hmem2 : (c, d) ∈ (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = a + b) := by
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hc, hd⟩, hcd, hsum⟩
    have heq := Finset.card_le_one.mp h1 hmem1 hmem2
    exact ⟨congr_arg Prod.fst heq, congr_arg Prod.snd heq⟩
  · -- Sidon → B₂[1]: distinct sums implies unique representation
    intro h n
    unfold sumRepCount
    rw [Finset.card_le_one]
    intro ⟨a, b⟩ hab ⟨c, d⟩ hcd
    simp only [Finset.mem_filter, Finset.mem_product] at hab hcd
    obtain ⟨⟨ha, hb⟩, hab_le, hab_sum⟩ := hab
    obtain ⟨⟨hc, hd⟩, hcd_le, hcd_sum⟩ := hcd
    have hsum : a + b = c + d := by omega
    have := h a ha b hb c hc d hd hab_le hcd_le hsum
    exact Prod.ext this.1 this.2

/-- Singleton sets are B₂[r] for any r ≥ 1. -/
theorem isB2r_singleton (a : ℕ) (r : ℕ) (hr : r ≥ 1) : IsB2r {a} r := by
  intro n
  unfold sumRepCount
  calc ({a} ×ˢ {a}).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card
      ≤ ({a} ×ˢ {a}).card := Finset.card_filter_le _ _
    _ = 1 := by simp [Finset.product_singleton_singleton]
    _ ≤ r := hr

/-- Singleton sets are difference B₂[r] for any r ≥ 1. -/
theorem isDiffB2r_singleton (a : ℕ) (r : ℕ) (hr : r ≥ 1) : IsDiffB2r {a} r := by
  intro n hn
  unfold diffRepCount
  calc ({a} ×ˢ {a}).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card
      ≤ ({a} ×ˢ {a}).card := Finset.card_filter_le _ _
    _ = 1 := by simp [Finset.product_singleton_singleton]
    _ ≤ r := hr
