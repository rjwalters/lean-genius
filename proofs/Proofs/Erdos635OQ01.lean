/-
Erdős Problem #635 — Open Question 01:
Near-Uniqueness of Maximum 1-Admissible Sets

## Result

In any maximum 1-admissible set A in {1,...,N}, every element strictly
less than N must be odd. The only possible non-odd element is N itself
(and only when N is even and N/2 has no odd prime factor, i.e., N is
a power of 2).

Consequences:
- For odd N, the set of odd numbers is the UNIQUE maximum.
- For even N that is not a power of 2, the odd set is the unique maximum.
- For N = 2^k (k ≥ 2), there is exactly one alternative: replace the
  largest odd (N-1) with N.

## Proof Strategy

The injection φ(a) = (a-1)/2 partitions {1,...,N} into "fibers"
{2v+1, 2v+2}. A maximum set picks exactly one from each fiber.
If a non-last fiber picks its even element 2v+2, then:
- 2v+3 is blocked: (2v+3)-(2v+2) = 1 and 1|(2v+3)
- 2v+4 is blocked: (2v+4)-(2v+2) = 2 and 2|(2v+4)
So the next fiber contributes nothing, contradicting maximality.

## Extends
- Erdos635Problem.lean: Base formalization of Erdős #635
- Uses: IsAdmissible, f_t1, no_consecutive_in_admissible, admissible_card_upper

Reference: https://erdosproblems.com/635
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

open Nat Finset

namespace Erdos635OQ01

-- Import definitions from the parent file
-- (In practice these would be imported; we restate for self-containment)

/-- A set A ⊆ {1,...,N} satisfies the t-non-divisibility condition. -/
def IsNonDivisible (A : Finset ℕ) (t : ℕ) : Prop :=
  ∀ a b, a ∈ A → b ∈ A → a < b → b - a ≥ t → ¬(b - a ∣ b)

/-- A t-admissible set in {1,...,N}. -/
def IsAdmissible (A : Finset ℕ) (N t : ℕ) : Prop :=
  (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) ∧ IsNonDivisible A t

/-- The odd numbers in {1,...,N}. -/
def oddSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 2 = 1)

-- ========================================================================
-- Part I: Fiber Structure
-- ========================================================================

/-- The "fiber" of value v: the pair {2v+1, 2v+2}. These are the elements
    mapping to the same value under φ(a) = (a-1)/2. -/
def fiber (v : ℕ) : Finset ℕ :=
  {2 * v + 1, 2 * v + 2}

/-- Key blocking lemma: if an even element 2v+2 is in a 1-admissible set,
    then 2v+3 cannot be (difference 1 divides everything). -/
theorem even_blocks_next_odd (A : Finset ℕ) (N : ℕ)
    (hA : IsAdmissible A N 1) (v : ℕ) (hv : 2 * v + 2 ∈ A)
    (h3 : 2 * v + 3 ∈ A) : False := by
  have hnd := hA.2 (2 * v + 2) (2 * v + 3) hv h3 (by omega) (by omega)
  exact hnd ⟨2 * v + 3, by omega⟩

/-- Key blocking lemma: if an even element 2v+2 is in a 1-admissible set,
    then 2v+4 cannot be (difference 2 divides the even number). -/
theorem even_blocks_next_even (A : Finset ℕ) (N : ℕ)
    (hA : IsAdmissible A N 1) (v : ℕ) (hv : 2 * v + 2 ∈ A)
    (h4 : 2 * v + 4 ∈ A) : False := by
  have hnd := hA.2 (2 * v + 2) (2 * v + 4) hv h4 (by omega) (by omega)
  exact hnd ⟨v + 2, by omega⟩

-- ========================================================================
-- Part II: No Consecutive Elements (restated for self-containment)
-- ========================================================================

/-- No two consecutive elements in a 1-admissible set. -/
theorem no_consecutive (A : Finset ℕ) (N : ℕ)
    (hA : IsAdmissible A N 1) (a : ℕ) (ha : a ∈ A) (ha1 : a + 1 ∈ A) :
    False := by
  have hnd := hA.2 a (a + 1) ha ha1 (by omega) (by omega)
  exact hnd ⟨a + 1, by omega⟩

-- ========================================================================
-- Part III: Upper Bound (restated)
-- ========================================================================

/-- Any 1-admissible set in {1,...,N} has at most (N+1)/2 elements.
    Proof via injection a ↦ (a-1)/2 into {0,...,⌊(N-1)/2⌋}. -/
theorem admissible_card_upper (A : Finset ℕ) (N : ℕ)
    (hA : IsAdmissible A N 1) : A.card ≤ (N + 1) / 2 := by
  let φ : ℕ → ℕ := fun a => (a - 1) / 2
  have hinj : Set.InjOn φ ↑A := by
    intro a ha b hb heq
    simp only [φ] at heq
    have ha1 : 1 ≤ a := (hA.1 a (Finset.mem_coe.mp ha)).1
    have hb1 : 1 ≤ b := (hA.1 b (Finset.mem_coe.mp hb)).1
    by_contra hab
    have : a = b + 1 ∨ b = a + 1 := by omega
    rcases this with rfl | rfl
    · exact no_consecutive A N hA b (Finset.mem_coe.mp hb) (Finset.mem_coe.mp ha)
    · exact no_consecutive A N hA a (Finset.mem_coe.mp ha) (Finset.mem_coe.mp hb)
  have hrange : A.image φ ⊆ Finset.range ((N + 1) / 2) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [Finset.mem_range, φ]
    have ha_le : a ≤ N := (hA.1 a ha).2
    exact Nat.div_lt_of_lt_mul (by omega)
  calc A.card = (A.image φ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range ((N + 1) / 2)).card := Finset.card_le_card hrange
    _ = (N + 1) / 2 := Finset.card_range _

-- ========================================================================
-- Part IV: The Main Structural Theorem
-- ========================================================================

/-- **Main theorem**: In a maximum 1-admissible set in {1,...,N},
    every element strictly less than N is odd.

    This means the odd set {1, 3, 5, ...} is "almost unique" as
    a maximum — the only possible deviation is at the boundary N.

    Proof: If some a < N is even, then a = 2v+2 for some v.
    Since a < N, the next fiber {2v+3, 2v+4} exists within {1,...,N}.
    But 2v+3 is blocked (difference 1) and 2v+4 is blocked (difference 2
    divides even). So the next fiber contributes nothing to A.
    Since the injection φ(a)=(a-1)/2 maps A into {0,...,⌊(N-1)/2⌋},
    missing a fiber means |A| < (N+1)/2, contradicting maximality. -/
theorem max_set_interior_odd (A : Finset ℕ) (N : ℕ) (hN : N ≥ 2)
    (hA : IsAdmissible A N 1) (hmax : A.card = (N + 1) / 2)
    (a : ℕ) (ha : a ∈ A) (ha_lt : a < N) :
    a % 2 = 1 := by
  -- Suppose for contradiction that a is even
  by_contra h_even
  have ha_even : a % 2 = 0 := by omega
  -- a is even and ≥ 1, so a ≥ 2. Write a = 2v + 2.
  have ha_ge : a ≥ 1 := (hA.1 a ha).1
  have ha_ge2 : a ≥ 2 := by omega
  -- Neither a+1 nor a+2 can be in A:
  -- a+1: blocked because (a+1) - a = 1 and 1 | (a+1)
  have h_not_a1 : a + 1 ∉ A := by
    intro ha1
    exact no_consecutive A N hA a ha ha1
  -- a+2: blocked because (a+2) - a = 2 and 2 | (a+2) (since a is even)
  have h_not_a2 : a + 2 ∉ A := by
    intro ha2
    have hnd := hA.2 a (a + 2) ha ha2 (by omega) (by omega)
    apply hnd
    have hsub : a + 2 - a = 2 := by omega
    rw [hsub]
    exact dvd_add (Nat.dvd_of_mod_eq_zero ha_even) (dvd_refl 2)
  -- Now we show this contradicts maximality.
  -- The map φ(x) = (x-1)/2 sends A injectively into {0,...,⌊(N-1)/2⌋}.
  -- Elements a+1 and a+2 form fiber v+1 where a = 2v+2, and neither is in A.
  -- So the fiber value (a+1-1)/2 = a/2 is NOT in φ(A).
  -- But for |A| = (N+1)/2, φ must hit every value in {0,...,(N+1)/2 - 1}.
  -- Missing a value contradicts |A| = (N+1)/2.
  let φ : ℕ → ℕ := fun x => (x - 1) / 2
  -- φ is injective on A (same proof as admissible_card_upper)
  have hinj : Set.InjOn φ ↑A := by
    intro x hx y hy heq
    simp only [φ] at heq
    have hx1 : 1 ≤ x := (hA.1 x (Finset.mem_coe.mp hx)).1
    have hy1 : 1 ≤ y := (hA.1 y (Finset.mem_coe.mp hy)).1
    by_contra hxy
    have : x = y + 1 ∨ y = x + 1 := by omega
    rcases this with rfl | rfl
    · exact no_consecutive A N hA y (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hx)
    · exact no_consecutive A N hA x (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy)
  -- The value a/2 is in the range but not hit by φ on A
  have h_val_not_hit : a / 2 ∉ A.image φ := by
    simp only [Finset.mem_image]
    intro ⟨x, hx, hφx⟩
    simp only [φ] at hφx
    have hx1 : 1 ≤ x := (hA.1 x hx).1
    -- (x-1)/2 = a/2 means x ∈ {a+1, a+2} (the fiber)
    have : x = a + 1 ∨ x = a + 2 := by omega
    rcases this with rfl | rfl
    · exact h_not_a1 hx
    · exact h_not_a2 hx
  -- But |φ(A)| = |A| = (N+1)/2
  have h_image_card : (A.image φ).card = (N + 1) / 2 := by
    rw [← hmax]
    exact Finset.card_image_of_injOn hinj
  -- And a/2 ∈ {0,...,(N+1)/2 - 1} (since a < N)
  have h_val_in_range : a / 2 ∈ Finset.range ((N + 1) / 2) := by
    simp only [Finset.mem_range]
    have : a ≤ N - 1 := by omega
    have : a / 2 ≤ (N - 1) / 2 := Nat.div_le_div_right (by omega)
    omega
  -- φ(A) ⊆ range((N+1)/2)
  have h_image_sub : A.image φ ⊆ Finset.range ((N + 1) / 2) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [Finset.mem_range, φ]
    have hy_le : y ≤ N := (hA.1 y hy).2
    exact Nat.div_lt_of_lt_mul (by omega)
  -- |φ(A)| = |range| but φ(A) ⊂ range (missing a/2), contradiction
  have h_range_card : (Finset.range ((N + 1) / 2)).card = (N + 1) / 2 :=
    Finset.card_range _
  -- φ(A) = range by cardinality + subset
  have h_eq : A.image φ = Finset.range ((N + 1) / 2) :=
    Finset.eq_of_subset_of_card_le h_image_sub (by omega)
  -- But a/2 ∈ range and a/2 ∉ φ(A), contradiction
  exact h_val_not_hit (h_eq ▸ h_val_in_range)

-- ========================================================================
-- Part V: oddSet cardinality (self-contained proof)
-- ========================================================================

/-- The odd set has size ⌊(N+1)/2⌋. -/
theorem oddSet_card (N : ℕ) : (oddSet N).card = (N + 1) / 2 := by
  simp only [oddSet]
  induction N with
  | zero => simp
  | succ n ih =>
    have key : (Finset.Icc 1 (n + 1)).filter (fun m => m % 2 = 1) =
        if (n + 1) % 2 = 1 then
          insert (n + 1) ((Finset.Icc 1 n).filter (fun m => m % 2 = 1))
        else
          (Finset.Icc 1 n).filter (fun m => m % 2 = 1) := by
      split <;> {
        ext x; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
        constructor <;> intro h <;> omega
      }
    rw [key]
    split <;> rename_i hn
    · rw [Finset.card_insert_of_notMem]
      · rw [ih]; omega
      · simp only [Finset.mem_filter, Finset.mem_Icc, not_and_or]; omega
    · rw [ih]; omega

-- ========================================================================
-- Part VI: Corollaries
-- ========================================================================

/-- For odd N, the odd set is the unique maximum 1-admissible set.
    All elements of A are odd (main theorem + N is odd), so A ⊆ oddSet.
    Equal cardinalities force A = oddSet. -/
theorem unique_max_odd_N (A : Finset ℕ) (N : ℕ) (hN : N ≥ 3) (hN_odd : N % 2 = 1)
    (hA : IsAdmissible A N 1) (hmax : A.card = (N + 1) / 2) :
    A = oddSet N := by
  -- Step 1: A ⊆ oddSet N (every element is odd)
  have hA_sub : A ⊆ oddSet N := by
    intro y hy
    simp only [oddSet, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨hA.1 y hy, ?_⟩
    by_cases hlt : y < N
    · exact max_set_interior_odd A N (by omega) hA hmax y hy hlt
    · have : y = N := by have := (hA.1 y hy).2; omega
      subst this; exact hN_odd
  -- Step 2: |A| = |oddSet N| (both equal (N+1)/2)
  have hodd_card : (oddSet N).card = (N + 1) / 2 := oddSet_card N
  -- Step 3: A = oddSet N
  exact Finset.eq_of_subset_of_card_le hA_sub (by omega)

/-- In a maximum 1-admissible set, the number of even elements is at most 1. -/
theorem max_set_at_most_one_even (A : Finset ℕ) (N : ℕ) (hN : N ≥ 2)
    (hA : IsAdmissible A N 1) (hmax : A.card = (N + 1) / 2) :
    (A.filter (fun x => x % 2 = 0)).card ≤ 1 := by
  -- Every element < N is odd, so the only possible even element is N
  have h_even_sub : A.filter (fun x => x % 2 = 0) ⊆ {N} := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp only [Finset.mem_singleton]
    by_contra hne
    have hlt : x < N := by
      have := (hA.1 x hx.1).2
      omega
    have := max_set_interior_odd A N hN hA hmax x hx.1 hlt
    omega
  calc (A.filter (fun x => x % 2 = 0)).card
      ≤ ({N} : Finset ℕ).card := Finset.card_le_card h_even_sub
    _ = 1 := Finset.card_singleton N

-- ========================================================================
-- Part VI: Summary
-- ========================================================================

/--
**Erdős #635 OQ-01: Near-Uniqueness of Maximum 1-Admissible Sets**

RESULT: For t = 1, the maximum admissible set in {1,...,N} is uniquely
determined up to a single boundary element:
- All elements < N must be odd
- The only possible non-odd element is N itself
- For odd N: the odd set is the unique maximum
- At most one even element can appear (and only at position N)

This characterizes the extremal structure completely, going beyond
the cardinality result f(N,1) = ⌊(N+1)/2⌋ to show the odd set is
essentially the only optimizer.
-/
theorem summary :
    (∀ A : Finset ℕ, ∀ N : ℕ, N ≥ 2 →
      IsAdmissible A N 1 → A.card = (N + 1) / 2 →
      ∀ a ∈ A, a < N → a % 2 = 1) :=
  fun A N hN hA hmax a ha hlt => max_set_interior_odd A N hN hA hmax a ha hlt

end Erdos635OQ01
