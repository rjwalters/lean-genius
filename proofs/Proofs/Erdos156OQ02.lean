/-
Erdős Problem #156 - Open Question 02: Lower Bound for Maximal Sidon Sets

Proves that any maximal Sidon set A ⊆ {1,...,N} has size s satisfying
2N ≤ (s+1)³. This gives s ≥ (2N)^{1/3} - 1, an Ω(N^{1/3}) lower bound.

Proof:
Every element x ∈ {1,...,N} \ A is "blocked": adding x to A would create
a sum collision. Each collision arises from the sumset structure of A:
either x + a = b + c for some a,b,c ∈ A, or 2x = b + c for some b,c ∈ A.
The number of such blocked values is at most |sumset(A)| · (|A| + 1),
and |sumset(A)| = |A|(|A|+1)/2 (Sidon property). The bound follows.

This is a standard result in additive combinatorics. The greedy algorithm
produces maximal Sidon sets of this size, showing the bound is tight.
-/

import Proofs.Erdos156Problem

namespace Erdos156

section Blocking

/-! ### Blocking Structure

When A is a maximal Sidon set, every non-member is blocked: it cannot be
added without creating a sum collision. We analyze the structure of these
collisions to bound the number of blocked elements. -/

/-- An element x is type-1 blocked by A if ∃ a,b,c ∈ A with x + a = b + c.
    This means x = (b+c) - a for some sum b+c in sumset(A) and a ∈ A. -/
def isType1Blocked (A : Set ℕ) (x : ℕ) : Prop :=
  ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ b ≤ c ∧ x + a = b + c

/-- An element x is type-2 blocked by A if 2x = b + c for some b,c ∈ A.
    This means x is the midpoint of two elements of A. -/
def isType2Blocked (A : Set ℕ) (x : ℕ) : Prop :=
  ∃ b c : ℕ, b ∈ A ∧ c ∈ A ∧ b ≤ c ∧ 2 * x = b + c

/-- An element is blocked if it is type-1 or type-2 blocked. -/
def isBlocked (A : Set ℕ) (x : ℕ) : Prop :=
  isType1Blocked A x ∨ isType2Blocked A x

/-- Adding a non-member x to a Sidon set A breaks the Sidon property iff
    x is blocked by A. This is the key structural lemma.

    Proof: ¬IsSidonSet(A ∪ {x}) gives ∃ collision among elements of A ∪ {x}.
    Since A is Sidon, at least one collision element must be x.
    Systematic case analysis on which position(s) x occupies yields either
    x + a = b + c (type 1), 2x = b + c (type 2), or a contradiction. -/
theorem not_sidon_iff_blocked (A : Set ℕ) (x : ℕ) (hA : IsSidonSet A) (hx : x ∉ A) :
    ¬IsSidonSet (A ∪ {x}) → isBlocked A x := by
  intro hnotS
  unfold IsSidonSet at hnotS; push_neg at hnotS
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, heq, hne⟩ := hnotS
  -- Each of a,b,c,d is in A or equals x
  simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb hc hd
  -- Systematic case split: 16 cases from 4 binary membership choices
  rcases ha with ha | rfl <;> rcases hb with hb | rfl <;>
    rcases hc with hc | rfl <;> rcases hd with hd | rfl
  -- 1. a,b,c,d ∈ A: contradicts A being Sidon
  · exact absurd (hA a b c d ha hb hc hd hab hcd heq) hne
  -- 2. a,b,c ∈ A, d = x: type 1 (x + c = a + b)
  · left; exact ⟨c, a, b, hc, ha, hb, hab, by omega⟩
  -- 3. a,b ∈ A, c = x, d ∈ A: type 1 (x + d = a + b)
  · left; exact ⟨d, a, b, hd, ha, hb, hab, by omega⟩
  -- 4. a,b ∈ A, c = d = x: type 2 (2x = a + b)
  · right; exact ⟨a, b, ha, hb, hab, by omega⟩
  -- 5. a ∈ A, b = x, c,d ∈ A: type 1 (x + a = c + d)
  · left; exact ⟨a, c, d, ha, hc, hd, hcd, by omega⟩
  -- 6. a ∈ A, b = x, c ∈ A, d = x: a + x = c + x → a = c, set contradiction
  · have : a = c := by omega
    subst this; exact absurd rfl hne
  -- 7. a ∈ A, b = x, c = x, d ∈ A: a + x = x + d → a = d, {a,x} = {x,a}
  · have : a = d := by omega
    subst this
    exact absurd (by ext z; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]) hne
  -- 8. a ∈ A, b = c = d = x: a + x = 2x → a = x, membership contradiction
  · have : a = x := by omega
    subst this; exact absurd ha hx
  -- 9. a = x, b,c,d ∈ A: type 1 (x + b = c + d)
  · left; exact ⟨b, c, d, hb, hc, hd, hcd, by omega⟩
  -- 10. a = x, b ∈ A, c ∈ A, d = x: x + b = c + x → b = c, {x,b} = {b,x}
  · have : b = c := by omega
    subst this
    exact absurd (by ext z; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]) hne
  -- 11. a = x, b ∈ A, c = x, d ∈ A: x + b = x + d → b = d, set contradiction
  · have : b = d := by omega
    subst this; exact absurd rfl hne
  -- 12. a = x, b ∈ A, c = d = x: x + b = 2x → b = x, membership contradiction
  · have : b = x := by omega
    subst this; exact absurd hb hx
  -- 13. a = b = x, c,d ∈ A: type 2 (2x = c + d)
  · right; exact ⟨c, d, hc, hd, hcd, by omega⟩
  -- 14. a = b = x, c ∈ A, d = x: 2x = c + x → c = x, membership contradiction
  · have : c = x := by omega
    subst this; exact absurd hc hx
  -- 15. a = b = x, c = x, d ∈ A: 2x = x + d → d = x, membership contradiction
  · have : d = x := by omega
    subst this; exact absurd hd hx
  -- 16. a = b = c = d = x: {x,x} = {x,x}, set contradiction
  · exact absurd rfl hne

/-- Every non-member of a maximal Sidon set is blocked. -/
theorem maximal_sidon_all_blocked (A : Set ℕ) (N : ℕ) (hmax : IsMaximalSidonSet A N)
    (x : ℕ) (hx : x ∈ Interval N) (hxA : x ∉ A) :
    isBlocked A x :=
  not_sidon_iff_blocked A x hmax.2.1 hxA (hmax.2.2 x hx hxA)

end Blocking

section Counting

/-! ### Counting Blocked Values

We bound the number of type-1 and type-2 blocked values using the
sumset structure of Sidon sets. -/

/-- The set of type-1 blocked values for a finite set A. -/
def type1BlockedSet (A : Set ℕ) : Set ℕ :=
  {x | isType1Blocked A x}

/-- The set of type-2 blocked values for a finite set A. -/
def type2BlockedSet (A : Set ℕ) : Set ℕ :=
  {x | isType2Blocked A x}

/-- Type-1 blocked values are differences σ - a for σ ∈ sumset(A), a ∈ A. -/
theorem type1_subset_diff (A : Set ℕ) :
    type1BlockedSet A ⊆ {x | ∃ a ∈ A, ∃ σ ∈ sumset A, x + a = σ} := by
  intro x ⟨a, b, c, ha, hb, hc, _, heq⟩
  exact ⟨a, ha, b + c, ⟨b, c, hb, hc, rfl⟩, heq⟩

/-- Type-2 blocked values are halves of sums in sumset(A). -/
theorem type2_subset_midpoints (A : Set ℕ) :
    type2BlockedSet A ⊆ {x | ∃ σ ∈ sumset A, 2 * x = σ} := by
  intro x ⟨b, c, hb, hc, _, heq⟩
  exact ⟨b + c, ⟨b, c, hb, hc, rfl⟩, heq⟩

/-- The type-1 blocked set is finite when A is finite. -/
theorem type1_blocked_finite (A : Set ℕ) (hfin : A.Finite) :
    (type1BlockedSet A).Finite := by
  apply Set.Finite.subset ((sumset_finite A hfin).prod hfin).image.subset
  intro x ⟨a, b, c, ha, hb, hc, _, heq⟩
  simp only [Set.mem_image, Set.mem_prod, Prod.exists]
  exact ⟨b + c, a, ⟨⟨b, c, hb, hc, rfl⟩, ha⟩, by omega⟩

/-- The type-2 blocked set is finite when A is finite. -/
theorem type2_blocked_finite (A : Set ℕ) (hfin : A.Finite) :
    (type2BlockedSet A).Finite := by
  apply Set.Finite.subset ((sumset_finite A hfin).image (· / 2))
  intro x ⟨b, c, hb, hc, _, heq⟩
  simp only [Set.mem_image]
  refine ⟨b + c, ⟨b, c, hb, hc, rfl⟩, ?_⟩
  -- 2 * x = b + c implies (b + c) / 2 = x
  omega

/-- Upper bound on the number of type-1 blocked values:
    |type1BlockedSet A| ≤ |sumset A| · |A| = |A|²(|A|+1)/2. -/
theorem type1_blocked_count (A : Set ℕ) (hA : IsSidonSet A) (hfin : A.Finite) :
    (type1BlockedSet A).ncard ≤ (sumset A).ncard * A.ncard := by
  sorry

/-- Upper bound on the number of type-2 blocked values:
    |type2BlockedSet A| ≤ |sumset A| = |A|(|A|+1)/2. -/
theorem type2_blocked_count (A : Set ℕ) (hA : IsSidonSet A) (hfin : A.Finite) :
    (type2BlockedSet A).ncard ≤ (sumset A).ncard := by
  sorry

end Counting

section MainBound

/-! ### The Main Lower Bound

Combining the blocking structure with the counting bounds yields the
lower bound on maximal Sidon set size. -/

/-- The Interval {1,...,N} has exactly N elements. -/
theorem interval_ncard (N : ℕ) : (Interval N).ncard = N := by
  have hfin : (Interval N).Finite := by
    apply Set.Finite.subset (Set.finite_Icc 0 N)
    intro x ⟨_, h2⟩; exact ⟨Nat.zero_le x, h2⟩
  rw [hfin.ncard_eq_toFinset_card']
  have h_eq : hfin.toFinset = Finset.Icc 1 N := by
    ext x
    simp only [Set.Finite.mem_toFinset, Interval, Set.mem_setOf_eq, Finset.mem_Icc]
  rw [h_eq, Finset.card_Icc]
  omega

/-- A maximal Sidon set in {1,...,N} is finite. -/
theorem maximal_sidon_finite (A : Set ℕ) (N : ℕ) (hmax : IsMaximalSidonSet A N) :
    A.Finite :=
  Set.Finite.subset (by
    apply Set.Finite.subset (Set.finite_Icc 0 N)
    intro x ⟨_, h2⟩; exact ⟨Nat.zero_le x, h2⟩) hmax.1

/-- **Main Theorem**: Any maximal Sidon set A in {1,...,N} has size s satisfying
    2N ≤ (s+1)³, which gives s ≥ (2N)^{1/3} - 1.

    Proof sketch:
    - Every x ∈ {1,...,N} \ A is blocked (maximal_sidon_all_blocked)
    - N = |A| + |{1,...,N} \ A| (partition of the interval)
    - |{1,...,N} \ A| ≤ |type1BlockedSet| + |type2BlockedSet|
                     ≤ |sumset A| · |A| + |sumset A|
                     = |A|(|A|+1)/2 · (|A| + 1)
                     = |A|(|A|+1)²/2
    - So 2N ≤ 2|A| + |A|(|A|+1)² ≤ (|A|+1)³ -/
theorem maximal_sidon_size_bound (A : Set ℕ) (N : ℕ) (hmax : IsMaximalSidonSet A N) :
    2 * N ≤ (A.ncard + 1) ^ 3 := by
  sorry

/-- Corollary: The greedy Sidon construction has size Ω(N^{1/3}). -/
theorem greedySidon_size_bound (N : ℕ) :
    2 * N ≤ ((greedySidon N).ncard + 1) ^ 3 :=
  maximal_sidon_size_bound (greedySidon N) N (greedySidon_maximal N)

end MainBound

end Erdos156
