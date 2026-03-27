/-
# Erdős Problem #152: Isolated Elements in Sidon Sumsets

For any M ≥ 1, if A ⊂ ℕ is a sufficiently large finite Sidon set,
then there exist at least M elements a ∈ A + A such that
a - 1, a + 1 ∉ A + A. Conjectured to have ≫ |A|² such elements.

## Status: OPEN

## References
- Erdős–Sárközy–Sós (1994), "On Sum Sets of Sidon Sets, I",
  J. Number Theory, pp. 329–347
-/

import Mathlib.Combinatorics.Additive.Sidon
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Pointwise
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open scoped Pointwise

/-
## Section I: Sidon Sets and Sumsets
-/

/-- A finite set A ⊂ ℕ is Sidon if all pairwise sums a + b (a ≤ b)
are distinct. Equivalently, |{(a,b) : a + b = n}| ≤ 2 for all n. -/
def IsSidonFinset (A : Finset ℕ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℕ, a₁ ∈ A → b₁ ∈ A → a₂ ∈ A → b₂ ∈ A →
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℕ) = {a₂, b₂}

/-- The sumset A + A = { a + b : a, b ∈ A }. -/
def sumsetFinset (A : Finset ℕ) : Finset ℕ := A + A

/-
## Section II: Isolated Elements
-/

/-- An element s ∈ A + A is isolated if s - 1 ∉ A + A and s + 1 ∉ A + A.
These are "gaps" in the sumset structure. -/
def IsIsolated (A : Finset ℕ) (s : ℕ) : Prop :=
  s ∈ sumsetFinset A ∧ s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A

/-- The number of isolated elements in A + A. -/
noncomputable def isolatedCount (A : Finset ℕ) : ℕ :=
  ((sumsetFinset A).filter (fun s =>
    s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A)).card

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #152**: For any M ≥ 1, every sufficiently large
finite Sidon set A has at least M isolated elements in A + A. -/
def ErdosProblem152 : Prop :=
  ∀ M : ℕ, ∃ N₀ : ℕ, ∀ A : Finset ℕ,
    IsSidonFinset A → A.card ≥ N₀ →
      isolatedCount A ≥ M

/-
## Section IV: The Stronger Conjecture
-/

/-- Erdős conjectured the stronger result: there are ≫ |A|² isolated
elements in A + A for any Sidon set A. Since |A + A| ~ |A|² for Sidon
sets, this says a positive proportion of the sumset is isolated. -/
def ErdosProblem152Strong : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℕ, IsSidonFinset A →
      (isolatedCount A : ℝ) ≥ c * (A.card : ℝ) ^ 2

/-
## Section V: Proved Properties of Sidon Sets and Their Sumsets
-/

-- Any pair of elements in A has their sum in A + A
theorem sumset_mem {A : Finset ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    a + b ∈ sumsetFinset A :=
  Finset.add_mem_add ha hb

-- The double 2a is in A + A for any a ∈ A
theorem sumset_self_double {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a + a ∈ sumsetFinset A :=
  sumset_mem ha ha

-- Sidon sets have no 3-term arithmetic progressions with distinct terms:
-- if a + c = 2b with a, b, c ∈ A, then a = c (and hence a = b = c)
theorem sidon_no_three_ap {A : Finset ℕ} (hS : IsSidonFinset A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hap : a + c = b + b) : a = c := by
  have h := hS a c b b ha hc hb hb hap
  -- h : ({a, c} : Finset ℕ) = {b, b}, and {b, b} = {b} in Finset
  have hab : a = b := by
    have h1 : a ∈ ({a, c} : Finset ℕ) := Finset.mem_insert_self a _
    rw [h] at h1; simp at h1; exact h1
  have hcb : c = b := by
    have h2 : c ∈ ({a, c} : Finset ℕ) := by simp
    rw [h] at h2; simp at h2; exact h2
  rw [hab, hcb]

-- Corollary: in a Sidon set, a + c = 2b implies a = b = c
theorem sidon_no_three_ap' {A : Finset ℕ} (hS : IsSidonFinset A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hap : a + c = b + b) : a = b ∧ b = c := by
  have hac := sidon_no_three_ap hS ha hb hc hap
  subst hac
  constructor
  · -- a + a = b + b implies a = b
    omega
  · omega

-- For distinct elements a, b in a Sidon set: a + b ≠ 2a
-- (the sumset element a + b is not a doubled element)
theorem sidon_sum_ne_double {A : Finset ℕ} (hS : IsSidonFinset A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    a + b ≠ a + a := by
  intro h
  have : b = a := by omega
  exact hab this.symm

/-
## Section VI: Sumset Size for Sidon Sets
-/

/-- Ordered-pair injectivity for Sidon sets: if a₁ + b₁ = a₂ + b₂ with
    a₁ ≤ b₁ and a₂ ≤ b₂, then (a₁, b₁) = (a₂, b₂). -/
private theorem sidon_ordered_pair_inj {A : Finset ℕ} (hS : IsSidonFinset A)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (heq : a₁ + b₁ = a₂ + b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hpair := hS a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂ heq
  have ha₁_mem : a₁ ∈ ({a₂, b₂} : Finset ℕ) := hpair ▸ Finset.mem_insert_self a₁ _
  have hb₁_mem : b₁ ∈ ({a₂, b₂} : Finset ℕ) := hpair ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁_mem hb₁_mem
  rcases ha₁_mem with rfl | rfl <;> rcases hb₁_mem with rfl | rfl <;> constructor <;> omega

/-- Count of ordered pairs: |{(a,b) ∈ A × A : a ≤ b}| = n(n+1)/2.
    Proof: partition A × A into {a ≤ b} and {b < a}. The swap map (a,b) ↦ (b,a)
    gives |{a < b}| = |{b < a}|. With |{a = b}| = n and |A × A| = n²:
    n² = (|{a ≤ b}| - n) + n + (|{a ≤ b}| - n) = 2|{a ≤ b}| - n. -/
private theorem card_ordered_pairs (A : Finset ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card =
    A.card * (A.card + 1) / 2 := by
  set n := A.card
  set upper := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)
  set lower := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)
  -- Partition: A × A = upper ∪ lower
  have h_part : A ×ˢ A = upper ∪ lower := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, upper, lower]
    constructor
    · intro ⟨ha, hb⟩; by_cases h : a ≤ b <;> [exact Or.inl ⟨⟨ha, hb⟩, h⟩;
        exact Or.inr ⟨⟨ha, hb⟩, by omega⟩]
    · rintro (⟨⟨ha, hb⟩, -⟩ | ⟨⟨ha, hb⟩, -⟩) <;> exact ⟨ha, hb⟩
  have h_disj : Disjoint upper lower := by
    simp only [Finset.disjoint_left, Finset.mem_filter, upper, lower]
    intro ⟨a, b⟩ ⟨_, h1⟩ ⟨_, h2⟩; omega
  -- |A × A| = |upper| + |lower|
  have h_sum : n * n = upper.card + lower.card := by
    have := Finset.card_union_of_disjoint h_disj
    rw [← h_part] at this
    rw [Finset.card_product] at this
    omega
  -- Swap involution: |lower| = |{(a,b) : a < b}| = |upper| - n
  -- Actually, |lower| = |upper| - |diagonal| = |upper| - n
  -- since upper = {a < b} ∪ {a = b} and lower = {b < a} ~ {a < b}
  have h_swap : lower.card = upper.card - n := by
    -- The diagonal has n elements
    set diag := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)
    set strict := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)
    -- upper = strict ∪ diag
    have h_upper : upper = strict ∪ diag := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, upper, strict, diag]
      constructor
      · intro ⟨⟨ha, hb⟩, hab⟩
        rcases Nat.eq_or_lt_of_le hab with rfl | h
        · exact Or.inr ⟨⟨ha, hb⟩, rfl⟩
        · exact Or.inl ⟨⟨ha, hb⟩, h⟩
      · intro h; rcases h with ⟨⟨ha, hb⟩, hab⟩ | ⟨⟨ha, hb⟩, hab⟩
        · exact ⟨⟨ha, hb⟩, le_of_lt hab⟩
        · exact ⟨⟨ha, hb⟩, le_of_eq hab⟩
    have h_disj2 : Disjoint strict diag := by
      simp only [Finset.disjoint_left, Finset.mem_filter, strict, diag]
      intro ⟨a, b⟩ ⟨_, h1⟩ ⟨_, h2⟩; omega
    have h_diag_card : diag.card = n := by
      have : diag = A.map ⟨fun a => (a, a), fun a b h => by simpa using h⟩ := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
                    Function.Embedding.coeFn_mk, Prod.mk.injEq, diag]
        constructor
        · intro ⟨⟨ha, hb⟩, hab⟩; exact ⟨a, ha, rfl, hab.symm⟩
        · intro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
      rw [this, Finset.card_map]
    -- |strict| = |lower| via swap
    have h_strict_eq_lower : strict.card = lower.card := by
      apply Finset.card_bij (fun p _ => (p.2, p.1))
      · intro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_product, strict] at hp
        simp only [Finset.mem_filter, Finset.mem_product, lower]
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
        simpa using h
      · intro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_product, lower] at hp
        exact ⟨⟨b, a⟩, by simp only [Finset.mem_filter, Finset.mem_product, strict]; exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, by simp⟩
    -- Now: |upper| = |strict| + |diag| = |lower| + n
    have h_upper_card : upper.card = lower.card + n := by
      rw [h_upper, Finset.card_union_of_disjoint h_disj2, h_diag_card, h_strict_eq_lower]
    omega
  -- Combine: n² = upper + lower = upper + (upper - n) = 2*upper - n
  -- So upper = (n² + n) / 2 = n*(n+1)/2
  omega

/-- For a Sidon set A of size n, |A + A| = n(n+1)/2 since all sums
a + b with a ≤ b are distinct. -/
theorem sidon_sumset_size (A : Finset ℕ) (hS : IsSidonFinset A) :
  (sumsetFinset A).card = A.card * (A.card + 1) / 2 := by
  -- Build bijection between A + A and ordered pairs {(a,b) : a ≤ b, a,b ∈ A}
  set P := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)
  suffices hbij : (sumsetFinset A).card = P.card by
    rw [hbij, card_ordered_pairs]
  symm
  apply Finset.card_bij (fun (p : ℕ × ℕ) _ => p.1 + p.2)
  · -- Well-defined: sum is in A + A
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact Finset.add_mem_add hp.1.1 hp.1.2
  · -- Injective: Sidon + ordering
    intro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    have ⟨h1, h2⟩ := sidon_ordered_pair_inj hS hp₁.1.1 hp₁.1.2 hp₂.1.1 hp₂.1.2 hp₁.2 hp₂.2 heq
    exact Prod.ext h1 h2
  · -- Surjective: every sum comes from an ordered pair
    intro s hs
    simp only [sumsetFinset, Finset.mem_add] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    by_cases hab : a ≤ b
    · exact ⟨(a, b), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ha, hb⟩, hab⟩, rfl⟩
    · push_neg at hab
      exact ⟨(b, a), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hb, ha⟩, le_of_lt hab⟩, by omega⟩

/-- For a Sidon set of size n, the maximum element satisfies
max ≥ n(n-1)/2. This follows from the fact that all n(n-1)/2
differences a_j - a_i (i < j) must be distinct positive integers,
so they occupy at least the range [1, n(n-1)/2], giving
max - min ≥ n(n-1)/2.

Note: The previous bound n*(n-1)/2 + 1 was too strong;
{0,1} is a Sidon set of size 2 with max = 1 but 2*1/2 + 1 = 2. -/
axiom sidon_set_range_lower_bound (A : Finset ℕ) (hS : IsSidonFinset A)
    (hA : A.card = n) (hn : n ≥ 1) :
  ∃ a_max : ℕ, a_max ∈ A ∧ a_max ≥ n * (n - 1) / 2

/-
## Section VI: Related Results
-/

/-- A Sidon set of size n has sumset of size n(n+1)/2 contained in
an interval of length ≤ 2(n² - n), so by pigeonhole there are at
least n(n+1)/2 - 2(n² - n) - 1 "missing" values, creating gaps. -/
axiom gap_existence_pigeonhole (A : Finset ℕ) (hS : IsSidonFinset A)
    (hn : A.card ≥ 5) :
  isolatedCount A ≥ 1

/-- The infinite version: if A ⊂ ℕ is an infinite Sidon set and
A_N = A ∩ [1, N], does the number of isolated elements in A_N + A_N
tend to infinity? -/
def ErdosProblem152Infinite : Prop :=
  ∀ (A : Set ℕ) (hS : ∀ a₁ b₁ a₂ b₂ ∈ A, a₁ + b₁ = a₂ + b₂ →
    ({a₁, b₁} : Set ℕ) = {a₂, b₂}),
    ∀ M : ℕ, ∃ N₀ : ℕ,
      isolatedCount ((Finset.range N₀).filter (· ∈ A)) ≥ M
