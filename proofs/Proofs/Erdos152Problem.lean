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
-- Sidon sets have distinct differences: if a > b, c > d, a-b = c-d then a=c, b=d
private theorem sidon_diff_injective {A : Finset ℕ} (hS : IsSidonFinset A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a > b) (_hcd : c > d) (heq : a - b = c - d) :
    a = c ∧ b = d := by
  have h1 : a + d = c + b := by omega
  have hpair := hS a d c b ha hd hc hb h1
  have ha_mem : a ∈ ({c, b} : Finset ℕ) := hpair ▸ Finset.mem_insert_self a _
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
  rcases ha_mem with rfl | rfl
  · exact ⟨rfl, by omega⟩
  · omega

theorem sidon_set_range_lower_bound (A : Finset ℕ) (hS : IsSidonFinset A)
    (hA : A.card = n) (hn : n ≥ 1) :
    ∃ a_max : ℕ, a_max ∈ A ∧ a_max ≥ n * (n - 1) / 2 := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨A.max' hne, Finset.max'_mem A hne, ?_⟩
  set M := A.max' hne
  -- D = ordered pairs (a, b) with b < a, both in A
  set D := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1)
  -- |D| = n(n-1)/2 (strict lower triangle of A×A)
  have hD_card : D.card = n * (n - 1) / 2 := by
    -- Same counting as card_ordered_pairs but for strict lower triangle
    set strict_upper := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2)
    -- D and strict_upper have same card by swap
    have hswap : D.card = strict_upper.card := by
      apply Finset.card_bij (fun p _ => (p.2, p.1))
      · intro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_product, D] at hp
        simp only [Finset.mem_filter, Finset.mem_product, strict_upper]
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h; simpa using h
      · intro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_product, strict_upper] at hp
        exact ⟨⟨b, a⟩, by simp only [Finset.mem_filter, Finset.mem_product, D];
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, by simp⟩
    -- |upper (≤)| = n(n+1)/2
    have h_upper := card_ordered_pairs A
    rw [hA] at h_upper
    -- Partition upper = strict_upper ∪ diag
    set upper := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)
    set diag := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 = p.2)
    have h_split : upper = strict_upper ∪ diag := by
      ext ⟨a, b⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        upper, strict_upper, diag]
      constructor
      · intro ⟨h, hab⟩; rcases Nat.eq_or_lt_of_le hab with rfl | h'
        · exact Or.inr ⟨h, rfl⟩
        · exact Or.inl ⟨h, h'⟩
      · rintro (⟨h, hab⟩ | ⟨h, hab⟩)
        · exact ⟨h, le_of_lt hab⟩
        · exact ⟨h, le_of_eq hab⟩
    have h_disj : Disjoint strict_upper diag := by
      simp only [Finset.disjoint_left, Finset.mem_filter, strict_upper, diag]
      intro ⟨a, b⟩ ⟨_, h1⟩ ⟨_, h2⟩; omega
    have h_diag : diag.card = n := by
      have : diag = A.map ⟨fun a => (a, a), fun a b h => by simpa using h⟩ := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
          Function.Embedding.coeFn_mk, Prod.mk.injEq, diag]
        constructor
        · intro ⟨⟨ha, _⟩, hab⟩; exact ⟨a, ha, rfl, hab.symm⟩
        · intro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
      rw [this, Finset.card_map, hA]
    rw [hswap, h_split, Finset.card_union_of_disjoint h_disj, h_diag] at h_upper ⊢
    omega
  -- Injection: D → Finset.range M via difference map, so |D| ≤ M
  suffices h : D.card ≤ M by omega
  calc D.card
      ≤ (Finset.range M).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1 - p.2 - 1)
        · intro ⟨a, b⟩ hp
          simp only [Finset.mem_filter, Finset.mem_product, D] at hp
          simp only [Finset.mem_range]
          have : a ≤ M := Finset.le_max' A a hp.1.1
          omega
        · intro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ heq
          simp only [Finset.mem_filter, Finset.mem_product, D] at hp₁ hp₂
          have ⟨ha, hb⟩ := sidon_diff_injective hS hp₁.1.1 hp₁.1.2 hp₂.1.1 hp₂.1.2
            hp₁.2 hp₂.2 (by omega)
          exact Prod.ext ha hb
    _ = M := Finset.card_range M

/-
## Section VI: Related Results
-/

/-- A Sidon set of size ≥ 5 has at least one isolated element in A + A.
Proof: The max sum 2M has no right neighbor. If M-1 ∉ A, it has no left
neighbor either, so 2M is isolated. If M-1 ∈ A, we use the min endpoint
or second-smallest element, exploiting that Sidon sets have at most one
pair of consecutive elements (by difference injectivity). -/
theorem gap_existence_pigeonhole (A : Finset ℕ) (hS : IsSidonFinset A)
    (hn : A.card ≥ 5) :
    isolatedCount A ≥ 1 := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set M := A.max' hne
  set m := A.min' hne
  have hM_mem : M ∈ A := Finset.max'_mem A hne
  have hm_mem : m ∈ A := Finset.min'_mem A hne
  have hle_M : ∀ a ∈ A, a ≤ M := fun a ha => Finset.le_max' A a ha
  have hge_m : ∀ a ∈ A, m ≤ a := fun a ha => Finset.min'_le A a ha
  have hM4 : M ≥ 4 := by
    have : A ⊆ Finset.range (M + 1) := fun a ha =>
      Finset.mem_range.mpr (Nat.lt_succ.mpr (hle_M a ha))
    linarith [Finset.card_le_card this, Finset.card_range (M + 1)]
  -- Suffices to find an isolated element
  suffices ∃ s ∈ sumsetFinset A, s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A by
    obtain ⟨s, hs, h⟩ := this
    exact Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, h⟩⟩
  -- All sums lie in [2m, 2M]
  have sum_le : ∀ s ∈ sumsetFinset A, s ≤ M + M := fun s hs => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    linarith [hle_M a ha, hle_M b hb]
  have sum_ge : ∀ s ∈ sumsetFinset A, m + m ≤ s := fun s hs => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    linarith [hge_m a ha, hge_m b hb]
  -- 2M ∈ A+A, 2M+1 ∉ A+A
  have h2M_in : M + M ∈ sumsetFinset A := Finset.add_mem_add hM_mem hM_mem
  have h2M1_out : M + M + 1 ∉ sumsetFinset A := fun h => by linarith [sum_le _ h]
  -- Case 1: M - 1 ∉ A → 2M is isolated
  by_cases hM1 : M - 1 ∈ A; swap
  · refine ⟨M + M, h2M_in, ?_, h2M1_out⟩
    intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
    have ha_le := hle_M a ha; have hb_le := hle_M b hb
    -- a + b = 2M - 1 with a, b ≤ M forces one to be M-1
    by_cases ha_eq : a = M
    · exact hM1 (show M - 1 ∈ A by have : b = M - 1 := by omega; rwa [this] at hb)
    · exact hM1 (show M - 1 ∈ A by have : a = M - 1 := by omega; rwa [this] at ha)
  -- Case 2: M - 1 ∈ A
  by_cases hm1 : m + 1 ∈ A
  · -- Case 2a: Both m+1 ∈ A and M-1 ∈ A → two diff-1 pairs → contradiction
    exfalso
    have hdiff := sidon_diff_injective hS hM_mem hM1 hm1 hm_mem
      (by omega) (by omega) (by omega)
    have : A ⊆ ({m, m + 1} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have := hge_m x hx; have := hle_M x hx; omega
    have : A.card ≤ 2 := by
      calc A.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card this
        _ ≤ 1 + 1 := Finset.card_insert_le _ _
        _ = 2 := by ring
    omega
  -- Case 2b: m + 1 ∉ A, M - 1 ∈ A
  by_cases hm0 : m = 0; swap
  · -- Case 2b-i: m ≥ 1 → 2m is isolated
    refine ⟨m + m, Finset.add_mem_add hm_mem hm_mem, ?_, ?_⟩
    · intro h; linarith [sum_ge _ h]  -- 2m - 1 < 2m
    · intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
      have ha_ge := hge_m a ha; have hb_ge := hge_m b hb
      -- a + b = 2m + 1, a ≥ m, b ≥ m → one is m+1
      by_cases ha_eq : a = m
      · exact hm1 (show m + 1 ∈ A by have : b = m + 1 := by omega; rwa [this] at hb)
      · exact hm1 (show m + 1 ∈ A by have : a = m + 1 := by omega; rwa [this] at ha)
  -- Case 2b-ii: m = 0, 1 ∉ A, M - 1 ∈ A → use second-smallest element
  subst hm0
  have hA'_ne : (A.erase 0).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hm_mem]; omega)
  set a₂ := (A.erase 0).min' hA'_ne
  have ha₂_er : a₂ ∈ A.erase 0 := Finset.min'_mem _ hA'_ne
  have ha₂_mem : a₂ ∈ A := Finset.mem_of_mem_erase ha₂_er
  have ha₂_ne0 : a₂ ≠ 0 := Finset.ne_of_mem_erase ha₂_er
  have ha₂_ge2 : a₂ ≥ 2 := by
    have : (1 : ℕ) ∉ A := by simpa using hm1
    have : a₂ ≠ 1 := fun h => this (h ▸ ha₂_mem); omega
  have ha₂_min : ∀ x ∈ A, x ≠ 0 → a₂ ≤ x :=
    fun x hx hx0 => Finset.min'_le _ x (Finset.mem_erase.mpr ⟨hx0, hx⟩)
  -- a₂ ∈ A+A (via 0 + a₂)
  have ha₂_in : a₂ ∈ sumsetFinset A :=
    show a₂ ∈ A + A from (zero_add a₂) ▸ Finset.add_mem_add hm_mem ha₂_mem
  -- a₂ - 1 ∉ A+A (no sums in (0, a₂))
  have ha₂_left : a₂ - 1 ∉ sumsetFinset A := by
    intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
    by_cases ha0 : a = 0
    · subst ha0; simp at hab; linarith [ha₂_min b hb (by omega : b ≠ 0)]
    · by_cases hb0 : b = 0
      · subst hb0; simp at hab; linarith [ha₂_min a ha ha0]
      · linarith [ha₂_min a ha ha0, ha₂_min b hb hb0]
  -- If a₂ + 1 ∉ A+A, then a₂ is isolated
  by_cases ha₂1 : a₂ + 1 ∈ sumsetFinset A; swap
  · exact ⟨a₂, ha₂_in, ha₂_left, ha₂1⟩
  -- a₂ + 1 ∈ A+A: must have a₂ + 1 ∈ A (only pair is {0, a₂+1})
  exfalso
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp ha₂1
  have h0 : a = 0 ∨ b = 0 := by
    by_contra h; push_neg at h
    linarith [ha₂_min a ha h.1, ha₂_min b hb h.2]
  have ha₂1_mem : a₂ + 1 ∈ A := by
    rcases h0 with rfl | rfl
    · rw [zero_add] at hab; rwa [hab] at hb
    · rw [add_zero] at hab; rwa [hab] at ha
  -- Two pairs with diff 1: (M, M-1) and (a₂+1, a₂) → a₂+1 = M
  have hdiff := sidon_diff_injective hS hM_mem hM1 ha₂1_mem ha₂_mem
    (by omega) (by omega) (by omega)
  -- A ⊆ {0, M-1, M} → |A| ≤ 3 < 5
  have : A ⊆ ({0, M - 1, M} : Finset ℕ) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hx0 : x = 0; · left; exact hx0
    · right; have := ha₂_min x hx hx0; have := hle_M x hx; omega
  have : A.card ≤ 3 := by
    calc A.card ≤ ({0, M - 1, M} : Finset ℕ).card := Finset.card_le_card this
      _ ≤ 1 + (1 + 1) := by
          calc _ ≤ ({M - 1, M} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
            _ ≤ (({M} : Finset ℕ).card + 1) + 1 := by linarith [Finset.card_insert_le (M-1) {M}]
            _ = 1 + (1 + 1) := by simp
  omega

/-- The infinite version: if A ⊂ ℕ is an infinite Sidon set and
A_N = A ∩ [1, N], does the number of isolated elements in A_N + A_N
tend to infinity? -/
def ErdosProblem152Infinite : Prop :=
  ∀ (A : Set ℕ) (hS : ∀ a₁ b₁ a₂ b₂ ∈ A, a₁ + b₁ = a₂ + b₂ →
    ({a₁, b₁} : Set ℕ) = {a₂, b₂}),
    ∀ M : ℕ, ∃ N₀ : ℕ,
      isolatedCount ((Finset.range N₀).filter (· ∈ A)) ≥ M
