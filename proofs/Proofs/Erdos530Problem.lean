/-
# Erdős Problem 530: Maximum Sidon Subsets of Finite Sets

*Reference:* [erdosproblems.com/530](https://www.erdosproblems.com/530)

For a finite set `A ⊂ ℝ` of size `N`, let `ℓ(N)` denote the maximum size
of a Sidon subset of `A` (where `a + b = c + d` implies `{a,b} = {c,d}`).
Determine the order of growth of `ℓ(N)`.

Originally posed by Riddell (1969). Erdős proved `N^{1/3} ≪ ℓ(N) ≤ (1+o(1))N^{1/2}`.
Komlós, Sulyok, and Szemerédi improved the lower bound to `N^{1/2} ≪ ℓ(N)`.
The conjecture is that `ℓ(N) ~ N^{1/2}`.

This remains an open problem.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
## Section 1: Sidon set definition

A set `S` is *Sidon* (also called a B₂-set) if all pairwise sums `a + b`
with `a ≤ b` are distinct. Equivalently, `a + b = c + d` with `a,b,c,d ∈ S`
implies `{a,b} = {c,d}`.
-/

namespace Erdos530

open Finset Classical

/-- A Finset of integers is Sidon if all pairwise sums are distinct:
    a + b = c + d with a ≤ b, c ≤ d implies a = c and b = d. -/
def IsSidon (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- The empty set is Sidon. -/
theorem isSidon_empty : IsSidon ∅ := by
  intro a ha
  exact absurd ha (Finset.notMem_empty a)

/-- Any singleton is Sidon. -/
theorem isSidon_singleton (x : ℤ) : IsSidon {x} := by
  intro a ha b hb c hc d hd hab hcd heq
  rw [Finset.mem_singleton] at ha hb hc hd
  exact ⟨by rw [ha, hc], by rw [hb, hd]⟩

/-- Any subset of a Sidon set is Sidon. -/
theorem isSidon_subset {S T : Finset ℤ} (hT : T ⊆ S) (hS : IsSidon S) : IsSidon T :=
  fun a ha b hb c hc d hd hab hcd heq =>
    hS a (hT ha) b (hT hb) c (hT hc) d (hT hd) hab hcd heq

/-
## Section 2: Maximum Sidon subset size

For a finite set `A` of size `N`, `maxSidonSize A` is the maximum
cardinality of a Sidon subset of `A`.
-/

/-- The maximum size of a Sidon subset of A. -/
noncomputable def maxSidonSize (A : Finset ℤ) : ℕ :=
  (A.powerset.filter (fun S => IsSidon S)).sup Finset.card

/-
## Section 3: Known bounds

The key results on `ℓ(N)`:
- Erdős: `N^{1/3} ≪ ℓ(N)` (lower bound)
- Trivially: `ℓ(N) ≤ (1 + o(1))N^{1/2}` (from {1,...,N})
- Komlós–Sulyok–Szemerédi: `N^{1/2} ≪ ℓ(N)` (improved lower bound)
-/

/-- Erdős's lower bound: every set of size N has a Sidon subset of
    size at least c · N^{1/3} for some absolute constant c. -/
axiom erdos_lower_bound :
  ∃ c : ℕ, c ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 8 →
      maxSidonSize A * maxSidonSize A * maxSidonSize A ≥ c * A.card

/-- Komlós–Sulyok–Szemerédi improved lower bound: every set of size N
    has a Sidon subset of size at least c · N^{1/2}. -/
axiom komlos_sulyok_szemeredi :
  ∃ c : ℕ, c ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 4 →
      maxSidonSize A * maxSidonSize A ≥ c * A.card

/-- Every Sidon subset of A is a subset, hence has cardinality ≤ |A|. -/
theorem maxSidonSize_le_card (A : Finset ℤ) : maxSidonSize A ≤ A.card := by
  unfold maxSidonSize
  apply Finset.sup_le (fun S hS => ?_)
  exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)

/-- maxSidonSize is monotone: A ⊆ B → maxSidonSize A ≤ maxSidonSize B. -/
theorem maxSidonSize_mono {A B : Finset ℤ} (h : A ⊆ B) : maxSidonSize A ≤ maxSidonSize B := by
  unfold maxSidonSize
  apply Finset.sup_le
  intro S hS
  have hSf := Finset.mem_filter.mp hS
  have hSB : S ∈ B.powerset.filter (fun S => IsSidon S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.Subset.trans (Finset.mem_powerset.mp hSf.1) h), hSf.2⟩
  exact Finset.le_sup hSB

/-- A nonempty set has maxSidonSize ≥ 1 (any singleton is Sidon). -/
theorem maxSidonSize_pos {A : Finset ℤ} (hA : A.Nonempty) : 1 ≤ maxSidonSize A := by
  obtain ⟨a, ha⟩ := hA
  unfold maxSidonSize
  have hmem : {a} ∈ A.powerset.filter (fun S => IsSidon S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
      isSidon_singleton a⟩
  calc 1 = ({a} : Finset ℤ).card := by simp
    _ ≤ _ := Finset.le_sup hmem

/-- Trivial upper bound: (maxSidonSize A)² ≤ |A|². Since any Sidon subset
    of A has at most |A| elements, squaring preserves the inequality.
    Note: the actual conjecture is the much stronger maxSidonSize A ≤ (1+o(1))√|A|. -/
theorem sidon_upper_bound :
  ∀ A : Finset ℤ,
    maxSidonSize A * maxSidonSize A ≤ A.card * A.card := by
  intro A
  exact Nat.mul_le_mul (maxSidonSize_le_card A) (maxSidonSize_le_card A)

/-
## Section 4: The main conjecture

Erdős conjectured that `ℓ(N) ~ N^{1/2}`, i.e., the lower and upper
bounds are of the same order.
-/

/-- Erdős Problem 530: ℓ(N) ~ N^{1/2}, where ℓ(N) = min over all A of size N of maxSidonSize A.

    Two parts:
    - Lower bound (universal): every set of size ≥ 4 has a Sidon subset of size ≥ c₁√N.
      This is KSS (1975).
    - Upper bound (existential): for each N, some set of size N has no Sidon subset > c₂√N.
      Note: the upper bound must be existential — a Sidon set A has maxSidonSize(A) = |A| ≫ √|A|,
      so a universal upper bound maxSidonSize(A)² ≤ c₂|A| for ALL A is false. -/
def ErdosProblem530 : Prop :=
  (∃ c₁ : ℕ, c₁ ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 4 →
      maxSidonSize A * maxSidonSize A ≥ c₁ * A.card) ∧
  (∃ c₂ : ℕ, c₂ ≥ 1 ∧
    ∀ N : ℕ, N ≥ 4 →
      ∃ A : Finset ℤ, A.card = N ∧
        maxSidonSize A * maxSidonSize A ≤ c₂ * N)

/-- The lower bound of Problem 530 follows directly from Komlós–Sulyok–Szemerédi. -/
theorem erdos530_lower_bound :
    ∃ c₁ : ℕ, c₁ ≥ 1 ∧ ∀ A : Finset ℤ, A.card ≥ 4 →
      maxSidonSize A * maxSidonSize A ≥ c₁ * A.card :=
  komlos_sulyok_szemeredi

/-
## Section 5: Sidon set partition conjecture

Alon and Erdős conjectured that any set of size N can be partitioned
into at most (1 + o(1)) · N^{1/2} Sidon sets.
-/

/-- A partition of A into Sidon sets. -/
def IsSidonPartition (A : Finset ℤ) (parts : Finset (Finset ℤ)) : Prop :=
  (∀ P ∈ parts, IsSidon P) ∧
  (∀ P ∈ parts, P ⊆ A) ∧
  (∀ a ∈ A, ∃! P, P ∈ parts ∧ a ∈ P)

/-- Alon–Erdős conjecture: any set of N integers can be partitioned into
    at most c · N^{1/2} Sidon sets. -/
axiom alon_erdos_partition_conjecture :
  ∃ c : ℕ, c ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 1 →
      ∃ parts : Finset (Finset ℤ),
        IsSidonPartition A parts ∧ parts.card * parts.card ≤ c * A.card

/-
## Section 6: Connection to B₂-sets and additive combinatorics

Sidon sets are also called B₂-sets in the additive combinatorics literature.
The study of maximum Sidon subsets connects to the broader theory of
sum-free sets, Szemerédi's theorem, and additive number theory.
-/

/-- The sum function is injective on sorted pairs of a Sidon set.
    This is the core property of Sidon sets: distinct pairs give distinct sums. -/
theorem sidon_sum_injective (S : Finset ℤ) (hS : IsSidon S) :
    Set.InjOn (fun p : ℤ × ℤ => p.1 + p.2)
      ((S ×ˢ S).filter (fun p => p.1 ≤ p.2) : Set (ℤ × ℤ)) := by
  intro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  simp only [Finset.coe_filter, Set.mem_setOf_eq,
    Finset.mem_product] at hab hcd
  obtain ⟨⟨haS, hbS⟩, hab_le⟩ := hab
  obtain ⟨⟨hcS, hdS⟩, hcd_le⟩ := hcd
  have := hS a haS b hbS c hcS d hdS hab_le hcd_le heq
  exact Prod.ext this.1 this.2

/-- The number of sorted pairs (a,b) with a ≤ b from a Finset of ℤ of size n
    is exactly n*(n+1)/2. This counts ordered pairs with repetition allowed. -/
theorem card_sorted_pairs (S : Finset ℤ) :
    ((S ×ˢ S).filter (fun p => p.1 ≤ p.2)).card = S.card * (S.card + 1) / 2 := by
  -- Strategy: partition S×S, use swap symmetry to relate upper/lower triangles
  -- le + gt = |S|²
  have h_total : ((S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 ≤ p.2)).card +
      ((S ×ˢ S).filter (fun p : ℤ × ℤ => ¬(p.1 ≤ p.2))).card = S.card * S.card := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_product]
  -- Key: |gt| + |S| = |le|
  suffices h_key : ((S ×ˢ S).filter (fun p : ℤ × ℤ => ¬(p.1 ≤ p.2))).card + S.card =
      ((S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 ≤ p.2)).card by
    -- From h_total and h_key, derive the result
    have h2 : 2 * ((S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 ≤ p.2)).card =
        S.card * S.card + S.card := by omega
    have h3 : S.card * S.card + S.card = S.card * (S.card + 1) := by ring
    rw [h3] at h2
    omega
  -- Decompose le = lt ∪ eq (disjoint)
  have h_decomp : (S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 ≤ p.2) =
      (S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 < p.2) ∪
      (S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 = p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product]
    constructor
    · intro ⟨⟨ha, hb⟩, hab⟩
      rcases lt_or_eq_of_le hab with h | h
      · exact Or.inl ⟨⟨ha, hb⟩, h⟩
      · exact Or.inr ⟨⟨ha, hb⟩, h⟩
    · rintro (⟨⟨ha, hb⟩, h⟩ | ⟨⟨ha, hb⟩, h⟩)
      · exact ⟨⟨ha, hb⟩, le_of_lt h⟩
      · exact ⟨⟨ha, hb⟩, le_of_eq h⟩
  have h_disj : Disjoint ((S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 < p.2))
      ((S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 = p.2)) := by
    rw [Finset.disjoint_filter]
    intro ⟨a, b⟩ _ h1 h2; linarith
  -- |gt| = |lt| via swap bijection (a,b) ↦ (b,a)
  have h_swap : ((S ×ˢ S).filter (fun p : ℤ × ℤ => ¬(p.1 ≤ p.2))).card =
      ((S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 < p.2)).card := by
    symm
    apply Finset.card_bij (fun p _ => Prod.swap p)
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product, not_le, Prod.swap] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · intro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h
      simp only [Prod.swap, Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product, not_le] at h
      exact ⟨⟨b, a⟩, by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩,
        by simp [Prod.swap]⟩
  -- |eq| = |S| (diagonal bijection (a,a) ↦ a)
  have h_diag : ((S ×ˢ S).filter (fun p : ℤ × ℤ => p.1 = p.2)).card = S.card := by
    symm
    apply Finset.card_bij (fun x _ => (x, x))
    · intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩
    · intro a1 _ a2 _ h; exact (Prod.mk.inj h).1
    · intro p h
      have hf := Finset.mem_filter.mp h
      have hp := Finset.mem_product.mp hf.1
      refine ⟨p.1, hp.1, ?_⟩
      ext
      · rfl
      · exact hf.2
  -- Combine: |le| = |lt| + |eq| = |gt| + |S|
  rw [h_decomp, Finset.card_union_of_disjoint h_disj, h_swap, h_diag]

/-- The number of distinct pairwise sums from a Sidon set S of size k
    is exactly k(k+1)/2 (all sums are distinct).
    Proved from sidon_sum_injective (distinct pairs ↦ distinct sums) and
    card_sorted_pairs (counting the sorted pairs).
    (Previously axiomatized; now derived.) -/
theorem sidon_sum_count (S : Finset ℤ) (hS : IsSidon S) :
  (((S ×ˢ S).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2)).card =
    S.card * (S.card + 1) / 2 := by
  rw [Finset.card_image_of_injOn (sidon_sum_injective S hS)]
  exact card_sorted_pairs S

end Erdos530
