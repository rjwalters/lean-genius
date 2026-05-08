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

/-- The Sidon property is inherited by subsets. -/
theorem isSidon_subset {S T : Finset ℤ} (hT : IsSidon T) (hST : S ⊆ T) : IsSidon S :=
  fun a ha b hb c hc d hd hab hcd heq =>
    hT a (hST ha) b (hST hb) c (hST hc) d (hST hd) hab hcd heq

/-- Any two-element set {x, y} is Sidon. When x = y this reduces to a singleton;
    when x ≠ y, the sums 2x, x+y, 2y are distinct so no non-trivial collision. -/
theorem isSidon_pair (x y : ℤ) : IsSidon ({x, y} : Finset ℤ) := by
  intro a ha b hb c hc d hd hab hcd heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    first | exact ⟨rfl, rfl⟩ | (constructor <;> omega)

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
    size at least c · N^{1/3} for some absolute constant c.
    Proof: follows immediately from the stronger KSS bound k² ≥ c·N.
    Since k ≥ 1, we have k³ = k·k² ≥ 1·(c·N) = c·N. -/
theorem erdos_lower_bound :
    ∃ c : ℕ, c ≥ 1 ∧
      ∀ A : Finset ℤ, A.card ≥ 8 →
        maxSidonSize A * maxSidonSize A * maxSidonSize A ≥ c * A.card := by
  obtain ⟨c, hc, hkss⟩ := komlos_sulyok_szemeredi
  refine ⟨c, hc, fun A hA => ?_⟩
  have h := hkss A (by omega : A.card ≥ 4)
  -- k³ = k · k² ≥ 1 · (c · |A|) = c · |A|
  calc c * A.card
      ≤ maxSidonSize A * maxSidonSize A := h
    _ ≤ maxSidonSize A * maxSidonSize A * maxSidonSize A :=
        le_mul_of_one_le_right (Nat.zero_le _)
          (maxSidonSize_pos (Finset.card_pos.mp (by omega : 0 < A.card)))

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

/-- For nonempty A, maxSidonSize A ≥ 1 (any singleton is Sidon). -/
theorem maxSidonSize_pos {A : Finset ℤ} (hA : A.Nonempty) : 1 ≤ maxSidonSize A := by
  obtain ⟨x, hx⟩ := hA
  unfold maxSidonSize
  calc 1 = ({x} : Finset ℤ).card := by simp
    _ ≤ (A.powerset.filter fun S => IsSidon S).sup Finset.card :=
        Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          (Finset.singleton_subset_iff.mpr hx), isSidon_singleton x⟩)

/-- For A with ≥ 2 elements, maxSidonSize A ≥ 2 (any pair is Sidon). -/
theorem maxSidonSize_ge_two {A : Finset ℤ} (hA : 2 ≤ A.card) : 2 ≤ maxSidonSize A := by
  obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  unfold maxSidonSize
  calc 2 = ({x, y} : Finset ℤ).card := by
        rw [Finset.card_pair hne]
    _ ≤ (A.powerset.filter fun S => IsSidon S).sup Finset.card :=
        Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
          (Finset.insert_subset (hx) (Finset.singleton_subset_iff.mpr hy)),
          isSidon_pair x y⟩)

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

/-- Erdős Problem 530: The maximum Sidon subset size ℓ(N) satisfies
    c₁ · N^{1/2} ≤ ℓ(N) ≤ c₂ · N^{1/2} for absolute constants c₁, c₂. -/
def ErdosProblem530 : Prop :=
  ∃ c₁ c₂ : ℕ, c₁ ≥ 1 ∧ c₂ ≥ 1 ∧
    ∀ A : Finset ℤ, A.card ≥ 4 →
      maxSidonSize A * maxSidonSize A ≥ c₁ * A.card ∧
      maxSidonSize A * maxSidonSize A ≤ c₂ * A.card

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

/-
## Section 7: Corrected problem statement

The original ErdosProblem530 above has a universal upper bound (∀ A, ℓ(A)² ≤ c₂|A|),
which is FALSE: geometric sequences {1, 2, 4, ..., 2^(N-1)} are entirely Sidon
(distinct binary representations give distinct pairwise sums), so maxSidonSize = N
and N² ≫ c₂·N for large N.

The correct formulation: the LOWER bound is universal (every set has big Sidon subset),
while the UPPER bound is existential (some sets of each size have bounded Sidon subsets).
-/

/-- Erdős Problem 530 (corrected): ℓ(N) = Θ(√N).
    Lower bound (∀): every N-element set has Sidon subset of size Ω(√N) — KSS.
    Upper bound (∃): for each N, some set has maxSidonSize ≤ O(√N) — {1,...,N}. -/
def ErdosProblem530Corrected : Prop :=
  (∃ c₁ : ℕ, c₁ ≥ 1 ∧ ∀ A : Finset ℤ, A.card ≥ 4 →
    maxSidonSize A * maxSidonSize A ≥ c₁ * A.card) ∧
  (∃ c₂ : ℕ, c₂ ≥ 1 ∧ ∀ N : ℕ, N ≥ 4 →
    ∃ A : Finset ℤ, A.card = N ∧ maxSidonSize A * maxSidonSize A ≤ c₂ * N)

/-
## Section 8: Upper bound for interval sets

For a Sidon subset S of {1,...,N}, the k(k+1)/2 distinct pairwise sums
all lie in {1,...,2N}. Since |{1,...,2N}| = 2N, we get k(k+1)/2 ≤ 2N.
Using evenness of k(k+1), this gives k(k+1) ≤ 4N, hence k² ≤ 4N.
-/

/-- Any Sidon subset of {1,...,N} has |S|² ≤ 4N.
    Proof: k(k+1)/2 distinct sums fit in {1,...,2N} of size 2N. -/
theorem sidon_subset_interval_bound (S : Finset ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hS : IsSidon S) (hRange : ∀ x ∈ S, 1 ≤ x ∧ x ≤ ↑N) :
    S.card * S.card ≤ 4 * N := by
  set k := S.card with hk_def
  have h_count := sidon_sum_count S hS
  -- Sums of sorted pairs from S lie in [1, 2N]
  have h_sub : ((S ×ˢ S).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2) ⊆
      Finset.Icc (1 : ℤ) (2 * ↑N) := by
    intro s hs
    simp only [Finset.mem_image, Prod.exists] at hs
    obtain ⟨a, b, hab, rfl⟩ := hs
    simp only [Finset.mem_filter, Finset.mem_product] at hab
    rw [Finset.mem_Icc]
    exact ⟨by linarith [(hRange a hab.1.1).1],
           by linarith [(hRange a hab.1.1).2, (hRange b hab.1.2).2]⟩
  -- |[1, 2N]| = 2N
  have h_icc : (Finset.Icc (1 : ℤ) (2 * ↑N)).card = 2 * N := by
    simp [Finset.card_Icc]; omega
  -- k(k+1)/2 ≤ 2N
  have h_sum_le : k * (k + 1) / 2 ≤ 2 * N := by
    calc k * (k + 1) / 2
        = (((S ×ˢ S).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2)).card :=
          h_count.symm
      _ ≤ (Finset.Icc (1 : ℤ) (2 * ↑N)).card := Finset.card_le_card h_sub
      _ = 2 * N := h_icc
  -- k(k+1) is even (one of k, k+1 is even)
  have h_even : 2 ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (k + 1), by rw [hm]; ring⟩
    · exact ⟨k * (m + 1), by rw [hm]; ring⟩
  -- k(k+1) = 2*(k(k+1)/2) ≤ 2*2N = 4N
  have h_prod : k * (k + 1) ≤ 4 * N :=
    calc k * (k + 1) = k * (k + 1) / 2 * 2 := (Nat.div_mul_cancel h_even).symm
      _ ≤ (2 * N) * 2 := Nat.mul_le_mul_right 2 h_sum_le
      _ = 4 * N := by ring
  -- k² ≤ k(k+1) ≤ 4N
  calc k * k ≤ k * (k + 1) := Nat.mul_le_mul_left k (Nat.le_succ k)
    _ ≤ 4 * N := h_prod

/-- **Sharp** interval bound: every Sidon subset S of {1,...,N} satisfies
    |S|(|S|+1) + 2 ≤ 4N (equivalently `k(k+1) ≤ 4N − 2`, sharper than the
    `k² ≤ 4N` of `sidon_subset_interval_bound`).

    Observation: pairwise sums `a + b` with `a, b ∈ S`, `a ≤ b` satisfy
    `2 ≤ a + b ≤ 2N` (since `a, b ≥ 1`), so they lie in
    `Finset.Icc 2 (2N)` of cardinality `2N − 1` rather than the
    looser `Finset.Icc 1 (2N)` of cardinality `2N`. The `k(k+1)/2`
    distinct Sidon sums therefore satisfy `k(k+1)/2 ≤ 2N − 1`, hence
    `k(k+1) ≤ 4N − 2`.

    Stated without ℕ-subtraction as `k(k+1) + 2 ≤ 4N`. -/
theorem sidon_subset_interval_bound_sharp (S : Finset ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hS : IsSidon S) (hRange : ∀ x ∈ S, 1 ≤ x ∧ x ≤ ↑N) :
    S.card * (S.card + 1) + 2 ≤ 4 * N := by
  set k := S.card with hk_def
  have h_count := sidon_sum_count S hS
  -- Sums of sorted pairs from S with min ≥ 1 lie in [2, 2N]
  have h_sub : ((S ×ˢ S).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2) ⊆
      Finset.Icc (2 : ℤ) (2 * ↑N) := by
    intro s hs
    simp only [Finset.mem_image, Prod.exists] at hs
    obtain ⟨a, b, hab, rfl⟩ := hs
    simp only [Finset.mem_filter, Finset.mem_product] at hab
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · linarith [(hRange a hab.1.1).1, (hRange b hab.1.2).1]
    · linarith [(hRange a hab.1.1).2, (hRange b hab.1.2).2]
  -- |[2, 2N]| = 2N - 1
  have h_icc : (Finset.Icc (2 : ℤ) (2 * ↑N)).card = 2 * N - 1 := by
    simp [Finset.card_Icc]; omega
  -- k(k+1)/2 ≤ 2N - 1
  have h_sum_le : k * (k + 1) / 2 ≤ 2 * N - 1 := by
    calc k * (k + 1) / 2
        = (((S ×ˢ S).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2)).card :=
          h_count.symm
      _ ≤ (Finset.Icc (2 : ℤ) (2 * ↑N)).card := Finset.card_le_card h_sub
      _ = 2 * N - 1 := h_icc
  -- k(k+1) is even (one of k, k+1 is even)
  have h_even : 2 ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (k + 1), by rw [hm]; ring⟩
    · exact ⟨k * (m + 1), by rw [hm]; ring⟩
  -- k(k+1) + 2 = 2·(k(k+1)/2) + 2 ≤ 2·(2N-1) + 2 = 4N
  have h_mul : k * (k + 1) / 2 * 2 ≤ (2 * N - 1) * 2 :=
    Nat.mul_le_mul_right 2 h_sum_le
  have h_div : k * (k + 1) / 2 * 2 = k * (k + 1) := Nat.div_mul_cancel h_even
  omega

/-- The interval {1,...,N} has maxSidonSize² ≤ 4N. -/
theorem interval_sidon_upper (N : ℕ) (hN : 1 ≤ N) :
    maxSidonSize (Finset.Icc (1 : ℤ) ↑N) * maxSidonSize (Finset.Icc (1 : ℤ) ↑N) ≤ 4 * N := by
  set A := Finset.Icc (1 : ℤ) ↑N
  set ss := A.powerset.filter (fun S => IsSidon S)
  by_cases hne : ss.Nonempty
  · obtain ⟨S₀, hS₀_mem, hS₀_max⟩ := ss.exists_max_image Finset.card hne
    have hsup : ss.sup Finset.card = S₀.card := le_antisymm
      (Finset.sup_le fun S hS => hS₀_max S hS) (Finset.le_sup hS₀_mem)
    show ss.sup Finset.card * ss.sup Finset.card ≤ 4 * N
    rw [hsup]
    have hf := Finset.mem_filter.mp hS₀_mem
    exact sidon_subset_interval_bound S₀ N hN hf.2
      (fun x hx => Finset.mem_Icc.mp (Finset.mem_powerset.mp hf.1 hx))
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    show ss.sup Finset.card * ss.sup Finset.card ≤ 4 * N
    simp [hne]

/-- The card of Finset.Icc 1 N equals N for integers. -/
private theorem icc_one_card (N : ℕ) : (Finset.Icc (1 : ℤ) ↑N).card = N := by
  simp [Finset.card_Icc]; omega

/-- The corrected Erdős Problem 530 is proved: ℓ(N) = Θ(√N).
    Lower bound from KSS axiom; upper bound from interval sum counting (proved).
    With c₁ from KSS and c₂ = 4, the witness is A = {1,...,N}. -/
theorem erdos530_corrected_proof : ErdosProblem530Corrected :=
  ⟨komlos_sulyok_szemeredi,
   ⟨4, by omega, fun N hN =>
     ⟨Finset.Icc (1 : ℤ) ↑N, icc_one_card N, interval_sidon_upper N (by omega)⟩⟩⟩

end Erdos530
