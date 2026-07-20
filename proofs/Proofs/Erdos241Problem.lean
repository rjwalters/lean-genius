/-
# Erdős Problem #241: Maximum Size of B₃ Sets

Let f(N) be the maximum size of A ⊆ {1,...,N} such that all
three-element sums a + b + c (a ≤ b ≤ c, a,b,c ∈ A) are distinct.
Is f(N) ~ N^{1/3}?

## Status: OPEN ($100 prize)

## References
- Bose–Chowla, "Theorems in the additive theory of numbers" (1962)
- Green, "The number of squares and B_h[g] sets" (2001)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
## Section I: B₃ Sets
-/

/-- The multiset of ordered three-element sums from A. -/
def threeSums (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A ×ˢ A).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)).image
    (fun t => t.1 + t.2.1 + t.2.2)

/-- A set A is B₃ if all ordered triples (a,b,c) with a ≤ b ≤ c from A
give distinct sums a + b + c. Equivalently, a₁+b₁+c₁ = a₂+b₂+c₂ implies
{a₁,b₁,c₁} = {a₂,b₂,c₂} as multisets. -/
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ c₁ ∈ A,
  ∀ a₂ ∈ A, ∀ b₂ ∈ A, ∀ c₂ ∈ A,
    a₁ ≤ b₁ → b₁ ≤ c₁ → a₂ ≤ b₂ → b₂ ≤ c₂ →
    a₁ + b₁ + c₁ = a₂ + b₂ + c₂ →
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂

noncomputable instance : DecidablePred (fun S : Finset ℕ => IsB3 S) :=
  fun _ => Classical.dec _

/-
## Section II: Maximum B₃ Subset Size
-/

/-- f(N): the maximum size of a B₃ subset of {1,...,N}. -/
noncomputable def maxB3Size (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => IsB3 S)).sup Finset.card

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #241**: Is f(N) ~ N^{1/3}?

More precisely: is it true that f(N) / N^{1/3} → 1 as N → ∞?
This would mean the Bose–Chowla construction is asymptotically optimal. -/
def ErdosProblem241 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (1 - ε) * (N : ℝ) ^ (1/3 : ℝ) ≤ (maxB3Size N : ℝ) ∧
      (maxB3Size N : ℝ) ≤ (1 + ε) * (N : ℝ) ^ (1/3 : ℝ)

/-
## Section IV: The Bose–Chowla Lower Bound
-/

/-  Bose and Chowla (1962) proved that f(N) ≥ (1+o(1)) · N^{1/3}.
They constructed explicit B₃ sets of this size using finite fields. -/

/-
## Section V: Green's Upper Bound
-/

/-  Green (2001) proved f(N) ≤ ((7/2)^{1/3} + o(1)) · N^{1/3},
where (7/2)^{1/3} ≈ 1.519. This is the best known upper bound. -/

/-
## Section VI: Generalized Bₕ Sets
-/

/-- A set A is Bₕ if all h-element sums with a₁ ≤ ... ≤ aₕ are distinct.
B₂ sets are Sidon sets (Problem #30). B₃ sets are the subject of this problem. -/
def IsBh (h : ℕ) (A : Finset ℕ) : Prop :=
  h ≥ 2 ∧
  ∀ (S₁ S₂ : Finset ℕ),
    S₁ ⊆ A → S₂ ⊆ A → S₁.card = h → S₂.card = h →
    S₁.sum id = S₂.sum id → S₁ = S₂

noncomputable instance (h : ℕ) : DecidablePred (fun S : Finset ℕ => IsBh h S) :=
  fun _ => Classical.dec _

/-- Maximum size of a Bₕ subset of {1,...,N}. -/
noncomputable def maxBhSize (h N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => IsBh h S)).sup Finset.card

/-- Bose–Chowla conjecture (general): for all h ≥ 2,
the maximum Bₕ set in {1,...,N} has size ~ N^{1/h}. -/
def BoseChowlaConjecture (h : ℕ) : Prop :=
  h ≥ 2 →
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (1 - ε) * (N : ℝ) ^ (1 / (h : ℝ)) ≤ (maxBhSize h N : ℝ) ∧
      (maxBhSize h N : ℝ) ≤ (1 + ε) * (N : ℝ) ^ (1 / (h : ℝ))

/-  The case h = 2 (Sidon sets) is resolved: Problem #30. -/

/-  Bose–Chowla lower bound holds for all h ≥ 2. -/

/-
## Section VII: Known Small B₃ Sets
-/

/-  Example: {1, 5, 14, 30} is a B₃ set.
All 20 ordered triple sums (a ≤ b ≤ c) are distinct:
3, 7, 11, 15, 16, 20, 24, 29, 32, 33, 36, 40, 42, 45, 49, 58, 61, 65, 74, 90.

Note: The previously claimed {1,2,4,8} is NOT B₃ since 1+1+4 = 2+2+2 = 6. -/

/- The trivial upper bound: a B₃ set in {1,...,N} has at most
O(N^{1/3}) elements since distinct sums lie in {3,...,3N}. -/

/-
## Section VIII: Foundational Lemmas (axiom-free)

Basic API for `threeSums`, `IsB3`, `maxB3Size`, `IsBh`, and `maxBhSize`.  All
lemmas below are fully machine-checked with no `sorry` and no `axiom`
(host-verified on Lean v4.31.0; `#print axioms` = propext/Classical.choice/Quot.sound
only — `Classical.choice` enters only through the `DecidablePred` instances above).
The deep content of Erdős #241 (the `f(N) ~ N^{1/3}` asymptotics of Bose–Chowla
and Green) remains documented-only; it needs finite-field / analytic machinery
beyond Mathlib. -/

/-- Membership characterisation of `threeSums`: `x` is an ordered triple sum. -/
theorem mem_threeSums {A : Finset ℕ} {x : ℕ} :
    x ∈ threeSums A ↔ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≤ b ∧ b ≤ c ∧ a + b + c = x := by
  simp only [threeSums, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b, c⟩, ⟨⟨ha, hb, hc⟩, hab, hbc⟩, rfl⟩
    exact ⟨a, ha, b, hb, c, hc, hab, hbc, rfl⟩
  · rintro ⟨a, ha, b, hb, c, hc, hab, hbc, rfl⟩
    exact ⟨⟨a, b, c⟩, ⟨⟨ha, hb, hc⟩, hab, hbc⟩, rfl⟩

/-- The empty set has no three-element sums. -/
theorem threeSums_empty : threeSums (∅ : Finset ℕ) = ∅ := by
  simp [threeSums]

/-- `threeSums` is monotone: enlarging `A` can only add sums. -/
theorem threeSums_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    threeSums A ⊆ threeSums B := by
  intro x hx
  rw [mem_threeSums] at hx ⊢
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hsum⟩ := hx
  exact ⟨a, hAB ha, b, hAB hb, c, hAB hc, hab, hbc, hsum⟩

/-- The empty set is (vacuously) a B₃ set. -/
theorem isB3_empty : IsB3 (∅ : Finset ℕ) := by
  intro a₁ ha₁
  exact absurd ha₁ (by simp)

/-- Every singleton is a B₃ set (its only ordered triple is `(a,a,a)`). -/
theorem isB3_singleton (a : ℕ) : IsB3 ({a} : Finset ℕ) := by
  intro a₁ ha₁ b₁ hb₁ c₁ hc₁ a₂ ha₂ b₂ hb₂ c₂ hc₂ _ _ _ _ _
  rw [Finset.mem_singleton] at ha₁ hb₁ hc₁ ha₂ hb₂ hc₂
  subst ha₁ hb₁ hc₁ ha₂ hb₂ hc₂
  exact ⟨rfl, rfl, rfl⟩

/-- The B₃ property is inherited by subsets. -/
theorem IsB3.subset {A B : Finset ℕ} (hAB : A ⊆ B) (hB : IsB3 B) : IsB3 A := by
  intro a₁ ha₁ b₁ hb₁ c₁ hc₁ a₂ ha₂ b₂ hb₂ c₂ hc₂ h1 h2 h3 h4 hsum
  exact hB a₁ (hAB ha₁) b₁ (hAB hb₁) c₁ (hAB hc₁)
    a₂ (hAB ha₂) b₂ (hAB hb₂) c₂ (hAB hc₂) h1 h2 h3 h4 hsum

/-- `f(N) = maxB3Size N` never exceeds the window size `N`. -/
theorem maxB3Size_le (N : ℕ) : maxB3Size N ≤ N := by
  unfold maxB3Size
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact (Finset.card_le_card hS.1).trans_eq (Finset.card_range N)

/-- `maxB3Size` is monotone in the window size. -/
theorem maxB3Size_mono {N M : ℕ} (h : N ≤ M) : maxB3Size N ≤ maxB3Size M := by
  unfold maxB3Size
  apply Finset.sup_mono
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  refine ⟨hS.1.trans ?_, hS.2⟩
  intro x hx
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

/-- `f(0) = 0`. -/
theorem maxB3Size_zero : maxB3Size 0 = 0 := Nat.le_zero.mp (maxB3Size_le 0)

/-- The Bₕ property is inherited by subsets. -/
theorem IsBh.subset {h : ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) (hB : IsBh h B) :
    IsBh h A := by
  obtain ⟨hh, hdist⟩ := hB
  refine ⟨hh, fun S₁ S₂ h1 h2 c1 c2 hsum => ?_⟩
  exact hdist S₁ S₂ (h1.trans hAB) (h2.trans hAB) c1 c2 hsum

/-- The empty set is a Bₕ set for every `h ≥ 2` (no `h`-subset exists to clash). -/
theorem isBh_empty {h : ℕ} (hh : 2 ≤ h) : IsBh h (∅ : Finset ℕ) := by
  refine ⟨hh, fun S₁ S₂ h1 _ c1 _ _ => ?_⟩
  rw [Finset.subset_empty] at h1
  subst h1
  rw [Finset.card_empty] at c1
  omega

/-- The maximum Bₕ subset size never exceeds the window size `N`. -/
theorem maxBhSize_le (h N : ℕ) : maxBhSize h N ≤ N := by
  unfold maxBhSize
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact (Finset.card_le_card hS.1).trans_eq (Finset.card_range N)

/-- `maxBhSize` is monotone in the window size. -/
theorem maxBhSize_mono {h N M : ℕ} (hNM : N ≤ M) : maxBhSize h N ≤ maxBhSize h M := by
  unfold maxBhSize
  apply Finset.sup_mono
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  refine ⟨hS.1.trans ?_, hS.2⟩
  intro x hx
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNM)
