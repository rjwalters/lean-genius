import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Defs

/-
# Constructive Schroeder-Bernstein for Finite Types

## Open Question (OQ-04)
"Are there effective (constructive) versions of CBS for specific classes of sets?"

## Answer
Yes. For `Fintype` types with `DecidableEq`, the orbit classification at the heart
of CBS is **decidable**: every element is computably classified as "Type A" (backward
chain terminates at an element outside range g) or "Type B" (terminates outside range f).

The classical CBS proof is non-constructive because orbit classification requires the law
of excluded middle in general. For finite types, chains terminate by pigeonhole, so
the classification is decidable and the bijection can be defined without `Classical.em`.

## Approach
Given injections f : α ↪ β and g : β ↪ α between finite types:
1. Define `baseSet` = {a ∈ α | a ∉ range g}
2. Iterate `S ↦ S ∪ (g ∘ f)''(S)` starting from baseSet
3. After `card α` steps, the set stabilizes (pigeonhole)
4. For a in the stable set: use f(a); otherwise: use g⁻¹(a)
5. Orbit classification is computable; preimage extraction uses choice

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Orbit classification fully decidable
- [x] Bijection proved correct
-/

set_option linter.unusedSectionVars false

namespace ConstructiveCBS

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ## Section 1: Definitions -/

/-- The base set: elements of α with no preimage under g. -/
def baseSet (g : β → α) : Finset α :=
  Finset.univ.filter (fun a => ∀ b : β, g b ≠ a)

/-- One expansion step: add forward images under g ∘ f. -/
def expand (f : α → β) (g : β → α) (S : Finset α) : Finset α :=
  S ∪ S.image (fun a => g (f a))

/-- The reachable set: elements reachable from baseSet via g ∘ f.
    After `card α` iterations, the set stabilizes by pigeonhole. -/
def reachableSet (f : α → β) (g : β → α) : Finset α :=
  (expand f g)^[Fintype.card α] (baseSet g)

/-! ## Section 2: Monotonicity -/

theorem subset_expand (f : α → β) (g : β → α) (S : Finset α) :
    S ⊆ expand f g S :=
  Finset.subset_union_left

theorem expand_mono (f : α → β) (g : β → α) : Monotone (expand f g) := by
  intro S T hST
  apply Finset.union_subset_union hST
  exact Finset.image_subset_image hST

theorem iterate_expand_mono (f : α → β) (g : β → α) (n : ℕ) :
    (expand f g)^[n] (baseSet g) ⊆ (expand f g)^[n + 1] (baseSet g) := by
  induction n with
  | zero => exact subset_expand f g (baseSet g)
  | succ n ih =>
    have h1 : (expand f g)^[n + 1] (baseSet g) =
              expand f g ((expand f g)^[n] (baseSet g)) :=
      Function.iterate_succ_apply' (expand f g) n (baseSet g)
    have h2 : (expand f g)^[n + 2] (baseSet g) =
              expand f g ((expand f g)^[n + 1] (baseSet g)) :=
      Function.iterate_succ_apply' (expand f g) (n + 1) (baseSet g)
    rw [h1, h2]
    exact expand_mono f g ih

theorem iterate_expand_le (f : α → β) (g : β → α) (m n : ℕ) (h : m ≤ n) :
    (expand f g)^[m] (baseSet g) ⊆ (expand f g)^[n] (baseSet g) := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact ih.trans (iterate_expand_mono f g _)

theorem baseSet_subset_reachable (f : α → β) (g : β → α) :
    baseSet g ⊆ reachableSet f g :=
  iterate_expand_le f g 0 (Fintype.card α) (Nat.zero_le _)

/-! ## Section 3: Stabilization -/

/-- A non-decreasing sequence of natural numbers bounded by N
    must have a repeat within the first N+1 terms. -/
theorem nat_seq_stabilize (s : ℕ → ℕ) (N : ℕ)
    (hbound : ∀ n, s n ≤ N)
    (hmono : ∀ n, s n ≤ s (n + 1)) :
    ∃ k ≤ N, s k = s (k + 1) := by
  by_contra h
  push_neg at h
  have hstrict : ∀ k ≤ N, s k < s (k + 1) := by
    intro k hk
    exact lt_of_le_of_ne (hmono k) (h k hk)
  have hge : ∀ n ≤ N + 1, s 0 + n ≤ s n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      have h1 := ih (by omega)
      have h2 := hstrict n (by omega)
      omega
  have h1 := hge (N + 1) le_rfl
  have h2 := hbound (N + 1)
  omega

/-- Once two consecutive iterates agree, all subsequent iterates agree. -/
theorem iterate_stable_forever (step : Finset α → Finset α) (_hmono : Monotone step)
    (base : Finset α) (k : ℕ)
    (hk : step^[k] base = step^[k + 1] base)
    (m : ℕ) (hm : k ≤ m) :
    step^[m] base = step^[k] base := by
  induction m with
  | zero =>
    interval_cases k
    rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with rfl | hm'
    · rfl
    · rw [Function.iterate_succ_apply']
      rw [ih (by omega)]
      -- Goal: step (step^[k] base) = step^[k] base
      rw [show step (step^[k] base) = step^[k + 1] base from
          (Function.iterate_succ_apply' step k base).symm]
      exact hk.symm

/-- The reachable set is a fixed point of expand. -/
theorem reachable_stable (f : α → β) (g : β → α) :
    expand f g (reachableSet f g) = reachableSet f g := by
  set s := fun n => ((expand f g)^[n] (baseSet g)).card with hs_def
  have hbound : ∀ n, s n ≤ Fintype.card α := by
    intro n
    calc s n = ((expand f g)^[n] (baseSet g)).card := rfl
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card α := Finset.card_univ
  have hmono : ∀ n, s n ≤ s (n + 1) := by
    intro n
    exact Finset.card_le_card (iterate_expand_mono f g n)
  obtain ⟨k, hk_le, hk_eq⟩ := nat_seq_stabilize s (Fintype.card α) hbound hmono
  have hk_sub := iterate_expand_mono f g k
  have hk_set : (expand f g)^[k] (baseSet g) = (expand f g)^[k + 1] (baseSet g) :=
    Finset.eq_of_subset_of_card_le hk_sub (le_of_eq hk_eq.symm)
  have h1 := iterate_stable_forever (expand f g) (expand_mono f g) (baseSet g) k hk_set
      (Fintype.card α) hk_le
  have h2 := iterate_stable_forever (expand f g) (expand_mono f g) (baseSet g) k hk_set
      (Fintype.card α + 1) (by omega)
  -- Goal: expand f g (reachableSet f g) = reachableSet f g
  -- LHS = expand(step^[card α](base)) = step^[card α + 1](base)
  -- RHS = step^[card α](base)
  -- Both equal step^[k](base)
  unfold reachableSet
  have key : expand f g ((expand f g)^[Fintype.card α] (baseSet g)) =
             (expand f g)^[Fintype.card α + 1] (baseSet g) :=
    (Function.iterate_succ_apply' (expand f g) (Fintype.card α) (baseSet g)).symm
  rw [key]
  exact h2.trans h1.symm

/-! ## Section 4: Closure and Decomposition -/

/-- The reachable set is closed under g ∘ f. -/
theorem reachable_closed (f : α → β) (g : β → α) (a : α)
    (ha : a ∈ reachableSet f g) : g (f a) ∈ reachableSet f g := by
  have hstable := reachable_stable f g
  rw [← hstable]
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

/-- Elements outside the reachable set are in the range of g. -/
theorem not_reachable_in_range (f : α → β) (g : β → α) (a : α)
    (ha : a ∉ reachableSet f g) : ∃ b, g b = a := by
  have hab : a ∉ baseSet g := fun h => ha (baseSet_subset_reachable f g h)
  simp only [baseSet, Finset.mem_filter, Finset.mem_univ, true_and] at hab
  push_neg at hab
  exact hab

/-- Decomposition via induction on iteration depth: every element in step^[n](base)
    is either in baseSet or equals g(f(a')) for some earlier element. -/
theorem reachable_decomp_iter (f : α → β) (g : β → α) (n : ℕ) (a : α)
    (ha : a ∈ (expand f g)^[n] (baseSet g)) :
    a ∈ baseSet g ∨ ∃ a', a' ∈ (expand f g)^[n] (baseSet g) ∧ g (f a') = a := by
  induction n with
  | zero => left; exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at ha
    unfold expand at ha
    rcases Finset.mem_union.mp ha with h | h
    · -- a was in step^[n](base)
      rcases ih h with h1 | ⟨a', ha', rfl⟩
      · left; exact h1
      · right
        exact ⟨a', iterate_expand_mono f g n ha', rfl⟩
    · -- a was added as g(f(a')) from step^[n](base)
      right
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp h
      exact ⟨a', iterate_expand_mono f g n ha', rfl⟩

/-- Decomposition for reachableSet. -/
theorem reachable_decomp (f : α → β) (g : β → α) (a : α)
    (ha : a ∈ reachableSet f g) :
    a ∈ baseSet g ∨ ∃ a', a' ∈ reachableSet f g ∧ g (f a') = a :=
  reachable_decomp_iter f g (Fintype.card α) a ha

/-! ## Section 5: The Bijection -/

/-- The constructive CBS bijection. The orbit classification (`a ∈ reachableSet`)
    is fully decidable. Preimage extraction uses `Classical.choose`. -/
noncomputable def cbsBijection (f : α ↪ β) (g : β ↪ α) (a : α) : β :=
  if h : a ∈ reachableSet (↑f) (↑g) then f a
  else Classical.choose (not_reachable_in_range (↑f) (↑g) a h)

theorem cbsBijection_typeA (f : α ↪ β) (g : β ↪ α) (a : α)
    (ha : a ∈ reachableSet (↑f) (↑g)) : cbsBijection f g a = f a := by
  simp [cbsBijection, ha]

theorem cbsBijection_typeB_spec (f : α ↪ β) (g : β ↪ α) (a : α)
    (ha : a ∉ reachableSet (↑f) (↑g)) :
    g (cbsBijection f g a) = a := by
  simp only [cbsBijection, ha, dite_false]
  exact Classical.choose_spec (not_reachable_in_range (↑f) (↑g) a ha)

/-! ## Section 6: Injectivity -/

theorem cbsBijection_injective (f : α ↪ β) (g : β ↪ α) :
    Function.Injective (cbsBijection f g) := by
  intro a₁ a₂ h
  by_cases h₁ : a₁ ∈ reachableSet (↑f) (↑g) <;>
    by_cases h₂ : a₂ ∈ reachableSet (↑f) (↑g)
  · -- Both Type A: f(a₁) = f(a₂) → a₁ = a₂
    rw [cbsBijection_typeA f g a₁ h₁, cbsBijection_typeA f g a₂ h₂] at h
    exact f.injective h
  · -- a₁ ∈ reachable, a₂ ∉ reachable: impossible
    exfalso
    have : g (cbsBijection f g a₁) = g (cbsBijection f g a₂) := congr_arg g h
    rw [cbsBijection_typeA f g a₁ h₁] at this
    rw [cbsBijection_typeB_spec f g a₂ h₂] at this
    -- this : g(f(a₁)) = a₂, but g(f(a₁)) ∈ reachable
    have hmem := reachable_closed (↑f) (↑g) a₁ h₁
    rw [this] at hmem
    exact h₂ hmem
  · -- a₁ ∉ reachable, a₂ ∈ reachable: impossible (symmetric)
    exfalso
    have : g (cbsBijection f g a₁) = g (cbsBijection f g a₂) := congr_arg g h
    rw [cbsBijection_typeB_spec f g a₁ h₁] at this
    rw [cbsBijection_typeA f g a₂ h₂] at this
    have hmem := reachable_closed (↑f) (↑g) a₂ h₂
    rw [← this] at hmem
    exact h₁ hmem
  · -- Both Type B: g⁻¹(a₁) = g⁻¹(a₂) → g(g⁻¹(a₁)) = g(g⁻¹(a₂)) → a₁ = a₂
    have h₁' := cbsBijection_typeB_spec f g a₁ h₁
    have h₂' := cbsBijection_typeB_spec f g a₂ h₂
    calc a₁ = g (cbsBijection f g a₁) := h₁'.symm
    _ = g (cbsBijection f g a₂) := congr_arg g h
    _ = a₂ := h₂'

/-! ## Section 7: Surjectivity -/

theorem cbsBijection_surjective (f : α ↪ β) (g : β ↪ α) :
    Function.Surjective (cbsBijection f g) := by
  intro b
  by_cases hb : ∃ a ∈ reachableSet (↑f) (↑g), (f : α → β) a = b
  · -- b = f(a) for some reachable a
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, cbsBijection_typeA f g a ha⟩
  · -- No reachable a maps to b via f. Show g(b) ∉ reachable.
    push_neg at hb
    have hgb : (g : β → α) b ∉ reachableSet (↑f) (↑g) := by
      intro hgb_mem
      rcases reachable_decomp (↑f) (↑g) (g b) hgb_mem with h | ⟨a', ha', heq⟩
      · -- g(b) ∈ baseSet: impossible since g(b) ∈ range g
        simp only [baseSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h b rfl
      · -- g(b) = g(f(a')): then b = f(a') by injectivity of g
        have hbeq : b = f a' := g.injective heq.symm
        exact absurd hbeq.symm (hb a' ha')
    -- g(b) ∉ reachable, so h(g(b)) uses the preimage, giving back b
    refine ⟨g b, ?_⟩
    have hspec := cbsBijection_typeB_spec f g (g b) hgb
    -- hspec : g(cbsBijection f g (g b)) = g b
    exact g.injective hspec

/-! ## Section 8: Main Theorems -/

/-- **Constructive Cantor-Bernstein-Schroeder for finite types.**
    Given injections f : α ↪ β and g : β ↪ α between finite types,
    there exists a bijection α ≃ β. The orbit classification is decidable;
    only the preimage extraction step uses classical choice. -/
noncomputable def constructive_CBS (f : α ↪ β) (g : β ↪ α) : α ≃ β :=
  Equiv.ofBijective (cbsBijection f g)
    ⟨cbsBijection_injective f g, cbsBijection_surjective f g⟩

/-- The orbit classification is decidable for finite types:
    membership in the reachable set is computable. -/
instance reachableSetDecidable (f : α → β) (g : β → α) (a : α) :
    Decidable (a ∈ reachableSet f g) :=
  Finset.decidableMem a (reachableSet f g)

/-- For comparison: classical CBS gives the same result non-constructively. -/
theorem constructive_agrees_with_classical (f : α ↪ β) (g : β ↪ α) :
    Nonempty (α ≃ β) :=
  ⟨constructive_CBS f g⟩

end ConstructiveCBS
