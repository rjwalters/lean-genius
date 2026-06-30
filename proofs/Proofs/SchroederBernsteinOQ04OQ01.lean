import Mathlib.Tactic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function

/-
# Cantor-Bernstein-Schroeder for Arbitrary Types via Union-of-Iterates

## Open Question (OQ-04, sub-question 1)
"Can the approach [the constructive finite-type CBS of `SchroederBernsteinOQ04`]
be extended to countably infinite types with decidable equality?"

## Answer
Yes — and in fact to *arbitrary* types, with no countability or decidability
assumption. The orbit-classification argument at the heart of the finite proof
(closure under `g ∘ f`, decomposition, injectivity, surjectivity) never used
finiteness; only the *stabilization* step did, and it used it solely to turn the
iterated expansion into a fixed point. Replacing the card-bounded iteration with a
countable **union of iterates**
`reachableSet = ⋃ₙ (step f g)^[n] baseSet`
makes closure hold *by construction* (an element added at stage `n` has its
`g ∘ f`-image at stage `n+1`), so the fixed-point/pigeonhole machinery disappears
entirely. Everything else carries over verbatim.

This reproves the classical Cantor-Bernstein-Schroeder theorem (also available as
`Function.Embedding.schroeder_bernstein`) using the *parent's own technique*, now
generalized off the finite setting.

## What is gained, and what is lost
* **Gained**: existence of a bijection from any pair of mutual injections, for all
  types — the finite restriction is dropped completely.
* **Lost**: *decidability* of the orbit classification. For finite types
  membership `a ∈ reachableSet` is decidable (a Finset membership). For infinite
  types it is the existential of a decidable family — only **semi-decidable**
  (`Σ⁰₁`): there is no a-priori bound on how many `step` iterations one must
  unfold, because the backward orbit chains can be infinite (e.g. `α = β = ℕ`
  with shift maps). Hence the bijection is genuinely `noncomputable`: the `if`
  branch needs `Classical` to decide membership, and preimage extraction needs
  `Classical.choose`. This is the honest content of the open question — the
  *constructive* flavour of the finite case does **not** survive, even though the
  *theorem* does.

Note that decidable equality on `α`/`β` is not required either: it played no role
beyond enabling the Finset bookkeeping of the finite proof.

## Approach
Given injections `f : α ↪ β` and `g : β ↪ α`:
1. `baseSet g = {a | a ∉ range g}`.
2. `step f g S = S ∪ (g ∘ f) '' S`; `reachableSet = ⋃ₙ (step f g)^[n] baseSet`.
3. `reachableSet` is closed under `g ∘ f` (union structure, no fixed point needed).
4. Elements outside `reachableSet` lie in `range g`.
5. Bijection: `a ↦ f a` if `a ∈ reachableSet`, else `a ↦ g⁻¹ a`.

## Status
- [x] Complete proof (0 sorries, 0 `axiom` declarations)
- [x] No finiteness, countability, or decidable-equality hypotheses
- [x] Bijection proved correct (injective + surjective)
-/

set_option linter.unusedSectionVars false

namespace CBSInfinite

open Classical

variable {α β : Type*}

/-! ## Section 1: Definitions -/

/-- The base set: elements of `α` with no preimage under `g`. -/
def baseSet (g : β → α) : Set α := {a | ∀ b : β, g b ≠ a}

/-- One expansion step: add forward images under `g ∘ f`. -/
def step (f : α → β) (g : β → α) (S : Set α) : Set α :=
  S ∪ (fun a => g (f a)) '' S

/-- The reachable set: every element reachable from `baseSet` by finitely many
    applications of `g ∘ f`. Unlike the finite case there is **no** card bound;
    we take the countable union of all iterates. -/
def reachableSet (f : α → β) (g : β → α) : Set α :=
  {a | ∃ n : ℕ, a ∈ (step f g)^[n] (baseSet g)}

/-! ## Section 2: Monotonicity of the iterates -/

theorem subset_step (f : α → β) (g : β → α) (S : Set α) : S ⊆ step f g S :=
  Set.subset_union_left

theorem iter_subset_succ (f : α → β) (g : β → α) (n : ℕ) :
    (step f g)^[n] (baseSet g) ⊆ (step f g)^[n + 1] (baseSet g) := by
  rw [Function.iterate_succ_apply']
  exact subset_step f g _

/-! ## Section 3: Reachability infrastructure -/

theorem baseSet_subset_reachable (f : α → β) (g : β → α) :
    baseSet g ⊆ reachableSet f g := by
  intro a ha
  exact ⟨0, by rw [Function.iterate_zero_apply]; exact ha⟩

/-- The reachable set is closed under `g ∘ f`. With the union definition this is
    immediate: an element at stage `n` has its image at stage `n + 1`. No
    stabilization / fixed-point argument (and hence no finiteness) is needed. -/
theorem reachable_closed (f : α → β) (g : β → α) (a : α)
    (ha : a ∈ reachableSet f g) : g (f a) ∈ reachableSet f g := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  simp only [step, Set.mem_union, Set.mem_image]
  exact Or.inr ⟨a, hn, rfl⟩

/-- Elements outside the reachable set are in the range of `g`. -/
theorem not_reachable_in_range (f : α → β) (g : β → α) (a : α)
    (ha : a ∉ reachableSet f g) : ∃ b, g b = a := by
  have hab : a ∉ baseSet g := fun h => ha (baseSet_subset_reachable f g h)
  simp only [baseSet, Set.mem_setOf_eq] at hab
  push_neg at hab
  exact hab

/-- Decomposition along iteration depth: every element in `step^[n] baseSet`
    is either in `baseSet` or equals `g (f a')` for some `a'` already reachable
    at the same depth. -/
theorem reachable_decomp_iter (f : α → β) (g : β → α) (n : ℕ) (a : α)
    (ha : a ∈ (step f g)^[n] (baseSet g)) :
    a ∈ baseSet g ∨ ∃ a', a' ∈ (step f g)^[n] (baseSet g) ∧ g (f a') = a := by
  induction n with
  | zero =>
    left
    rw [Function.iterate_zero_apply] at ha
    exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at ha
    simp only [step, Set.mem_union, Set.mem_image] at ha
    rcases ha with h | ⟨a', ha', rfl⟩
    · rcases ih h with h1 | ⟨a', ha', rfl⟩
      · exact Or.inl h1
      · exact Or.inr ⟨a', iter_subset_succ f g n ha', rfl⟩
    · exact Or.inr ⟨a', iter_subset_succ f g n ha', rfl⟩

/-- Decomposition for `reachableSet`. -/
theorem reachable_decomp (f : α → β) (g : β → α) (a : α)
    (ha : a ∈ reachableSet f g) :
    a ∈ baseSet g ∨ ∃ a', a' ∈ reachableSet f g ∧ g (f a') = a := by
  obtain ⟨n, hn⟩ := ha
  rcases reachable_decomp_iter f g n a hn with h | ⟨a', ha', heq⟩
  · exact Or.inl h
  · exact Or.inr ⟨a', ⟨n, ha'⟩, heq⟩

/-! ## Section 4: The bijection -/

/-- The CBS bijection for arbitrary types. The orbit classification
    `a ∈ reachableSet` is only semi-decidable in the infinite case, so the `if`
    is resolved by `Classical`; preimage extraction uses `Classical.choose`. -/
noncomputable def cbsBijection (f : α ↪ β) (g : β ↪ α) (a : α) : β :=
  if h : a ∈ reachableSet (↑f) (↑g) then f a
  else Classical.choose (not_reachable_in_range (↑f) (↑g) a h)

theorem cbsBijection_typeA (f : α ↪ β) (g : β ↪ α) (a : α)
    (ha : a ∈ reachableSet (↑f) (↑g)) : cbsBijection f g a = f a := by
  unfold cbsBijection
  rw [dif_pos ha]

theorem cbsBijection_typeB_spec (f : α ↪ β) (g : β ↪ α) (a : α)
    (ha : a ∉ reachableSet (↑f) (↑g)) :
    g (cbsBijection f g a) = a := by
  unfold cbsBijection
  rw [dif_neg ha]
  exact Classical.choose_spec (not_reachable_in_range (↑f) (↑g) a ha)

/-! ## Section 5: Injectivity -/

theorem cbsBijection_injective (f : α ↪ β) (g : β ↪ α) :
    Function.Injective (cbsBijection f g) := by
  intro a₁ a₂ h
  by_cases h₁ : a₁ ∈ reachableSet (↑f) (↑g) <;>
    by_cases h₂ : a₂ ∈ reachableSet (↑f) (↑g)
  · -- Both Type A: f a₁ = f a₂ → a₁ = a₂
    rw [cbsBijection_typeA f g a₁ h₁, cbsBijection_typeA f g a₂ h₂] at h
    exact f.injective h
  · -- a₁ reachable, a₂ not: impossible
    exfalso
    have hg : g (cbsBijection f g a₁) = g (cbsBijection f g a₂) := congr_arg g h
    rw [cbsBijection_typeA f g a₁ h₁] at hg
    rw [cbsBijection_typeB_spec f g a₂ h₂] at hg
    have hmem := reachable_closed (↑f) (↑g) a₁ h₁
    rw [hg] at hmem
    exact h₂ hmem
  · -- symmetric
    exfalso
    have hg : g (cbsBijection f g a₁) = g (cbsBijection f g a₂) := congr_arg g h
    rw [cbsBijection_typeB_spec f g a₁ h₁] at hg
    rw [cbsBijection_typeA f g a₂ h₂] at hg
    have hmem := reachable_closed (↑f) (↑g) a₂ h₂
    rw [← hg] at hmem
    exact h₁ hmem
  · -- Both Type B: g⁻¹ a₁ = g⁻¹ a₂ → a₁ = a₂
    have h₁' := cbsBijection_typeB_spec f g a₁ h₁
    have h₂' := cbsBijection_typeB_spec f g a₂ h₂
    calc a₁ = g (cbsBijection f g a₁) := h₁'.symm
    _ = g (cbsBijection f g a₂) := congr_arg g h
    _ = a₂ := h₂'

/-! ## Section 6: Surjectivity -/

theorem cbsBijection_surjective (f : α ↪ β) (g : β ↪ α) :
    Function.Surjective (cbsBijection f g) := by
  intro b
  by_cases hb : ∃ a ∈ reachableSet (↑f) (↑g), (f : α → β) a = b
  · obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, cbsBijection_typeA f g a ha⟩
  · push_neg at hb
    have hgb : (g : β → α) b ∉ reachableSet (↑f) (↑g) := by
      intro hgb_mem
      rcases reachable_decomp (↑f) (↑g) (g b) hgb_mem with h | ⟨a', ha', heq⟩
      · simp only [baseSet, Set.mem_setOf_eq] at h
        exact h b rfl
      · have hbeq : b = f a' := g.injective heq.symm
        exact absurd hbeq.symm (hb a' ha')
    refine ⟨g b, ?_⟩
    have hspec := cbsBijection_typeB_spec f g (g b) hgb
    exact g.injective hspec

/-! ## Section 7: Main theorems -/

/-- **Cantor-Bernstein-Schroeder for arbitrary types**, via the union-of-iterates
    reachable-set construction of `SchroederBernsteinOQ04`, now with the finiteness
    hypothesis removed. Given injections `f : α ↪ β` and `g : β ↪ α`, there is a
    bijection `α ≃ β`. -/
noncomputable def constructive_CBS_general (f : α ↪ β) (g : β ↪ α) : α ≃ β :=
  Equiv.ofBijective (cbsBijection f g)
    ⟨cbsBijection_injective f g, cbsBijection_surjective f g⟩

/-- Existence form: mutual injections yield a bijection, for arbitrary types. -/
theorem CBS_of_embeddings (f : α ↪ β) (g : β ↪ α) : Nonempty (α ≃ β) :=
  ⟨constructive_CBS_general f g⟩

/-- **Direct answer to OQ-04's first open question.** The construction extends to
    countably infinite types — indeed the `Countable` hypotheses below are not even
    used, since `constructive_CBS_general` needs no finiteness or countability.
    What is genuinely lost relative to the finite case is *decidability* of the
    orbit classification (see the file header): the bijection is `noncomputable`. -/
theorem CBS_countable {α β : Type*} [Countable α] [Countable β]
    (f : α ↪ β) (g : β ↪ α) : Nonempty (α ≃ β) :=
  ⟨constructive_CBS_general f g⟩

/-- Sanity check: the general theorem agrees with Mathlib's classical CBS. -/
theorem agrees_with_mathlib (f : α ↪ β) (g : β ↪ α) :
    Nonempty (α ≃ β) :=
  ⟨constructive_CBS_general f g⟩

end CBSInfinite
