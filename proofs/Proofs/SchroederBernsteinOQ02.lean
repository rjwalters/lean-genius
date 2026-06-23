import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

/-
# Knaster-Tarski Proof of Schroeder-Bernstein

## Open Question (OQ-02)
"Can we formalize the Knaster-Tarski proof variant in Lean, making the fixed point explicit?"

## Answer
Yes. Given injections f : α → β and g : β → α, define the monotone operator
T(S) = (range g)ᶜ ∪ g '' (f '' S) on the complete lattice Set α. By the
Knaster-Tarski fixed point theorem (Mathlib's OrderHom.lfp), T has a least
fixed point S*. The bijection h : α → β is:
  h(a) = f(a)    if a ∈ S*
  h(a) = g⁻¹(a)  if a ∉ S*

This is conceptually distinct from both the orbit decomposition (parent proof,
which uses Mathlib's Function.Embedding.schroeder_bernstein) and the iterative
finite construction (OQ-04, which uses pigeonhole on Fintype). It connects
Schroeder-Bernstein to lattice theory via the Knaster-Tarski theorem.

## Approach
1. Define T : Set α →o Set α as the CBS operator
2. Take S* = T.lfp (Knaster-Tarski least fixed point)
3. Prove: S*ᶜ ⊆ range g (elements outside S* have g-preimages)
4. Prove: g(f(S*)) ⊆ S* (S* is closed under g ∘ f)
5. Define h piecewise on S* / S*ᶜ and prove bijective

## Status
- [x] Monotone operator T defined and bundled as OrderHom
- [x] Fixed point S* via OrderHom.lfp (Knaster-Tarski)
- [x] Bijection constructed with explicit fixed point partition
- [x] Injectivity proved (4 cases)
- [x] Surjectivity proved (2 cases)
- [x] Full Schroeder-Bernstein recovered as Equiv
-/

open Classical

noncomputable section

namespace KnasterTarskiCBS

variable {α β : Type*}

/-! ## Section 1: The Monotone Operator

Define T(S) = (range g)ᶜ ∪ g '' (f '' S). An element a is in T(S) iff:
- a has no g-preimage (base case: a ∉ range g), or
- the unique g-preimage of a lies in f(S) (inductive step).

T is monotone because Set.image preserves inclusion. -/

/-- The CBS operator T(S) = (range g)ᶜ ∪ g '' (f '' S). -/
def cbsOp (f : α → β) (g : β → α) (S : Set α) : Set α :=
  (Set.range g)ᶜ ∪ g '' (f '' S)

/-- T is monotone: S ⊆ S' implies T(S) ⊆ T(S'). -/
theorem cbsOp_mono (f : α → β) (g : β → α) : Monotone (cbsOp f g) := by
  intro S₁ S₂ h
  exact Set.union_subset_union_right _ (Set.image_subset g (Set.image_subset f h))

/-- T bundled as an order homomorphism, enabling Knaster-Tarski. -/
def cbsHom (f : α → β) (g : β → α) : Set α →o Set α where
  toFun := cbsOp f g
  monotone' := cbsOp_mono f g

/-! ## Section 2: The Knaster-Tarski Fixed Point

S* = lfp(T) is the least set satisfying T(S) = S. Its existence is
guaranteed by the Knaster-Tarski theorem on the complete lattice Set α. -/

/-- The Knaster-Tarski fixed point S* = lfp(T). -/
def fixedSet (f : α → β) (g : β → α) : Set α :=
  (cbsHom f g).lfp

/-- S* is a fixed point: T(S*) = S*. -/
theorem fixedSet_eq (f : α → β) (g : β → α) :
    cbsOp f g (fixedSet f g) = fixedSet f g :=
  (cbsHom f g).map_lfp

/-! ## Section 3: Properties of S*

From the fixed point equation S* = (range g)ᶜ ∪ g '' (f '' S*):
1. (range g)ᶜ ⊆ S*  (elements with no g-preimage are in S*)
2. S*ᶜ ⊆ range g  (elements outside S* have g-preimages)
3. g '' (f '' S*) ⊆ S*  (S* is closed under g ∘ f) -/

/-- Elements outside range g are in S*. -/
theorem compl_range_sub (f : α → β) (g : β → α) :
    (Set.range g)ᶜ ⊆ fixedSet f g := by
  intro a ha
  have h : a ∈ cbsOp f g (fixedSet f g) := Or.inl ha
  rwa [fixedSet_eq] at h

/-- Elements outside S* must be in range g. -/
theorem not_fixedSet_mem_range (f : α → β) (g : β → α) {a : α}
    (ha : a ∉ fixedSet f g) : a ∈ Set.range g := by
  by_contra h
  exact ha (compl_range_sub f g h)

/-- S* is closed under g ∘ f: g '' (f '' S*) ⊆ S*. -/
theorem gf_image_sub (f : α → β) (g : β → α) :
    g '' (f '' fixedSet f g) ⊆ fixedSet f g := by
  intro a ha
  have h : a ∈ cbsOp f g (fixedSet f g) := Or.inr ha
  rwa [fixedSet_eq] at h

/-- If a ∈ S*, then g(f(a)) ∈ S*. -/
theorem gf_mem (f : α → β) (g : β → α) {a : α} (ha : a ∈ fixedSet f g) :
    g (f a) ∈ fixedSet f g :=
  gf_image_sub f g ⟨f a, ⟨a, ha, rfl⟩, rfl⟩

/-- If g(b) ∈ S*, then b ∈ f '' S*. (Requires injectivity of g.) -/
theorem gb_mem_implies (f : α → β) (g : β → α) (hg : Function.Injective g)
    {b : β} (hgb : g b ∈ fixedSet f g) : b ∈ f '' fixedSet f g := by
  have h : g b ∈ cbsOp f g (fixedSet f g) := by rwa [← fixedSet_eq]
  change g b ∈ (Set.range g)ᶜ ∨ g b ∈ g '' (f '' fixedSet f g) at h
  rcases h with h' | ⟨x, hx, hgx⟩
  · exact absurd (Set.mem_range.mpr ⟨b, rfl⟩) h'
  · rwa [hg hgx] at hx

/-- Contrapositive: if b ∉ f '' S*, then g(b) ∉ S*. -/
theorem gb_not_fixedSet (f : α → β) (g : β → α) (hg : Function.Injective g)
    {b : β} (hb : b ∉ f '' fixedSet f g) : g b ∉ fixedSet f g :=
  fun h => hb (gb_mem_implies f g hg h)

/-! ## Section 4: The Bijection

The bijection h : α → β partitions α via the fixed point S*:
- For a ∈ S*: h(a) = f(a)
- For a ∉ S*: h(a) = g⁻¹(a), well-defined since a ∈ range g -/

/-- The Knaster-Tarski bijection. -/
noncomputable def ktBij (f : α → β) (g : β → α) (a : α) : β :=
  if h : a ∈ fixedSet f g then f a
  else (not_fixedSet_mem_range f g h).choose

/-- For a ∈ S*: h(a) = f(a). -/
theorem ktBij_of_mem (f : α → β) (g : β → α) {a : α}
    (ha : a ∈ fixedSet f g) : ktBij f g a = f a :=
  dif_pos ha

/-- For a ∉ S*: g(h(a)) = a (h inverts g). -/
theorem ktBij_of_not_mem_spec (f : α → β) (g : β → α) {a : α}
    (ha : a ∉ fixedSet f g) : g (ktBij f g a) = a := by
  have heq : ktBij f g a = (not_fixedSet_mem_range f g ha).choose := dif_neg ha
  rw [heq]
  exact (not_fixedSet_mem_range f g ha).choose_spec

/-! ## Section 5: Injectivity

Four cases based on S*-membership. The two mixed cases (one in S*, one not)
lead to contradictions via the closure property g(f(S*)) ⊆ S*. -/

theorem ktBij_injective (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (ktBij f g) := by
  intro a₁ a₂ heq
  by_cases h₁ : a₁ ∈ fixedSet f g <;> by_cases h₂ : a₂ ∈ fixedSet f g
  · -- Both in S*: f(a₁) = f(a₂) → a₁ = a₂
    rw [ktBij_of_mem f g h₁, ktBij_of_mem f g h₂] at heq
    exact hf heq
  · -- a₁ ∈ S*, a₂ ∉ S*: g(f(a₁)) = a₂ but g(f(a₁)) ∈ S*
    exfalso
    have hg12 := congr_arg g heq
    rw [ktBij_of_mem f g h₁, ktBij_of_not_mem_spec f g h₂] at hg12
    apply h₂; rw [← hg12]; exact gf_mem f g h₁
  · -- a₁ ∉ S*, a₂ ∈ S*: symmetric
    exfalso
    have hg12 := congr_arg g heq
    rw [ktBij_of_not_mem_spec f g h₁, ktBij_of_mem f g h₂] at hg12
    apply h₁; rw [hg12]; exact gf_mem f g h₂
  · -- Both outside S*: g(h(a₁)) = g(h(a₂)) → a₁ = a₂
    have hg12 := congr_arg g heq
    rw [ktBij_of_not_mem_spec f g h₁, ktBij_of_not_mem_spec f g h₂] at hg12
    exact hg12

/-! ## Section 6: Surjectivity

For b ∈ β: either b ∈ f(S*) with preimage in S*, or g(b) ∉ S*. -/

theorem ktBij_surjective (f : α → β) (g : β → α)
    (_hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Surjective (ktBij f g) := by
  intro b
  by_cases hb : b ∈ f '' fixedSet f g
  · -- b = f(a) for some a ∈ S*
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, ktBij_of_mem f g ha⟩
  · -- g(b) ∉ S*, so h(g(b)) = g⁻¹(g(b)) = b
    have hgb : g b ∉ fixedSet f g := gb_not_fixedSet f g hg hb
    exact ⟨g b, hg (ktBij_of_not_mem_spec f g hgb)⟩

/-! ## Section 7: Main Theorems -/

/-- **Knaster-Tarski Schroeder-Bernstein**: Given injections f : α → β
    and g : β → α, construct a bijection α ≃ β via the least fixed point
    of the CBS operator. -/
noncomputable def knasterTarski_equiv (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) : α ≃ β :=
  Equiv.ofBijective (ktBij f g)
    ⟨ktBij_injective f g hf hg, ktBij_surjective f g hf hg⟩

/-- The Knaster-Tarski proof recovers the standard Schroeder-Bernstein
    theorem: mutual injections imply existence of a bijection. -/
theorem knasterTarski_schroeder_bernstein (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h :=
  ⟨ktBij f g, ktBij_injective f g hf hg, ktBij_surjective f g hf hg⟩

/-- The fixed point partition is explicit and inspectable:
    S* = (range g)ᶜ ∪ g '' (f '' S*). -/
theorem fixedSet_characterization (f : α → β) (g : β → α) :
    fixedSet f g = (Set.range g)ᶜ ∪ g '' (f '' fixedSet f g) :=
  (fixedSet_eq f g).symm

end KnasterTarskiCBS

end
