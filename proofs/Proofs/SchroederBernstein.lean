import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# The Schroeder-Bernstein Theorem

## What This Proves
We prove that if there exist injections f: A → B and g: B → A, then there
exists a bijection between A and B. This establishes that the cardinality
relation on sets is antisymmetric.

## Approach
- **Foundation (from Mathlib):** We use the `Function.Embedding.schroeder_bernstein`
  theorem from Mathlib which provides the core result. We also use `Equiv` for
  bijections and basic function properties.
- **Original Contributions:** We provide pedagogical wrapper theorems with
  different formulations, explicit documentation of the proof strategy, and
  connections to cardinality theory.
- **Proof Techniques Demonstrated:** Working with embeddings and equivalences,
  using Mathlib's cardinal infrastructure, alternative formulations of the
  same theorem.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.SetTheory.Cardinal.SchroederBernstein` : The core Schroeder-Bernstein theorem
- `Mathlib.Logic.Equiv.Defs` : Equivalence (bijection) definitions
- `Mathlib.Logic.Function.Basic` : Injective, Surjective, Bijective definitions
- `Mathlib.Tactic` : Standard tactic library

## Historical Note
The theorem is named after Ernst Schröder (1896) and Felix Bernstein (1898),
though it was first proven by Richard Dedekind in 1887 (unpublished). It's
also known as the Cantor-Bernstein-Schroeder theorem.

## Classical vs Constructive
This theorem requires classical logic (specifically, the law of excluded middle).
In constructive mathematics, it does not hold—in fact, it is equivalent to
excluded middle (assuming the axiom of infinity). The proof relies on partitioning
elements into orbits and making a non-constructive choice about which injection
to use for each orbit.

## Wiedijk's 100 Theorems: #25
-/

namespace SchroederBernstein

/-! ## Main Theorem -/

/-- **Schroeder-Bernstein Theorem (Function form)**: Given injections
    f : α → β and g : β → α, there exists a bijection between α and β.

    This is the fundamental result establishing that cardinality is
    antisymmetric: if |A| ≤ |B| and |B| ≤ |A|, then |A| = |B|. -/
theorem schroeder_bernstein {α : Type*} {β : Type*}
    (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h :=
  -- Mathlib's schroeder_bernstein directly gives us this
  Function.Embedding.schroeder_bernstein hf hg

/-- **Schroeder-Bernstein (Equivalence form)**: Given injections both ways,
    we can construct an actual equivalence (bijection with explicit inverse).
    This uses classical choice to extract from the existence proof. -/
noncomputable def schroeder_bernstein_equiv {α : Type*} {β : Type*}
    (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    α ≃ β :=
  -- Extract the equivalence from Nonempty using classical choice
  Classical.choice (Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩)

/-! ## Embedding Formulation -/

/-- An embedding is an injective function packaged with its injectivity proof. -/
example {α β : Type*} (e : α ↪ β) : Function.Injective e := e.injective

/-- **Schroeder-Bernstein (Embedding form)**: Given embeddings both ways,
    there exists an equivalence. This is the form most directly available in Mathlib. -/
theorem schroeder_bernstein_embedding {α : Type*} {β : Type*}
    (f : α ↪ β) (g : β ↪ α) : Nonempty (α ≃ β) :=
  Function.Embedding.antisymm f g

/-- Extract an actual equivalence from embeddings (noncomputable). -/
noncomputable def schroeder_bernstein_embedding_equiv {α : Type*} {β : Type*}
    (f : α ↪ β) (g : β ↪ α) : α ≃ β :=
  Classical.choice (Function.Embedding.antisymm f g)

/-! ## Cardinality Formulation -/

universe u

/-- The cardinality ordering is antisymmetric: if α embeds into β and
    β embeds into α, then they have the same cardinality.
    Note: Both types must be in the same universe for cardinal equality. -/
theorem cardinal_antisymm {α β : Type u}
    (f : α ↪ β) (g : β ↪ α) :
    Cardinal.mk α = Cardinal.mk β :=
  Cardinal.mk_congr (Classical.choice (Function.Embedding.antisymm f g))

/-! ## The Proof Strategy

The classical proof of Schroeder-Bernstein works as follows:

1. **Partition α into orbits**: Starting from any element a ∈ α, we can trace
   its path: a → f(a) → g(f(a)) → f(g(f(a))) → ...
   Similarly, we can trace backwards using g⁻¹ and f⁻¹ where defined.

2. **Classify elements by orbit type**:
   - **Type A**: Elements whose backward chain terminates in α
   - **Type B**: Elements whose backward chain terminates in β
   - **Type C**: Elements with infinite backward chains (cycles)

3. **Define the bijection h piecewise**:
   - For Type A and C elements: h(a) = f(a)
   - For Type B elements: h(a) = g⁻¹(a)

4. **Verify h is a bijection**: The injectivity of f and g ensures this
   piecewise construction works correctly.

The key insight is that we can always "match up" the elements because
the injections preserve enough structure.
-/

/-! ## Corollaries -/

/-- If sets are in bijection via two injections, the composition
    g ∘ f is injective on the original set. -/
theorem composition_injective {α : Type*} {β : Type*}
    (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  hg.comp hf

/-- The inverse direction: β ≃ α also exists. -/
noncomputable def schroeder_bernstein_symm {α : Type*} {β : Type*}
    (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    β ≃ α :=
  (schroeder_bernstein_equiv f g hf hg).symm

/-! ## Set-Theoretic Formulation -/

/-- **Set version**: If there are injective functions between two sets
    (as subtypes), then the sets have equal cardinality. -/
theorem schroeder_bernstein_set {α : Type*} (A B : Set α)
    (f : A → B) (g : B → A)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Cardinal.mk A = Cardinal.mk B := by
  have h := Function.Embedding.schroeder_bernstein hf hg
  obtain ⟨bij, hbij⟩ := h
  exact Cardinal.mk_congr (Equiv.ofBijective bij hbij)

/-! ## Connection to Cantor's Theorem

Schroeder-Bernstein is often used together with Cantor's theorem.
While Cantor shows |A| < |P(A)| (strict inequality), Schroeder-Bernstein
allows us to establish equality when we have injections both ways.

For example, to show |ℝ| = |P(ℕ)|, we would:
1. Find an injection ℝ → P(ℕ) (via decimal expansions)
2. Find an injection P(ℕ) → ℝ (via binary representation)
3. Apply Schroeder-Bernstein to conclude |ℝ| = |P(ℕ)|
-/

/-! ## Visualization of the Proof

```
α                           β
●──f──→ ○                   ○──g──→ ●
         ↘                 ↙
           ○ ←──g── ●──f──→ ○
                     ↘
                       ...

Orbits:
  Type A: ●→○→●→○→...  (starts in α, use f throughout)
  Type B: ○→●→○→●→...  (starts in β, use g⁻¹ for α elements)
  Type C: ...→●→○→●→○→... (infinite both ways, use f)

The bijection h is:
  - h(a) = f(a) for Type A and C elements of α
  - h(a) = g⁻¹(a) for Type B elements of α
```
-/

#check schroeder_bernstein
#check schroeder_bernstein_equiv
#check schroeder_bernstein_embedding
#check cardinal_antisymm

end SchroederBernstein
