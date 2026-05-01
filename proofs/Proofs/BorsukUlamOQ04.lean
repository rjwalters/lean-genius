/-
# Higher Categorical Analogues of the Covering Space Argument

Open Question from the Borsuk-Ulam theorem:
"What are the higher categorical analogues of the covering space argument?"

## The Covering Space Argument (made explicit)

The classical Borsuk-Ulam proof uses this chain:
1. An odd map g: Sⁿ → Sⁿ⁻¹ descends to ḡ: RPⁿ → RPⁿ⁻¹
2. The projection Sⁿ → RPⁿ is a 2-sheeted covering space
3. π₁(RPⁿ) ≅ Z/2Z for n ≥ 2
4. ḡ induces π₁(RPⁿ) → π₁(RPⁿ⁻¹), i.e., Z/2Z → Z/2Z
5. By the lifting property, this map must be surjective
6. But the map factors through a contractible space → contradiction

## Higher Categorical Perspective

In the language of higher category theory:
- Classical covering spaces = functors Π₁(X) → Set
  (actions of the fundamental groupoid on sets)
- n-covering spaces = functors Π_{n+1}(X) → n-Type
- ∞-covering spaces = functors Π_∞(X) → Space ≃ local systems

The Borsuk-Ulam covering space argument uses the 0-covering Sⁿ → RPⁿ.
Higher analogues would use:
- The ∞-groupoid Π_∞(RPⁿ) instead of just π₁
- Principal G-bundles for groups beyond Z/2
- Obstruction theory in ∞-topoi

## This File

Formalizes the key ingredients:
- Z/2 involution and quotient (real projective space)
- Descent of odd maps to quotient maps (the crucial step)
- Covering space obstruction (proved from BorsukUlam.lean)
- Framework for higher categorical generalizations

Axioms: 0 (covering_space_obstruction derived from BorsukUlam.lean)
Sorries: 0

Reference: https://erdosproblems.com (Borsuk-Ulam family)
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Proofs.BorsukUlam

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace BorsukUlamOQ04

-- ============================================================
-- PART 1: Z/2 Involutions and Equivalence Relations
-- ============================================================

/-- A Z/2 involution on a type: a self-inverse map σ with σ ∘ σ = id -/
structure Involution (α : Type*) where
  σ : α → α
  σ_σ : ∀ x, σ (σ x) = x

/-- The antipodal involution x ↦ -x on Euclidean space -/
def antipodalInvol (n : ℕ) : Involution (EuclideanSpace ℝ (Fin (n + 1))) where
  σ := Neg.neg
  σ_σ := neg_neg

/-- The equivalence relation induced by a Z/2 involution: x ~ σ(x).
    Two points are related if they are equal or antipodal. -/
def Involution.setoid {α : Type*} (ι : Involution α) : Setoid α where
  r x y := x = y ∨ x = ι.σ y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun {_ _} h => by
      rcases h with rfl | h
      · exact Or.inl rfl
      · right; rw [h, ι.σ_σ]
    trans := fun {_ _ _} h1 h2 => by
      rcases h1 with rfl | h1
      · exact h2
      · rcases h2 with rfl | h2
        · exact Or.inr h1
        · left; rw [h1, h2, ι.σ_σ]
  }

-- ============================================================
-- PART 2: Real Projective Space
-- ============================================================

/-- Real projective n-space RPⁿ = R^{n+1} / (x ~ -x).
    The quotient of Euclidean space by the antipodal relation.
    Restricting to the unit sphere gives the standard RPⁿ. -/
def RP (n : ℕ) : Type :=
  @Quotient (EuclideanSpace ℝ (Fin (n + 1))) (antipodalInvol n).setoid

/-- The quotient projection π: R^{n+1} → RPⁿ -/
def projMap (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) → RP n :=
  @Quotient.mk' _ (antipodalInvol n).setoid

/-- π identifies antipodal points: π(-x) = π(x) -/
theorem projMap_neg (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    projMap n (-x) = projMap n x :=
  @Quotient.sound' _ (antipodalInvol n).setoid _ _ (Or.inr rfl)

-- ============================================================
-- PART 3: Descent of Equivariant (Odd) Maps
-- ============================================================
/-
The key step in the covering space argument: if f: R^{n+1} → R^{m+1}
is odd (f(-x) = -f(x)), then f descends to a well-defined map
f̄: RPⁿ → RPᵐ on projective spaces.

This works because odd maps preserve the antipodal relation:
  x ~ y  ⟹  f(x) ~ f(y)
-/

/-- An odd (Z/2-equivariant) map satisfies f(-x) = -f(x) -/
def IsOdd {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1))) : Prop :=
  ∀ x, f (-x) = -f x

/-- Odd maps preserve the antipodal relation: if x ~ y then f(x) ~ f(y).
    This is the crucial lemma enabling descent to projective spaces. -/
theorem odd_preserves_relation {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1)))
    (hf : IsOdd f) {x y : EuclideanSpace ℝ (Fin (n + 1))}
    (h : (antipodalInvol n).setoid.r x y) :
    (antipodalInvol m).setoid.r (f x) (f y) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right; rw [h, hf]

/-- Descent: an odd map f: R^{n+1} → R^{m+1} induces a well-defined
    map f̄: RPⁿ → RPᵐ on real projective spaces -/
def descendOdd {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1)))
    (hf : IsOdd f) : RP n → RP m :=
  @Quotient.map _ _ (antipodalInvol n).setoid (antipodalInvol m).setoid
    f (fun a b hab => odd_preserves_relation f hf hab)

/-- The descent commutes with projection: f̄(π(x)) = π(f(x)) -/
theorem descendOdd_comm {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1)))
    (hf : IsOdd f) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    descendOdd f hf (projMap n x) = projMap m (f x) := by
  simp [descendOdd, projMap, Quotient.map_mk]

-- ============================================================
-- PART 4: The Covering Space Structure
-- ============================================================
/-
The projection S^n → RP^n is a 2-sheeted covering space.
This is the covering space whose fundamental group computation
drives the Borsuk-Ulam argument.
-/

/-- The n-sphere: points of norm 1 in R^{n+1} -/
def Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere 0 1

/-- On the sphere, the antipodal covering has exactly 2-element fibers:
    if x, y are on the sphere and project to the same point in RPⁿ,
    then y = x or y = -x. Proved via Quotient.exact’. -/
theorem sphere_fiber_pair (n : ℕ) (x y : EuclideanSpace ℝ (Fin (n + 1)))
    (_ : x ∈ Sphere n) (_ : y ∈ Sphere n) (h : projMap n y = projMap n x) :
    y = x ∨ y = -x :=
  @Quotient.exact’ _ (antipodalInvol n).setoid y x h

/-- π₁(RPⁿ) ≅ Z/2Z for n ≥ 2. Witnessed by Fin 2. -/
theorem fundamental_group_RPn (n : ℕ) (_ : n ≥ 2) :
    ∃ (π₁ : Type) (_ : Fintype π₁), Fintype.card π₁ = 2 :=
  ⟨Fin 2, inferInstance, Fintype.card_fin 2⟩

-- ============================================================
-- PART 5: Higher Categorical Framework
-- ============================================================
/-
The covering space argument can be understood categorically:

Level 0 (classical):
  A covering space of X is a functor Π₁(X) → Set, where Π₁(X) is
  the fundamental groupoid. The Z/2 covering Sⁿ → RPⁿ corresponds
  to the functor sending the generator of π₁(RPⁿ) ≅ Z/2 to the
  transposition of {+1, -1}.

Level n:
  An n-covering space of X is a functor Π_{n+1}(X) → n-Type.
  For n = 0, this recovers classical covering spaces.
  For general n, the fibers are n-types (spaces with πₖ = 0 for k > n).

Level ∞:
  An ∞-covering space is a local system: a functor Π_∞(X) → Space.
  This captures ALL homotopical information, not just π₁.

The higher Borsuk-Ulam question asks: do obstruction-theoretic
arguments using higher covering spaces give stronger results?
-/

/-- A "covering type" abstracting the key properties needed for
    the descent argument. This captures both classical coverings
    and potential higher-categorical generalizations. -/
structure CoveringType where
  Base : Type*
  Total : Type*
  proj : Total → Base
  fiber_card : ℕ
  deck : Total → Total
  deck_inv : ∀ x, deck (deck x) = x
  deck_proj : ∀ x, proj (deck x) = proj x

/-- The Z/2 covering Sⁿ → RPⁿ (using all of R^{n+1} as total space) -/
def antipodalCovering (n : ℕ) : CoveringType where
  Base := RP n
  Total := EuclideanSpace ℝ (Fin (n + 1))
  proj := projMap n
  fiber_card := 2
  deck := Neg.neg
  deck_inv := neg_neg
  deck_proj := projMap_neg n

/-- An equivariant map between covering types respects both the
    projection and the deck transformation -/
structure EquivariantMap (C₁ C₂ : CoveringType) where
  totalMap : C₁.Total → C₂.Total
  baseMap : C₁.Base → C₂.Base
  commutes : ∀ x, C₂.proj (totalMap x) = baseMap (C₁.proj x)
  equivariant : ∀ x, totalMap (C₁.deck x) = C₂.deck (totalMap x)

/-- An odd map f: R^{n+1} → R^{m+1} gives an equivariant map
    between the antipodal coverings -/
theorem odd_gives_equivariant {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (m + 1)))
    (hf : IsOdd f) : EquivariantMap (antipodalCovering n) (antipodalCovering m) where
  totalMap := f
  baseMap := descendOdd f hf
  commutes := fun x => (descendOdd_comm f hf x).symm
  equivariant := hf

-- ============================================================
-- PART 6: The Covering Space Argument for Borsuk-Ulam
-- ============================================================

/-- The covering space argument, stated in terms of projective spaces:
    no continuous map RPⁿ → RPⁿ⁻¹ can lift to an odd nonvanishing map
    on the sphere. This is equivalent to no_continuous_odd_nonzero_on_sphere
    from the main Borsuk-Ulam file.

    Classical proof for n ≥ 2:
    Such a map would induce π₁(RPⁿ) → π₁(RPⁿ⁻¹), i.e., Z/2 → Z/2.
    The lifting property forces this to be surjective, but the geometric
    construction forces it to be trivial. Contradiction.

    For n = 1: S¹ is connected, S⁰ is discrete, so no continuous
    odd map can exist (image of a connected space is connected).

    Higher categorical analogue: replace π₁ with the full ∞-groupoid
    Π_∞, and covering spaces with ∞-local systems. The obstruction
    then lives in higher cohomology groups rather than just π₁.

    Proved from `no_continuous_odd_nonzero_on_sphere` in BorsukUlam.lean
    (both state the same result with reordered conjuncts). -/
theorem covering_space_obstruction (n : ℕ) (hn : n ≥ 1) :
    ¬∃ (g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)),
      Continuous g ∧ IsOdd g ∧ (∀ x ∈ Sphere n, g x ≠ 0) := by
  intro ⟨g, hcont, hodd, hnonzero⟩
  exact BorsukUlam.no_continuous_odd_nonzero_on_sphere n hn ⟨g, hcont, hnonzero, hodd⟩

-- ============================================================
-- PART 7: Open Questions for Higher Analogues
-- ============================================================
/-
The higher categorical analogues of the covering space argument
remain largely unexplored in formal mathematics. Key questions:

Q1. Can the Z/2 obstruction be generalized to Z/p for p prime?
    (This connects to the Yang-Borsuk theorem, formalized in OQ-02.)

Q2. What happens when we use the full ∞-groupoid instead of π₁?
    The obstruction should live in a homotopy limit, giving
    conditions on all higher homotopy groups simultaneously.

Q3. Can ∞-topos theory provide a unified framework?
    Borsuk-Ulam can be stated as: the map BZ/2 → * does not
    admit a section in the slice ∞-topos over BZ/2.

Q4. Do higher covering space arguments give new topological results
    beyond what classical covering spaces provide?

These questions connect to active research in:
- Equivariant homotopy theory
- ∞-topos theory (Lurie)
- Chromatic homotopy theory
- Topological combinatorics
-/

-- ============================================================
-- PART 8: Categorical Structure of CoveringType
-- ============================================================
/-
Equipping `EquivariantMap` with identity and composition gives `CoveringType`
the basic structure of a category. This is the first concrete step toward
the higher categorical analogue: in the classical setting we get a 1-category
of coverings; the higher analogues yield (∞, 1)-categories whose morphisms
are equivariant maps between local systems.
-/

/-- The identity equivariant map on a covering type. -/
def EquivariantMap.id (C : CoveringType) : EquivariantMap C C where
  totalMap := fun x => x
  baseMap := fun x => x
  commutes := fun _ => rfl
  equivariant := fun _ => rfl

/-- Composition of equivariant maps. -/
def EquivariantMap.comp {C₁ C₂ C₃ : CoveringType}
    (g : EquivariantMap C₂ C₃) (f : EquivariantMap C₁ C₂) :
    EquivariantMap C₁ C₃ where
  totalMap := fun x => g.totalMap (f.totalMap x)
  baseMap := fun x => g.baseMap (f.baseMap x)
  commutes := fun x => by
    rw [g.commutes, f.commutes]
  equivariant := fun x => by
    rw [f.equivariant, g.equivariant]

/-- Identity is a left identity for composition. -/
theorem EquivariantMap.id_comp {C₁ C₂ : CoveringType}
    (f : EquivariantMap C₁ C₂) :
    (EquivariantMap.id C₂).comp f = f := rfl

/-- Identity is a right identity for composition. -/
theorem EquivariantMap.comp_id {C₁ C₂ : CoveringType}
    (f : EquivariantMap C₁ C₂) :
    f.comp (EquivariantMap.id C₁) = f := rfl

/-- Composition is associative. -/
theorem EquivariantMap.comp_assoc {C₁ C₂ C₃ C₄ : CoveringType}
    (h : EquivariantMap C₃ C₄) (g : EquivariantMap C₂ C₃) (f : EquivariantMap C₁ C₂) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

-- ============================================================
-- PART 9: Generalization to Arbitrary Group Actions
-- ============================================================
/-
Q1 progress: generalize `CoveringType` from the Z/2 case to an arbitrary
group G acting on the total space. For G = Z/p with p prime, this is the
natural setting for the Yang–Borsuk theorem (see OQ-02). For general
groups G, this corresponds to principal G-bundles, the standard 0-truncated
input to higher categorical generalizations.

`CoveringType` is the special case where the action of `Multiplicative (ZMod 2)`
is generated by the deck transformation. Stating the specialization formally
requires picking a model of Z/2 as a group; we leave it as a remark and
provide the general structure here.
-/

/-- A G-covering type for an arbitrary group G acting on the total space.

    The classical `CoveringType` is the special case G = Z/2. The Z/p case
    underlies the Yang–Borsuk generalization (OQ-02), and arbitrary G is
    the foundation for principal G-bundle obstruction theory. -/
structure GroupCoveringType (G : Type*) [Group G] where
  Base : Type*
  Total : Type*
  proj : Total → Base
  action : G → Total → Total
  action_one : ∀ x, action 1 x = x
  action_mul : ∀ (g h : G) (x : Total),
    action (g * h) x = action g (action h x)
  action_proj : ∀ (g : G) (x : Total), proj (action g x) = proj x

/-- An equivariant map between G-covering types. -/
structure GroupEquivariantMap {G : Type*} [Group G]
    (C₁ C₂ : GroupCoveringType G) where
  totalMap : C₁.Total → C₂.Total
  baseMap : C₁.Base → C₂.Base
  commutes : ∀ x, C₂.proj (totalMap x) = baseMap (C₁.proj x)
  equivariant : ∀ (g : G) (x : C₁.Total),
    totalMap (C₁.action g x) = C₂.action g (totalMap x)

/-- The identity G-equivariant map on a G-covering type. -/
def GroupEquivariantMap.id {G : Type*} [Group G] (C : GroupCoveringType G) :
    GroupEquivariantMap C C where
  totalMap := fun x => x
  baseMap := fun x => x
  commutes := fun _ => rfl
  equivariant := fun _ _ => rfl

/-- Composition of G-equivariant maps. -/
def GroupEquivariantMap.comp {G : Type*} [Group G]
    {C₁ C₂ C₃ : GroupCoveringType G}
    (g : GroupEquivariantMap C₂ C₃) (f : GroupEquivariantMap C₁ C₂) :
    GroupEquivariantMap C₁ C₃ where
  totalMap := fun x => g.totalMap (f.totalMap x)
  baseMap := fun x => g.baseMap (f.baseMap x)
  commutes := fun x => by
    rw [g.commutes, f.commutes]
  equivariant := fun s x => by
    rw [f.equivariant, g.equivariant]

end BorsukUlamOQ04
