/-
  Brouwer Fixed Point OQ-04-OQ-03-OQ-01:
  The Singleton Correspondence Bridge — Single-Valued Fixed Point Theorems
  as Special Cases of Set-Valued Ones

  Context (parent chain):
  - OQ-04       : Kakutani Fixed Point Theorem (set-valued, finite-dim)
  - OQ-04-OQ-03 : Fan-Glicksberg extension to locally convex spaces
                  (both stated as axioms — genuine open/hard formalizations)

  This child isolates the ONE piece of that hierarchy that is fully
  machine-checkable with zero axioms: the precise sense in which every
  single-valued fixed point theorem (Brouwer, Schauder) is a special case
  of its set-valued counterpart (Kakutani, Fan-Glicksberg).

  The bridge is the "singleton correspondence"
        F_f (x) := { f x }.
  We prove, with no axioms:

    1. F_f is upper hemicontinuous  ⟺  f is continuous
    2. F_f always has nonempty values
    3. F_f has closed values         (in a T1 space)
    4. F_f has convex values         (in a real vector space)
    5. x is a fixed point of F_f     ⟺  f x = x
    6. Reduction theorem: any set-valued fixed point principle satisfying
       Kakutani's hypotheses yields the corresponding single-valued
       (Brouwer-type) fixed point theorem — stated axiom-free, taking the
       set-valued principle as a hypothesis rather than an axiom.

  Together these say: single-valued fixed point theory embeds faithfully
  into set-valued fixed point theory, and the embedding preserves exactly
  the hypotheses (continuity ↦ upper hemicontinuity + nonempty/closed/convex
  values) and conclusions (fixed points).

  All results are `verified`, 0-axiom, 0-sorry.

  References:
  - Kakutani, "A generalization of Brouwer's fixed point theorem" (1941)
  - Border, "Fixed Point Theorems with Applications to Economics and
    Game Theory" (1985), Ch. 15 (singleton correspondences)
-/

import Mathlib

namespace BrouwerOQ04OQ03OQ01

open Set

-- ============================================================
-- PART I: Set-valued maps (mirrors the parent OQ-04-OQ-03 file)
-- ============================================================

/-- A set-valued map (correspondence) from `X` to `Y`. -/
def SetValuedMap (X Y : Type*) := X → Set Y

/-- Upper hemicontinuity: the "upper preimage" of every open set is open.
    Equivalently, for every open `U ⊇ F x` there is a neighbourhood `V` of
    `x` with `F y ⊆ U` for all `y ∈ V`. -/
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : SetValuedMap X Y) : Prop :=
  ∀ U : Set Y, IsOpen U → IsOpen {x | F x ⊆ U}

/-- A set-valued map has nonempty values. -/
def HasNonemptyValues {X Y : Type*} (F : SetValuedMap X Y) : Prop :=
  ∀ x, (F x).Nonempty

/-- A set-valued map has closed values. -/
def HasClosedValues {X Y : Type*} [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ x, IsClosed (F x)

/-- A set-valued map has convex values (in a real vector space). -/
def HasConvexValues {X Y : Type*} [AddCommMonoid Y] [Module ℝ Y]
    (F : SetValuedMap X Y) : Prop :=
  ∀ x, Convex ℝ (F x)

/-- `x` is a fixed point of a self-correspondence: `x ∈ F x`. -/
def IsFixedPoint {X : Type*} (F : SetValuedMap X X) (x : X) : Prop :=
  x ∈ F x

/-- The singleton correspondence attached to a single-valued map `f`. -/
def singletonMap {X Y : Type*} (f : X → Y) : SetValuedMap X Y := fun x => {f x}

-- ============================================================
-- PART II: The key set identity
-- ============================================================

/-- The upper preimage of `U` under the singleton correspondence of `f`
    is exactly the ordinary preimage `f ⁻¹' U`. This is the computational
    core of every result below. -/
theorem upperPreimage_singletonMap {X Y : Type*} (f : X → Y) (U : Set Y) :
    {x | singletonMap f x ⊆ U} = f ⁻¹' U := by
  ext x
  simp only [singletonMap, mem_setOf_eq, singleton_subset_iff, mem_preimage]

-- ============================================================
-- PART III: Continuity ⟺ upper hemicontinuity for singletons
-- ============================================================

/-- **Bridge (topology).** The singleton correspondence `F_f (x) = {f x}` is
    upper hemicontinuous if and only if `f` is continuous. This is precisely
    why Brouwer's continuous-map hypothesis matches Kakutani's upper
    hemicontinuity hypothesis. -/
theorem singleton_uhc_iff_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsUpperHemicontinuous (singletonMap f) ↔ Continuous f := by
  rw [continuous_def]
  constructor
  · intro h U hU
    have := h U hU
    rwa [upperPreimage_singletonMap] at this
  · intro h U hU
    have := h U hU
    rw [upperPreimage_singletonMap]
    exact this

-- ============================================================
-- PART IV: The remaining Kakutani hypotheses for singletons
-- ============================================================

/-- Singleton values are always nonempty. -/
theorem singleton_hasNonemptyValues {X Y : Type*} (f : X → Y) :
    HasNonemptyValues (singletonMap f) :=
  fun x => ⟨f x, rfl⟩

/-- Singleton values are closed in a T1 space. -/
theorem singleton_hasClosedValues {X Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (f : X → Y) : HasClosedValues (singletonMap f) :=
  fun _ => isClosed_singleton

/-- Singleton values are convex in a real vector space. -/
theorem singleton_hasConvexValues {X Y : Type*} [AddCommMonoid Y] [Module ℝ Y]
    (f : X → Y) : HasConvexValues (singletonMap f) :=
  fun _ => convex_singleton _

-- ============================================================
-- PART V: Fixed points transfer exactly
-- ============================================================

/-- **Bridge (fixed points).** `x` is a fixed point of the singleton
    correspondence of `f` iff `x` is an ordinary fixed point `f x = x`. -/
theorem singleton_isFixedPoint_iff {X : Type*} (f : X → X) (x : X) :
    IsFixedPoint (singletonMap f) x ↔ f x = x := by
  unfold IsFixedPoint singletonMap
  rw [mem_singleton_iff]
  exact eq_comm

-- ============================================================
-- PART VI: Reduction theorem (axiom-free)
-- ============================================================

/-- **Brouwer reduces to Kakutani.** Suppose we are handed *any* set-valued
    fixed point principle `kakutani`: on a fixed nonempty compact convex
    domain `K ⊆ Y`, every self-correspondence with nonempty, closed, convex
    values that is upper hemicontinuous and maps `K` into itself has a fixed
    point in `K`. Then every continuous single-valued self-map `f` of `K`
    has an ordinary fixed point in `K`.

    This is stated with the set-valued principle as a *hypothesis*, so the
    theorem itself is fully verified and axiom-free: it is the rigorous
    content of "single-valued ⊆ set-valued". Instantiating `kakutani` with
    the actual Kakutani/Fan-Glicksberg theorem recovers the classical
    Brouwer/Schauder fixed point theorem on `K`. -/
theorem brouwer_from_kakutani_principle
    {Y : Type*} [TopologicalSpace Y] [T1Space Y] [AddCommMonoid Y] [Module ℝ Y]
    (K : Set Y)
    (kakutani : ∀ F : SetValuedMap Y Y,
      (∀ x ∈ K, F x ⊆ K) →
      IsUpperHemicontinuous F →
      HasNonemptyValues F →
      HasClosedValues F →
      HasConvexValues F →
      ∃ x ∈ K, IsFixedPoint F x)
    (f : Y → Y) (hf : ∀ x ∈ K, f x ∈ K) (hcont : Continuous f) :
    ∃ x ∈ K, f x = x := by
  obtain ⟨x, hxK, hx⟩ := kakutani (singletonMap f)
    (fun x hx => by
      simp only [singletonMap, singleton_subset_iff]; exact hf x hx)
    ((singleton_uhc_iff_continuous f).mpr hcont)
    (singleton_hasNonemptyValues f)
    (singleton_hasClosedValues f)
    (singleton_hasConvexValues f)
  exact ⟨x, hxK, (singleton_isFixedPoint_iff f x).mp hx⟩

end BrouwerOQ04OQ03OQ01
