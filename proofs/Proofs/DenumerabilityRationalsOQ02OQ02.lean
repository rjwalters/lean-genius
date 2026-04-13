import Mathlib

/-!
# ℝ as the Unique Complete Ordered Field

## Research Problem: denumerability-rationals-oq-02-oq-02

**Open Question**: Prove that ℝ is the unique complete ordered field, analogous to
Cantor's characterization of ℚ as the unique countable dense linear order.

## Mathematical Background

A **complete ordered field** is a field with a linear order such that:
1. The order is compatible with field operations
2. **Completeness**: every nonempty set bounded above has a supremum

The central theorem: up to order-preserving ring isomorphism, **ℝ is the only complete
ordered field**. This is the real-analytic analogue of Cantor's categoricity theorem for ℚ.

## Proof Strategy (Dedekind Cut Map)

Any complete ordered field F must:
1. Contain a copy of ℚ (prime subfield, characteristic 0)
2. Satisfy the Archimedean property (forced by completeness + ℚ copy)
3. Be determined by its Dedekind cuts: x = sup{q ∈ ℚ | (q : F) ≤ x}

The map φ : F → ℝ defined by φ(x) = sup{q ∈ ℚ | q ≤ x} is the unique isomorphism.
This is formalized in Mathlib as `ConditionallyCompleteLinearOrderedField.InducedMap`.

## Historical Context

Dedekind (1872) constructed ℝ from ℚ via cuts, implicitly showing uniqueness. The
categorical formulation — "ℝ is the unique structure satisfying its axioms" — was made
explicit in 20th-century algebra. It is now standard in analysis textbooks.

## Relation to ℚ Categoricity (Parent Proof OQ-02)

| Number System | Characterization | Isomorphism Type | Proof Method |
|---|---|---|---|
| ℚ | Unique CDLO without endpoints | Order isomorphism | Back-and-forth (Cantor) |
| ℝ | Unique complete ordered field | Ordered ring isomorphism | Dedekind cuts |

## Tags: analysis, ordered-fields, completeness, categoricity, real-numbers, dedekind-cuts
-/

namespace DenumerabilityRationalsOQ02OQ02

-- Open the induced map namespace to access `inducedOrderRingIso` and `uniqueOrderRingIso`
open ConditionallyCompleteLinearOrderedField.InducedMap

-- ============================================================================
-- Section 1: ℝ as a Complete Ordered Field
-- ============================================================================

/-- ℝ is a complete ordered field: the `ConditionallyCompleteLinearOrderedField` instance. -/
example : ConditionallyCompleteLinearOrderedField ℝ := inferInstance

/-- ℝ is Archimedean: for any x : ℝ, there exists n : ℕ with x < n. -/
theorem real_archimedean : Archimedean ℝ := inferInstance

/-- The least-upper-bound property for ℝ: every nonempty bounded-above set has a supremum. -/
theorem real_lub (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) :
    IsLUB S (sSup S) :=
  isLUB_csSup hne hbdd

-- ============================================================================
-- Section 2: The Dedekind Cut Isomorphism (Main Construction)
-- ============================================================================

/-- **Main Construction**: For any complete ordered field F, there is a canonical
    order-ring isomorphism F ≃+*o ℝ.

    This is the **Dedekind cut map**: φ(x) = sup{q ∈ ℚ | (q : F) ≤ x} ∈ ℝ.

    - **Well-defined**: By Archimedean property, the rational cut is nonempty and
      bounded above, so the supremum in ℝ exists.
    - **Ring homomorphism**: Preserved by the algebraic structure of cuts.
    - **Order-preserving**: x ≤ y implies {q | q ≤ x} ⊆ {q | q ≤ y}.
    - **Bijective**: Surjective (every real is a cut), injective (cuts determine elements). -/
noncomputable def isoToReal (F : Type*) [ConditionallyCompleteLinearOrderedField F] :
    F ≃+*o ℝ :=
  inducedOrderRingIso F ℝ

/-- The Dedekind cut isomorphism is order-preserving. -/
theorem isoToReal_mono (F : Type*) [ConditionallyCompleteLinearOrderedField F] :
    Monotone (isoToReal F) :=
  (isoToReal F).monotone

/-- The isomorphism fixes rationals: φ((q : F)) = (q : ℝ). -/
theorem isoToReal_ratCast (F : Type*) [ConditionallyCompleteLinearOrderedField F] (q : ℚ) :
    isoToReal F (q : F) = (q : ℝ) :=
  map_ratCast (isoToReal F) q

-- ============================================================================
-- Section 3: Uniqueness
-- ============================================================================

/-- **Uniqueness**: Any two order-ring isomorphisms F ≃+*o ℝ are equal.
    There is no choice: the Dedekind cut construction is canonical.

    Proof: Two such isomorphisms agree on ℚ (both fix rationals), and by density
    of ℚ in F and continuity (i.e., order-preservation), they agree everywhere. -/
theorem iso_to_real_unique (F : Type*) [ConditionallyCompleteLinearOrderedField F]
    (f g : F ≃+*o ℝ) : f = g := by
  haveI : Unique (F ≃+*o ℝ) := inferInstance
  exact Unique.eq_default f |>.trans (Unique.eq_default g).symm

/-- **Existence and Uniqueness**: there is exactly one ordered ring isomorphism F ≃+*o ℝ. -/
theorem iso_to_real_exists_unique (F : Type*) [ConditionallyCompleteLinearOrderedField F] :
    ∃! f : F ≃+*o ℝ, True :=
  ⟨isoToReal F, trivial, fun g _ => (iso_to_real_unique F g (isoToReal F)).symm⟩

-- ============================================================================
-- Section 4: Categoricity
-- ============================================================================

/-- **Categoricity**: Any two complete ordered fields are isomorphic as ordered rings.
    ℝ is the unique model of "complete ordered field" up to isomorphism. -/
noncomputable def completeOrderedFieldIso (F G : Type*)
    [ConditionallyCompleteLinearOrderedField F]
    [ConditionallyCompleteLinearOrderedField G] :
    F ≃+*o G :=
  inducedOrderRingIso F G

/-- The isomorphism between any two complete ordered fields is unique. -/
theorem complete_ordered_fields_iso_unique (F G : Type*)
    [ConditionallyCompleteLinearOrderedField F]
    [ConditionallyCompleteLinearOrderedField G]
    (f g : F ≃+*o G) : f = g := by
  haveI : Unique (F ≃+*o G) := inferInstance
  exact Unique.eq_default f |>.trans (Unique.eq_default g).symm

-- ============================================================================
-- Section 5: The Archimedean Property Is Forced by Completeness
-- ============================================================================

/-- **Theorem**: Every complete ordered field is Archimedean. Completeness implies
    Archimedean: if ℕ were bounded above in F, sup ℕ would exist, but sup ℕ - 1
    cannot be an upper bound, giving a contradiction.

    This shows there is no non-Archimedean complete ordered field. -/
theorem complete_ordered_field_archimedean (F : Type*)
    [ConditionallyCompleteLinearOrderedField F] : Archimedean F :=
  inferInstance

/-- ℕ is cofinal in every complete ordered field. -/
theorem nat_cofinal (F : Type*) [ConditionallyCompleteLinearOrderedField F]
    (x : F) : ∃ n : ℕ, x < n :=
  exists_nat_gt x

/-- ℤ is cofinal in both directions: for any x in a complete ordered field,
    there exists a negative integer less than x. -/
theorem int_below (F : Type*) [ConditionallyCompleteLinearOrderedField F]
    (x : F) : ∃ m : ℤ, (m : F) < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-x)
  exact ⟨-n, by push_cast; linarith⟩

-- ============================================================================
-- Section 6: ℚ Density in Every Complete Ordered Field
-- ============================================================================

/-- ℚ is order-dense in every complete ordered field: between any two elements
    of F there is a rational. This mirrors the density of ℚ in ℝ. -/
theorem rat_dense (F : Type*) [ConditionallyCompleteLinearOrderedField F]
    (x y : F) (h : x < y) : ∃ q : ℚ, x < q ∧ (q : F) < y :=
  exists_rat_btwn h

/-- The rational cast ℚ → F is strictly order-preserving. -/
theorem ratCast_strictMono (F : Type*) [ConditionallyCompleteLinearOrderedField F] :
    StrictMono ((↑) : ℚ → F) :=
  Rat.cast_strictMono

-- ============================================================================
-- Section 7: ℝ Has No Non-Trivial Automorphisms as an Ordered Field
-- ============================================================================

/-- ℝ has a unique automorphism as an ordered ring: the identity.
    This follows from categoricity: any automorphism ℝ ≃+*o ℝ is the unique element
    of the `Unique (ℝ ≃+*o ℝ)` instance. -/
theorem real_automorphism_unique (f : ℝ ≃+*o ℝ) : f = OrderRingIso.refl ℝ := by
  haveI : Unique (ℝ ≃+*o ℝ) := inferInstance
  exact Subsingleton.elim f (OrderRingIso.refl ℝ)

-- ============================================================================
-- Section 8: Main Theorem (Summary Statement)
-- ============================================================================

/-- **Main Theorem**: ℝ is (up to unique isomorphism) the unique complete ordered field.

    Precisely: for any type F carrying a `ConditionallyCompleteLinearOrderedField`
    structure, there exists a unique ordered ring isomorphism F ≃+*o ℝ.

    This is the categorical characterization of the real numbers. -/
theorem real_unique_complete_ordered_field (F : Type*)
    [ConditionallyCompleteLinearOrderedField F] :
    ∃! f : F ≃+*o ℝ, True :=
  iso_to_real_exists_unique F

-- ============================================================================
-- Section 9: Parallel with Cantor's Theorem for ℚ
-- ============================================================================

/-- The two great categoricity theorems of classical mathematics:

    **Cantor 1895 (ℚ)**: Any countable dense linear order without endpoints ≃o ℚ.
    **Dedekind/classical (ℝ)**: Any complete ordered field ≃+*o ℝ.

    Both show that a familiar number system is the unique model of its axioms. -/
theorem categoricity_parallel :
    (∀ (A : Type*) [LinearOrder A] [Countable A] [DenselyOrdered A]
       [NoMinOrder A] [NoMaxOrder A] [Nonempty A], Nonempty (A ≃o ℚ)) ∧
    (∀ (F : Type*) [ConditionallyCompleteLinearOrderedField F], Nonempty (F ≃+*o ℝ)) := by
  exact ⟨fun A _ _ _ _ _ _ => ⟨Order.iso_of_countable_dense A ℚ⟩,
         fun F _ => ⟨isoToReal F⟩⟩

end DenumerabilityRationalsOQ02OQ02
