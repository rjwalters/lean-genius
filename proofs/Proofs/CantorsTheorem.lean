import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

/-!
# Cantor's Theorem (Wiedijk #63)

## What This Proves
For any set A, there is no surjection from A to its power set P(A).

**Mathematical Statement**: ∀ A, ¬∃ f: A → 𝒫(A), Surjective(f)

## Approach
- **Foundation (from Mathlib):** We use `Function.cantor_surjective` from Mathlib
  which establishes this result. We also provide an original proof using the
  diagonal construction.
- **Original Contributions:** Alternative proof presentations, pedagogical
  documentation, and connection to `CantorDiagonalization.lean`.
- **Proof Techniques Demonstrated:** Diagonal argument, proof by contradiction,
  classical logic via `by_cases`.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Function.cantor_surjective` : Cantor's theorem (no surjection A → (A → Prop))
- `Function.Surjective` : Definition of surjectivity

## Historical Note
Georg Cantor proved this theorem in 1891. It establishes the foundation of
the theory of transfinite cardinal numbers: for any set A, we have |A| < |P(A)|.

## Connection to CantorDiagonalization.lean
This is the **general** form of Cantor's theorem (Wiedijk #63). The proof in
`CantorDiagonalization.lean` proves the **specific** case for binary sequences
(Wiedijk #22), showing that ℝ is uncountable. That proof also contains a
power set version (`cantor_powerset`) which we reference here.

The relationship:
- **Wiedijk #63 (this file)**: ∀ A, ¬∃ f: A → P(A) surjective (general)
- **Wiedijk #22 (CantorDiagonalization)**: ℕ → ℝ has no surjection (special case)
-/

namespace CantorsTheorem

/-! ## Main Theorem Using Mathlib -/

/-- **Cantor's Theorem (Wiedijk #63)**: For any type A, there is no surjection
    from A to its power set (A → Prop).

    This is Mathlib's `Function.cantor_surjective` with a cleaner statement.
    The proof uses the diagonal construction: if f were surjective, the set
    D = {x | x ∉ f x} would be in the range, leading to contradiction. -/
theorem cantor_no_surjection (A : Type*) :
    ¬∃ f : A → (A → Prop), Function.Surjective f :=
  fun ⟨f, hf⟩ => Function.cantor_surjective f hf

/-! ## Alternative: Using Set Instead of (A → Prop) -/

/-- The diagonal set: given f : A → Set A, construct the set of elements
    not contained in their own image. -/
def diagonalSet {A : Type*} (f : A → Set A) : Set A :=
  { x | x ∉ f x }

/-- **Cantor's Theorem (Set formulation)**: No function from A to Set A
    can be surjective.

    Proof: Assume f : A → Set A is surjective.
    1. Define D = {x ∈ A | x ∉ f(x)} (the diagonal set)
    2. Since f is surjective, ∃ b with f(b) = D
    3. Question: Is b ∈ D?
       - If b ∈ D, then by definition of D, b ∉ f(b) = D. Contradiction!
       - If b ∉ D, then by definition of D, b ∈ f(b) = D. Contradiction!
    4. Therefore, no such surjection exists. -/
theorem cantor_no_surjection_set (A : Type*) :
    ¬∃ f : A → Set A, Function.Surjective f := by
  -- Assume f : A → Set A is surjective
  intro ⟨f, hf⟩
  -- Define D = {x | x ∉ f x}
  let D : Set A := diagonalSet f
  -- By surjectivity, D is in the range: ∃ b, f b = D
  obtain ⟨b, hb⟩ := hf D
  -- We derive a contradiction: b ∈ D ↔ b ∉ D
  have h : b ∈ D ↔ b ∉ f b := Iff.rfl
  -- Substitute f b = D
  simp only [hb] at h
  -- Now h : b ∈ D ↔ b ∉ D, which is absurd
  by_cases hbD : b ∈ D
  · exact h.mp hbD hbD
  · exact hbD (h.mpr hbD)

/-! ## The Core Lemma: Diagonal Paradox -/

/-- The diagonal paradox: if f(b) = D where D = {x | x ∉ f x},
    then b ∈ D ↔ b ∉ D. This is the heart of Cantor's argument. -/
theorem diagonal_paradox {A : Type*} (f : A → Set A) (b : A)
    (hb : f b = diagonalSet f) : b ∈ diagonalSet f ↔ b ∉ diagonalSet f := by
  -- By definition: b ∈ D ↔ b ∉ f b
  have h : b ∈ diagonalSet f ↔ b ∉ f b := Iff.rfl
  -- Substitute f b = D
  simp only [hb] at h
  exact h

/-! ## Corollaries -/

/-- The power set of any set has strictly greater cardinality.
    This is a reformulation emphasizing |A| < |P(A)|. -/
theorem powerset_strictly_larger (A : Type*) :
    ¬∃ f : A → Set A, Function.Surjective f :=
  cantor_no_surjection_set A

/-- No set can be put in bijection with its power set. -/
theorem no_bijection_to_powerset (A : Type*) :
    ¬∃ f : A → Set A, Function.Bijective f := by
  intro ⟨f, hbi⟩
  exact cantor_no_surjection_set A ⟨f, hbi.2⟩

/-! ## Relationship to Cardinal Arithmetic -/

/-- Cantor's inequality: for any set A, |A| < |P(A)|.

    While we state this as the non-existence of a surjection (which implies
    the strict inequality), the full cardinal statement requires Mathlib's
    Cardinal type. See `Cardinal.mk_set_lt` in Mathlib for the cardinal version. -/
theorem cantor_cardinal_inequality (A : Type*) :
    ¬∃ f : A → Set A, Function.Surjective f :=
  cantor_no_surjection_set A

/-! ## Constructive Note

The standard proof of Cantor's theorem is constructive in the sense that
given any f : A → Set A, we can explicitly construct a set D not in the
range of f. The set D = {x | x ∉ f x} witnesses the non-surjectivity.

This is in contrast to many other existence proofs in mathematics that
rely on non-constructive principles. -/

/-- Given any f : A → Set A, we can construct a set not in f's range. -/
theorem cantor_witness (A : Type*) (f : A → Set A) :
    ∃ D : Set A, ∀ a : A, f a ≠ D := by
  use diagonalSet f
  intro a ha
  -- If f a = D, we get the diagonal paradox
  have := diagonal_paradox f a ha
  by_cases h : a ∈ diagonalSet f
  · exact this.mp h h
  · exact h (this.mpr h)

#check cantor_no_surjection
#check cantor_no_surjection_set
#check cantor_witness

end CantorsTheorem
