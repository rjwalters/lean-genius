/-
# Is ℤ purely Diophantine over ℚ? — Σ₁ vs Π₂ definability

This file refines `Hilbert10OQ01.lean` by drawing the precise distinction
between Σ₁ (purely existential / Diophantine) and Π₂ (universal-existential,
"∀∃") definability, which is the mathematical content separating the OPEN
question from Koenigsmann's 2016 theorem.

## The OPEN question (OQ-01-OQ-02)

  Is ℤ ⊆ ℚ a purely Diophantine subset?
  Equivalently: does there exist P ∈ ℚ[t, x₁,…,xₖ] such that
        t ∈ ℤ  ⟺  ∃ x₁,…,xₖ ∈ ℚ : P(t, x₁,…,xₖ) = 0?

This is the Σ₁ formula version. The negation of this question is implied
by Mazur's conjecture (1992). Either answer would be a major milestone:

  positive ⟹ H10/ℚ undecidable (immediate from MRDP);
  negative ⟹ Mazur-conjecture-style topology constraints on ℚ-points,
              but does NOT immediately settle H10/ℚ decidability.

## What IS proved (Koenigsmann 2016, Annals)

  ℤ is Π₂-definable in ℚ:
    ∃ P ∈ ℚ[t, y₁,…,yₙ, z₁,…,zₘ] such that
      t ∈ ℤ  ⟺  ∀ y ∈ ℚⁿ, ∃ z ∈ ℚᵐ : P(t, y, z) = 0.

So Π₂ is settled; Σ₁ remains the central open question.

## Companion to Hilbert10OQ01.lean

We import `Proofs.Hilbert10OQ01` to reuse `RatDiophantinePoly`,
`hasRationalSolution`, `IntegersDiophantineOverQ`, `H10_Rational_Decidable`,
and the existing reduction axiom `integers_diophantine_implies_undecidable`,
rather than redefining them.

## Status

OPEN, axiomatized: 2 axioms.
  1. `koenigsmann_2016_universal` — Π₂-definability of ℤ in ℚ (PROVED in
     Koenigsmann, Annals 2016; axiomatized here pending model-theoretic
     formalization).
  2. `mazur_conjecture_implies_not_diophantine_over_Q` — Mazur ⟹ ¬Σ₁
     (a topological argument; restated against this file's predicate).

The Σ₁ question itself is left as a `Prop`-valued statement, NOT axiomatized
either way: we encode it as `IntegersDiophantineOverQ` (already in OQ-01) and
expose the equivalent statement `IsDiophantineDefinition (Set.range Int)`.

## References

- Koenigsmann, J. (2016). *Defining ℤ in ℚ.* Annals of Math. 183, 73–93.
- Mazur, B. (1992). *The topology of rational points.* Experimental Math. 1, 35–45.
- Poonen, B. (2009). *The set of nonsquares in a number field is Diophantine.*
  Math. Res. Lett. 16, 165–170.
- Eisenträger, K. & Park, J. (2018). *Universally and existentially definable
  subsets of global fields.*
- Daans, N. (2021). *Universally defining ℤ in ℚ with 10 quantifiers.*
  J. Number Theory.
-/

import Proofs.Hilbert10OQ01
-- S8 (iter 8, Path B): one Mathlib import for `sub_eq_zero` on ℚ, used to
-- generalize `singletonZero` (S6) to arbitrary singletons `{a}` for `a : ℚ`.
-- This is the first Mathlib import in this file; iterations 1–7 were
-- entirely zero-Mathlib (Path A discipline). See state.md for context.
import Mathlib.Algebra.Group.Basic
-- S9 (iter 9, Path B): `mul_eq_zero` (and `zero_mul` / `mul_zero`) on ℚ
-- for closure of Σ₁ under binary union and Π₁ under binary intersection.
-- ℚ is a field, hence `NoZeroDivisors`, so `mul_eq_zero` applies.
import Mathlib.Algebra.GroupWithZero.Basic
-- S12 (iter 12, Path B): `mul_self_nonneg` for the sum-of-squares witness
-- used in closure of Σ₁ under binary intersection. ℚ is a LinearOrderedField,
-- so `0 ≤ a*a` for every `a : ℚ`. Provided transitively via
-- `Mathlib.Algebra.Order.Ring.Basic` (Mathlib v4.26.0; the historic
-- `Mathlib.Algebra.Order.Ring.Lemmas` barrel file was removed).
import Mathlib.Algebra.Order.Ring.Basic
-- S12 (iter 12, Path B): `linarith` to discharge the conclusion
-- `a*a + b*b = 0  ∧  0 ≤ a*a  ∧  0 ≤ b*b  →  a*a = 0  ∧  b*b = 0`.
import Mathlib.Tactic.Linarith
-- v4.26.0 (Path B mechanic): `ring` tactic, formerly pulled in transitively
-- via the now-removed `Mathlib.Algebra.Order.Ring.Lemmas` barrel; must be
-- imported explicitly at v4.26.0.
import Mathlib.Tactic.Ring
-- Iter 17 (Path B): `Finset.toList` and `Finset.mem_toList` for Finset
-- transports of the iter 10 / iter 14 / iter 15 list closures.
import Mathlib.Data.Finset.Basic

namespace Hilbert10Rationals

-- ============================================================
-- Part I: Subsets of ℚ as predicates
-- ============================================================

/-- A subset S ⊆ ℚ, represented as a predicate. -/
abbrev RatSubset := Rat → Prop

/-- The integers ℤ as a subset of ℚ (image of `Int.cast`). -/
def IntSubset : RatSubset := fun q => ∃ z : Int, q = z

-- ============================================================
-- Part II: Σ₁ (Diophantine / purely existential) definability
-- ============================================================

/-- A subset S ⊆ ℚ is **Diophantine** (Σ₁-definable) if there exists a
    parametric family of rational polynomial equations P_q such that
    q ∈ S iff P_q has a rational solution.

    Concretely: ∃ P ∈ ℚ[t, x₁,…,xₖ], ∀ q ∈ ℚ : q ∈ S ⟺ ∃ x ∈ ℚᵏ, P(q, x) = 0.

    This is the Σ₁ (existential) layer of the arithmetic hierarchy over ℚ. -/
def IsDiophantineDefinition (S : RatSubset) : Prop :=
  ∃ P : Rat → RatDiophantinePoly,
    ∀ q : Rat, S q ↔ hasRationalSolution (P q)

/-- The OPEN question OQ-01-OQ-02: ℤ is Σ₁-definable in ℚ.

    This is mathematically equivalent to `IntegersDiophantineOverQ`
    from `Hilbert10OQ01.lean`. We expose the equivalence below. -/
def IntegersAreDiophantineOverQ : Prop :=
  IsDiophantineDefinition IntSubset

/-- The two formulations agree definitionally: `IsDiophantineDefinition`
    over `IntSubset` unfolds to the existing `IntegersDiophantineOverQ`. -/
theorem integers_diophantine_iff :
    IntegersAreDiophantineOverQ ↔ IntegersDiophantineOverQ := Iff.rfl

-- ============================================================
-- Part III: Π₂ (universal-existential, "∀∃") definability
-- ============================================================

/-- A subset S ⊆ ℚ is **Π₂-definable** ("universal-existential") if there
    exists a polynomial P parametric in q AND in a universal quantifier block
    y : ℕ → ℚ such that
        q ∈ S  ⟺  ∀ y : ℕ → ℚ, ∃ x : ℕ → ℚ : P(q, y, x) = 0.

    This is the layer at which Koenigsmann (2016) places ℤ ⊂ ℚ. -/
def IsUniversalExistentialDefinition (S : RatSubset) : Prop :=
  ∃ P : Rat → (Nat → Rat) → RatDiophantinePoly,
    ∀ q : Rat, S q ↔ ∀ y : Nat → Rat, hasRationalSolution (P q y)

/-- **Koenigsmann's theorem** (Annals 2016):

    ℤ is Π₂-definable in ℚ.

    The proof is constructive — Koenigsmann exhibits an explicit polynomial
    using Hilbert symbols and quaternion algebras over ℚ. We axiomatize the
    statement here pending a Lean formalization of that construction. -/
axiom koenigsmann_2016_universal :
    IsUniversalExistentialDefinition IntSubset

-- ============================================================
-- Part IV: Σ₁ ⊆ Π₂ (one-line containment)
-- ============================================================

/-- Every Σ₁-definable subset of ℚ is also Π₂-definable.

    Reason: if S q ⟺ ∃ x, P(q, x) = 0, then taking the universal block
    `y` to be a dummy and the polynomial to ignore `y`, we have
    S q ⟺ ∀ y, ∃ x, P(q, x) = 0 trivially.

    This makes precise that the Σ₁/Π₂ refinement is non-trivial only in
    the OTHER direction: a Π₂ definition need NOT collapse to Σ₁. -/
theorem diophantine_implies_universal_existential
    (S : RatSubset) (h : IsDiophantineDefinition S) :
    IsUniversalExistentialDefinition S := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun q _ => P q, ?_⟩
  intro q
  constructor
  · intro hSq _y
    exact (hP q).mp hSq
  · intro hAll
    exact (hP q).mpr (hAll (fun _ => 0))

/-- Corollary: if ℤ is Σ₁-definable in ℚ, this is consistent with — and in
    fact strengthens — Koenigsmann's Π₂ definability. The OPEN question is
    whether such a strengthening exists. -/
theorem integers_diophantine_strengthens_koenigsmann :
    IntegersAreDiophantineOverQ → IsUniversalExistentialDefinition IntSubset :=
  diophantine_implies_universal_existential IntSubset

-- ============================================================
-- Part V: Consequence — Σ₁ definability ⟹ H10/ℚ undecidable
-- ============================================================

/-- The reduction axiom from `Hilbert10OQ01.lean`, restated against the
    Σ₁ formulation in this file. This is a re-export, not a new axiom:
    the `↔` of definitions makes this a pure logical consequence. -/
theorem integers_diophantine_sigma1_implies_h10_q_undecidable :
    IntegersAreDiophantineOverQ → ¬H10_Rational_Decidable := by
  intro h
  exact integers_diophantine_implies_undecidable
    (integers_diophantine_iff.mp h)

-- ============================================================
-- Part VI: Mazur's conjecture against the Σ₁ predicate
-- ============================================================

/-- **Mazur's conjecture against Σ₁**:

    If Mazur's conjecture holds, then ℤ is NOT Σ₁-definable in ℚ.

    Restatement of `mazur_implies_not_diophantine` (from OQ-01) against
    `IntegersAreDiophantineOverQ`. Pure logical consequence of the
    Σ₁ ↔ existing-formulation equivalence; not a new axiom. -/
theorem mazur_implies_not_sigma1_definable :
    MazurConjecture → ¬IntegersAreDiophantineOverQ := by
  intro hMazur hSigma1
  exact mazur_implies_not_diophantine hMazur (integers_diophantine_iff.mp hSigma1)

-- ============================================================
-- Part VII: Π₁ (universal) Definability and the Σ₁/Π₁ Duality
-- ============================================================

/-- A subset S ⊆ ℚ is **Π₁-definable** ("co-Diophantine", purely universal)
    if there exists a parametric polynomial family `P_q` such that

        q ∈ S  ⟺  ∀ x ∈ ℚᵏ : P_q(x) ≠ 0,

    i.e., q ∈ S iff the equation `P_q(x) = 0` has NO rational solution.

    Equivalently, the complement of a Π₁ subset is Σ₁ (Diophantine);
    see `diophantine_iff_codiophantine_complement` below. -/
def IsCoDiophantineDefinition (S : RatSubset) : Prop :=
  ∃ P : Rat → RatDiophantinePoly,
    ∀ q : Rat, S q ↔ ¬ hasRationalSolution (P q)

/-- The complement of `IntSubset` in ℚ: the rationals that are NOT integers. -/
def NotIntSubset : RatSubset := fun q => ¬ IntSubset q

/-- **Σ₁ / Π₁ duality** (general):

    A subset S ⊆ ℚ is Σ₁-definable iff its complement is Π₁-definable.

    Formally proves the narrative claim "Σ₁ ⟺ ¬(Π₁ for the complement)"
    asserted in the introduction of this file. The proof uses one
    classical excluded-middle step (`Classical.byContradiction`) for the
    direction Π₁(¬S) → Σ₁(S), reflecting the well-known fact that
    complementing is classical. -/
theorem diophantine_iff_codiophantine_complement (S : RatSubset) :
    IsDiophantineDefinition S ↔ IsCoDiophantineDefinition (fun q => ¬ S q) := by
  constructor
  · intro h
    obtain ⟨P, hP⟩ := h
    refine ⟨P, fun q => ?_⟩
    refine ⟨fun hnSq hsol => hnSq ((hP q).mpr hsol),
            fun hnsol hSq => hnsol ((hP q).mp hSq)⟩
  · intro h
    obtain ⟨P, hP⟩ := h
    refine ⟨P, fun q => ?_⟩
    refine ⟨fun hSq => ?_, fun hsol => ?_⟩
    · apply Classical.byContradiction
      intro hnsol
      have hnSq : ¬ S q := (hP q).mpr hnsol
      exact hnSq hSq
    · apply Classical.byContradiction
      intro hnSq
      have hnsol : ¬ hasRationalSolution (P q) := (hP q).mp hnSq
      exact hnsol hsol

/-- **Specialization to ℤ ⊂ ℚ**:

    ℤ is Σ₁-definable in ℚ (the OPEN question OQ-01-OQ-02) iff its
    complement ℚ \ ℤ is Π₁-definable in ℚ. -/
theorem integers_diophantine_iff_complement_codiophantine :
    IntegersAreDiophantineOverQ ↔ IsCoDiophantineDefinition NotIntSubset :=
  diophantine_iff_codiophantine_complement IntSubset

/-- Π₁-definability of ℚ \ ℤ in ℚ implies H10/ℚ undecidable.

    Pure logical consequence of `integers_diophantine_iff_complement_codiophantine`
    composed with `integers_diophantine_sigma1_implies_h10_q_undecidable`;
    NOT a new axiom. Witnesses that the OPEN question can equivalently be
    stated in Π₁ form on the complement. -/
theorem codiophantine_complement_implies_h10_q_undecidable :
    IsCoDiophantineDefinition NotIntSubset → ¬H10_Rational_Decidable := by
  intro hCodiop
  exact integers_diophantine_sigma1_implies_h10_q_undecidable
    (integers_diophantine_iff_complement_codiophantine.mpr hCodiop)

/-- Mazur's conjecture rules out Π₁-definability of ℚ \ ℤ in ℚ.

    Pure logical consequence of `integers_diophantine_iff_complement_codiophantine`
    composed with `mazur_implies_not_sigma1_definable`; NOT a new axiom. -/
theorem mazur_implies_not_codiophantine_complement :
    MazurConjecture → ¬IsCoDiophantineDefinition NotIntSubset := by
  intro hMazur hCodiop
  exact mazur_implies_not_sigma1_definable hMazur
    (integers_diophantine_iff_complement_codiophantine.mpr hCodiop)

-- ============================================================
-- Part VIII: Σ₂ (∃∀, "existential-universal") Definability
--           and the Σ₂/Π₂ Duality
-- ============================================================

/-- A subset S ⊆ ℚ is **Σ₂-definable** ("existential-universal", "∃∀") if
    there exists a polynomial family `P` parametric in `q` AND in an
    existential block `y : ℕ → ℚ` such that

        q ∈ S  ⟺  ∃ y : ℕ → ℚ, ∀ x : ℕ → ℚ : P(q, y, x) ≠ 0,

    i.e., there is a choice of `y` for which the polynomial `P(q, y, ·)`
    has no rational solution.

    This is the dual of `IsUniversalExistentialDefinition` (Π₂); the
    duality is `S ∈ Σ₂  ⟺  (¬S) ∈ Π₂`, proved as
    `existentialUniversal_iff_universalExistential_complement`. -/
def IsExistentialUniversalDefinition (S : RatSubset) : Prop :=
  ∃ P : Rat → (Nat → Rat) → RatDiophantinePoly,
    ∀ q : Rat, S q ↔ ∃ y : Nat → Rat, ¬ hasRationalSolution (P q y)

/-- **Π₁ ⊆ Σ₂** (one-line containment, axiom-free):

    Every Π₁-definable subset of ℚ is also Σ₂-definable.

    Reason: if `S q ⟺ ∀ x, P(q, x) ≠ 0`, take the existential block `y`
    to be a dummy and the polynomial to ignore `y`. Then
    `∃ y, ∀ x, P(q, x) ≠ 0` collapses to the Π₁ form again.

    Precise dual of `diophantine_implies_universal_existential` (Σ₁ ⊆ Π₂). -/
theorem codiophantine_implies_existentialUniversal
    (S : RatSubset) (h : IsCoDiophantineDefinition S) :
    IsExistentialUniversalDefinition S := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun q _ => P q, ?_⟩
  intro q
  constructor
  · intro hSq
    refine ⟨fun _ => 0, ?_⟩
    exact (hP q).mp hSq
  · intro hex
    obtain ⟨_y, hnsol⟩ := hex
    exact (hP q).mpr hnsol

/-- **Σ₂ / Π₂ duality** (axiom-free up to classical excluded middle):

    A subset S ⊆ ℚ is Σ₂-definable iff its complement is Π₂-definable.

    Higher-level analog of `diophantine_iff_codiophantine_complement`
    (the Σ₁/Π₁ duality). Both directions use one classical
    `Classical.byContradiction` step to convert `¬¬` to identity. -/
theorem existentialUniversal_iff_universalExistential_complement (S : RatSubset) :
    IsExistentialUniversalDefinition S ↔
      IsUniversalExistentialDefinition (fun q => ¬ S q) := by
  constructor
  · intro h
    obtain ⟨P, hP⟩ := h
    refine ⟨P, fun q => ?_⟩
    constructor
    · intro hnSq y
      apply Classical.byContradiction
      intro hnsol
      exact hnSq ((hP q).mpr ⟨y, hnsol⟩)
    · intro hAll hSq
      obtain ⟨y, hnsol⟩ := (hP q).mp hSq
      exact hnsol (hAll y)
  · intro h
    obtain ⟨P, hP⟩ := h
    refine ⟨P, fun q => ?_⟩
    constructor
    · intro hSq
      apply Classical.byContradiction
      intro hnex
      have hAll : ∀ y : Nat → Rat, hasRationalSolution (P q y) := by
        intro y
        apply Classical.byContradiction
        intro hnsol
        exact hnex ⟨y, hnsol⟩
      exact ((hP q).mpr hAll) hSq
    · intro hex
      obtain ⟨y, hnsol⟩ := hex
      apply Classical.byContradiction
      intro hnSq
      exact hnsol ((hP q).mp hnSq y)

/-- The Π₂ class is invariant under propositional equivalence of the
    defining predicate. Pure logical congruence; no axioms. -/
theorem universalExistentialDefinition_iff_of_pred_iff
    {S S' : RatSubset} (h : ∀ q, S q ↔ S' q) :
    IsUniversalExistentialDefinition S ↔ IsUniversalExistentialDefinition S' := by
  constructor
  · intro hS
    obtain ⟨P, hP⟩ := hS
    refine ⟨P, fun q => ?_⟩
    exact (h q).symm.trans (hP q)
  · intro hS'
    obtain ⟨P, hP⟩ := hS'
    refine ⟨P, fun q => ?_⟩
    exact (h q).trans (hP q)

/-- The Σ₁ class is invariant under propositional equivalence of the
    defining predicate. Pure logical congruence; no axioms.

    Direct analog of `universalExistentialDefinition_iff_of_pred_iff`
    (Π₂ congruence). Useful when bridging between Σ₁ predicates whose
    statements are propositionally equivalent up to a classical
    rewrite (e.g., `¬¬p ↔ p`). -/
theorem diophantineDefinition_iff_of_pred_iff
    {S S' : RatSubset} (h : ∀ q, S q ↔ S' q) :
    IsDiophantineDefinition S ↔ IsDiophantineDefinition S' := by
  constructor
  · intro hS
    obtain ⟨P, hP⟩ := hS
    refine ⟨P, fun q => ?_⟩
    exact (h q).symm.trans (hP q)
  · intro hS'
    obtain ⟨P, hP⟩ := hS'
    refine ⟨P, fun q => ?_⟩
    exact (h q).trans (hP q)

/-- The Π₁ class is invariant under propositional equivalence of the
    defining predicate. Pure logical congruence; no axioms.

    Direct analog of `universalExistentialDefinition_iff_of_pred_iff`
    (Π₂ congruence). -/
theorem coDiophantineDefinition_iff_of_pred_iff
    {S S' : RatSubset} (h : ∀ q, S q ↔ S' q) :
    IsCoDiophantineDefinition S ↔ IsCoDiophantineDefinition S' := by
  constructor
  · intro hS
    obtain ⟨P, hP⟩ := hS
    refine ⟨P, fun q => ?_⟩
    exact (h q).symm.trans (hP q)
  · intro hS'
    obtain ⟨P, hP⟩ := hS'
    refine ⟨P, fun q => ?_⟩
    exact (h q).trans (hP q)

/-- The Σ₂ class is invariant under propositional equivalence of the
    defining predicate. Pure logical congruence; no axioms.

    Direct analog of `universalExistentialDefinition_iff_of_pred_iff`
    (Π₂ congruence). Completes the four-class congruence story:
    Σ₁, Π₁, Σ₂, Π₂ are all invariant under propositional equivalence
    of the defining predicate. -/
theorem existentialUniversalDefinition_iff_of_pred_iff
    {S S' : RatSubset} (h : ∀ q, S q ↔ S' q) :
    IsExistentialUniversalDefinition S ↔ IsExistentialUniversalDefinition S' := by
  constructor
  · intro hS
    obtain ⟨P, hP⟩ := hS
    refine ⟨P, fun q => ?_⟩
    exact (h q).symm.trans (hP q)
  · intro hS'
    obtain ⟨P, hP⟩ := hS'
    refine ⟨P, fun q => ?_⟩
    exact (h q).trans (hP q)

/-- **Corollary of Koenigsmann via Σ₂/Π₂ duality**:

    The complement `ℚ \ ℤ` is Σ₂-definable in ℚ.

    Proof: by `existentialUniversal_iff_universalExistential_complement`,
    Σ₂(ℚ\ℤ) ⟺ Π₂(¬(ℚ\ℤ)) = Π₂(¬¬ ℤ). Classically, ¬¬ ℤ ⟺ ℤ, so
    Π₂(¬¬ ℤ) ⟺ Π₂(ℤ), which is `koenigsmann_2016_universal`. NOT a new
    axiom — pure logical consequence of Koenigsmann + Σ₂/Π₂ duality. -/
theorem koenigsmann_implies_complement_existentialUniversal :
    IsExistentialUniversalDefinition NotIntSubset := by
  have hbridge : ∀ q : Rat, IntSubset q ↔ ¬ NotIntSubset q :=
    fun q => ⟨fun hZ hnZ => hnZ hZ, fun hnnZ => Classical.byContradiction hnnZ⟩
  have hPi2 : IsUniversalExistentialDefinition (fun q => ¬ NotIntSubset q) :=
    (universalExistentialDefinition_iff_of_pred_iff hbridge).mp
      koenigsmann_2016_universal
  exact (existentialUniversal_iff_universalExistential_complement NotIntSubset).mpr
    hPi2

-- ============================================================
-- Part VIII.5 (iter 5): Symmetric duality forms — Σ₁ vs Π₁(¬·) and Σ₂ vs Π₂(¬·)
-- ============================================================

/-- **Symmetric Σ₁/Π₁ duality** (iteration 5):

    A subset `S` is Π₁-definable iff its complement `¬ S` is Σ₁-definable.

    This is the symmetric companion of `diophantine_iff_codiophantine_complement`
    (which states `S ∈ Σ₁ ⟺ ¬S ∈ Π₁`). Together, the two forms exhibit the
    Σ₁/Π₁ duality as an involutive bijection (modulo classical
    double-negation), and either direction implies the other via the
    `_iff_of_pred_iff` congruence and the bridge `S q ↔ ¬¬ S q`.

    Proved here directly (no congruence detour) — same structural pattern
    as the Σ₁→Π₁ direction, with one classical step. -/
theorem codiophantine_iff_diophantine_complement (S : RatSubset) :
    IsCoDiophantineDefinition S ↔ IsDiophantineDefinition (fun q => ¬ S q) := by
  constructor
  · intro h
    obtain ⟨P, hP⟩ := h
    refine ⟨P, fun q => ?_⟩
    -- need: ¬ S q ↔ hasRationalSolution (P q)
    -- hP q : S q ↔ ¬ hasRationalSolution (P q)
    refine ⟨fun hnSq => ?_, fun hsol hSq => ?_⟩
    · apply Classical.byContradiction
      intro hnsol
      exact hnSq ((hP q).mpr hnsol)
    · exact ((hP q).mp hSq) hsol
  · intro h
    obtain ⟨P, hP⟩ := h
    refine ⟨P, fun q => ?_⟩
    -- need: S q ↔ ¬ hasRationalSolution (P q)
    -- hP q : ¬ S q ↔ hasRationalSolution (P q)
    refine ⟨fun hSq hsol => ?_, fun hnsol => ?_⟩
    · exact ((hP q).mpr hsol) hSq
    · apply Classical.byContradiction
      intro hnSq
      exact hnsol ((hP q).mp hnSq)

/-- **Symmetric Σ₂/Π₂ duality** (iteration 5):

    A subset `S` is Π₂-definable iff its complement `¬ S` is Σ₂-definable.

    Higher-level analog of `codiophantine_iff_diophantine_complement`.
    Symmetric companion of `existentialUniversal_iff_universalExistential_complement`.

    Proof: derived as a corollary of the existing duality applied to `¬ S`,
    using the Π₂ congruence helper to rewrite `¬¬ S` back to `S`.
    No new axioms; pure classical-logic glue. -/
theorem universalExistential_iff_existentialUniversal_complement (S : RatSubset) :
    IsUniversalExistentialDefinition S ↔
      IsExistentialUniversalDefinition (fun q => ¬ S q) := by
  have hbridge : ∀ q : Rat, S q ↔ ¬ ¬ S q :=
    fun q => ⟨fun hSq hnSq => hnSq hSq, fun hnnSq => Classical.byContradiction hnnSq⟩
  have hStep1 : IsUniversalExistentialDefinition S ↔
      IsUniversalExistentialDefinition (fun q => ¬ ¬ S q) :=
    universalExistentialDefinition_iff_of_pred_iff hbridge
  have hStep2 : IsUniversalExistentialDefinition (fun q => ¬ ¬ S q) ↔
      IsExistentialUniversalDefinition (fun q => ¬ S q) :=
    (existentialUniversal_iff_universalExistential_complement (fun q => ¬ S q)).symm
  exact hStep1.trans hStep2

-- ============================================================
-- Part VIII.6 (iter 5): Trivial-set definability across all four classes
-- ============================================================

/-- The "always-zero" rational polynomial — a witness that the trivial
    equation `0 = 0` always has a rational solution. Used as a building
    block for trivial-set Σ₁/Π₂ membership. -/
private def zeroPoly : RatDiophantinePoly := fun _ => 0

/-- The "always-one" rational polynomial — a witness that the trivial
    equation `1 = 0` never has a rational solution. Used as a building
    block for trivial-set Π₁/Σ₂ membership and complement constructions. -/
private def onePoly : RatDiophantinePoly := fun _ => 1

private theorem hasRationalSolution_zeroPoly : hasRationalSolution zeroPoly :=
  ⟨fun _ => 0, rfl⟩

private theorem rat_one_ne_zero : (1 : Rat) ≠ 0 := by decide

private theorem not_hasRationalSolution_onePoly : ¬ hasRationalSolution onePoly := by
  rintro ⟨_, h⟩
  exact rat_one_ne_zero (show (1 : Rat) = 0 from h)

/-- The empty subset of ℚ (predicate `False`) is Σ₁-definable. Witness:
    the always-one polynomial, which has no rational solution.

    Foundational closure-under-emptiness fact for the Σ₁ class. -/
theorem empty_isDiophantineDefinition :
    IsDiophantineDefinition (fun _ : Rat => False) := by
  refine ⟨fun _ => onePoly, fun q => ?_⟩
  exact ⟨False.elim, fun h => not_hasRationalSolution_onePoly h⟩

/-- The empty subset of ℚ is Π₁-definable. Witness: the always-zero
    polynomial, which always has a rational solution; its negation is
    therefore always false. -/
theorem empty_isCoDiophantineDefinition :
    IsCoDiophantineDefinition (fun _ : Rat => False) := by
  refine ⟨fun _ => zeroPoly, fun q => ?_⟩
  exact ⟨False.elim, fun hnsol => hnsol hasRationalSolution_zeroPoly⟩

/-- The full subset of ℚ (predicate `True`) is Σ₁-definable. Witness:
    the always-zero polynomial, whose rational solution set is all of ℚᵏ. -/
theorem universe_isDiophantineDefinition :
    IsDiophantineDefinition (fun _ : Rat => True) := by
  refine ⟨fun _ => zeroPoly, fun q => ?_⟩
  exact ⟨fun _ => hasRationalSolution_zeroPoly, fun _ => trivial⟩

/-- The full subset of ℚ is Π₁-definable. Witness: the always-one
    polynomial, whose negation is always true (no rational solution). -/
theorem universe_isCoDiophantineDefinition :
    IsCoDiophantineDefinition (fun _ : Rat => True) := by
  refine ⟨fun _ => onePoly, fun q => ?_⟩
  exact ⟨fun _ => not_hasRationalSolution_onePoly, fun _ => trivial⟩

/-- The empty subset of ℚ is Π₂-definable.

    Witness: the polynomial `P(q, y, x) = 1`, which never vanishes; the
    inner existential `∃ x, P(q, y, x) = 0` is therefore false for every
    `y`, and `Nat → Rat` is inhabited (by `fun _ => 0`), so the outer
    universal quantifier `∀ y, False` is `False`. -/
theorem empty_isUniversalExistentialDefinition :
    IsUniversalExistentialDefinition (fun _ : Rat => False) := by
  refine ⟨fun _ _ => onePoly, fun q => ?_⟩
  refine ⟨False.elim, fun hAll => ?_⟩
  exact not_hasRationalSolution_onePoly (hAll (fun _ => 0))

/-- The full subset of ℚ is Π₂-definable.

    Witness: the polynomial `P(q, y, x) = 0`, whose inner existential
    block `∃ x, 0 = 0` is true for every `y`; the outer universal is then
    vacuously true. -/
theorem universe_isUniversalExistentialDefinition :
    IsUniversalExistentialDefinition (fun _ : Rat => True) := by
  refine ⟨fun _ _ => zeroPoly, fun q => ?_⟩
  exact ⟨fun _ _ => hasRationalSolution_zeroPoly, fun _ => trivial⟩

/-- The empty subset of ℚ is Σ₂-definable. Derivable from the Π₂ universe
    fact via the symmetric Σ₂/Π₂ duality: `Σ₂(∅) ⟺ Π₂(¬∅) = Π₂(univ)`. -/
theorem empty_isExistentialUniversalDefinition :
    IsExistentialUniversalDefinition (fun _ : Rat => False) := by
  have hbridge : ∀ q : Rat, ¬ (fun _ : Rat => False) q ↔ (fun _ : Rat => True) q :=
    fun q => ⟨fun _ => trivial, fun _ hF => hF⟩
  have hPi2 : IsUniversalExistentialDefinition (fun q => ¬ (fun _ : Rat => False) q) :=
    (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr
      universe_isUniversalExistentialDefinition
  exact (existentialUniversal_iff_universalExistential_complement
    (fun _ : Rat => False)).mpr hPi2

/-- The full subset of ℚ is Σ₂-definable. Derivable from the Π₂ empty
    fact via the symmetric Σ₂/Π₂ duality: `Σ₂(univ) ⟺ Π₂(¬univ) = Π₂(∅)`. -/
theorem universe_isExistentialUniversalDefinition :
    IsExistentialUniversalDefinition (fun _ : Rat => True) := by
  have hbridge : ∀ q : Rat, ¬ (fun _ : Rat => True) q ↔ (fun _ : Rat => False) q :=
    fun q => ⟨fun hnT => hnT trivial, fun hF _ => hF⟩
  have hPi2 : IsUniversalExistentialDefinition (fun q => ¬ (fun _ : Rat => True) q) :=
    (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr
      empty_isUniversalExistentialDefinition
  exact (existentialUniversal_iff_universalExistential_complement
    (fun _ : Rat => True)).mpr hPi2

-- ============================================================
-- Part VIII.7 (iter 6): Singleton {0} and complement ℚ\{0} definability
-- ============================================================

/-- The "projection" parametric polynomial: for each `q : ℚ`, the polynomial
    that ignores its variable assignment and returns the constant `q`.

    Concretely, `parameterPoly q = fun _ => q`. This is the simplest
    `q`-dependent polynomial witness in the file, used to place the
    smallest non-trivial subset `{0} ⊂ ℚ` (and its complement) into the
    Σ₁ and Π₁ classes respectively.

    Beyond the iteration-5 trivial-set witnesses (`zeroPoly`, `onePoly`),
    which are constant in *both* the parameter and the variable, this
    polynomial is constant only in the variable. -/
private def parameterPoly : Rat → RatDiophantinePoly := fun q _ => q

/-- The singleton `{0} ⊂ ℚ` is Σ₁-definable.

    Witness: the projection polynomial `P(q, x) = q`. Then
    `hasRationalSolution (P q) ⟺ ∃ x, q = 0 ⟺ q = 0` (the polynomial
    is constant in `x`, so existence of a rational solution reduces to
    the constant value being `0`).

    This is the smallest non-trivial Σ₁ subset of ℚ — beyond the trivial
    `∅` and `ℚ` cases of iteration 5, here the polynomial genuinely
    depends on the parameter `q`. No new axioms; no Mathlib import. -/
theorem singletonZero_isDiophantineDefinition :
    IsDiophantineDefinition (fun q : Rat => q = 0) := by
  refine ⟨parameterPoly, fun q => ?_⟩
  exact ⟨fun hq => ⟨fun _ => 0, hq⟩, fun ⟨_, hP⟩ => hP⟩

/-- The complement `ℚ \ {0}` is Π₁-definable.

    Witness: the same projection polynomial `P(q, x) = q`. Then
    `¬ hasRationalSolution (P q) ⟺ ∀ x, q ≠ 0 ⟺ q ≠ 0` (since the
    polynomial value does not depend on `x`).

    Direct dual of `singletonZero_isDiophantineDefinition`, obtained from
    the same polynomial witness by negating the equivalence. -/
theorem notZero_isCoDiophantineDefinition :
    IsCoDiophantineDefinition (fun q : Rat => q ≠ 0) := by
  refine ⟨parameterPoly, fun q => ?_⟩
  exact ⟨fun hq ⟨_, hP⟩ => hq hP, fun hnsol hq => hnsol ⟨fun _ => 0, hq⟩⟩

/-- The singleton `{0}` is Π₂-definable.

    Corollary of `singletonZero_isDiophantineDefinition` via the trivial
    inclusion `Σ₁ ⊆ Π₂` (`diophantine_implies_universal_existential`).
    The Π₂ witness is the projection polynomial padded with a dummy
    universal block, in line with iteration 4's congruence story. -/
theorem singletonZero_isUniversalExistentialDefinition :
    IsUniversalExistentialDefinition (fun q : Rat => q = 0) :=
  diophantine_implies_universal_existential _ singletonZero_isDiophantineDefinition

/-- The complement `ℚ \ {0}` is Σ₂-definable.

    Corollary of `notZero_isCoDiophantineDefinition` via the trivial
    inclusion `Π₁ ⊆ Σ₂` (`codiophantine_implies_existentialUniversal`).
    Together with `singletonZero_isUniversalExistentialDefinition`, this
    completes the four-class placement of `{0}` and `ℚ \ {0}`. -/
theorem notZero_isExistentialUniversalDefinition :
    IsExistentialUniversalDefinition (fun q : Rat => q ≠ 0) :=
  codiophantine_implies_existentialUniversal _ notZero_isCoDiophantineDefinition

-- ============================================================
-- Part VIII.8 (iter 7): ¬¬-shadow / double-negation invariance
-- ============================================================

/-- Classical double-negation bridge for an arbitrary `RatSubset`:
    `S q ↔ ¬¬ S q`. Packaged as a reusable named lemma for the four
    `_iff_of_pred_iff` congruence helpers below.

    Already used inline in iteration 5's
    `universalExistential_iff_existentialUniversal_complement`; factored
    out here so the four ¬¬-shadow theorems are uniform one-liners. The
    only non-constructive step is `Classical.byContradiction`. -/
private theorem doubleNeg_pred_iff (S : RatSubset) :
    ∀ q : Rat, S q ↔ ¬ ¬ S q :=
  fun _ => ⟨fun hSq hnSq => hnSq hSq, fun hnnSq => Classical.byContradiction hnnSq⟩

/-- **Σ₁ ¬¬-shadow** (iteration 7): the Σ₁ (Diophantine) class is
    invariant under classical double-negation of the predicate.

        Σ₁(¬¬ S)  ⟺  Σ₁(S).

    Pure logic; pulls back through the Σ₁ class congruence
    `diophantineDefinition_iff_of_pred_iff` (iteration 4) along the
    classical bridge `doubleNeg_pred_iff`. No new axioms. -/
theorem diophantineDefinition_doubleNeg_iff (S : RatSubset) :
    IsDiophantineDefinition (fun q => ¬ ¬ S q) ↔ IsDiophantineDefinition S :=
  (diophantineDefinition_iff_of_pred_iff (doubleNeg_pred_iff S)).symm

/-- **Π₁ ¬¬-shadow** (iteration 7): the Π₁ (co-Diophantine) class is
    invariant under classical double-negation of the predicate.

        Π₁(¬¬ S)  ⟺  Π₁(S).

    Pure logic; pulls back through `coDiophantineDefinition_iff_of_pred_iff`
    (iteration 4) along the classical bridge. No new axioms. -/
theorem coDiophantineDefinition_doubleNeg_iff (S : RatSubset) :
    IsCoDiophantineDefinition (fun q => ¬ ¬ S q) ↔ IsCoDiophantineDefinition S :=
  (coDiophantineDefinition_iff_of_pred_iff (doubleNeg_pred_iff S)).symm

/-- **Π₂ ¬¬-shadow** (iteration 7): the Π₂ (universal-existential) class
    is invariant under classical double-negation of the predicate.

        Π₂(¬¬ S)  ⟺  Π₂(S).

    Pure logic; pulls back through `universalExistentialDefinition_iff_of_pred_iff`
    (iteration 3) along the classical bridge. No new axioms. -/
theorem universalExistentialDefinition_doubleNeg_iff (S : RatSubset) :
    IsUniversalExistentialDefinition (fun q => ¬ ¬ S q) ↔
      IsUniversalExistentialDefinition S :=
  (universalExistentialDefinition_iff_of_pred_iff (doubleNeg_pred_iff S)).symm

/-- **Σ₂ ¬¬-shadow** (iteration 7): the Σ₂ (existential-universal) class
    is invariant under classical double-negation of the predicate.

        Σ₂(¬¬ S)  ⟺  Σ₂(S).

    Pure logic; pulls back through `existentialUniversalDefinition_iff_of_pred_iff`
    (iteration 4) along the classical bridge. Completes the four-class
    ¬¬-shadow story (Σ₁/Π₁/Σ₂/Π₂ all stable under classical double
    negation of the predicate). No new axioms. -/
theorem existentialUniversalDefinition_doubleNeg_iff (S : RatSubset) :
    IsExistentialUniversalDefinition (fun q => ¬ ¬ S q) ↔
      IsExistentialUniversalDefinition S :=
  (existentialUniversalDefinition_iff_of_pred_iff (doubleNeg_pred_iff S)).symm

/-- **OPEN-question reformulation through the shadow** (iteration 7):
    the OPEN Σ₁ question for ℤ ⊂ ℚ is equivalent to its double-negation
    shadow.

        IntegersAreDiophantineOverQ
          ⟺  IsDiophantineDefinition (fun q => ¬¬ IntSubset q).

    Concrete consequence of the Σ₁ ¬¬-shadow at the predicate `IntSubset`.
    Useful when a putative refutation argument naturally produces a `¬¬`
    layer (e.g., from a classical decomposition of a Π₁ counter-witness)
    — the shadow reformulation lets one stay inside the Σ₁ class while
    using the doubly-negated predicate. -/
theorem integers_diophantine_iff_doubleNeg :
    IntegersAreDiophantineOverQ ↔
      IsDiophantineDefinition (fun q => ¬ ¬ IntSubset q) :=
  (diophantineDefinition_doubleNeg_iff IntSubset).symm

-- ============================================================
-- Part VIII.9 (iter 8, Path B): Arbitrary singletons {a} for a : ℚ
-- ============================================================

/-- "Shift" parametric polynomial witness: for each `a : ℚ`, the polynomial
    that ignores its variable assignment and returns `q - a`. This generalizes
    iteration 6's `parameterPoly` (the constant-zero shift) to an arbitrary
    rational shift `a`.

    Concretely, `shiftPoly a = fun q _ => q - a`. The polynomial is constant
    in the variable assignment; its zero set in `q` is exactly `{a}`. Used
    to place every singleton `{a} ⊂ ℚ` (and its complement `ℚ \ {a}`) into
    the Σ₁ class (resp. Π₁ class).

    Path B (Mathlib): the proofs use `sub_eq_zero` from `Mathlib.Algebra.Group.Basic`
    to bridge `q - a = 0 ↔ q = a`. -/
private def shiftPoly (a : Rat) : Rat → RatDiophantinePoly := fun q _ => q - a

/-- Iter 8, Path B: **the singleton `{a} ⊂ ℚ` is Σ₁-definable** for every
    `a : ℚ`.

    Witness: `shiftPoly a`, i.e., `P(q, x) = q - a`. Then
    `hasRationalSolution (P q) ⟺ ∃ x, q - a = 0 ⟺ q - a = 0 ⟺ q = a`.
    The first iff is trivial (the polynomial does not depend on `x`); the
    second is `sub_eq_zero` from Mathlib's additive-group library.

    This is the proper generalization of S6's `singletonZero_isDiophantineDefinition`
    (the special case `a = 0`, modulo `sub_zero`) to arbitrary `a : ℚ`. The
    OPEN Σ₁ question for ℤ ⊂ ℚ is genuinely harder: ℤ is the union of the
    family of singletons `{n}` for `n : ℤ ⊂ ℚ`, but Σ₁-definability is NOT
    known to be closed under countable union (unlike finite union — see
    closure properties to be added in S9+).

    Path B (Mathlib import): adds `Mathlib.Algebra.Group.Basic`. No new
    axioms. -/
theorem singletonOf_isDiophantineDefinition (a : Rat) :
    IsDiophantineDefinition (fun q : Rat => q = a) := by
  refine ⟨shiftPoly a, fun q => ?_⟩
  exact ⟨fun hq => ⟨fun _ => 0, sub_eq_zero.mpr hq⟩,
          fun ⟨_, hP⟩ => sub_eq_zero.mp hP⟩

/-- Iter 8, Path B: **the complement `ℚ \ {a}` is Π₁-definable** for every
    `a : ℚ`.

    Witness: the same `shiftPoly a`, i.e., `P(q, x) = q - a`. Then
    `¬ hasRationalSolution (P q) ⟺ ¬ ∃ x, q - a = 0 ⟺ q - a ≠ 0 ⟺ q ≠ a`.

    Direct dual of `singletonOf_isDiophantineDefinition`, generalizing S6's
    `notZero_isCoDiophantineDefinition` (the special case `a = 0`) to
    arbitrary `a : ℚ`. -/
theorem notSingletonOf_isCoDiophantineDefinition (a : Rat) :
    IsCoDiophantineDefinition (fun q : Rat => q ≠ a) := by
  refine ⟨shiftPoly a, fun q => ?_⟩
  exact ⟨fun hq ⟨_, hP⟩ => hq (sub_eq_zero.mp hP),
          fun hnsol hq => hnsol ⟨fun _ => 0, sub_eq_zero.mpr hq⟩⟩

/-- Iter 8, Path B: **the singleton `{a}` is Π₂-definable** for every
    `a : ℚ`.

    Corollary of `singletonOf_isDiophantineDefinition` via the trivial
    inclusion `Σ₁ ⊆ Π₂` (`diophantine_implies_universal_existential`).
    Generalizes S6's `singletonZero_isUniversalExistentialDefinition`. -/
theorem singletonOf_isUniversalExistentialDefinition (a : Rat) :
    IsUniversalExistentialDefinition (fun q : Rat => q = a) :=
  diophantine_implies_universal_existential _ (singletonOf_isDiophantineDefinition a)

/-- Iter 8, Path B: **the complement `ℚ \ {a}` is Σ₂-definable** for every
    `a : ℚ`.

    Corollary of `notSingletonOf_isCoDiophantineDefinition` via the trivial
    inclusion `Π₁ ⊆ Σ₂` (`codiophantine_implies_existentialUniversal`).
    Generalizes S6's `notZero_isExistentialUniversalDefinition`. -/
theorem notSingletonOf_isExistentialUniversalDefinition (a : Rat) :
    IsExistentialUniversalDefinition (fun q : Rat => q ≠ a) :=
  codiophantine_implies_existentialUniversal _ (notSingletonOf_isCoDiophantineDefinition a)

/-- Iter 8, Path B: **S6 recovered as the special case `a = 0`** of S8.

    The S8 family `singletonOf_isDiophantineDefinition` evaluated at `a = 0`
    yields a Σ₁-definability proof of `{q | q = 0}`, the same predicate as
    S6's `singletonZero_isDiophantineDefinition`. This concrete instance
    documents that S8 properly generalizes S6 (NOT replaces it: the S6
    polynomial witness `parameterPoly = fun _ => q` is leaner than the S8
    witness `shiftPoly 0 = fun _ => q - 0`, so S6 remains the preferred
    Path A witness for `{0}` specifically). -/
theorem singletonOf_zero_isDiophantineDefinition :
    IsDiophantineDefinition (fun q : Rat => q = 0) :=
  singletonOf_isDiophantineDefinition 0

-- ============================================================
-- Part VIII.10 (iter 9, Path B): Σ₁ closed under binary union;
--                                Π₁ closed under binary intersection
-- ============================================================

/-- Iter 9, Path B: **the Σ₁ class is closed under binary union**.

    If `S₁` and `S₂` are both Σ₁-definable over ℚ, then so is the
    pointwise disjunction `fun q => S₁ q ∨ S₂ q`.

    Witness: the product polynomial `P(q, x) = P₁(q, x) · P₂(q, x)`,
    where `P₁` and `P₂` are the witnesses for `S₁` and `S₂` respectively
    (both witnesses share the same infinite variable assignment block,
    which is fine for union — the existential quantifier is OR-ed across
    which factor vanishes).

    The Σ₁ side uses the fact that a single `x` makes the product zero
    iff it makes one of the factors zero (`mul_eq_zero` over ℚ;
    `NoZeroDivisors` from ℚ being a field). Specifically:

    * Forward (`S₁ q ∨ S₂ q → ∃ x, P₁(q,x)·P₂(q,x) = 0`): pick the
      witness `x` for whichever side holds and use `zero_mul` /
      `mul_zero` to conclude the product vanishes.
    * Reverse (`∃ x, P₁(q,x)·P₂(q,x) = 0 → S₁ q ∨ S₂ q`): apply
      `mul_eq_zero` at the witness to split into `P₁(q,x) = 0` or
      `P₂(q,x) = 0`, and feed back through `(hP_i q).mpr`.

    Path B (Mathlib): adds `Mathlib.Algebra.GroupWithZero.Basic` for
    `mul_eq_zero` (no other API surfaces). No new axioms.

    By iterating over a finite list, this lifts to closure under any
    *finite* union. The OPEN Σ₁ question for ℤ ⊂ ℚ is precisely the
    question of whether finite-union closure extends to *countable*
    union along the family of singletons `{n} : n : ℤ` (each of which
    is Σ₁ by `singletonOf_isDiophantineDefinition` from S8). -/
theorem union_isDiophantineDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsDiophantineDefinition S₁) (h₂ : IsDiophantineDefinition S₂) :
    IsDiophantineDefinition (fun q => S₁ q ∨ S₂ q) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨fun q x => (P₁ q x) * (P₂ q x), fun q => ?_⟩
  constructor
  · rintro (hS₁ | hS₂)
    · obtain ⟨x, hx⟩ := (hP₁ q).mp hS₁
      exact ⟨x, by simp only [hx, zero_mul]⟩
    · obtain ⟨x, hx⟩ := (hP₂ q).mp hS₂
      exact ⟨x, by simp only [hx, mul_zero]⟩
  · rintro ⟨x, hx⟩
    rcases mul_eq_zero.mp hx with hzero | hzero
    · exact Or.inl ((hP₁ q).mpr ⟨x, hzero⟩)
    · exact Or.inr ((hP₂ q).mpr ⟨x, hzero⟩)

/-- Iter 9, Path B: **the Π₁ class is closed under binary intersection**.

    If `S₁` and `S₂` are both Π₁-definable over ℚ, then so is the
    pointwise conjunction `fun q => S₁ q ∧ S₂ q`.

    Direct dual of `union_isDiophantineDefinition`: the same product
    polynomial `P(q, x) = P₁(q, x) · P₂(q, x)` works as the Π₁ witness,
    via `mul_eq_zero` (in its contrapositive form: a product is nonzero
    iff each factor is nonzero, applied at every `x`).

    Concretely:

    * Forward (`S₁ q ∧ S₂ q → ∀ x, P₁(q,x)·P₂(q,x) ≠ 0`): if both `S_i q`
      hold, then by `(hP_i q).mp`, neither `P_i q` admits a rational
      solution; for any `x`, if `P₁(q,x)·P₂(q,x) = 0` then by
      `mul_eq_zero` one factor is zero, contradicting one of the `(hP_i q).mp` hypotheses.
    * Reverse (`(∀ x, P₁(q,x)·P₂(q,x) ≠ 0) → S₁ q ∧ S₂ q`): if any single
      factor `P_i q x = 0`, multiplying by zero on the other side gives
      the product zero, contradicting the universal nonvanishing.

    Path B (Mathlib): same import as union closure. No new axioms.

    By iterating over a finite list, this lifts to closure of Π₁ under
    any *finite* intersection — the dual statement to finite-union
    closure of Σ₁. -/
theorem intersection_isCoDiophantineDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsCoDiophantineDefinition S₁) (h₂ : IsCoDiophantineDefinition S₂) :
    IsCoDiophantineDefinition (fun q => S₁ q ∧ S₂ q) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨fun q x => (P₁ q x) * (P₂ q x), fun q => ?_⟩
  constructor
  · rintro ⟨hS₁, hS₂⟩ ⟨x, hx⟩
    rcases mul_eq_zero.mp hx with hzero | hzero
    · exact ((hP₁ q).mp hS₁) ⟨x, hzero⟩
    · exact ((hP₂ q).mp hS₂) ⟨x, hzero⟩
  · intro hnsol
    refine ⟨?_, ?_⟩
    · apply (hP₁ q).mpr
      rintro ⟨x, hx⟩
      exact hnsol ⟨x, by simp only [hx, zero_mul]⟩
    · apply (hP₂ q).mpr
      rintro ⟨x, hx⟩
      exact hnsol ⟨x, by simp only [hx, mul_zero]⟩

/-- Iter 9 corollary, Path B: **every pair `{a, b} ⊂ ℚ` is Σ₁-definable**
    for any `a, b : ℚ`.

    Direct application of `union_isDiophantineDefinition` to the two S8
    singleton witnesses `singletonOf_isDiophantineDefinition a` and
    `singletonOf_isDiophantineDefinition b`. -/
theorem singletonPair_isDiophantineDefinition (a b : Rat) :
    IsDiophantineDefinition (fun q : Rat => q = a ∨ q = b) :=
  union_isDiophantineDefinition (singletonOf_isDiophantineDefinition a)
    (singletonOf_isDiophantineDefinition b)

/-- Iter 9 corollary, Path B: **every "complement-of-a-pair"
    `ℚ \ {a, b}` is Π₁-definable** for any `a, b : ℚ`.

    Direct application of `intersection_isCoDiophantineDefinition` to
    the two S8 co-singleton witnesses
    `notSingletonOf_isCoDiophantineDefinition a` and `... b`. -/
theorem notSingletonPair_isCoDiophantineDefinition (a b : Rat) :
    IsCoDiophantineDefinition (fun q : Rat => q ≠ a ∧ q ≠ b) :=
  intersection_isCoDiophantineDefinition
    (notSingletonOf_isCoDiophantineDefinition a)
    (notSingletonOf_isCoDiophantineDefinition b)

/-- Iter 9 corollary, Path B: **every pair `{a, b}` is Π₂-definable**
    via the trivial inclusion `Σ₁ ⊆ Π₂`. -/
theorem singletonPair_isUniversalExistentialDefinition (a b : Rat) :
    IsUniversalExistentialDefinition (fun q : Rat => q = a ∨ q = b) :=
  diophantine_implies_universal_existential _
    (singletonPair_isDiophantineDefinition a b)

/-- Iter 9 corollary, Path B: **every complement-of-a-pair `ℚ \ {a, b}`
    is Σ₂-definable** via the trivial inclusion `Π₁ ⊆ Σ₂`. -/
theorem notSingletonPair_isExistentialUniversalDefinition (a b : Rat) :
    IsExistentialUniversalDefinition (fun q : Rat => q ≠ a ∧ q ≠ b) :=
  codiophantine_implies_existentialUniversal _
    (notSingletonPair_isCoDiophantineDefinition a b)

-- ============================================================
-- Part VIII.10: Finite-list closure (iteration 10, S10.3)
-- ============================================================

/-- Iter 10, Path B: **every FINITE subset of ℚ is Σ₁-definable**.

    By induction on a list `l : List Rat`, the predicate `q ∈ l` is
    Σ₁-definable. Base case: empty list, predicate is `False` — covered
    by `empty_isDiophantineDefinition`. Inductive step: `q ∈ a :: t`
    unfolds (via `List.mem_cons`) to `q = a ∨ q ∈ t`, which is
    Σ₁-definable by `union_isDiophantineDefinition` of S8's
    `singletonOf_isDiophantineDefinition a` and the induction hypothesis.

    The product polynomial witness for the induction step is
    `P(q, x) = (q - a) · P_t(q, x)` where `P_t` is the inductive witness
    for `q ∈ t`; existence of a rational solution corresponds (via
    `mul_eq_zero`) to either `q = a` or `q ∈ t`.

    This makes precise the OPEN/closed-under-finite gap: every FINITE
    truncation `⋃_{n ∈ [-N, N] ∩ ℤ} {n}` of ℤ ⊂ ℚ is Σ₁-definable for
    every finite `N`, but a UNIFORM Σ₁ witness for the full countable
    union `⋃_{n : ℤ} {n}` is the OPEN content of the question. -/
theorem finUnionList_singletons_isDiophantineDefinition (l : List Rat) :
    IsDiophantineDefinition (fun q : Rat => q ∈ l) := by
  induction l with
  | nil =>
    -- `q ∈ ([] : List Rat)` reduces to `False` propositionally.
    have hbridge : ∀ q : Rat, (fun q : Rat => q ∈ ([] : List Rat)) q ↔
        (fun _ : Rat => False) q := by
      intro q; simp
    exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr
      empty_isDiophantineDefinition
  | cons a t ih =>
    -- `q ∈ a :: t  ↔  q = a ∨ q ∈ t`, then close via union closure of S9.
    have hbridge : ∀ q : Rat, (fun q : Rat => q ∈ (a :: t)) q ↔
        (fun q : Rat => q = a ∨ q ∈ t) q := by
      intro q; exact List.mem_cons
    have h_singleton : IsDiophantineDefinition (fun q : Rat => q = a) :=
      singletonOf_isDiophantineDefinition a
    have h_union : IsDiophantineDefinition (fun q : Rat => q = a ∨ q ∈ t) :=
      union_isDiophantineDefinition h_singleton ih
    exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr h_union

/-- Iter 10 corollary, Path B: **every complement of a finite subset of ℚ
    is Π₁-definable**.

    Direct dual of `finUnionList_singletons_isDiophantineDefinition`: the
    predicate `q ∉ l` is Π₁-definable for every `l : List Rat`. Proved by
    induction mirroring the Σ₁ case, using
    `intersection_isCoDiophantineDefinition` (S9 dual) for the inductive
    step and `notSingletonOf_isCoDiophantineDefinition` for the cons head. -/
theorem finIntersectionList_complement_singletons_isCoDiophantineDefinition
    (l : List Rat) :
    IsCoDiophantineDefinition (fun q : Rat => q ∉ l) := by
  induction l with
  | nil =>
    -- `q ∉ ([] : List Rat)` is `True` propositionally.
    have hbridge : ∀ q : Rat, (fun q : Rat => q ∉ ([] : List Rat)) q ↔
        (fun _ : Rat => True) q := by
      intro q; simp
    exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr
      universe_isCoDiophantineDefinition
  | cons a t ih =>
    -- `q ∉ a :: t  ↔  q ≠ a ∧ q ∉ t`, then close via intersection closure of S9.
    have hbridge : ∀ q : Rat, (fun q : Rat => q ∉ (a :: t)) q ↔
        (fun q : Rat => q ≠ a ∧ q ∉ t) q := by
      intro q
      constructor
      · intro hq
        refine ⟨fun heq => hq ?_, fun hmem => hq ?_⟩
        · exact List.mem_cons.mpr (Or.inl heq)
        · exact List.mem_cons.mpr (Or.inr hmem)
      · rintro ⟨hne, hnt⟩ hq
        rcases List.mem_cons.mp hq with h | h
        · exact hne h
        · exact hnt h
    have h_notSingleton : IsCoDiophantineDefinition (fun q : Rat => q ≠ a) :=
      notSingletonOf_isCoDiophantineDefinition a
    have h_intersection : IsCoDiophantineDefinition (fun q : Rat => q ≠ a ∧ q ∉ t) :=
      intersection_isCoDiophantineDefinition h_notSingleton ih
    exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr h_intersection

/-- Iter 10 corollary, Path B: **every finite subset of ℚ is Π₂-definable**
    via the trivial inclusion `Σ₁ ⊆ Π₂`. -/
theorem finUnionList_singletons_isUniversalExistentialDefinition (l : List Rat) :
    IsUniversalExistentialDefinition (fun q : Rat => q ∈ l) :=
  diophantine_implies_universal_existential _
    (finUnionList_singletons_isDiophantineDefinition l)

/-- Iter 10 corollary, Path B: **every complement of a finite subset of ℚ
    is Σ₂-definable** via the trivial inclusion `Π₁ ⊆ Σ₂`. -/
theorem finIntersectionList_complement_singletons_isExistentialUniversalDefinition
    (l : List Rat) :
    IsExistentialUniversalDefinition (fun q : Rat => q ∉ l) :=
  codiophantine_implies_existentialUniversal _
    (finIntersectionList_complement_singletons_isCoDiophantineDefinition l)

/-- Iter 11, Path B: **Π₁ ⊆ Π₂** via the polynomial-inversion trick
    (axiom-free).

    Every Π₁-definable subset of ℚ is also Π₂-definable. Closes the
    last "diagonal" containment in the Σ₁/Π₁/Σ₂/Π₂ square not derivable
    from a dummy-block argument.

    **Strategy** (polynomial-inversion). If `S q ⟺ ∀ y, P(q, y) ≠ 0`,
    replace each non-vanishing constraint by an existential witness for
    the rational inverse: in the field ℚ,

        a ≠ 0  ⟺  ∃ z : ℚ, a · z - 1 = 0     (z = a⁻¹).

    The Π₂ polynomial witness is therefore

        P'(q, y, x) := P(q, y) · x 0 - 1,

    and `∀ y, ∃ x, P'(q, y, x) = 0` is equivalent to `∀ y, P(q, y) ≠ 0`,
    i.e., to the Π₁ form of `S q`.

    **Path B** (Mathlib): uses `mul_inv_cancel₀` from
    `Mathlib.Algebra.GroupWithZero.Basic` (already imported for the S9
    union/intersection closure) and `sub_eq_zero` from
    `Mathlib.Algebra.Group.Basic` (already imported for the S8
    `singletonOf` generalization). No new imports.

    **Diagonal companion** of `diophantine_implies_universal_existential`
    (Σ₁ ⊆ Π₂, dummy-block trick) and
    `codiophantine_implies_existentialUniversal` (Π₁ ⊆ Σ₂, dummy-block
    trick). With this lemma, the Σ₁/Π₁/Σ₂/Π₂ square has all four
    "vertical" containments (Σ₁ ⊆ Π₂, Σ₁ ⊆ Σ₂?, Π₁ ⊆ Π₂, Π₁ ⊆ Σ₂)
    proved except Σ₁ ⊆ Σ₂, which has no obvious axiom-free proof in
    this framework (the arithmetic hierarchy is not "collapsed" by
    inversion or dummy-blocks). -/
theorem coDiophantine_implies_universal_existential
    (S : RatSubset) (h : IsCoDiophantineDefinition S) :
    IsUniversalExistentialDefinition S := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun q y x => P q y * x 0 - 1, fun q => ?_⟩
  constructor
  · -- Forward: `S q` → `∀ y, ∃ x, P q y * x 0 - 1 = 0`. Pick the inverse.
    intro hSq y
    have hne : P q y ≠ 0 := fun hzero => (hP q).mp hSq ⟨y, hzero⟩
    refine ⟨fun _ => (P q y)⁻¹, ?_⟩
    show P q y * (P q y)⁻¹ - 1 = 0
    rw [mul_inv_cancel₀ hne, sub_self]
  · -- Reverse: `∀ y, ∃ x, P q y * x 0 - 1 = 0` → `S q`. Existence of an
    -- inverse rules out `P q y = 0`, which discharges the Π₁ form of `S q`.
    intro hAll
    apply (hP q).mpr
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hAll y
    have heq : P q y * x 0 = 1 := sub_eq_zero.mp hx
    rw [hy, zero_mul] at heq
    exact zero_ne_one heq

-- ============================================================
-- Part VIII.12 (iter 12, Path B): Σ₁ closed under binary intersection
--                                  (sum-of-squares + interleave packing)
-- ============================================================

/-- Even-indexed projection of an infinite rational variable assignment.
    Used in the variable-packing for `intersection_isDiophantineDefinition`
    to expose the "first half" `x ↦ x (2*n)` of an `x : Nat → Rat` to one
    of the two argument polynomials. -/
private def evenProj (x : Nat → Rat) : Nat → Rat := fun n => x (2 * n)

/-- Odd-indexed projection of an infinite rational variable assignment.
    Used in the variable-packing for `intersection_isDiophantineDefinition`
    to expose the "second half" `x ↦ x (2*n + 1)` of an `x : Nat → Rat`
    to the other argument polynomial. -/
private def oddProj (x : Nat → Rat) : Nat → Rat := fun n => x (2 * n + 1)

/-- Interleave two infinite rational variable assignments into one.
    `interleave x₁ x₂` puts `x₁ n` at the even index `2*n` and `x₂ n` at
    the odd index `2*n + 1`. This is the section/inverse of the pair
    `(evenProj, oddProj)`. -/
private def interleave (x₁ x₂ : Nat → Rat) : Nat → Rat :=
  fun n => if n % 2 = 0 then x₁ (n / 2) else x₂ (n / 2)

/-- The even-indexed projection of an interleaved assignment recovers the
    first input. Pure Nat-arithmetic: `(2*n) % 2 = 0` and `(2*n) / 2 = n`. -/
private theorem evenProj_interleave (x₁ x₂ : Nat → Rat) :
    evenProj (interleave x₁ x₂) = x₁ := by
  funext n
  show (if (2 * n) % 2 = 0 then x₁ ((2 * n) / 2) else x₂ ((2 * n) / 2)) = x₁ n
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [if_pos h1, h2]

/-- The odd-indexed projection of an interleaved assignment recovers the
    second input. Pure Nat-arithmetic: `(2*n+1) % 2 = 1 ≠ 0` and
    `(2*n+1) / 2 = n`. -/
private theorem oddProj_interleave (x₁ x₂ : Nat → Rat) :
    oddProj (interleave x₁ x₂) = x₂ := by
  funext n
  show (if (2 * n + 1) % 2 = 0 then x₁ ((2 * n + 1) / 2) else x₂ ((2 * n + 1) / 2)) = x₂ n
  have h1 : (2 * n + 1) % 2 ≠ 0 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [if_neg h1, h2]

/-- Iter 12, Path B: **the Σ₁ class is closed under binary intersection**.

    If `S₁` and `S₂` are both Σ₁-definable over ℚ, then so is the
    pointwise conjunction `fun q => S₁ q ∧ S₂ q`.

    **Witness** (sum-of-squares with variable packing): given Σ₁ witnesses
    `P₁` for `S₁` and `P₂` for `S₂`, the polynomial

        P(q, x) := P₁(q, evenProj x)·P₁(q, evenProj x)
                 + P₂(q, oddProj x)·P₂(q, oddProj x)

    has a rational solution `x` iff both `P₁(q, ·)` and `P₂(q, ·)` have
    rational solutions. The variable-packing puts `P₁`'s witness on the
    even-indexed slots `{2*n : n : ℕ}` of `x` and `P₂`'s witness on the
    odd-indexed slots `{2*n+1 : n : ℕ}`, so the two witnesses can coexist
    in a single `x : Nat → Rat`.

    **Forward** (`S₁ q ∧ S₂ q → ∃ x, P(q, x) = 0`): combine `x₁` and `x₂`
    via `interleave`. The projection lemmas
    `evenProj_interleave : evenProj (interleave x₁ x₂) = x₁` and
    `oddProj_interleave : oddProj (interleave x₁ x₂) = x₂` make
    `P₁(q, evenProj x) = P₁(q, x₁) = 0` and
    `P₂(q, oddProj x) = P₂(q, x₂) = 0`, so each square term vanishes
    and the sum is zero.

    **Reverse** (`∃ x, P(q, x) = 0 → S₁ q ∧ S₂ q`): write
    `a := P₁(q, evenProj x)` and `b := P₂(q, oddProj x)`. The hypothesis
    is `a*a + b*b = 0`. Over the LinearOrderedField ℚ, both `a*a ≥ 0`
    and `b*b ≥ 0` (`mul_self_nonneg`), so `linarith` forces `a*a = 0`
    and `b*b = 0`. By `mul_eq_zero` (NoZeroDivisors over ℚ), `a = 0`
    and `b = 0`. Feeding back through `(hP_i q).mpr` yields `S₁ q` and
    `S₂ q`.

    **Path B** (Mathlib): adds `Mathlib.Algebra.Order.Ring.Lemmas` for
    `mul_self_nonneg` and `Mathlib.Tactic.Linarith` for the
    `a*a + b*b = 0  ∧  0 ≤ a*a  ∧  0 ≤ b*b  →  a*a = 0` step. The
    interleave / projection lemmas are pure Nat arithmetic via `omega`.
    No new axioms.

    **Combined with S9** (`union_isDiophantineDefinition`): the Σ₁ class
    over ℚ is closed under both binary union AND binary intersection,
    hence under arbitrary FINITE Boolean combinations using `∪` and `∩`.
    Σ₁ is NOT (known to be) closed under complement — that would
    collapse the Σ₁/Π₁ duality and is equivalent to the OPEN question
    of whether Σ₁ = Π₁ over ℚ.

    By iterating over a finite list, this lifts to closure under any
    *finite* intersection of Σ₁-definable sets. The OPEN Σ₁ question
    for ℤ ⊂ ℚ is unaffected: it is precisely the question of whether
    the *countable* union of singletons admits a uniform Σ₁ witness;
    intersection closure is "orthogonal" to that question. -/
theorem intersection_isDiophantineDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsDiophantineDefinition S₁) (h₂ : IsDiophantineDefinition S₂) :
    IsDiophantineDefinition (fun q => S₁ q ∧ S₂ q) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨fun q x =>
    (P₁ q (evenProj x)) * (P₁ q (evenProj x)) +
    (P₂ q (oddProj x)) * (P₂ q (oddProj x)), fun q => ?_⟩
  constructor
  · rintro ⟨hS₁, hS₂⟩
    obtain ⟨x₁, hx₁⟩ := (hP₁ q).mp hS₁
    obtain ⟨x₂, hx₂⟩ := (hP₂ q).mp hS₂
    refine ⟨interleave x₁ x₂, ?_⟩
    show P₁ q (evenProj (interleave x₁ x₂)) * P₁ q (evenProj (interleave x₁ x₂)) +
         P₂ q (oddProj (interleave x₁ x₂)) * P₂ q (oddProj (interleave x₁ x₂)) = 0
    rw [evenProj_interleave, oddProj_interleave, hx₁, hx₂]
    ring
  · rintro ⟨x, hx⟩
    -- `hx : a*a + b*b = 0` where a := P₁ q (evenProj x), b := P₂ q (oddProj x)
    set a := P₁ q (evenProj x)
    set b := P₂ q (oddProj x)
    have haa_nn : (0 : Rat) ≤ a * a := mul_self_nonneg a
    have hbb_nn : (0 : Rat) ≤ b * b := mul_self_nonneg b
    have haa_zero : a * a = 0 := by linarith
    have hbb_zero : b * b = 0 := by linarith
    have ha : a = 0 := (mul_eq_zero.mp haa_zero).elim id id
    have hb : b = 0 := (mul_eq_zero.mp hbb_zero).elim id id
    refine ⟨(hP₁ q).mpr ⟨evenProj x, ha⟩, (hP₂ q).mpr ⟨oddProj x, hb⟩⟩

/-- Iter 12 corollary, Path B: **Π₂ class is closed under binary
    intersection of Σ₁-definable subsets**.

    Direct application of `intersection_isDiophantineDefinition` followed
    by `diophantine_implies_universal_existential` (Σ₁ ⊆ Π₂). Stated as
    a transport: if `S₁`, `S₂` are Σ₁-definable, then `S₁ ∩ S₂` is also
    Π₂-definable.

    This is NOT the strongest possible Π₂-closure statement (which would
    require a direct Π₂ witness for `S₁ ∩ S₂` when `S₁`, `S₂` are
    arbitrary Π₂-definable subsets — that's a strictly bigger claim than
    Σ₁ closure). The stronger Π₂ ∩ Π₂ ⊆ Π₂ closure is left as future
    work; this file's S11.1 (`coDiophantine_implies_universal_existential`)
    handles the unary Π₁ ⊆ Π₂ direction without intersection. -/
theorem intersection_isUniversalExistentialDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsDiophantineDefinition S₁) (h₂ : IsDiophantineDefinition S₂) :
    IsUniversalExistentialDefinition (fun q => S₁ q ∧ S₂ q) :=
  diophantine_implies_universal_existential _
    (intersection_isDiophantineDefinition h₁ h₂)

-- ============================================================
-- Part VIII.13 (iter 13, Path B): Π₁ closed under binary union
--                                  (duality + S11.2 sum-of-squares)
-- ============================================================

/-- Iter 13, Path B: **the Π₁ class is closed under binary union**.

    If `S₁` and `S₂` are both Π₁-definable over ℚ, then so is the
    pointwise disjunction `fun q => S₁ q ∨ S₂ q`.

    **Strategy** (no new Mathlib lemmas, no new imports): chain through
    the iter 5 Σ₁/Π₁ duality, iter 12's binary intersection closure of
    Σ₁, and the iter 4 Σ₁ class congruence helper.

      Π₁(S₁), Π₁(S₂)
        →[iter 5 codiophantine_iff_diophantine_complement]  Σ₁(¬S₁), Σ₁(¬S₂)
        →[iter 12 intersection_isDiophantineDefinition]      Σ₁(¬S₁ ∧ ¬S₂)
        →[iter 4 diophantineDefinition_iff_of_pred_iff
           via constructive de Morgan ¬S₁ ∧ ¬S₂ ↔ ¬(S₁ ∨ S₂)] Σ₁(¬(S₁ ∨ S₂))
        →[iter 5 codiophantine_iff_diophantine_complement]   Π₁(S₁ ∨ S₂)

    The "underlying" polynomial witness (after unfolding the iter 5
    duality, which is identity on the polynomial family P) is therefore
    the same sum-of-squares construction as iter 12:

        P(q, x) := P₁(q, evenProj x)² + P₂(q, oddProj x)²

    where `P_i` is now interpreted as the Π₁ witness of `S_i` (so
    `S_i q ↔ ¬ ∃ x, P_i(q, x) = 0`). This is the symmetric companion
    of iter 12's Σ₁ ∩ closure under the Σ₁/Π₁ duality.

    The de Morgan bridge `¬ S₁ q ∧ ¬ S₂ q ↔ ¬ (S₁ q ∨ S₂ q)` is
    **constructive** (no LEM needed). The two duality steps each use
    the iter 5 `Classical.byContradiction` move internally, but no NEW
    classical reasoning is introduced beyond what was already required
    in iter 5.

    **Combined with iter 9** (`intersection_isCoDiophantineDefinition`):
    the Π₁ class over ℚ is closed under both binary union AND binary
    intersection — hence under arbitrary FINITE Boolean combinations
    using ∪ and ∩. Π₁ is NOT (known to be) closed under complement;
    that would collapse Π₁ = Σ₁, equivalent to the OPEN question.

    Combined with iter 9 (Σ₁ ∪, Π₁ ∩) and iter 12 (Σ₁ ∩), this completes
    the **2×2 closure grid** for finite Boolean combinations:

        | Class | ∪ closure | ∩ closure |
        |-------|-----------|-----------|
        | Σ₁    | iter 9    | iter 12   |
        | Π₁    | iter 13   | iter 9    |

    Neither class is (known to be) closed under complement; that would
    collapse Σ₁ = Π₁ over ℚ, equivalent to the OPEN question (via
    `diophantine_iff_codiophantine_complement`). -/
theorem union_isCoDiophantineDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsCoDiophantineDefinition S₁) (h₂ : IsCoDiophantineDefinition S₂) :
    IsCoDiophantineDefinition (fun q => S₁ q ∨ S₂ q) := by
  -- Step 1: dualize each Π₁ to Σ₁ on the complement (iter 5 duality).
  have hd₁ : IsDiophantineDefinition (fun q => ¬ S₁ q) :=
    (codiophantine_iff_diophantine_complement S₁).mp h₁
  have hd₂ : IsDiophantineDefinition (fun q => ¬ S₂ q) :=
    (codiophantine_iff_diophantine_complement S₂).mp h₂
  -- Step 2: Σ₁ closed under binary intersection (iter 12, S11.2).
  have hcap : IsDiophantineDefinition (fun q => ¬ S₁ q ∧ ¬ S₂ q) :=
    intersection_isDiophantineDefinition hd₁ hd₂
  -- Step 3: bridge via constructive de Morgan
  --     `¬ S₁ q ∧ ¬ S₂ q ↔ ¬ (S₁ q ∨ S₂ q)`.
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ¬ S₁ q ∧ ¬ S₂ q) q ↔
        (fun q : Rat => ¬ (S₁ q ∨ S₂ q)) q := by
    intro q
    refine ⟨fun ⟨hn₁, hn₂⟩ hor => hor.elim hn₁ hn₂,
            fun hnor => ⟨fun h₁q => hnor (Or.inl h₁q),
                          fun h₂q => hnor (Or.inr h₂q)⟩⟩
  have hd : IsDiophantineDefinition (fun q : Rat => ¬ (S₁ q ∨ S₂ q)) :=
    (diophantineDefinition_iff_of_pred_iff hbridge).mp hcap
  -- Step 4: Σ₁(¬T) ↔ Π₁(T) via duality (iter 5), with T = S₁ ∪ S₂.
  exact (codiophantine_iff_diophantine_complement
    (fun q => S₁ q ∨ S₂ q)).mpr hd

/-- Iter 13 corollary, Path B: **the Σ₂ class contains every binary union
    of Π₁-definable subsets**.

    Direct application of `union_isCoDiophantineDefinition` followed by
    `codiophantine_implies_existentialUniversal` (Π₁ ⊆ Σ₂). Stated as a
    transport: if `S₁`, `S₂` are Π₁-definable, then `S₁ ∪ S₂` is
    Σ₂-definable.

    NOT the strongest possible Σ₂-closure statement (which would require
    a direct Σ₂ witness for `S₁ ∪ S₂` when `S₁`, `S₂` are arbitrary
    Σ₂-definable subsets — strictly bigger than Π₁ ∪ closure). The
    stronger Σ₂ ∪ Σ₂ ⊆ Σ₂ closure is left as future work. -/
theorem union_isExistentialUniversalDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsCoDiophantineDefinition S₁) (h₂ : IsCoDiophantineDefinition S₂) :
    IsExistentialUniversalDefinition (fun q => S₁ q ∨ S₂ q) :=
  codiophantine_implies_existentialUniversal _
    (union_isCoDiophantineDefinition h₁ h₂)

-- ============================================================
-- Part VIII.14 (iter 14, Path B): list version of Σ₁ ∩ closure
-- ============================================================

/-- Iter 14, Path B: **the Σ₁ class is closed under finite list intersection**.

    If every set in a list `l : List RatSubset` is Σ₁-definable, then so is
    the pointwise universal predicate `fun q => ∀ S ∈ l, S q`. Direct list
    lift of iter 12's `intersection_isDiophantineDefinition` by induction on
    the list, with the empty list giving the universe set
    (vacuous quantifier ↔ True).

    **Strategy** (no new Mathlib lemmas, no new imports): induction on `l`,
    base case via `universe_isDiophantineDefinition` + iter-4 congruence
    bridge, step case via iter-12 `intersection_isDiophantineDefinition`
    applied to the head and the inductive hypothesis on the tail.

    **Significance**: pairs with iter-10's
    `finUnionList_singletons_isDiophantineDefinition` (list union of
    *singletons*) to give arbitrary list intersection of arbitrary
    Σ₁-definable subsets. With iter 13 the 2×2 finite Boolean closure grid
    for Σ₁ and Π₁ over ℚ is now closed under FINITE arbitrary-arity ∩, ∪
    on the appropriate side. -/
theorem finIntersectionList_isDiophantineDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsDiophantineDefinition S) :
    IsDiophantineDefinition (fun q : Rat => ∀ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => True) q := by
      intro q; simp
    exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr
      universe_isDiophantineDefinition
  | cons a t ih =>
    have h_head : IsDiophantineDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsDiophantineDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsDiophantineDefinition (fun q : Rat => ∀ S ∈ t, S q) :=
      ih h_tail
    have h_inter : IsDiophantineDefinition
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) :=
      intersection_isDiophantineDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) q := by
      intro q
      constructor
      · intro hall
        refine ⟨hall a (List.mem_cons_self),
          fun S hS => hall S (List.mem_cons_of_mem a hS)⟩
      · rintro ⟨ha, htail⟩ S hS
        rcases List.mem_cons.mp hS with rfl | hSt
        · exact ha
        · exact htail S hSt
    exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr h_inter

/-- Iter 14 corollary, Path B: **list intersection of Σ₁-definable subsets
    is Π₂-definable** via the trivial inclusion `Σ₁ ⊆ Π₂`. -/
theorem finIntersectionList_isUniversalExistentialDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsDiophantineDefinition S) :
    IsUniversalExistentialDefinition (fun q : Rat => ∀ S ∈ l, S q) :=
  diophantine_implies_universal_existential _
    (finIntersectionList_isDiophantineDefinition l h)

-- ============================================================
-- Part VIII.15 (iter 14, Path B): list version of Π₁ ∪ closure
-- ============================================================

/-- Iter 14, Path B: **the Π₁ class is closed under finite list union**.

    If every set in a list `l : List RatSubset` is Π₁-definable, then so is
    the pointwise existential predicate `fun q => ∃ S ∈ l, S q`. Direct
    list lift of iter 13's `union_isCoDiophantineDefinition` by induction
    on the list, with the empty list giving the empty set
    (vacuous existential ↔ False).

    **Strategy**: induction on `l`, base case via
    `empty_isCoDiophantineDefinition` + iter-4 congruence bridge, step case
    via iter-13 `union_isCoDiophantineDefinition` applied to the head and
    the inductive hypothesis on the tail.

    **Significance**: pairs with iter 14's
    `finIntersectionList_isDiophantineDefinition` to give the list-arity
    closure side of the 2×2 closure grid; both classes are now closed
    under arbitrary FINITE-arity Boolean combinations within their own
    operation (Σ₁ under list ∩ and ∪, Π₁ under list ∩ and ∪). Neither
    class is (known to be) closed under complement; that would collapse
    Π₁ = Σ₁, equivalent to the OPEN question. -/
theorem finUnionList_isCoDiophantineDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
    IsCoDiophantineDefinition (fun q : Rat => ∃ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => False) q := by
      intro q; simp
    exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr
      empty_isCoDiophantineDefinition
  | cons a t ih =>
    have h_head : IsCoDiophantineDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsCoDiophantineDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsCoDiophantineDefinition (fun q : Rat => ∃ S ∈ t, S q) :=
      ih h_tail
    have h_union : IsCoDiophantineDefinition
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) :=
      union_isCoDiophantineDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) q := by
      intro q
      constructor
      · rintro ⟨S, hSmem, hSq⟩
        rcases List.mem_cons.mp hSmem with rfl | hSt
        · exact Or.inl hSq
        · exact Or.inr ⟨S, hSt, hSq⟩
      · rintro (ha | ⟨S, hSt, hSq⟩)
        · exact ⟨a, List.mem_cons_self, ha⟩
        · exact ⟨S, List.mem_cons_of_mem a hSt, hSq⟩
    exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr h_union

/-- Iter 14 corollary, Path B: **list union of Π₁-definable subsets is
    Σ₂-definable** via the trivial inclusion `Π₁ ⊆ Σ₂`. -/
theorem finUnionList_isExistentialUniversalDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
    IsExistentialUniversalDefinition (fun q : Rat => ∃ S ∈ l, S q) :=
  codiophantine_implies_existentialUniversal _
    (finUnionList_isCoDiophantineDefinition l h)

-- ============================================================
-- Part VIII.16 (iter 15, Path B): list version of Σ₁ ∪ closure
-- ============================================================

/-- Iter 15, Path B: **the Σ₁ class is closed under finite list union of
    arbitrary Σ₁-definable subsets**.

    If every set in a list `l : List RatSubset` is Σ₁-definable, then so
    is the pointwise existential predicate `fun q => ∃ S ∈ l, S q`.
    Direct list lift of iter 9's `union_isDiophantineDefinition` by
    induction on the list, with the empty list giving the empty set
    (vacuous existential ↔ False).

    **Strategy** (no new Mathlib lemmas, no new imports): induction on
    `l`, base case via `empty_isDiophantineDefinition` + iter-4
    congruence bridge, step case via iter-9 `union_isDiophantineDefinition`
    applied to the head and the inductive hypothesis on the tail. Same
    structural template as iter 14's
    `finUnionList_isCoDiophantineDefinition` (Π₁ list ∪), but with the
    iter 9 binary witness (product polynomial `P₁·P₂` via `mul_eq_zero`)
    instead of iter 13's sum-of-squares — hence cheaper, with one fewer
    even/odd interleaving per cons step.

    **Significance**: generalizes iter 10's
    `finUnionList_singletons_isDiophantineDefinition` (which restricted
    to SINGLETONS) to ARBITRARY Σ₁-definable subsets. Pairs with iter 14
    `finIntersectionList_isDiophantineDefinition` (Σ₁ list ∩) and iter
    14 `finUnionList_isCoDiophantineDefinition` (Π₁ list ∪) to fully
    populate the 2×2 closure grid at finite-list arity for arbitrary
    Σ₁/Π₁ subsets:

        | Class | binary ∪  | binary ∩  | list ∪    | list ∩    |
        |-------|-----------|-----------|-----------|-----------|
        | Σ₁    | iter 9    | iter 12   | iter 15   | iter 14   |
        | Π₁    | iter 13   | iter 9    | iter 14   | iter 15   |

    Neither class is (known to be) closed under complement; that would
    collapse Σ₁ = Π₁, equivalent to the OPEN question. -/
theorem finUnionList_isDiophantineDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsDiophantineDefinition S) :
    IsDiophantineDefinition (fun q : Rat => ∃ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => False) q := by
      intro q; simp
    exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr
      empty_isDiophantineDefinition
  | cons a t ih =>
    have h_head : IsDiophantineDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsDiophantineDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsDiophantineDefinition (fun q : Rat => ∃ S ∈ t, S q) :=
      ih h_tail
    have h_union : IsDiophantineDefinition
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) :=
      union_isDiophantineDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) q := by
      intro q
      constructor
      · rintro ⟨S, hSmem, hSq⟩
        rcases List.mem_cons.mp hSmem with rfl | hSt
        · exact Or.inl hSq
        · exact Or.inr ⟨S, hSt, hSq⟩
      · rintro (ha | ⟨S, hSt, hSq⟩)
        · exact ⟨a, List.mem_cons_self, ha⟩
        · exact ⟨S, List.mem_cons_of_mem a hSt, hSq⟩
    exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr h_union

/-- Iter 15 corollary, Path B: **list union of Σ₁-definable subsets is
    Π₂-definable** via the trivial inclusion `Σ₁ ⊆ Π₂`. -/
theorem finUnionList_isUniversalExistentialDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsDiophantineDefinition S) :
    IsUniversalExistentialDefinition (fun q : Rat => ∃ S ∈ l, S q) :=
  diophantine_implies_universal_existential _
    (finUnionList_isDiophantineDefinition l h)

-- ============================================================
-- Part VIII.17 (iter 15, Path B): list version of Π₁ ∩ closure
-- ============================================================

/-- Iter 15, Path B: **the Π₁ class is closed under finite list
    intersection of arbitrary Π₁-definable subsets**.

    If every set in a list `l : List RatSubset` is Π₁-definable, then so
    is the pointwise universal predicate `fun q => ∀ S ∈ l, S q`. Direct
    list lift of iter 9's `intersection_isCoDiophantineDefinition` by
    induction on the list, with the empty list giving the universe set
    (vacuous quantifier ↔ True).

    **Strategy** (no new Mathlib lemmas, no new imports): induction on
    `l`, base case via `universe_isCoDiophantineDefinition` + iter-4
    congruence bridge, step case via iter-9
    `intersection_isCoDiophantineDefinition` applied to the head and the
    inductive hypothesis on the tail. Same structural template as iter
    14's `finIntersectionList_isDiophantineDefinition` (Σ₁ list ∩), but
    with the iter 9 binary witness (product polynomial `P₁·P₂` via the
    contrapositive of `mul_eq_zero`) instead of iter 12's sum-of-squares.

    **Significance**: generalizes iter 10's
    `finIntersectionList_complement_singletons_isCoDiophantineDefinition`
    (which restricted to COMPLEMENTS-OF-SINGLETONS) to ARBITRARY
    Π₁-definable subsets. Together with iter 15's
    `finUnionList_isDiophantineDefinition` (the Σ₁ dual, this same PR)
    and iter 14's two list closures, the 2×2 closure grid is fully
    populated at finite-list arity for arbitrary Σ₁/Π₁ subsets. -/
theorem finIntersectionList_isCoDiophantineDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
    IsCoDiophantineDefinition (fun q : Rat => ∀ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => True) q := by
      intro q; simp
    exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr
      universe_isCoDiophantineDefinition
  | cons a t ih =>
    have h_head : IsCoDiophantineDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsCoDiophantineDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsCoDiophantineDefinition (fun q : Rat => ∀ S ∈ t, S q) :=
      ih h_tail
    have h_inter : IsCoDiophantineDefinition
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) :=
      intersection_isCoDiophantineDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) q := by
      intro q
      constructor
      · intro hall
        refine ⟨hall a (List.mem_cons_self),
          fun S hS => hall S (List.mem_cons_of_mem a hS)⟩
      · rintro ⟨ha, htail⟩ S hS
        rcases List.mem_cons.mp hS with rfl | hSt
        · exact ha
        · exact htail S hSt
    exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr h_inter

/-- Iter 15 corollary, Path B: **list intersection of Π₁-definable
    subsets is Σ₂-definable** via the trivial inclusion `Π₁ ⊆ Σ₂`. -/
theorem finIntersectionList_isExistentialUniversalDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
    IsExistentialUniversalDefinition (fun q : Rat => ∀ S ∈ l, S q) :=
  codiophantine_implies_existentialUniversal _
    (finIntersectionList_isCoDiophantineDefinition l h)

-- ============================================================
-- Part VIII.19 (iter 17, Path B): Finset transport of the singleton-list
-- closure of iter 10 (S11.4).
-- ============================================================

/-- Iter 17, Path B: **every `Finset Rat`-indexed finite subset of ℚ is
    Σ₁-definable**.

    Direct Finset transport of iter 10's
    `finUnionList_singletons_isDiophantineDefinition`: for any
    `s : Finset Rat`, the predicate `q ∈ s` is Σ₁-definable. Routed
    through the Mathlib bridge `Finset.mem_toList : a ∈ s.toList ↔ a ∈ s`
    via the iter 4 Σ₁ class congruence helper. The polynomial witness is
    iter 10's inductive product polynomial on `s.toList`, unchanged.

    **Significance**: completes the iter-13 next-action priority **S11.4**
    (Finset arity for the singletons-list closure). Pairs with iter 10's
    List version to give Σ₁-definability of every finite subset of ℚ
    indexed either by `List Rat` or by `Finset Rat`. The OPEN content
    remains unchanged: it is still the COUNTABLY-INFINITE union
    `⋃_{n : ℤ} {n}` that requires a UNIFORM Σ₁ witness. Iter 17 only
    promotes the FINITE side from list-indexing to set-indexing, not
    the open Σ₁ question. -/
theorem finUnionFinset_singletons_isDiophantineDefinition (s : Finset Rat) :
    IsDiophantineDefinition (fun q : Rat => q ∈ s) := by
  have hbridge : ∀ q : Rat, (fun q : Rat => q ∈ s) q ↔
      (fun q : Rat => q ∈ s.toList) q := by
    intro q; exact Finset.mem_toList.symm
  exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr
    (finUnionList_singletons_isDiophantineDefinition s.toList)

/-- Iter 17 dual, Path B: **every `Finset Rat`-indexed cofinite subset of
    ℚ is Π₁-definable**.

    Direct Finset transport of iter 10's
    `finIntersectionList_complement_singletons_isCoDiophantineDefinition`:
    for any `s : Finset Rat`, the predicate `q ∉ s` is Π₁-definable.
    Routed through `not_congr Finset.mem_toList` + iter 4 Π₁ congruence. -/
theorem finIntersectionFinset_complement_singletons_isCoDiophantineDefinition
    (s : Finset Rat) :
    IsCoDiophantineDefinition (fun q : Rat => q ∉ s) := by
  have hbridge : ∀ q : Rat, (fun q : Rat => q ∉ s) q ↔
      (fun q : Rat => q ∉ s.toList) q := by
    intro q; exact (not_congr Finset.mem_toList).symm
  exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr
    (finIntersectionList_complement_singletons_isCoDiophantineDefinition s.toList)

/-- Iter 17 corollary, Path B: **every `Finset Rat`-indexed finite subset
    of ℚ is Π₂-definable** via the trivial inclusion `Σ₁ ⊆ Π₂`. -/
theorem finUnionFinset_singletons_isUniversalExistentialDefinition
    (s : Finset Rat) :
    IsUniversalExistentialDefinition (fun q : Rat => q ∈ s) :=
  diophantine_implies_universal_existential _
    (finUnionFinset_singletons_isDiophantineDefinition s)

/-- Iter 17 corollary, Path B: **every `Finset Rat`-indexed cofinite
    subset of ℚ is Σ₂-definable** via the trivial inclusion `Π₁ ⊆ Σ₂`. -/
theorem finIntersectionFinset_complement_singletons_isExistentialUniversalDefinition
    (s : Finset Rat) :
    IsExistentialUniversalDefinition (fun q : Rat => q ∉ s) :=
  codiophantine_implies_existentialUniversal _
    (finIntersectionFinset_complement_singletons_isCoDiophantineDefinition s)

-- ============================================================
-- Part VIII.20 (iter 17, Path B): Finset transport of the arbitrary-
-- subset list closures of iter 14 / iter 15.
-- ============================================================

/-- Iter 17, Path B: **the Σ₁ class is closed under `Finset RatSubset`-
    indexed intersection of arbitrary Σ₁-definable subsets**.

    Finset analog of iter 14's `finIntersectionList_isDiophantineDefinition`,
    transported via `Finset.mem_toList`. The witness polynomial is the
    inductive sum-of-squares + interleave on `s.toList` from iter 14
    (which itself unfolds to iter 12 per cons step). -/
theorem finIntersectionFinset_isDiophantineDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsDiophantineDefinition S) :
    IsDiophantineDefinition (fun q : Rat => ∀ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsDiophantineDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∀ S ∈ s, S q) q ↔
      (fun q : Rat => ∀ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · intro hall S hS; exact hall S (Finset.mem_toList.mp hS)
    · intro hall S hS; exact hall S (Finset.mem_toList.mpr hS)
  exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr
    (finIntersectionList_isDiophantineDefinition s.toList h_list)

/-- Iter 17, Path B: **the Π₁ class is closed under `Finset RatSubset`-
    indexed union of arbitrary Π₁-definable subsets**.

    Finset analog of iter 14's `finUnionList_isCoDiophantineDefinition`,
    transported via `Finset.mem_toList`. -/
theorem finUnionFinset_isCoDiophantineDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsCoDiophantineDefinition S) :
    IsCoDiophantineDefinition (fun q : Rat => ∃ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsCoDiophantineDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∃ S ∈ s, S q) q ↔
      (fun q : Rat => ∃ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mpr hS, hSq⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mp hS, hSq⟩
  exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr
    (finUnionList_isCoDiophantineDefinition s.toList h_list)

/-- Iter 17, Path B: **the Σ₁ class is closed under `Finset RatSubset`-
    indexed union of arbitrary Σ₁-definable subsets**.

    Finset analog of iter 15's `finUnionList_isDiophantineDefinition`,
    transported via `Finset.mem_toList`. The witness polynomial is the
    inductive product polynomial on `s.toList` from iter 15 (which
    itself unfolds to iter 9 per cons step). -/
theorem finUnionFinset_isDiophantineDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsDiophantineDefinition S) :
    IsDiophantineDefinition (fun q : Rat => ∃ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsDiophantineDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∃ S ∈ s, S q) q ↔
      (fun q : Rat => ∃ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mpr hS, hSq⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mp hS, hSq⟩
  exact (diophantineDefinition_iff_of_pred_iff hbridge).mpr
    (finUnionList_isDiophantineDefinition s.toList h_list)

/-- Iter 17, Path B: **the Π₁ class is closed under `Finset RatSubset`-
    indexed intersection of arbitrary Π₁-definable subsets**.

    Finset analog of iter 15's `finIntersectionList_isCoDiophantineDefinition`,
    transported via `Finset.mem_toList`. -/
theorem finIntersectionFinset_isCoDiophantineDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsCoDiophantineDefinition S) :
    IsCoDiophantineDefinition (fun q : Rat => ∀ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsCoDiophantineDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∀ S ∈ s, S q) q ↔
      (fun q : Rat => ∀ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · intro hall S hS; exact hall S (Finset.mem_toList.mp hS)
    · intro hall S hS; exact hall S (Finset.mem_toList.mpr hS)
  exact (coDiophantineDefinition_iff_of_pred_iff hbridge).mpr
    (finIntersectionList_isCoDiophantineDefinition s.toList h_list)

-- ============================================================
-- Part VIII.21 (iter 20, Path B): Σ₂ closed under binary intersection
--                                 (∃y₁∀x P₁≠0 ∧ ∃y₂∀x P₂≠0 ⟹ ∃y∀x P≠0;
--                                 product polynomial + interleave on the
--                                 existential `y`-block, shared `x`).
-- ============================================================

/-- Iter 20, Path B: **the Σ₂ class is closed under binary intersection**.

    Direct level-2 analog of iter 9's `union_isDiophantineDefinition`
    (Σ₁ ∪ via product polynomial) and the missing pair to iter 16's
    `pi2_intersection_isUniversalExistentialDefinition` (Π₂ ∩) /
    `sigma2_union_isExistentialUniversalDefinition` (Σ₂ ∪): if `S₁`
    and `S₂` are both Σ₂-definable over ℚ, then so is the pointwise
    conjunction `fun q => S₁ q ∧ S₂ q`.

    **Witness** (product polynomial with variable packing on the
    existential `y`-block; universal `x`-block shared): given Σ₂
    witnesses `P_i (q, y, x)` for `S_i`, the polynomial

        Q(q, y, x) := P₁(q, evenProj y, x) · P₂(q, oddProj y, x)

    has the property that for every `y`, the rational solution set of
    `Q(q, y, ·)` is empty iff for that `y` neither `P₁(q, evenProj y, ·)`
    nor `P₂(q, oddProj y, ·)` has a rational solution. Crucially, the
    universal `x`-block is **shared** between the two factors — there
    is no need to interleave `x`, only the existential `y`. This is
    the **dual situation** of iter 16's Π₂ ∩ closure (which packs `x`
    and shares `y`); here the inner `∀x` is the same in both factors,
    while the outer `∃y` may differ between `S₁` and `S₂`, hence the
    interleave on `y`.

    **Forward** (`(S₁ q ∧ S₂ q) → ∃ y, ¬ ∃ x, Q(q, y, x) = 0`): peel
    `y_i` witnesses from each `(hP_i q).mp hS_i`, then take
    `y := interleave y₁ y₂`. The projection lemmas
    `evenProj_interleave : evenProj (interleave y₁ y₂) = y₁` and
    `oddProj_interleave : oddProj (interleave y₁ y₂) = y₂` rewrite
    `Q(q, interleave y₁ y₂, ·) = P₁(q, y₁, ·) · P₂(q, y₂, ·)`. If a
    common `x` made the product zero, by `mul_eq_zero` (NoZeroDivisors
    over ℚ) one of the factors `P_i(q, y_i, x)` must equal zero,
    contradicting `hy_i : ¬ ∃ x, P_i(q, y_i, x) = 0`.

    **Reverse** (`(∃ y, ¬ ∃ x, Q = 0) → S₁ q ∧ S₂ q`): peel the witness
    `y`, then split into the `S₁` and `S₂` halves via
    `evenProj y` (resp. `oddProj y`). For each half: a putative
    `x : (P_i q (evenProj y)) x = 0` would give `Q(q, y, x) =
    0 · P_₂(...) x = 0` (resp. `P_₁(...) x · 0`), contradicting the Σ₂
    hypothesis on `Q`.

    **Path B** (Mathlib): no new imports — reuses `mul_eq_zero`
    (`Mathlib.Algebra.GroupWithZero.Basic`, already imported in iter 9
    for `union_isDiophantineDefinition`) and the iter 12 packing
    helpers `evenProj`, `oddProj`, `interleave`, `evenProj_interleave`,
    `oddProj_interleave`. No new axioms.

    **Strictly bigger than iter 13's transport**: iter 13's
    `union_isExistentialUniversalDefinition` only delivers Σ₂ closure
    under union when both inputs are Π₁; this iter delivers Σ₂ closure
    under intersection even when the inputs are properly Σ₂ (e.g., the
    Σ₂(ℚ \ ℤ) corollary of Koenigsmann from
    `koenigsmann_implies_complement_existentialUniversal`). In
    particular, this iter yields:

        koenigsmann_implies_complement_existentialUniversal
          ∧ koenigsmann_implies_complement_existentialUniversal
            → IsExistentialUniversalDefinition (fun q => ¬ IntSubset q ∧ ¬ IntSubset q)

    (the Σ₂-definability of `(ℚ \ ℤ) ∩ (ℚ \ ℤ) = ℚ \ ℤ`, a tautology
    in this case but a genuinely new closure step in cases where the
    two Σ₂ inputs are not identical).

    **Completes the Σ₂ binary closure grid** (combined with iter 16's
    `sigma2_union_isExistentialUniversalDefinition`): Σ₂ is closed
    under both binary union AND binary intersection — hence under
    arbitrary FINITE Boolean combinations using ∪ and ∩. Σ₂ is NOT
    (known to be) closed under complement; that would collapse Σ₂ = Π₂
    over ℚ — a level-2 analog of the OPEN Σ₁ vs Π₁ question, currently
    OPEN at level 2 as well. -/
theorem sigma2_intersection_isExistentialUniversalDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsExistentialUniversalDefinition S₁)
    (h₂ : IsExistentialUniversalDefinition S₂) :
    IsExistentialUniversalDefinition (fun q => S₁ q ∧ S₂ q) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨fun q y x =>
    (P₁ q (evenProj y)) x * (P₂ q (oddProj y)) x, fun q => ?_⟩
  constructor
  · rintro ⟨hS₁, hS₂⟩
    obtain ⟨y₁, hy₁⟩ := (hP₁ q).mp hS₁
    obtain ⟨y₂, hy₂⟩ := (hP₂ q).mp hS₂
    refine ⟨interleave y₁ y₂, ?_⟩
    rintro ⟨x, hx⟩
    simp only [evenProj_interleave, oddProj_interleave] at hx
    rcases mul_eq_zero.mp hx with h1 | h2
    · exact hy₁ ⟨x, h1⟩
    · exact hy₂ ⟨x, h2⟩
  · rintro ⟨y, hy⟩
    refine ⟨(hP₁ q).mpr ⟨evenProj y, ?_⟩, (hP₂ q).mpr ⟨oddProj y, ?_⟩⟩
    · rintro ⟨x, hx⟩
      apply hy
      exact ⟨x, by simp only [hx, zero_mul]⟩
    · rintro ⟨x, hx⟩
      apply hy
      exact ⟨x, by simp only [hx, mul_zero]⟩

-- ============================================================
-- Part VIII.22 (iter 20, Path B): Π₂ closed under binary union
--                                 (corollary via Σ₂/Π₂ duality
--                                 + iter 20 Σ₂ ∩ closure).
-- ============================================================

/-- Iter 20, Path B: **the Π₂ class is closed under binary union**.

    The missing pair to iter 16's
    `pi2_intersection_isUniversalExistentialDefinition` (Π₂ ∩):
    direct dual via the iter 5 Σ₂/Π₂ duality, the iter 20 Σ₂ ∩ closure
    above, and the iter 4 Π₂ class congruence helper —
    structurally identical to iter 13's construction of
    `union_isCoDiophantineDefinition` from `intersection_isDiophantineDefinition`,
    one level higher.

      Π₂(S₁), Π₂(S₂)
        →[iter 5 universalExistential_iff_existentialUniversal_complement]
                                                       Σ₂(¬S₁), Σ₂(¬S₂)
        →[iter 20 sigma2_intersection_isExistentialUniversalDefinition]
                                                       Σ₂(¬S₁ ∧ ¬S₂)
        →[iter 4 existentialUniversalDefinition_iff_of_pred_iff
           via constructive de Morgan ¬S₁ ∧ ¬S₂ ↔ ¬(S₁ ∨ S₂)]
                                                       Σ₂(¬(S₁ ∨ S₂))
        →[iter 5 universalExistential_iff_existentialUniversal_complement]
                                                       Π₂(S₁ ∨ S₂)

    The de Morgan bridge is **constructive** (no LEM beyond what the
    iter 5 duality already uses internally — two `Classical.byContradiction`
    invocations, the same as iter 5).

    **Strictly bigger than iter 12's transport**: iter 12's
    `intersection_isUniversalExistentialDefinition` only delivers Π₂
    closure under intersection when both inputs are Σ₁; this iter
    delivers Π₂ closure under union even when the inputs are properly
    Π₂ (e.g., `IntSubset` itself, via `koenigsmann_2016_universal`).

    **Completes the Π₂ binary closure grid** (combined with iter 16's
    `pi2_intersection_isUniversalExistentialDefinition`): Π₂ is closed
    under both binary union AND binary intersection. The level-2 Σ₂/Π₂
    duality at the binary level is now fully populated:

        | Class | binary ∪          | binary ∩          |
        |-------|-------------------|-------------------|
        | Σ₂    | iter 16 (#17456)  | iter 20 (this PR) |
        | Π₂    | iter 20 (this PR) | iter 16 (#17456)  |

    Path B (Mathlib): no new imports beyond what iter 20's Σ₂ ∩ closure
    already requires. No new axioms. -/
theorem pi2_union_isUniversalExistentialDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsUniversalExistentialDefinition S₁)
    (h₂ : IsUniversalExistentialDefinition S₂) :
    IsUniversalExistentialDefinition (fun q => S₁ q ∨ S₂ q) := by
  -- Step 1: dualize each Π₂ to Σ₂ on the complement (iter 5 duality).
  have hd₁ : IsExistentialUniversalDefinition (fun q => ¬ S₁ q) :=
    (universalExistential_iff_existentialUniversal_complement S₁).mp h₁
  have hd₂ : IsExistentialUniversalDefinition (fun q => ¬ S₂ q) :=
    (universalExistential_iff_existentialUniversal_complement S₂).mp h₂
  -- Step 2: Σ₂ closed under binary intersection (iter 20, main lemma).
  have hcap : IsExistentialUniversalDefinition (fun q => ¬ S₁ q ∧ ¬ S₂ q) :=
    sigma2_intersection_isExistentialUniversalDefinition hd₁ hd₂
  -- Step 3: bridge via constructive de Morgan
  --     `¬ S₁ q ∧ ¬ S₂ q ↔ ¬ (S₁ q ∨ S₂ q)`.
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ¬ S₁ q ∧ ¬ S₂ q) q ↔
        (fun q : Rat => ¬ (S₁ q ∨ S₂ q)) q := by
    intro q
    refine ⟨fun ⟨hn₁, hn₂⟩ hor => hor.elim hn₁ hn₂,
            fun hnor => ⟨fun h₁q => hnor (Or.inl h₁q),
                          fun h₂q => hnor (Or.inr h₂q)⟩⟩
  have hd : IsExistentialUniversalDefinition (fun q : Rat => ¬ (S₁ q ∨ S₂ q)) :=
    (existentialUniversalDefinition_iff_of_pred_iff hbridge).mp hcap
  -- Step 4: Σ₂(¬T) → Π₂(T) via duality (iter 5), with T = S₁ ∪ S₂.
  exact (universalExistential_iff_existentialUniversal_complement
    (fun q => S₁ q ∨ S₂ q)).mpr hd

-- ============================================================
-- Part VIII.23 (iter 21, Path B): list version of Σ₂ ∩ closure
-- ============================================================

/-- Iter 21, Path B: **the Σ₂ class is closed under finite list intersection**.

    Direct list lift of iter 20's `sigma2_intersection_isExistentialUniversalDefinition`
    by induction on the list, with the empty list giving the universe set
    (vacuous universal `∀ S ∈ [], S q ↔ True`).

    **Strategy** (mirrors iter 14's `finIntersectionList_isDiophantineDefinition`
    at level 1, one level higher): induction on `l : List RatSubset`,
    base case via `universe_isExistentialUniversalDefinition` + iter-4 Σ₂
    class congruence bridge, step case via iter-20
    `sigma2_intersection_isExistentialUniversalDefinition` applied to the
    head and the inductive hypothesis on the tail.

    **Significance**: lifts iter 20's binary Σ₂ ∩ closure to arbitrary
    finite list arity. Combined with iter 18 (Σ₂ list ∪, in PR #17552
    stacked on iter 16 PR #17456), the list-arity Σ₂ binary-Boolean
    closure grid is fully populated:

        | Class | binary ∪          | binary ∩          | list ∪      | list ∩      |
        |-------|-------------------|-------------------|-------------|-------------|
        | Σ₂    | iter 16 (#17456)  | iter 20 (on main) | iter 18 (#17552) | iter 21 (this) |
        | Π₂    | iter 20 (on main) | iter 16 (#17456)  | iter 21 (this) | iter 18 (#17552) |

    See `pi2_unionList_isUniversalExistentialDefinition` (just below)
    for the Π₂ side.

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 20's binary `sigma2_intersection_isExistentialUniversalDefinition`
    (already on origin/main via #17628), iter 5's
    `universe_isExistentialUniversalDefinition`, iter 4's Σ₂ class
    congruence helper `existentialUniversalDefinition_iff_of_pred_iff`,
    and the standard Lean-core list helpers `List.mem_cons_self`,
    `List.mem_cons_of_mem`, `List.mem_cons`.

    **OPEN content unchanged**: the central Σ₁ question for ℤ ⊂ ℚ is
    unaffected. Iter 21 only sharpens the level-2 list-arity closure
    properties. -/
theorem sigma2_intersectionList_isExistentialUniversalDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsExistentialUniversalDefinition S) :
    IsExistentialUniversalDefinition (fun q : Rat => ∀ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => True) q := by
      intro q; simp
    exact (existentialUniversalDefinition_iff_of_pred_iff hbridge).mpr
      universe_isExistentialUniversalDefinition
  | cons a t ih =>
    have h_head : IsExistentialUniversalDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsExistentialUniversalDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsExistentialUniversalDefinition
        (fun q : Rat => ∀ S ∈ t, S q) :=
      ih h_tail
    have h_inter : IsExistentialUniversalDefinition
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) :=
      sigma2_intersection_isExistentialUniversalDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) q := by
      intro q
      constructor
      · intro hall
        refine ⟨hall a (List.mem_cons_self),
          fun S hS => hall S (List.mem_cons_of_mem a hS)⟩
      · rintro ⟨ha, htail⟩ S hS
        rcases List.mem_cons.mp hS with rfl | hSt
        · exact ha
        · exact htail S hSt
    exact (existentialUniversalDefinition_iff_of_pred_iff hbridge).mpr h_inter

-- ============================================================
-- Part VIII.24 (iter 21, Path B): list version of Π₂ ∪ closure
-- ============================================================

/-- Iter 21, Path B: **the Π₂ class is closed under finite list union**.

    Direct list lift of iter 20's `pi2_union_isUniversalExistentialDefinition`
    by induction on the list, with the empty list giving the empty set
    (vacuous existential `∃ S ∈ [], S q ↔ False`).

    **Strategy** (mirrors iter 14's `finUnionList_isCoDiophantineDefinition`
    at level 1, one level higher): induction on `l : List RatSubset`,
    base case via `empty_isUniversalExistentialDefinition` + iter-4 Π₂
    class congruence bridge, step case via iter-20
    `pi2_union_isUniversalExistentialDefinition` applied to the head and
    the inductive hypothesis on the tail.

    **Significance**: completes the list-arity row of the level-2 binary
    Boolean closure grid (alongside iter 21's
    `sigma2_intersectionList_isExistentialUniversalDefinition` above and
    iter 18 PR #17552 for the iter-16-based cells). Every finite list
    union of Π₂-definable subsets is itself Π₂-definable.

    **Strictly bigger than iter 14's transports**: iter 14 only handles
    diagonal-input cases (Σ₁ list ∪ → Π₂ via Σ₁ ⊆ Π₂); iter 21 handles
    arbitrary Π₂ inputs (e.g., a list containing the Π₂ predicate
    `IntSubset` from `koenigsmann_2016_universal`, or any of the Π₂
    subsets produced by trivial inclusions Σ₁ ⊆ Π₂ from iter 11).

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 20's binary `pi2_union_isUniversalExistentialDefinition`
    (already on origin/main via #17628), iter 5's
    `empty_isUniversalExistentialDefinition`, iter 4's Π₂ class
    congruence helper `universalExistentialDefinition_iff_of_pred_iff`,
    and the standard Lean-core list helpers `List.mem_cons_self`,
    `List.mem_cons_of_mem`, `List.mem_cons`.

    **OPEN content unchanged**: the central Σ₁ question for ℤ ⊂ ℚ is
    unaffected. Iter 21 only sharpens the level-2 list-arity closure
    properties. -/
theorem pi2_unionList_isUniversalExistentialDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsUniversalExistentialDefinition S) :
    IsUniversalExistentialDefinition (fun q : Rat => ∃ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => False) q := by
      intro q; simp
    exact (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr
      empty_isUniversalExistentialDefinition
  | cons a t ih =>
    have h_head : IsUniversalExistentialDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsUniversalExistentialDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsUniversalExistentialDefinition
        (fun q : Rat => ∃ S ∈ t, S q) :=
      ih h_tail
    have h_union : IsUniversalExistentialDefinition
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) :=
      pi2_union_isUniversalExistentialDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) q := by
      intro q
      constructor
      · rintro ⟨S, hSmem, hSq⟩
        rcases List.mem_cons.mp hSmem with rfl | hSt
        · exact Or.inl hSq
        · exact Or.inr ⟨S, hSt, hSq⟩
      · rintro (ha | ⟨S, hSt, hSq⟩)
        · exact ⟨a, List.mem_cons_self, ha⟩
        · exact ⟨S, List.mem_cons_of_mem a hSt, hSq⟩
    exact (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr h_union

-- ============================================================
-- Part VIII.25 (iter 22, Path B): Finset transport of iter 21's
--                                 list-arity Σ₂ ∩ closure
-- ============================================================

/-- Iter 22, Path B: **the Σ₂ class is closed under `Finset RatSubset`-
    indexed intersection of arbitrary Σ₂-definable subsets**.

    Finset analog of iter 21's
    `sigma2_intersectionList_isExistentialUniversalDefinition`, transported
    via `Finset.mem_toList`. Mirrors iter 17's Finset transport template
    one level higher: the underlying polynomial witness is unchanged from
    iter 21 (which itself unfolds to iter 20's binary Σ₂ ∩ per cons step
    on `s.toList`).

    **Strategy**: lift hypotheses from `s : Finset RatSubset` to
    `s.toList : List RatSubset` via `Finset.mem_toList.mp`, bridge the
    Finset/list quantifier predicates with `Finset.mem_toList.mp`/`.mpr`,
    and apply iter-4 Σ₂ class congruence
    (`existentialUniversalDefinition_iff_of_pred_iff`) to iter 21's
    list-arity result.

    **Significance**: extends iter 21's list-arity Σ₂ ∩ closure to
    `Finset`-indexed intersections of arbitrary Σ₂-definable subsets,
    completing the Finset-arity entry for the level-2 cell already on
    main via iter 20 + iter 21:

        | Class | binary ∪          | binary ∩          | list ∪      | list ∩      | finset ∪   | finset ∩   |
        |-------|-------------------|-------------------|-------------|-------------|------------|------------|
        | Σ₁    | iter 9 (on main)  | iter 12 (on main) | iter 15     | iter 14     | iter 17 (on main, ∪) | iter 17 (on main, ∩) |
        | Π₁    | iter 13 (on main) | iter 9 (on main)  | iter 14     | iter 15     | iter 17 (on main, ∪) | iter 17 (on main, ∩) |
        | Σ₂    | open in #17456    | iter 20 (on main) | open #17552 | iter 21 (on main) | open in #17602 (Σ₂∪) | **this PR (Σ₂∩)** |
        | Π₂    | iter 20 (on main) | open in #17456    | iter 21 (on main) | open #17552 | **this PR (Π₂∪)** | open in #17602 (Π₂∩) |

    **OPEN content unchanged**: the central Σ₁ question for ℤ ⊂ ℚ is
    unaffected; iter 22 only sharpens the structural understanding of
    finite-arity Σ₂/Π₂ closure properties at the Finset arity, for the
    iter-21-based cells (the iter-16-based finset cells remain
    in-flight in PR #17602).

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 21's list-arity
    `sigma2_intersectionList_isExistentialUniversalDefinition`
    (already on origin/main via #17676), iter 4's Σ₂ class congruence
    helper `existentialUniversalDefinition_iff_of_pred_iff` (already on
    origin/main since iter 4 PR #17026), and the standard Mathlib lemma
    `Finset.mem_toList.mp`/`.mpr` (`Mathlib.Data.Finset.Basic`, already
    imported since iter 17 PR #17478). -/
theorem sigma2_intersectionFinset_isExistentialUniversalDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsExistentialUniversalDefinition S) :
    IsExistentialUniversalDefinition (fun q : Rat => ∀ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsExistentialUniversalDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∀ S ∈ s, S q) q ↔
      (fun q : Rat => ∀ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · intro hall S hS; exact hall S (Finset.mem_toList.mp hS)
    · intro hall S hS; exact hall S (Finset.mem_toList.mpr hS)
  exact (existentialUniversalDefinition_iff_of_pred_iff hbridge).mpr
    (sigma2_intersectionList_isExistentialUniversalDefinition s.toList h_list)

-- ============================================================
-- Part VIII.26 (iter 22, Path B): Finset transport of iter 21's
--                                 list-arity Π₂ ∪ closure
-- ============================================================

/-- Iter 22, Path B: **the Π₂ class is closed under `Finset RatSubset`-
    indexed union of arbitrary Π₂-definable subsets**.

    Finset analog of iter 21's
    `pi2_unionList_isUniversalExistentialDefinition`, transported via
    `Finset.mem_toList`. Symmetric to the Σ₂ Finset ∩ closure above.

    **Strategy**: identical structure to
    `sigma2_intersectionFinset_isExistentialUniversalDefinition` above,
    with `∀ S ∈ ·` replaced by `∃ S ∈ ·` and Σ₂ class congruence
    replaced by Π₂ class congruence
    (`universalExistentialDefinition_iff_of_pred_iff`).

    **Significance**: extends iter 21's list-arity Π₂ ∪ closure to
    `Finset`-indexed unions of arbitrary Π₂-definable subsets,
    completing the Finset-arity row for the iter-20-based level-2
    Boolean cells. Strictly bigger than iter 17's Σ₁ ⊆ Π₂ Finset
    transports: iter 22 handles arbitrary Π₂ inputs (e.g., a Finset
    containing the Π₂ predicate `IntSubset` from
    `koenigsmann_2016_universal`, or any properly Π₂ subset arising
    from iter 20's binary Π₂ ∪ + iter 21's list lift).

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 21's list-arity
    `pi2_unionList_isUniversalExistentialDefinition` (already on
    origin/main via #17676), iter 4's Π₂ class congruence helper
    `universalExistentialDefinition_iff_of_pred_iff` (on origin/main
    since iter 4 PR #17026), and the standard `Finset.mem_toList`
    bridge (on origin/main since iter 17 PR #17478). -/
theorem pi2_unionFinset_isUniversalExistentialDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsUniversalExistentialDefinition S) :
    IsUniversalExistentialDefinition (fun q : Rat => ∃ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsUniversalExistentialDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∃ S ∈ s, S q) q ↔
      (fun q : Rat => ∃ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mpr hS, hSq⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mp hS, hSq⟩
  exact (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr
    (pi2_unionList_isUniversalExistentialDefinition s.toList h_list)

-- ============================================================
-- Part VIII.27 (iter 23, Path B): the level-2 OPEN question
--   `Σ₂(ℤ) ⟺ Π₂(ℚ \ ℤ)` — symmetric companion of iter 0's
--   `Σ₁(ℤ) ⟺ Π₁(ℚ \ ℤ)` (`integers_diophantine_iff_complement_codiophantine`)
-- ============================================================

/-- **Iteration 23 — level-2 OPEN question, Prop form**:

    The Σ₂-definability of ℤ ⊂ ℚ, exposed as a named `Prop`.

    Currently OPEN (2026). This is the level-2 analog of the central
    Σ₁-definability question (`IntegersAreDiophantineOverQ`,
    equivalently `IntegersDiophantineOverQ` from `Hilbert10OQ01.lean`):
    Koenigsmann places ℤ in Π₂, and Σ₂(ℚ \ ℤ) follows by the Σ₂/Π₂
    duality (`koenigsmann_implies_complement_existentialUniversal`),
    but Σ₂(ℤ) itself is not currently known.

    Significance:
    - A *positive* Σ₂(ℤ) answer would NOT directly imply H10/ℚ
      undecidability the way Σ₁(ℤ) does (Σ₂ does not carry the MRDP
      transfer); it *would*, however, place ℤ in `Δ₂ := Σ₂ ∩ Π₂`,
      yielding a strict refinement of Koenigsmann's Π₂ result.
    - A *negative* Σ₂(ℤ) answer would imply Π₂ \ Σ₂ is non-empty at
      this level — a level-2 analog of the conjectured Π₁ \ Σ₁
      separation at level 1 (the central problem).
    - The status is sensitive to model-theoretic content beyond
      MRDP: it asks whether the Koenigsmann construction can be
      "reflected" through Σ₂ rather than (only) Π₂. -/
def IntegersAreExistentialUniversalOverQ : Prop :=
  IsExistentialUniversalDefinition IntSubset

/-- **Iteration 23 — level-2 complement duality, specialized**:

    `Σ₂(ℤ ⊂ ℚ) ⟺ Π₂(ℚ \ ℤ)`. Both sides are currently OPEN, but the
    duality is provable as a one-line specialization of
    `existentialUniversal_iff_universalExistential_complement` (the
    general symmetric Σ₂/Π₂ duality, iter 5) at `S := IntSubset`.

    This completes the symmetric pair of complement-dualities for the
    two OPEN questions tracked in this file:

    | Level | Theorem                                                         | Predicate     | Dual on `NotIntSubset` |
    |-------|-----------------------------------------------------------------|---------------|------------------------|
    | 1     | `integers_diophantine_iff_complement_codiophantine` (iter 0)    | `Σ₁(ℤ)`       | `Π₁(ℚ \ ℤ)`            |
    | 2     | `integers_existentialUniversal_iff_complement_universalExistential` (this iter) | `Σ₂(ℤ)`       | `Π₂(ℚ \ ℤ)`            |

    The level-1 row is the CENTRAL OPEN problem of this file
    (`IntegersAreDiophantineOverQ`); the level-2 row is the
    second-level analog (`IntegersAreExistentialUniversalOverQ`),
    independently OPEN.

    Asymmetry across the two rows: Π₂(ℤ) is PROVED (Koenigsmann), so
    the level-2 dual Σ₂(ℚ \ ℤ) is also PROVED
    (`koenigsmann_implies_complement_existentialUniversal`); by
    contrast, neither direction at level 1 is currently known.

    This is NOT a new axiom — pure logical glue specializing iter 5's
    duality. NO new Mathlib API; uses only
    `existentialUniversal_iff_universalExistential_complement` at the
    instance `S := IntSubset`. -/
theorem integers_existentialUniversal_iff_complement_universalExistential :
    IntegersAreExistentialUniversalOverQ ↔
      IsUniversalExistentialDefinition NotIntSubset :=
  existentialUniversal_iff_universalExistential_complement IntSubset

/-- **Iteration 23 — Π₂(ℤ) ⟹ Π₂(¬¬ ℤ) via class congruence**:

    Π₂-definability of ℤ ⊂ ℚ is invariant under the classical
    double-negation rewrite. Specialization of iter 7's
    `universalExistentialDefinition_doubleNeg_iff` to `S := IntSubset`
    combined with `koenigsmann_2016_universal`. NOT a new axiom and
    NOT a new theorem statement (the doubleNeg form is recoverable
    from iter 7 + Koenigsmann), but exposes the form that the level-2
    dual `koenigsmann_implies_complement_existentialUniversal` uses
    internally. Useful as a re-export when a downstream argument
    needs the `¬¬ IntSubset` form directly. -/
theorem koenigsmann_2016_universal_doubleNeg :
    IsUniversalExistentialDefinition (fun q : Rat => ¬ ¬ IntSubset q) := by
  have hbridge : ∀ q : Rat, IntSubset q ↔ ¬ ¬ IntSubset q :=
    fun q => ⟨fun hZ hnZ => hnZ hZ, fun hnnZ => Classical.byContradiction hnnZ⟩
  exact (universalExistentialDefinition_iff_of_pred_iff hbridge).mp
    koenigsmann_2016_universal

-- ============================================================
-- Part VIII.28 (iter 24a, Path B): the missing diagonal at level 2 —
--                                   Π₂ ∩ Π₂ ⊆ Π₂ binary
--                                   + Σ₂ ∪ Σ₂ ⊆ Σ₂ binary
-- ============================================================

/-- **Iter 24a (Π₂ binary intersection closure)**: the Π₂ class is
    closed under binary intersection.

    Direct level-2 analog of iter 12's
    `intersection_isDiophantineDefinition`: the existential `x`-block is
    packed via `evenProj`/`oddProj` while the universal `y`-block is
    shared between the two Π₂ inputs. The polynomial witness is the
    same sum-of-squares construction as iter 12, with one outer `∀ y`
    added uniformly.

    Polynomial witness:

      Q(q, y, x) := P₁(q, y, evenProj x)² + P₂(q, y, oddProj x)²

    Combined with iter 20's `pi2_union_isUniversalExistentialDefinition`,
    this **completes the Π₂ binary closure grid** (∪ AND ∩). Neither
    class is (known to be) closed under complement; that would collapse
    Σ₂ = Π₂ over ℚ, equivalent to the OPEN question via
    `existentialUniversal_iff_universalExistential_complement`.

    Re-implementation off current `origin/main` of the stale stack
    PR #17456 (CONFLICTING/DIRTY since 2026-05-08); see PREP
    `2026-05-13-iter24-prep-iter16-stack-audit.md` for the audit
    establishing tractability. ZERO new Mathlib imports; ZERO new
    helper lemmas (uses only iter 12's packing helpers `evenProj`,
    `oddProj`, `interleave`, `evenProj_interleave`,
    `oddProj_interleave`; plus `mul_self_nonneg`, `linarith`,
    `mul_eq_zero`). -/
theorem pi2_intersection_isUniversalExistentialDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsUniversalExistentialDefinition S₁)
    (h₂ : IsUniversalExistentialDefinition S₂) :
    IsUniversalExistentialDefinition (fun q => S₁ q ∧ S₂ q) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨fun q y x =>
    (P₁ q y (evenProj x)) * (P₁ q y (evenProj x)) +
    (P₂ q y (oddProj x)) * (P₂ q y (oddProj x)), fun q => ?_⟩
  constructor
  · rintro ⟨hS₁, hS₂⟩ y
    -- For each y, peel x_i from each Π₂ witness at SAME y, interleave.
    obtain ⟨x₁, hx₁⟩ := (hP₁ q).mp hS₁ y
    obtain ⟨x₂, hx₂⟩ := (hP₂ q).mp hS₂ y
    refine ⟨interleave x₁ x₂, ?_⟩
    show P₁ q y (evenProj (interleave x₁ x₂)) * P₁ q y (evenProj (interleave x₁ x₂)) +
         P₂ q y (oddProj (interleave x₁ x₂)) * P₂ q y (oddProj (interleave x₁ x₂)) = 0
    rw [evenProj_interleave, oddProj_interleave, hx₁, hx₂]
    ring
  · intro hAll
    -- For each y: sum-of-squares = 0 ⇒ each factor = 0 ⇒ S_i witness at that y.
    have hSep : ∀ y : Nat → Rat,
        (∃ x : Nat → Rat, P₁ q y x = 0) ∧ (∃ x : Nat → Rat, P₂ q y x = 0) := by
      intro y
      obtain ⟨x, hx⟩ := hAll y
      set a := P₁ q y (evenProj x)
      set b := P₂ q y (oddProj x)
      have haa_nn : (0 : Rat) ≤ a * a := mul_self_nonneg a
      have hbb_nn : (0 : Rat) ≤ b * b := mul_self_nonneg b
      have haa_zero : a * a = 0 := by linarith
      have hbb_zero : b * b = 0 := by linarith
      have ha : a = 0 := (mul_eq_zero.mp haa_zero).elim id id
      have hb : b = 0 := (mul_eq_zero.mp hbb_zero).elim id id
      exact ⟨⟨evenProj x, ha⟩, ⟨oddProj x, hb⟩⟩
    refine ⟨(hP₁ q).mpr fun y => (hSep y).1,
            (hP₂ q).mpr fun y => (hSep y).2⟩

/-- **Iter 24a (Σ₂ binary union closure)**: the Σ₂ class is closed
    under binary union.

    Direct level-2 analog of iter 13's `union_isCoDiophantineDefinition`:
    chain through iter 5's Σ₂/Π₂ duality, iter 24a's Π₂ ∩ closure
    (above), and iter 7's Π₂ class congruence helper.

      Σ₂(S₁), Σ₂(S₂)
        →[iter 5 existentialUniversal_iff_universalExistential_complement]  Π₂(¬S₁), Π₂(¬S₂)
        →[iter 24a pi2_intersection_isUniversalExistentialDefinition]        Π₂(¬S₁ ∧ ¬S₂)
        →[iter 7 universalExistentialDefinition_iff_of_pred_iff
           via constructive de Morgan ¬S₁ ∧ ¬S₂ ↔ ¬(S₁ ∨ S₂)]              Π₂(¬(S₁ ∨ S₂))
        →[iter 5 existentialUniversal_iff_universalExistential_complement]   Σ₂(S₁ ∨ S₂)

    Combined with iter 20's
    `sigma2_intersection_isExistentialUniversalDefinition`, this
    **completes the Σ₂ binary closure grid** (∪ AND ∩). The underlying
    polynomial witness (after unfolding the iter 5 duality, which is
    identity on the polynomial family P) is the same sum-of-squares
    construction as the Π₂ ∩ closure above.

    Re-implementation off current `origin/main` of the stale stack
    PR #17456 (CONFLICTING/DIRTY since 2026-05-08). -/
theorem sigma2_union_isExistentialUniversalDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsExistentialUniversalDefinition S₁)
    (h₂ : IsExistentialUniversalDefinition S₂) :
    IsExistentialUniversalDefinition (fun q => S₁ q ∨ S₂ q) := by
  -- Step 1: dualize each Σ₂ to Π₂ on the complement (iter 5 duality).
  have hd₁ : IsUniversalExistentialDefinition (fun q => ¬ S₁ q) :=
    (existentialUniversal_iff_universalExistential_complement S₁).mp h₁
  have hd₂ : IsUniversalExistentialDefinition (fun q => ¬ S₂ q) :=
    (existentialUniversal_iff_universalExistential_complement S₂).mp h₂
  -- Step 2: Π₂ closed under binary intersection (iter 24a, this section).
  have hcap : IsUniversalExistentialDefinition (fun q => ¬ S₁ q ∧ ¬ S₂ q) :=
    pi2_intersection_isUniversalExistentialDefinition hd₁ hd₂
  -- Step 3: bridge via constructive de Morgan
  --     `¬ S₁ q ∧ ¬ S₂ q ↔ ¬ (S₁ q ∨ S₂ q)`.
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ¬ S₁ q ∧ ¬ S₂ q) q ↔
        (fun q : Rat => ¬ (S₁ q ∨ S₂ q)) q := by
    intro q
    refine ⟨fun ⟨hn₁, hn₂⟩ hor => hor.elim hn₁ hn₂,
            fun hnor => ⟨fun h₁q => hnor (Or.inl h₁q),
                          fun h₂q => hnor (Or.inr h₂q)⟩⟩
  have hd : IsUniversalExistentialDefinition (fun q : Rat => ¬ (S₁ q ∨ S₂ q)) :=
    (universalExistentialDefinition_iff_of_pred_iff hbridge).mp hcap
  -- Step 4: Π₂(¬T) ↔ Σ₂(T) via iter 5 duality, with T = S₁ ∪ S₂.
  exact (existentialUniversal_iff_universalExistential_complement
    (fun q => S₁ q ∨ S₂ q)).mpr hd

-- ============================================================
-- Part VIII.29 (iter 25, Path B): list version of Σ₂ ∪ closure
-- ============================================================

/-- Iter 25, Path B: **the Σ₂ class is closed under finite list union**.

    Direct list lift of iter 24a's
    `sigma2_union_isExistentialUniversalDefinition` by induction on the
    list, with the empty list giving the empty set (vacuous existential
    `∃ S ∈ [], S q ↔ False`).

    **Strategy** (direct mirror of iter 21's
    `sigma2_intersectionList_isExistentialUniversalDefinition`, swapping
    `∀`↔`∃`, `∧`↔`∨`, `universe`↔`empty`, and `iter 20 ∩`↔`iter 24a ∪`):
    induction on `l : List RatSubset`, base case via
    `empty_isExistentialUniversalDefinition` + iter-4 Σ₂ class congruence
    bridge, step case via iter-24a
    `sigma2_union_isExistentialUniversalDefinition` applied to the head
    and the inductive hypothesis on the tail.

    **Significance**: lifts iter 24a's binary Σ₂ ∪ closure to arbitrary
    finite list arity. Combined with iter 21's
    `sigma2_intersectionList_isExistentialUniversalDefinition` (already
    on main), this **completes the list-arity row of the Σ₂ binary
    Boolean closure grid**:

        | Class | binary ∪    | binary ∩    | list ∪      | list ∩      |
        |-------|-------------|-------------|-------------|-------------|
        | Σ₂    | iter 24a    | iter 20     | **iter 25** | iter 21     |
        | Π₂    | iter 20     | iter 24a    | iter 21     | **iter 25** |

    See `pi2_intersectionList_isUniversalExistentialDefinition` (just
    below) for the Π₂ side.

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 24a's binary `sigma2_union_isExistentialUniversalDefinition`
    (just above, also on origin/main via #18659), iter 5's
    `empty_isExistentialUniversalDefinition`, iter 4's Σ₂ class
    congruence helper `existentialUniversalDefinition_iff_of_pred_iff`,
    and the standard Lean-core list helpers `List.mem_cons_self`,
    `List.mem_cons_of_mem`, `List.mem_cons`.

    **OPEN content unchanged**: the central Σ₁ question for ℤ ⊂ ℚ is
    unaffected. Iter 25 only sharpens the level-2 list-arity closure
    properties at the previously-missing iter-24a cells. -/
theorem sigma2_unionList_isExistentialUniversalDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsExistentialUniversalDefinition S) :
    IsExistentialUniversalDefinition (fun q : Rat => ∃ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => False) q := by
      intro q; simp
    exact (existentialUniversalDefinition_iff_of_pred_iff hbridge).mpr
      empty_isExistentialUniversalDefinition
  | cons a t ih =>
    have h_head : IsExistentialUniversalDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsExistentialUniversalDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsExistentialUniversalDefinition
        (fun q : Rat => ∃ S ∈ t, S q) :=
      ih h_tail
    have h_union : IsExistentialUniversalDefinition
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) :=
      sigma2_union_isExistentialUniversalDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∃ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∨ (∃ S ∈ t, S q)) q := by
      intro q
      constructor
      · rintro ⟨S, hSmem, hSq⟩
        rcases List.mem_cons.mp hSmem with rfl | hSt
        · exact Or.inl hSq
        · exact Or.inr ⟨S, hSt, hSq⟩
      · rintro (ha | ⟨S, hSt, hSq⟩)
        · exact ⟨a, List.mem_cons_self, ha⟩
        · exact ⟨S, List.mem_cons_of_mem a hSt, hSq⟩
    exact (existentialUniversalDefinition_iff_of_pred_iff hbridge).mpr h_union

-- ============================================================
-- Part VIII.30 (iter 25, Path B): list version of Π₂ ∩ closure
-- ============================================================

/-- Iter 25, Path B: **the Π₂ class is closed under finite list intersection**.

    Direct list lift of iter 24a's
    `pi2_intersection_isUniversalExistentialDefinition` by induction on
    the list, with the empty list giving the universe set (vacuous
    universal `∀ S ∈ [], S q ↔ True`).

    **Strategy** (direct mirror of iter 21's
    `pi2_unionList_isUniversalExistentialDefinition`, swapping `∃`↔`∀`,
    `∨`↔`∧`, `empty`↔`universe`, and `iter 20 ∪`↔`iter 24a ∩`):
    induction on `l : List RatSubset`, base case via
    `universe_isUniversalExistentialDefinition` + iter-4 Π₂ class
    congruence bridge, step case via iter-24a
    `pi2_intersection_isUniversalExistentialDefinition` applied to the
    head and the inductive hypothesis on the tail.

    **Significance**: completes the list-arity row of the level-2 Π₂
    binary Boolean closure grid (alongside
    `sigma2_unionList_isExistentialUniversalDefinition` above and iter
    21's list closures on main). Every finite list intersection of
    Π₂-definable subsets is itself Π₂-definable.

    **Strictly bigger than iter 14's diagonal transports**: iter 14
    only handles diagonal-input cases (Σ₁ list ∩ → Π₂ via Σ₁ ⊆ Π₂);
    iter 25 handles arbitrary Π₂ inputs (e.g., a list containing the
    Π₂ predicate `IntSubset` from `koenigsmann_2016_universal`, or any
    properly-Π₂ subset arising from iter 24a's binary Π₂ ∩ + this list
    lift).

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 24a's binary `pi2_intersection_isUniversalExistentialDefinition`
    (already on origin/main via #18659), iter 5's
    `universe_isUniversalExistentialDefinition`, iter 4's Π₂ class
    congruence helper `universalExistentialDefinition_iff_of_pred_iff`,
    and the standard Lean-core list helpers `List.mem_cons_self`,
    `List.mem_cons_of_mem`, `List.mem_cons`.

    **OPEN content unchanged**: the central Σ₁ question for ℤ ⊂ ℚ is
    unaffected. Iter 25 only sharpens the level-2 list-arity closure
    properties at the previously-missing iter-24a cells. -/
theorem pi2_intersectionList_isUniversalExistentialDefinition
    (l : List RatSubset) (h : ∀ S ∈ l, IsUniversalExistentialDefinition S) :
    IsUniversalExistentialDefinition (fun q : Rat => ∀ S ∈ l, S q) := by
  induction l with
  | nil =>
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ ([] : List RatSubset), S q) q ↔
        (fun _ : Rat => True) q := by
      intro q; simp
    exact (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr
      universe_isUniversalExistentialDefinition
  | cons a t ih =>
    have h_head : IsUniversalExistentialDefinition a :=
      h a (List.mem_cons_self)
    have h_tail : ∀ S ∈ t, IsUniversalExistentialDefinition S :=
      fun S hS => h S (List.mem_cons_of_mem a hS)
    have ih_def : IsUniversalExistentialDefinition
        (fun q : Rat => ∀ S ∈ t, S q) :=
      ih h_tail
    have h_inter : IsUniversalExistentialDefinition
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) :=
      pi2_intersection_isUniversalExistentialDefinition h_head ih_def
    have hbridge : ∀ q : Rat,
        (fun q : Rat => ∀ S ∈ (a :: t), S q) q ↔
        (fun q : Rat => a q ∧ (∀ S ∈ t, S q)) q := by
      intro q
      constructor
      · intro hall
        refine ⟨hall a (List.mem_cons_self),
          fun S hS => hall S (List.mem_cons_of_mem a hS)⟩
      · rintro ⟨ha, htail⟩ S hS
        rcases List.mem_cons.mp hS with rfl | hSt
        · exact ha
        · exact htail S hSt
    exact (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr h_inter

-- ============================================================
-- Part VIII.31 (iter 26a, Path B): Finset transport of iter 25's
--                                  list-arity Σ₂ ∪ closure
-- ============================================================

/-- Iter 26a, Path B: **the Σ₂ class is closed under `Finset RatSubset`-
    indexed union of arbitrary Σ₂-definable subsets**.

    Finset analog of iter 25's
    `sigma2_unionList_isExistentialUniversalDefinition`
    (`Part VIII.29`, just above), transported via `Finset.mem_toList`.
    Direct mirror of iter 22's
    `sigma2_intersectionFinset_isExistentialUniversalDefinition`
    (`Part VIII.25`), swapping `∀ S ∈ ·` ↔ `∃ S ∈ ·` and the list lift
    target from iter 21 to iter 25.

    **Strategy**: identical structure to iter 22's Finset transports.
    Reduce membership in `s : Finset RatSubset` to membership in
    `s.toList : List RatSubset` via `Finset.mem_toList.mp`/`.mpr`,
    apply iter 25's list-arity union closure, and bridge the predicate
    forms via iter 4's Σ₂ class congruence.

    **Significance**: completes the Finset-arity row of the iter 24a-
    based level-2 Σ₂ ∪ closure grid. Combined with iter 22's
    `sigma2_intersectionFinset_isExistentialUniversalDefinition`
    (already on main), this gives Σ₂ closure under arbitrary
    Finset-indexed unions AND intersections of properly-Σ₂ inputs:

        | Class | binary ∪      | binary ∩      | list ∪      | list ∩      | finset ∪      | finset ∩      |
        |-------|---------------|---------------|-------------|-------------|---------------|---------------|
        | Σ₂    | iter 24a      | iter 20       | iter 25     | iter 21     | **iter 26a**  | iter 22       |
        | Π₂    | iter 20       | iter 24a      | iter 21     | iter 25     | iter 22       | **iter 26a**  |

    See `pi2_intersectionFinset_isUniversalExistentialDefinition` (just
    below) for the Π₂ side.

    **Strictly bigger than iter 17's Σ₁ ⊆ Π₂ Finset transports**: iter
    17 handles only Σ₁-input Finset unions lifted to Σ₂ via the
    inclusion; iter 26a handles arbitrary Σ₂-definable inputs
    (e.g., a Finset containing `koenigsmann_2016_universal_complement`-
    style predicates, or any subset constructed via iter 24a's binary
    Σ₂ ∪ + iter 25's list lift).

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 25's list-arity
    `sigma2_unionList_isExistentialUniversalDefinition`
    (Part VIII.29 above, on this PR's branch and proposed by iter 25 PR
    #18785), iter 4's Σ₂ class congruence helper
    `existentialUniversalDefinition_iff_of_pred_iff` (on main since
    iter 4 PR #17026), and the standard `Finset.mem_toList` bridge
    (`Mathlib.Data.Finset.Basic`, on main since iter 17 PR #17478).

    **OPEN content unchanged**: the central Σ₁ question for ℤ ⊂ ℚ is
    unaffected. Iter 26a only sharpens the level-2 Finset-arity
    closure properties at the previously-missing iter-25 cells. -/
theorem sigma2_unionFinset_isExistentialUniversalDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsExistentialUniversalDefinition S) :
    IsExistentialUniversalDefinition (fun q : Rat => ∃ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsExistentialUniversalDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∃ S ∈ s, S q) q ↔
      (fun q : Rat => ∃ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mpr hS, hSq⟩
    · rintro ⟨S, hS, hSq⟩; exact ⟨S, Finset.mem_toList.mp hS, hSq⟩
  exact (existentialUniversalDefinition_iff_of_pred_iff hbridge).mpr
    (sigma2_unionList_isExistentialUniversalDefinition s.toList h_list)

-- ============================================================
-- Part VIII.32 (iter 26a, Path B): Finset transport of iter 25's
--                                  list-arity Π₂ ∩ closure
-- ============================================================

/-- Iter 26a, Path B: **the Π₂ class is closed under `Finset RatSubset`-
    indexed intersection of arbitrary Π₂-definable subsets**.

    Finset analog of iter 25's
    `pi2_intersectionList_isUniversalExistentialDefinition`
    (`Part VIII.30`, just above), transported via `Finset.mem_toList`.
    Symmetric to the Σ₂ Finset ∪ closure
    `sigma2_unionFinset_isExistentialUniversalDefinition` immediately
    above; direct mirror of iter 22's
    `pi2_unionFinset_isUniversalExistentialDefinition`
    (`Part VIII.26`), swapping `∃ S ∈ ·` ↔ `∀ S ∈ ·` and the list lift
    target from iter 21 to iter 25.

    **Strategy**: identical structure to iter 22's Finset transports
    and the Σ₂ side above, with `∃ S ∈ ·` replaced by `∀ S ∈ ·` and
    Σ₂ class congruence replaced by Π₂ class congruence
    (`universalExistentialDefinition_iff_of_pred_iff`).

    **Significance**: completes the Finset-arity row of the iter 24a-
    based level-2 Π₂ ∩ closure grid (see the grid table in the Σ₂ side
    above). After this PR, every binary / list / Finset combination of
    union/intersection over Σ₂-or-Π₂ inputs stays in the same class.
    Strictly bigger than iter 17's Π₁ ⊆ Σ₂ Finset transports: iter 26a
    handles arbitrary Π₂ inputs (e.g., `IntSubset` from
    `koenigsmann_2016_universal`, or any properly-Π₂ subset arising
    from iter 24a's binary Π₂ ∩ + iter 25's list lift).

    **Mathlib API surface**: ZERO new imports, ZERO new lemmas. Uses
    only iter 25's list-arity
    `pi2_intersectionList_isUniversalExistentialDefinition`
    (Part VIII.30 above), iter 4's Π₂ class congruence helper
    `universalExistentialDefinition_iff_of_pred_iff` (on main since
    iter 4 PR #17026), and the standard `Finset.mem_toList` bridge
    (`Mathlib.Data.Finset.Basic`, on main since iter 17 PR #17478).

    **OPEN content unchanged**: the central Σ₁ question for ℤ ⊂ ℚ is
    unaffected. Iter 26a only sharpens the level-2 Finset-arity
    closure properties at the previously-missing iter-25 cells. -/
theorem pi2_intersectionFinset_isUniversalExistentialDefinition
    (s : Finset RatSubset) (h : ∀ S ∈ s, IsUniversalExistentialDefinition S) :
    IsUniversalExistentialDefinition (fun q : Rat => ∀ S ∈ s, S q) := by
  have h_list : ∀ S ∈ s.toList, IsUniversalExistentialDefinition S :=
    fun S hS => h S (Finset.mem_toList.mp hS)
  have hbridge : ∀ q : Rat,
      (fun q : Rat => ∀ S ∈ s, S q) q ↔
      (fun q : Rat => ∀ S ∈ s.toList, S q) q := by
    intro q
    refine ⟨?_, ?_⟩
    · intro hall S hS; exact hall S (Finset.mem_toList.mp hS)
    · intro hall S hS; exact hall S (Finset.mem_toList.mpr hS)
  exact (universalExistentialDefinition_iff_of_pred_iff hbridge).mpr
    (pi2_intersectionList_isUniversalExistentialDefinition s.toList h_list)

-- ============================================================
-- Part VIII.33 (iter 27a-δ): Combined / contrapositive forms of the
--                            H10/ℚ implication chain
-- ============================================================

/-- **Contrapositive of `integers_diophantine_sigma1_implies_h10_q_undecidable`**:

    If H10/ℚ is decidable, then ℤ is NOT Σ₁-definable in ℚ.

    Pure logical re-export of the existing Σ₁ → ¬H10/ℚ-decidable
    direction. No new axioms. Useful when an argument takes H10/ℚ
    decidability as a working hypothesis and wants to derive the
    negation of the OPEN Σ₁ question. -/
theorem h10_decidable_implies_not_sigma1_integers :
    H10_Rational_Decidable → ¬IntegersAreDiophantineOverQ := by
  intro hDec hSigma1
  exact integers_diophantine_sigma1_implies_h10_q_undecidable hSigma1 hDec

/-- **Contrapositive of `codiophantine_complement_implies_h10_q_undecidable`**:

    If H10/ℚ is decidable, then ℚ \ ℤ is NOT Π₁-definable in ℚ.

    Symmetric companion of `h10_decidable_implies_not_sigma1_integers`
    on the Π₁(complement) side, equivalent via the iter-5 specialization
    `integers_diophantine_iff_complement_codiophantine`. No new axioms. -/
theorem h10_decidable_implies_not_codiophantine_complement :
    H10_Rational_Decidable → ¬IsCoDiophantineDefinition NotIntSubset := by
  intro hDec hCodiop
  exact codiophantine_complement_implies_h10_q_undecidable hCodiop hDec

/-- **Mazur + Koenigsmann: Π₂(ℤ) is strict above Σ₁(ℤ)**:

    Under `MazurConjecture`, ℤ is Π₂-definable in ℚ (by Koenigsmann)
    but NOT Σ₁-definable in ℚ (by Mazur). Packages the two existing
    conditional facts into a single conjunctive strict-containment
    witness at the integer subset — making explicit that Mazur posits
    the Σ₁ ⊊ Π₂ gap to be non-trivial at `IntSubset`.

    Pure logical re-export — uses only the existing axiom
    `koenigsmann_2016_universal` and (transitively, via
    `mazur_implies_not_sigma1_definable`) the OQ-01 axiom
    `mazur_implies_not_diophantine`. No new axioms. -/
theorem mazur_implies_pi2_strict_above_sigma1_at_integers :
    MazurConjecture →
      IsUniversalExistentialDefinition IntSubset ∧ ¬IntegersAreDiophantineOverQ :=
  fun hM => ⟨koenigsmann_2016_universal, mazur_implies_not_sigma1_definable hM⟩

/-- **H10/ℚ decidable + Koenigsmann: Π₂(ℤ) is strict above Σ₁(ℤ)**:

    Under `H10_Rational_Decidable`, ℤ is Π₂-definable in ℚ (by
    Koenigsmann) but NOT Σ₁-definable in ℚ (by the contrapositive
    `h10_decidable_implies_not_sigma1_integers`). Same conclusion as
    `mazur_implies_pi2_strict_above_sigma1_at_integers`, from a
    different conditional antecedent: H10/ℚ-decidability also forces
    the Σ₁ ⊊ Π₂ gap to be non-trivial at `IntSubset`.

    Pure logical re-export — no new axioms. -/
theorem h10_decidable_implies_pi2_strict_above_sigma1_at_integers :
    H10_Rational_Decidable →
      IsUniversalExistentialDefinition IntSubset ∧ ¬IntegersAreDiophantineOverQ :=
  fun hDec => ⟨koenigsmann_2016_universal,
                h10_decidable_implies_not_sigma1_integers hDec⟩

/-- **Symmetric Π₁/Σ₂ analog at the complement**:

    Under `MazurConjecture`, ℚ \ ℤ is Σ₂-definable in ℚ (corollary of
    Koenigsmann via Σ₂/Π₂ duality, already on file as
    `koenigsmann_implies_complement_existentialUniversal`) but NOT
    Π₁-definable in ℚ (by Mazur via the iter-5 Σ₁/Π₁ duality, already
    on file as `mazur_implies_not_codiophantine_complement`). Same
    strict-containment structure as
    `mazur_implies_pi2_strict_above_sigma1_at_integers`, transported
    to the complement side via the two dualities.

    Pure logical re-export — no new axioms. -/
theorem mazur_implies_sigma2_strict_above_codiophantine_at_complement_integers :
    MazurConjecture →
      IsExistentialUniversalDefinition NotIntSubset ∧
        ¬IsCoDiophantineDefinition NotIntSubset :=
  fun hM => ⟨koenigsmann_implies_complement_existentialUniversal,
             mazur_implies_not_codiophantine_complement hM⟩

-- ============================================================
-- Part IX: The landscape, sharpened
-- ============================================================

/-
## Σ₁ vs Π₁ vs Σ₂ vs Π₂: the precise gap

| Class | Statement on ℤ ⊂ ℚ                       | Status (2026) |
|-------|------------------------------------------|----------------|
| Σ₁ (∃)            | ℤ Diophantine over ℚ                | **OPEN** (THIS PROBLEM) |
| Π₁ (∀, complement) | ℚ \ ℤ Π₁-definable over ℚ            | **OPEN** (equivalent to Σ₁ via duality) |
| Σ₂ (∃∀, complement) | ℚ \ ℤ Σ₂-definable over ℚ          | **PROVED** (corollary of Koenigsmann) |
| Π₂ (∀∃)           | ℤ universally-existentially def. in ℚ | **PROVED** (Koenigsmann 2016) |

The Σ₁ ⟺ Π₁(complement) and Σ₂ ⟺ Π₂(complement) dualities are now
proved as `diophantine_iff_codiophantine_complement` and
`existentialUniversal_iff_universalExistential_complement`, with the
Σ₂(ℚ\ℤ) entry derived from Koenigsmann via duality as
`koenigsmann_implies_complement_existentialUniversal`. The non-trivial
open gap is Σ₁ vs Π₂ (equivalently, Π₁(complement) vs Σ₂(complement)).

## Why this distinction matters

- The implication chain `Σ₁ → ¬H10/ℚ-decidable` (from MRDP) is PRECISELY
  Σ₁; Π₂ does NOT yield this implication directly (it gives only a weaker
  encoding that does not transfer the undecidability of H10/ℤ to H10/ℚ).
- Mazur's conjecture refutes Σ₁ but is consistent with Π₂.
- A positive Σ₁ answer would be a constructive polynomial witness; a
  negative answer would likely come from a structural theorem on the
  topological / Brauer–Manin geometry of ℚ-points.
- The Π₁(complement) reformulation is sometimes more tractable for a
  putative refutation: a Π₁ definition of ℚ \ ℤ would mean a polynomial
  P(q, x) such that q ∉ ℤ ⟺ ∃ x rational with P(q,x) = 0.
- The Σ₂(complement) corollary places `ℚ \ ℤ` on the second level of the
  arithmetic hierarchy unconditionally, sharpening the "what is known"
  side of the picture.
- The smallest *non-trivial* parameter-dependent witness is the projection
  polynomial `P(q, x) = q`, which places `{0} ⊂ ℚ` (resp. `ℚ \ {0}`) into
  Σ₁ (resp. Π₁); these in turn place them into Π₂ and Σ₂ via the trivial
  inclusions `Σ₁ ⊆ Π₂` and `Π₁ ⊆ Σ₂`. This sharpens the iteration-5
  trivial-set library (∅, ℚ) to the smallest non-degenerate subset.
- All four classes are stable under classical *double-negation* of the
  predicate (iter 7): `Class(¬¬ S) ⟺ Class(S)` for `Class ∈ {Σ₁, Π₁, Σ₂, Π₂}`.
  In particular, the OPEN Σ₁ question for ℤ ⊂ ℚ is equivalent to its
  ¬¬-shadow `Σ₁(¬¬ IntSubset)`, which is occasionally a more tractable
  reformulation when a refutation argument naturally produces a `¬¬`
  layer (e.g., a classical decomposition of a Π₁ counter-witness).
- **Every singleton `{a} ⊂ ℚ` is Σ₁-definable** for `a : ℚ` (iter 8): the
  shift polynomial `P(q, x) = q - a` places `{a}` (resp. `ℚ \ {a}`) into
  Σ₁ (resp. Π₁), and hence into Π₂ (resp. Σ₂) via the trivial inclusions.
  This properly generalizes S6's special case `a = 0` to arbitrary
  `a : ℚ`, recovering S6 as `singletonOf_zero_isDiophantineDefinition`.
  ℤ as a *family* of singletons `{n} : n : ℤ` does NOT immediately yield
  Σ₁-definability of ℤ ⊂ ℚ: Σ₁-definability is closed under finite union
  (and finite intersection) but NOT known to be closed under countable
  union (the OPEN Σ₁ question for ℤ is precisely the question of whether
  this particular countable union admits a uniform Σ₁ witness).
- **Σ₁ is closed under binary union; Π₁ is closed under binary intersection**
  (iter 9): the same product polynomial witness `P(q, x) = P₁(q, x)·P₂(q, x)`
  serves both — `mul_eq_zero` over ℚ provides the bridge in both
  directions. Two concrete corollaries: every PAIR `{a, b} ⊂ ℚ` is
  Σ₁-definable, every "complement-of-a-pair" `ℚ \ {a, b}` is
  Π₁-definable, for any `a, b : ℚ`. By an obvious induction on a finite
  list, finite *unions* of singletons (i.e., any FINITE subset of ℚ) are
  Σ₁-definable. The OPEN Σ₁ question for ℤ ⊂ ℚ thus reduces precisely
  to whether the countable union `⋃_{n : ℤ} {n}` admits a *uniform*
  polynomial witness — finite truncations `⋃_{n : ℤ ∩ [-N, N]} {n}` are
  Σ₁-definable for every finite `N`, but the limit `N → ∞` requires a
  single polynomial whose existence is the OPEN content.
- **Σ₁ is closed under binary intersection** (iter 12): a sum-of-squares
  witness with variable-packing — `P(q, x) = (P₁(q, evenProj x))² +
  (P₂(q, oddProj x))²` — serves the role. Over the LinearOrderedField
  ℚ, both squares are nonneg, so a zero sum forces each square (hence
  each polynomial value) to vanish individually. The variable-packing
  via `interleave : (Nat → Rat) → (Nat → Rat) → (Nat → Rat)` puts P₁'s
  witness on even indices and P₂'s on odd indices, so the two
  polynomial constraints can be simultaneously witnessed by a single
  `x : Nat → Rat`. **Combined with iter 9**: Σ₁ over ℚ is closed under
  finite ∪ AND finite ∩ — hence under arbitrary finite Boolean
  combinations using ∪ and ∩. Σ₁ is NOT (known to be) closed under
  complement; that would collapse Σ₁ = Π₁, which is the OPEN question
  in disguise.
- **Π₁ is closed under binary union** (iter 13): the missing dual of
  iter 9's Σ₁-union closure. Constructed via the iter 5 Σ₁/Π₁ duality,
  iter 12's Σ₁ ∩ closure, and the iter 4 Σ₁ class congruence helper —
  with the underlying polynomial witness identical to iter 12's
  sum-of-squares construction (the duality is identity on the
  polynomial family P). **Combined with iter 9 (Σ₁ ∪, Π₁ ∩) and
  iter 12 (Σ₁ ∩)**, this completes the 2×2 closure grid for finite
  Boolean combinations: every finite ∪/∩-combination of Σ₁-definable
  (resp. Π₁-definable) subsets of ℚ remains in the same class. Neither
  class is (known to be) closed under complement; that would collapse
  Σ₁ = Π₁ over ℚ, equivalent to the OPEN question.
- **Σ₂ is closed under binary intersection; Π₂ is closed under binary
  union** (iter 20, this file): closes the two cells flagged "open at
  this level" by iter 16's `pi2_intersection_isUniversalExistentialDefinition`
  PR description. The Σ₂ ∩ closure has a direct product polynomial
  `Q(q, y, x) = P₁(q, evenProj y, x) · P₂(q, oddProj y, x)`, dual to
  iter 16's sum-of-squares for Π₂ ∩: here the existential `y`-block
  is **packed via interleave** (the two `y`-witnesses can differ),
  while the universal `x`-block is **shared** (both factors must
  reject the same `x`); `mul_eq_zero` over ℚ provides the bridge in
  both directions. The Π₂ ∪ closure is the symmetric corollary via
  the Σ₂/Π₂ duality + iter 4 Π₂ class congruence helper, structurally
  identical to iter 13's Π₁ ∪ from Σ₁ ∩ one level up. **Combined with
  iter 16 (Σ₂ ∪, Π₂ ∩) and iter 12/13 (Σ₁/Π₁ ⊆ Π₂/Σ₂ transports)**,
  this completes the binary 2×2 Boolean closure grid for the SECOND
  level (Σ₂/Π₂) over ℚ — strictly stronger than the iter 12/13
  transports, which only handled Σ₁/Π₁ inputs. Σ₂ is NOT (known to
  be) closed under complement; that would collapse Σ₂ = Π₂ at level
  2 — a level-2 analog of the OPEN Σ₁ vs Π₁ question, currently OPEN
  at level 2 as well (Koenigsmann places ℤ in Π₂ but Σ₂(ℤ) is not
  known).
- **The level-2 Σ₂(ℤ) question is named and dualized** (iter 23,
  Part VIII.27): `IntegersAreExistentialUniversalOverQ` exposes the
  Σ₂-definability of ℤ ⊂ ℚ as a top-level `Prop` (mirroring the
  level-1 `IntegersAreDiophantineOverQ`), and
  `integers_existentialUniversal_iff_complement_universalExistential`
  is the one-line specialization of iter 5's
  `existentialUniversal_iff_universalExistential_complement` at
  `S := IntSubset`. Both sides are OPEN, completing the symmetric
  pair of complement-dualities for the OPEN content of this file:

  | Level | Theorem on `IntSubset`                                                  | OPEN dual on `NotIntSubset`           |
  |-------|-------------------------------------------------------------------------|---------------------------------------|
  | 1     | `integers_diophantine_iff_complement_codiophantine`                     | `IsCoDiophantineDefinition NotIntSubset` |
  | 2     | `integers_existentialUniversal_iff_complement_universalExistential`     | `IsUniversalExistentialDefinition NotIntSubset` |

  Asymmetry across rows: at level 2, the *other* side
  (`koenigsmann_implies_complement_existentialUniversal`) is
  PROVED via Koenigsmann + iter 5 duality, so the level-2 OPEN
  content collapses to the single Σ₂(ℤ) question; at level 1,
  neither side is currently known. Iter 23 also exposes the
  doubleNeg form of Koenigsmann (`koenigsmann_2016_universal_doubleNeg`)
  via iter 7's Π₂ doubleNeg invariance — useful when a downstream
  argument naturally produces `¬¬ IntSubset` (e.g. via
  `Classical.byContradiction` on a Π₁ counter-witness).

## Axioms in THIS file (1 net new)

  1. `koenigsmann_2016_universal` — Π₂-definability of ℤ in ℚ
     (proved in Koenigsmann 2016; axiomatized pending Lean formalization
     of the explicit Hilbert-symbol polynomial witness).

All other declared `theorem`s are NOT new axioms — they are logical
consequences of the OQ-01 axioms together with the Σ₁ ↔ existing-formulation,
Σ₁ ↔ Π₁(complement), and Σ₂ ↔ Π₂(complement) equivalences proved here.

## Theorems in THIS file (selected — see source for the full list)

  - `integers_diophantine_iff` (Σ₁ predicate ↔ existing formulation)
  - `diophantine_implies_universal_existential` (Σ₁ ⊆ Π₂)
  - `integers_diophantine_strengthens_koenigsmann` (positive answer ⟹ Π₂)
  - `integers_diophantine_sigma1_implies_h10_q_undecidable` (re-export)
  - `mazur_implies_not_sigma1_definable` (re-export)
  - `diophantine_iff_codiophantine_complement` (Σ₁/Π₁ duality, general)
  - `integers_diophantine_iff_complement_codiophantine` (specialization to ℤ)
  - `codiophantine_complement_implies_h10_q_undecidable` (Π₁(ℚ\ℤ) re-export)
  - `mazur_implies_not_codiophantine_complement` (Π₁(ℚ\ℤ) re-export)
  - `codiophantine_implies_existentialUniversal` (Π₁ ⊆ Σ₂, dual of Σ₁ ⊆ Π₂)
  - `existentialUniversal_iff_universalExistential_complement` (Σ₂/Π₂ duality)
  - `universalExistentialDefinition_iff_of_pred_iff` (Π₂ class congruence)
  - `diophantineDefinition_iff_of_pred_iff` (Σ₁ class congruence, iter 4)
  - `coDiophantineDefinition_iff_of_pred_iff` (Π₁ class congruence, iter 4)
  - `existentialUniversalDefinition_iff_of_pred_iff` (Σ₂ class congruence, iter 4)
  - `koenigsmann_implies_complement_existentialUniversal` (Σ₂(ℚ\ℤ) corollary)
  - `codiophantine_iff_diophantine_complement` (Π₁/Σ₁ symmetric duality, iter 5)
  - `universalExistential_iff_existentialUniversal_complement` (Π₂/Σ₂ symmetric duality, iter 5)
  - `empty_isDiophantineDefinition` (∅ is Σ₁, iter 5)
  - `empty_isCoDiophantineDefinition` (∅ is Π₁, iter 5)
  - `universe_isDiophantineDefinition` (ℚ is Σ₁, iter 5)
  - `universe_isCoDiophantineDefinition` (ℚ is Π₁, iter 5)
  - `empty_isUniversalExistentialDefinition` (∅ is Π₂, iter 5)
  - `universe_isUniversalExistentialDefinition` (ℚ is Π₂, iter 5)
  - `empty_isExistentialUniversalDefinition` (∅ is Σ₂, iter 5)
  - `universe_isExistentialUniversalDefinition` (ℚ is Σ₂, iter 5)
  - `singletonZero_isDiophantineDefinition` ({0} is Σ₁, iter 6)
  - `notZero_isCoDiophantineDefinition` (ℚ\{0} is Π₁, iter 6)
  - `singletonZero_isUniversalExistentialDefinition` ({0} is Π₂, iter 6)
  - `notZero_isExistentialUniversalDefinition` (ℚ\{0} is Σ₂, iter 6)
  - `diophantineDefinition_doubleNeg_iff` (Σ₁ ¬¬-shadow, iter 7)
  - `coDiophantineDefinition_doubleNeg_iff` (Π₁ ¬¬-shadow, iter 7)
  - `universalExistentialDefinition_doubleNeg_iff` (Π₂ ¬¬-shadow, iter 7)
  - `existentialUniversalDefinition_doubleNeg_iff` (Σ₂ ¬¬-shadow, iter 7)
  - `integers_diophantine_iff_doubleNeg` (OPEN Σ₁ question ⟺ its ¬¬-shadow, iter 7)
  - `singletonOf_isDiophantineDefinition a` ({a} ⊂ ℚ is Σ₁ for any a : ℚ, iter 8 Path B)
  - `notSingletonOf_isCoDiophantineDefinition a` (ℚ\{a} is Π₁ for any a : ℚ, iter 8 Path B)
  - `singletonOf_isUniversalExistentialDefinition a` ({a} is Π₂ for any a : ℚ, iter 8 Path B)
  - `notSingletonOf_isExistentialUniversalDefinition a` (ℚ\{a} is Σ₂ for any a : ℚ, iter 8 Path B)
  - `singletonOf_zero_isDiophantineDefinition` (S6 recovered as a = 0 instance, iter 8)
  - `union_isDiophantineDefinition` (Σ₁ closed under binary union, iter 9 Path B)
  - `intersection_isCoDiophantineDefinition` (Π₁ closed under binary intersection, iter 9 Path B)
  - `singletonPair_isDiophantineDefinition a b` ({a, b} ⊂ ℚ is Σ₁ for any a, b : ℚ, iter 9)
  - `notSingletonPair_isCoDiophantineDefinition a b` (ℚ\{a, b} is Π₁ for any a, b : ℚ, iter 9)
  - `singletonPair_isUniversalExistentialDefinition a b` ({a, b} is Π₂, iter 9)
  - `notSingletonPair_isExistentialUniversalDefinition a b` (ℚ\{a, b} is Σ₂, iter 9)
  - `finUnionList_singletons_isDiophantineDefinition l` (every finite subset of ℚ is Σ₁, iter 10)
  - `finIntersectionList_complement_singletons_isCoDiophantineDefinition l` (complement of every finite subset is Π₁, iter 10)
  - `finUnionList_singletons_isUniversalExistentialDefinition l` (every finite subset is Π₂, iter 10)
  - `finIntersectionList_complement_singletons_isExistentialUniversalDefinition l` (complement of every finite subset is Σ₂, iter 10)
  - `coDiophantine_implies_universal_existential` (Π₁ ⊆ Π₂ via inversion, iter 11)
  - `intersection_isDiophantineDefinition` (Σ₁ closed under binary intersection via sum-of-squares + interleave, iter 12)
  - `intersection_isUniversalExistentialDefinition` (Σ₁ ∩ Σ₁ ⊆ Π₂ corollary, iter 12)
  - `union_isCoDiophantineDefinition` (Π₁ closed under binary union via iter 5 duality + iter 12 Σ₁ ∩ closure, iter 13)
  - `union_isExistentialUniversalDefinition` (Π₁ ∪ Π₁ ⊆ Σ₂ corollary, iter 13)
  - `sigma2_intersection_isExistentialUniversalDefinition` (Σ₂ closed under binary intersection via product polynomial + interleave on existential block, iter 20)
  - `pi2_union_isUniversalExistentialDefinition` (Π₂ closed under binary union via iter 5 duality + iter 20 Σ₂ ∩ closure, iter 20)
  - `sigma2_intersectionList_isExistentialUniversalDefinition` (Σ₂ closed under finite list intersection via iter 20 + list induction, iter 21)
  - `pi2_unionList_isUniversalExistentialDefinition` (Π₂ closed under finite list union via iter 20 + list induction, iter 21)
  - `sigma2_intersectionFinset_isExistentialUniversalDefinition` (Σ₂ closed under Finset-indexed intersection via iter 21 + `Finset.mem_toList`, iter 22)
  - `pi2_unionFinset_isUniversalExistentialDefinition` (Π₂ closed under Finset-indexed union via iter 21 + `Finset.mem_toList`, iter 22)
  - `IntegersAreExistentialUniversalOverQ` (Σ₂(ℤ) as named Prop — level-2 OPEN analog of `IntegersAreDiophantineOverQ`, iter 23)
  - `integers_existentialUniversal_iff_complement_universalExistential` (Σ₂(ℤ) ⟺ Π₂(ℚ\ℤ), iter 23)
  - `koenigsmann_2016_universal_doubleNeg` (Π₂(¬¬ ℤ) re-export of Koenigsmann via iter 7 doubleNeg invariance, iter 23)
  - `pi2_intersection_isUniversalExistentialDefinition` (Π₂ closed under binary intersection via sum-of-squares + interleave on existential block, iter 24a)
  - `sigma2_union_isExistentialUniversalDefinition` (Σ₂ closed under binary union via iter 5 duality + iter 24a Π₂ ∩ closure, iter 24a)
  - `sigma2_unionList_isExistentialUniversalDefinition` (Σ₂ closed under finite list union via iter 24a + list induction, iter 25)
  - `pi2_intersectionList_isUniversalExistentialDefinition` (Π₂ closed under finite list intersection via iter 24a + list induction, iter 25)
  - `h10_decidable_implies_not_sigma1_integers` (H10/ℚ decidable ⟹ ¬Σ₁(ℤ); contrapositive re-export, iter 27a-δ)
  - `h10_decidable_implies_not_codiophantine_complement` (H10/ℚ decidable ⟹ ¬Π₁(ℚ\ℤ); contrapositive re-export on the complement side, iter 27a-δ)
  - `mazur_implies_pi2_strict_above_sigma1_at_integers` (Mazur + Koenigsmann ⟹ Π₂(ℤ) ∧ ¬Σ₁(ℤ) — Σ₁ ⊊ Π₂ non-trivial at ℤ under Mazur, iter 27a-δ)
  - `h10_decidable_implies_pi2_strict_above_sigma1_at_integers` (H10/ℚ decidable + Koenigsmann ⟹ Π₂(ℤ) ∧ ¬Σ₁(ℤ) — same Σ₁ ⊊ Π₂ non-collapse from a different conditional antecedent, iter 27a-δ)
  - `mazur_implies_sigma2_strict_above_codiophantine_at_complement_integers` (Mazur + Koenigsmann/duality ⟹ Σ₂(ℚ\ℤ) ∧ ¬Π₁(ℚ\ℤ) — Π₁ ⊊ Σ₂ non-trivial at ℚ\ℤ under Mazur, iter 27a-δ)
-/

#check @IsDiophantineDefinition
#check @IsUniversalExistentialDefinition
#check @IsCoDiophantineDefinition
#check @IsExistentialUniversalDefinition
#check @koenigsmann_2016_universal
#check @integers_diophantine_iff
#check @diophantine_implies_universal_existential
#check @diophantine_iff_codiophantine_complement
#check @integers_diophantine_iff_complement_codiophantine
#check @codiophantine_implies_existentialUniversal
#check @existentialUniversal_iff_universalExistential_complement
#check @diophantineDefinition_iff_of_pred_iff
#check @coDiophantineDefinition_iff_of_pred_iff
#check @existentialUniversalDefinition_iff_of_pred_iff
#check @koenigsmann_implies_complement_existentialUniversal
#check @codiophantine_iff_diophantine_complement
#check @universalExistential_iff_existentialUniversal_complement
#check @empty_isDiophantineDefinition
#check @empty_isCoDiophantineDefinition
#check @universe_isDiophantineDefinition
#check @universe_isCoDiophantineDefinition
#check @empty_isUniversalExistentialDefinition
#check @universe_isUniversalExistentialDefinition
#check @empty_isExistentialUniversalDefinition
#check @universe_isExistentialUniversalDefinition
#check @singletonZero_isDiophantineDefinition
#check @notZero_isCoDiophantineDefinition
#check @singletonZero_isUniversalExistentialDefinition
#check @notZero_isExistentialUniversalDefinition
#check @diophantineDefinition_doubleNeg_iff
#check @coDiophantineDefinition_doubleNeg_iff
#check @universalExistentialDefinition_doubleNeg_iff
#check @existentialUniversalDefinition_doubleNeg_iff
#check @integers_diophantine_iff_doubleNeg
#check @singletonOf_isDiophantineDefinition
#check @notSingletonOf_isCoDiophantineDefinition
#check @singletonOf_isUniversalExistentialDefinition
#check @notSingletonOf_isExistentialUniversalDefinition
#check @singletonOf_zero_isDiophantineDefinition
#check @union_isDiophantineDefinition
#check @intersection_isCoDiophantineDefinition
#check @singletonPair_isDiophantineDefinition
#check @notSingletonPair_isCoDiophantineDefinition
#check @singletonPair_isUniversalExistentialDefinition
#check @notSingletonPair_isExistentialUniversalDefinition
#check @finUnionList_singletons_isDiophantineDefinition
#check @finIntersectionList_complement_singletons_isCoDiophantineDefinition
#check @finUnionList_singletons_isUniversalExistentialDefinition
#check @finIntersectionList_complement_singletons_isExistentialUniversalDefinition
#check @coDiophantine_implies_universal_existential
#check @intersection_isDiophantineDefinition
#check @intersection_isUniversalExistentialDefinition
#check @union_isCoDiophantineDefinition
#check @union_isExistentialUniversalDefinition
#check @finIntersectionList_isDiophantineDefinition
#check @finIntersectionList_isUniversalExistentialDefinition
#check @finUnionList_isCoDiophantineDefinition
#check @finUnionList_isExistentialUniversalDefinition
#check @finUnionList_isDiophantineDefinition
#check @finUnionList_isUniversalExistentialDefinition
#check @finIntersectionList_isCoDiophantineDefinition
#check @finIntersectionList_isExistentialUniversalDefinition
#check @sigma2_intersection_isExistentialUniversalDefinition
#check @pi2_union_isUniversalExistentialDefinition
#check @sigma2_intersectionList_isExistentialUniversalDefinition
#check @pi2_unionList_isUniversalExistentialDefinition
#check @sigma2_intersectionFinset_isExistentialUniversalDefinition
#check @pi2_unionFinset_isUniversalExistentialDefinition
#check @IntegersAreExistentialUniversalOverQ
#check @integers_existentialUniversal_iff_complement_universalExistential
#check @koenigsmann_2016_universal_doubleNeg
#check @pi2_intersection_isUniversalExistentialDefinition
#check @sigma2_union_isExistentialUniversalDefinition
#check @sigma2_unionList_isExistentialUniversalDefinition
#check @pi2_intersectionList_isUniversalExistentialDefinition
#check @sigma2_unionFinset_isExistentialUniversalDefinition
#check @pi2_intersectionFinset_isUniversalExistentialDefinition
#check @h10_decidable_implies_not_sigma1_integers
#check @h10_decidable_implies_not_codiophantine_complement
#check @mazur_implies_pi2_strict_above_sigma1_at_integers
#check @h10_decidable_implies_pi2_strict_above_sigma1_at_integers
#check @mazur_implies_sigma2_strict_above_codiophantine_at_complement_integers

end Hilbert10Rationals
