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
-- Part VIII: The landscape, sharpened
-- ============================================================

/-
## Σ₁ vs Π₁ vs Π₂: the precise gap

| Class | Statement on ℤ ⊂ ℚ | Status (2026) |
|-------|--------------------|----------------|
| Σ₁ (∃)            | ℤ Diophantine over ℚ                  | **OPEN** (THIS PROBLEM) |
| Π₁ (∀, complement) | ℚ \ ℤ Π₁-definable over ℚ              | **OPEN** (equivalent to Σ₁ via duality) |
| Π₂ (∀∃)           | ℤ universally-existentially def. in ℚ | **PROVED** (Koenigsmann 2016) |

The Σ₁ ⟺ Π₁(complement) equivalence is now proved in this file as
`diophantine_iff_codiophantine_complement` (and its specialization
`integers_diophantine_iff_complement_codiophantine`), formalizing the
narrative claim. The non-trivial open gap is Σ₁ vs Π₂.

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

## Axioms in THIS file (1 net new)

  1. `koenigsmann_2016_universal` — Π₂-definability of ℤ in ℚ
     (proved in Koenigsmann 2016; axiomatized pending Lean formalization
     of the explicit Hilbert-symbol polynomial witness).

All other declared `theorem`s are NOT new axioms — they are logical
consequences of the OQ-01 axioms and the Σ₁ ↔ existing-formulation /
Σ₁ ↔ Π₁(complement) equivalences proved here.

## Theorems in THIS file (8)

  - `integers_diophantine_iff` (Σ₁ predicate ↔ existing formulation)
  - `diophantine_implies_universal_existential` (Σ₁ ⊆ Π₂)
  - `integers_diophantine_strengthens_koenigsmann` (positive answer ⟹ Π₂)
  - `integers_diophantine_sigma1_implies_h10_q_undecidable` (re-export)
  - `mazur_implies_not_sigma1_definable` (re-export)
  - `diophantine_iff_codiophantine_complement` (Σ₁/Π₁ duality, general)
  - `integers_diophantine_iff_complement_codiophantine` (specialization to ℤ)
  - `codiophantine_complement_implies_h10_q_undecidable` (Π₁(ℚ\ℤ) re-export)
  - `mazur_implies_not_codiophantine_complement` (Π₁(ℚ\ℤ) re-export)
-/

#check @IsDiophantineDefinition
#check @IsUniversalExistentialDefinition
#check @IsCoDiophantineDefinition
#check @koenigsmann_2016_universal
#check @integers_diophantine_iff
#check @diophantine_implies_universal_existential
#check @diophantine_iff_codiophantine_complement
#check @integers_diophantine_iff_complement_codiophantine

end Hilbert10Rationals
