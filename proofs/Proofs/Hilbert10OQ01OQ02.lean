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

## Axioms in THIS file (1 net new)

  1. `koenigsmann_2016_universal` — Π₂-definability of ℤ in ℚ
     (proved in Koenigsmann 2016; axiomatized pending Lean formalization
     of the explicit Hilbert-symbol polynomial witness).

All other declared `theorem`s are NOT new axioms — they are logical
consequences of the OQ-01 axioms together with the Σ₁ ↔ existing-formulation,
Σ₁ ↔ Π₁(complement), and Σ₂ ↔ Π₂(complement) equivalences proved here.

## Theorems in THIS file (35)

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

end Hilbert10Rationals
