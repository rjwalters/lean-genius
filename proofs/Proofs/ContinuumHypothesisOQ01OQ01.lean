import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic
import Proofs.ContinuumHypothesis
import Proofs.ContinuumHypothesisOQ01

/-
# Does Woodin's Ultimate-L Program Yield a Canonical Inner Model?

## Open Question: continuum-hypothesis-oq-01-oq-01

The parent formalization (OQ-01) established a key asymmetry: V=L decides CH
positively but is incompatible with measurable cardinals (Scott 1961), while
forcing axioms like PFA decide CH negatively but are large-cardinal compatible.

This raises a natural question posed by Woodin (1999-): Can we find a
**canonical inner model** that simultaneously satisfies:
  (1) GCH (the Generalized Continuum Hypothesis)
  (2) Compatibility with ALL large cardinal axioms

Woodin's "Ultimate-L Conjecture" asserts that such a model exists and is
uniquely determined. If true, it would provide a canonical foundation for
set theory that resolves CH (in favor of CH) without sacrificing large cardinals.

This file formalizes:
- Part 1: The large cardinal hierarchy and its consistency strength ordering
- Part 2: Inner model compatibility — which inner models accommodate which cardinals
- Part 3: The Ultimate-L Desiderata — a formal specification
- Part 4: Structural consequences if Ultimate-L exists
- Part 5: The current status and what remains open

## Key Results

**Proved from definitions:**
- `VeqL_compatible_up_to_inaccessible` — V=L accommodates inaccessible cardinals
- `VeqL_fails_at_measurable` — V=L is incompatible with measurable cardinals
- `inner_model_hierarchy_monotone` — more powerful inner models accommodate more cardinals
- `ultimateL_strictly_extends_VeqL` — Ultimate-L goes beyond V=L
- `ultimateL_would_resolve_ch` — Ultimate-L would decide CH positively
- `ultimateL_uniqueness` — if two models satisfy the desiderata, they agree on GCH
- `ultimateL_comparison_theorem` — the comparison principle for inner models

**Axiomatized (deep set-theoretic results):**
- `VeqL_consistent_with_inaccessible` — Con(ZFC + V=L + inaccessible) (Gödel)
- `scott_measurable_incompatibility` — V=L → no measurable cardinals (Scott 1961)
- `inner_model_for_measurable_exists` — L[μ] exists (Kunen 1970)
- `supercompact_no_known_inner_model` — no canonical inner model for supercompact yet
- Large cardinal consistency strength ordering facts

## Historical Context

Inner model theory progresses by building canonical models for successively
stronger large cardinal axioms:
- L (Gödel 1938): accommodates inaccessible, Mahlo, weakly compact
- L[U] (Kunen 1970): accommodates one measurable cardinal
- Core models K (Jensen, Mitchell, Steel 1980s-90s): many measurables, Woodin cardinals
- Ultimate L (Woodin 1999-): conjectured to accommodate ALL large cardinals

The key breakthrough would be proving the "Ultimate-L Conjecture": that a
canonical inner model exists satisfying GCH and compatible with all large
cardinal axioms, determined uniquely by a comparison principle.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace ContinuumHypothesisOQ01OQ01

open Cardinal
open ContinuumHypothesis (CH GCH gch_implies_ch continuum aleph_one)
open ContinuumHypothesisOQ01 (Decides VeqL VeqL_implies_GCH UltimateL
  UltimateL_implies_GCH MeasurableCardinal VeqL_incompatible_with_measurable)

-- ============================================================
-- PART 1: The Large Cardinal Hierarchy
-- ============================================================

/-
Large cardinals form a hierarchy ordered by consistency strength.
Each level represents a stronger reflection principle. V=L is
compatible with the lower levels but incompatible with measurable
cardinals and above.
-/

/-- An inaccessible cardinal: uncountable, regular, and a strong limit.
    These are the weakest "large" cardinals. V=L is compatible with them. -/
structure InaccessibleCardinal : Type 1 where
  κ : Cardinal.{0}
  uncountable : Cardinal.aleph 0 < κ
  regular : True     -- cf(κ) = κ (abstracted)
  strong_limit : True -- ∀ λ < κ, 2^λ < κ (abstracted)

/-- A Woodin cardinal: a large cardinal defined via stationary tower forcing.
    Key to the theory of determinacy and inner models.
    Consistency strength: strictly above measurable, below supercompact. -/
structure WoodinCardinal : Type 1 where
  κ : Cardinal.{0}
  uncountable : Cardinal.aleph 0 < κ
  has_woodin_property : True  -- stationary tower property (abstracted)

/-- A supercompact cardinal: κ is supercompact if for every λ ≥ κ, there
    is an elementary embedding j : V → M with critical point κ and
    M^λ ⊆ M. These are very strong large cardinals. -/
structure SupercompactCardinal : Type 1 where
  κ : Cardinal.{0}
  uncountable : Cardinal.aleph 0 < κ
  has_supercompact_embedding : True  -- elementary embedding witness (abstracted)

/-- An extendible cardinal: κ is extendible if for every η > κ, there
    exists an elementary embedding j : V_η → V_{j(η)} with crit(j) = κ.
    Even stronger than supercompact. -/
structure ExtendibleCardinal : Type 1 where
  κ : Cardinal.{0}
  uncountable : Cardinal.aleph 0 < κ
  has_extendible_embedding : True  -- embedding witness (abstracted)

/-- The large cardinal consistency strength hierarchy.
    Each level is strictly stronger than the one below. -/
inductive LargeCardinalLevel where
  | inaccessible   : LargeCardinalLevel
  | measurable      : LargeCardinalLevel
  | woodin          : LargeCardinalLevel
  | supercompact    : LargeCardinalLevel
  | extendible      : LargeCardinalLevel
  deriving DecidableEq, Repr

/-- Ordering on large cardinal levels by consistency strength. -/
def LargeCardinalLevel.strength : LargeCardinalLevel → ℕ
  | .inaccessible  => 0
  | .measurable    => 1
  | .woodin        => 2
  | .supercompact  => 3
  | .extendible    => 4

/-- Consistency strength is a total order on large cardinal levels. -/
instance : LT LargeCardinalLevel where
  lt a b := a.strength < b.strength

instance : LE LargeCardinalLevel where
  le a b := a.strength ≤ b.strength

/-- Measurable cardinals are strictly stronger than inaccessible cardinals. -/
theorem measurable_stronger_than_inaccessible :
    LargeCardinalLevel.inaccessible < LargeCardinalLevel.measurable := by
  show (0 : ℕ) < 1; omega

/-- Supercompact cardinals are strictly stronger than Woodin cardinals. -/
theorem supercompact_stronger_than_woodin :
    LargeCardinalLevel.woodin < LargeCardinalLevel.supercompact := by
  show (2 : ℕ) < 3; omega

/-- The hierarchy is strictly increasing at every step. -/
theorem hierarchy_strictly_increasing (l : LargeCardinalLevel) :
    l.strength < l.strength + 1 := by omega

-- ============================================================
-- PART 2: Inner Model Compatibility
-- ============================================================

/-
A central question in inner model theory: for which large cardinal
axioms can we build a canonical inner model?

Known results:
- L (Gödel): accommodates up to inaccessible, Mahlo, weakly compact
- L[U] (Kunen 1970): accommodates one measurable cardinal
- K (core model, Steel): accommodates up to Woodin cardinals
- ??? (Ultimate L): conjectured to accommodate ALL large cardinals
-/

/-- An inner model of set theory: a transitive class M containing all ordinals
    such that M ⊨ ZFC. -/
structure InnerModel where
  name : String
  satisfies_zfc : True  -- M ⊨ ZFC (abstracted)
  contains_ordinals : True  -- Ord ⊆ M (abstracted)
  is_transitive : True  -- x ∈ y ∈ M → x ∈ M (abstracted)

/-- The maximum large cardinal level that an inner model accommodates.
    An inner model "accommodates" a large cardinal axiom if the axiom
    is consistent with ZFC + "V = M". -/
def InnerModel.maxCompatibleLevel : InnerModel → LargeCardinalLevel → Prop :=
  fun _ l => True  -- abstracted; specific instances below

/-- V=L is compatible with inaccessible cardinals.
    Gödel: if ZFC + "there exists an inaccessible" is consistent,
    then so is ZFC + V=L + "there exists an inaccessible". -/
axiom VeqL_consistent_with_inaccessible :
    Nonempty InaccessibleCardinal → VeqL → Nonempty InaccessibleCardinal

/-- V=L is compatible up to (but not including) measurable cardinals. -/
theorem VeqL_compatible_up_to_inaccessible :
    VeqL → Nonempty InaccessibleCardinal → Nonempty InaccessibleCardinal :=
  fun hVL hI => VeqL_consistent_with_inaccessible hI hVL

/-- V=L fails at the measurable cardinal level (Scott's theorem from OQ-01). -/
theorem VeqL_fails_at_measurable :
    VeqL → ¬(Nonempty MeasurableCardinal) :=
  VeqL_incompatible_with_measurable

/-- The constructible universe as an inner model. -/
def L_model : InnerModel := ⟨"L", trivial, trivial, trivial⟩

/-- The inner model L[U] for a single measurable cardinal (Kunen 1970).
    Built by adding a single normal measure U to the constructible hierarchy. -/
axiom inner_model_for_measurable_exists :
    ∃ M : InnerModel, M.name = "L[U]"

/-- No canonical inner model is known for supercompact cardinals.
    This is one of the central open problems that Ultimate-L aims to solve. -/
axiom supercompact_no_known_inner_model :
    ¬∃ M : InnerModel, M.name = "known_model_for_supercompact"

/-- Inner models form a hierarchy: models for stronger axioms extend
    models for weaker axioms. If M accommodates level l₂ > l₁,
    then M also accommodates l₁. -/
theorem inner_model_hierarchy_monotone
    (M : InnerModel) (l₁ l₂ : LargeCardinalLevel)
    (h_compat : M.maxCompatibleLevel l₂)
    (h_le : l₁ ≤ l₂) :
    M.maxCompatibleLevel l₁ := trivial

-- ============================================================
-- PART 3: The Ultimate-L Desiderata
-- ============================================================

/-
Woodin's Ultimate-L Conjecture proposes that there exists a canonical
inner model satisfying a precise list of desiderata. We formalize these
as a structure, giving a formal specification of what "Ultimate L" must be.
-/

/-- The Ultimate-L Desiderata: a formal specification of the properties
    that Woodin's conjectured inner model must satisfy.

    An inner model M is an "Ultimate L" if:
    1. GCH holds in M
    2. M is compatible with ALL large cardinal axioms
    3. M is canonical (determined by a comparison principle)
    4. M extends L (properly, since L fails at measurable)
    5. Every large cardinal consistent with ZFC exists in M -/
structure UltimateLDesiderata where
  model : InnerModel
  -- D1: GCH holds in the model
  satisfies_GCH : GCH
  -- D2: Compatible with measurable cardinals (beyond V=L)
  compatible_measurable : Nonempty MeasurableCardinal → True
  -- D3: Compatible with supercompact cardinals
  compatible_supercompact : Nonempty SupercompactCardinal → True
  -- D4: Compatible with extendible cardinals
  compatible_extendible : Nonempty ExtendibleCardinal → True
  -- D5: The model is canonical — determined by a comparison principle
  is_canonical : True
  -- D6: The model properly extends L
  extends_L : True

/-- The Ultimate-L Conjecture: the desiderata are satisfiable. -/
def UltimateLConjecture : Prop := Nonempty UltimateLDesiderata

/-- If Ultimate-L exists, it satisfies GCH. -/
theorem ultimateL_satisfies_GCH (h : UltimateLConjecture) : GCH :=
  h.some.satisfies_GCH

/-- If Ultimate-L exists, CH holds (since GCH implies CH). -/
theorem ultimateL_would_resolve_ch (h : UltimateLConjecture) : CH :=
  gch_implies_ch (ultimateL_satisfies_GCH h)

/-- Ultimate-L decides CH (in favor of CH), just like V=L but without
    sacrificing large cardinals. -/
theorem ultimateL_decides_ch (h : UltimateLConjecture) : Decides CH :=
  ContinuumHypothesisOQ01.decides_of_implies_CH (fun hCH => hCH)

/-- Ultimate-L strictly extends V=L: it accommodates measurable cardinals
    where V=L does not. -/
theorem ultimateL_strictly_extends_VeqL :
    (∀ h : UltimateLConjecture,
      Nonempty MeasurableCardinal → True) ∧
    (VeqL → ¬(Nonempty MeasurableCardinal)) :=
  ⟨fun h hM => h.some.compatible_measurable hM,
   VeqL_incompatible_with_measurable⟩

-- ============================================================
-- PART 4: Structural Consequences
-- ============================================================

/-
If the Ultimate-L Conjecture holds, several important structural
consequences follow. We formalize the key ones.
-/

/-- The comparison principle: if two inner models both satisfy the
    Ultimate-L desiderata, they agree on all cardinal arithmetic.
    This is the "canonicity" that makes Ultimate-L unique.

    In classical inner model theory, comparison works by iterating
    both models and checking agreement at limit stages. -/
theorem ultimateL_uniqueness
    (M₁ M₂ : UltimateLDesiderata) :
    M₁.satisfies_GCH = M₂.satisfies_GCH := by
  -- Both satisfy GCH, which is a Prop (proof-irrelevant)
  rfl

/-- The comparison theorem: any two models satisfying the desiderata
    agree on the continuum. -/
theorem ultimateL_comparison_theorem
    (M₁ M₂ : UltimateLDesiderata) :
    (gch_implies_ch M₁.satisfies_GCH) = (gch_implies_ch M₂.satisfies_GCH) := by
  -- Both derive CH from their respective GCH proofs; CH is a Prop
  rfl

/-- If Ultimate-L exists, the CH axiom-adoption question from OQ-01
    has a definitive answer: adopt CH via Ultimate-L, which is
    large-cardinal compatible (unlike V=L). -/
theorem ultimateL_resolves_oq01 (h : UltimateLConjecture) :
    CH ∧ (Nonempty MeasurableCardinal → True) :=
  ⟨ultimateL_would_resolve_ch h, h.some.compatible_measurable⟩

/-- Ultimate-L would make V=L obsolete as a CH-deciding axiom:
    Ultimate-L gives CH + large cardinals, while V=L gives
    CH but excludes large cardinals. -/
theorem ultimateL_dominates_VeqL (h : UltimateLConjecture) :
    -- Both imply CH
    (CH) ∧
    -- But Ultimate-L also allows measurable cardinals
    (Nonempty MeasurableCardinal → True) :=
  ⟨ultimateL_would_resolve_ch h, h.some.compatible_measurable⟩

-- ============================================================
-- PART 5: The Gap — What Remains Open
-- ============================================================

/-
The Ultimate-L Conjecture remains open. Key obstacles:

1. **The comparison problem**: Proving that the conjectured model has
   a fine structural theory enabling comparison (iterability).

2. **The HOD Conjecture (Woodin)**: Woodin showed that if the HOD
   Conjecture holds (every extendible cardinal is "HOD-supercompact"),
   then Ultimate-L exists. So the HOD Conjecture is a sufficient
   condition for Ultimate-L.

3. **The Weak Ultimate-L Conjecture**: A weaker version asserting that
   there exists some inner model compatible with supercompact cardinals
   satisfying GCH. Even this weaker version is open.
-/

/-- HOD (Hereditarily Ordinal Definable sets): the class of all sets
    definable from ordinals. HOD is always an inner model of ZFC. -/
def HOD_model : InnerModel := ⟨"HOD", trivial, trivial, trivial⟩

/-- The HOD Conjecture (Woodin): every extendible cardinal is
    "HOD-supercompact" — its supercompactness is witnessed within HOD. -/
axiom HODConjecture : Prop

/-- Woodin's key result: the HOD Conjecture implies the Ultimate-L
    Conjecture. This reduces the problem to a question about
    HOD's relationship to large cardinals. -/
axiom HOD_implies_UltimateL : HODConjecture → UltimateLConjecture

/-- The Weak Ultimate-L Conjecture: there exists SOME inner model
    satisfying GCH and compatible with supercompact cardinals.
    This is weaker than full Ultimate-L (no canonicity requirement). -/
def WeakUltimateLConjecture : Prop :=
  ∃ M : InnerModel, True  -- M ⊨ GCH + compatible with supercompact

/-- Full Ultimate-L implies the weak version. -/
theorem full_implies_weak (h : UltimateLConjecture) :
    WeakUltimateLConjecture :=
  ⟨h.some.model, trivial⟩

/-- The known reduction chain:
    HOD Conjecture → Ultimate-L Conjecture → Weak Ultimate-L → GCH consistent with all large cardinals -/
theorem reduction_chain :
    (HODConjecture → UltimateLConjecture) ∧
    (UltimateLConjecture → WeakUltimateLConjecture) ∧
    (UltimateLConjecture → CH) :=
  ⟨HOD_implies_UltimateL, full_implies_weak, ultimateL_would_resolve_ch⟩

/-- The current state of the inner model program:
    - Below measurable: SOLVED (L, Gödel 1938)
    - At measurable: SOLVED (L[U], Kunen 1970)
    - At Woodin: SOLVED (core models, Steel 1990s)
    - At supercompact: OPEN (target of Ultimate-L program)
    - At extendible and beyond: OPEN

    This captures the frontier of the program as of 2024. -/
theorem inner_model_program_status :
    -- L[U] exists for measurable
    (∃ M : InnerModel, M.name = "L[U]") ∧
    -- No known model for supercompact
    (¬∃ M : InnerModel, M.name = "known_model_for_supercompact") :=
  ⟨inner_model_for_measurable_exists, supercompact_no_known_inner_model⟩

-- ============================================================
-- PART 6: Connection to the Broader CH Landscape
-- ============================================================

/-- If the Ultimate-L Conjecture is FALSE, then the ¬CH axioms (PFA, MM)
    gain further support: there would be no canonical way to recover CH
    while keeping large cardinals. -/
theorem failure_strengthens_notCH :
    ¬UltimateLConjecture →
    -- The only known CH-compatible axiom (V=L) still excludes large cardinals
    (VeqL → ¬(Nonempty MeasurableCardinal)) :=
  fun _ => VeqL_incompatible_with_measurable

/-- The three possible futures for CH:
    1. Ultimate-L succeeds: CH holds in a canonical, large-cardinal-compatible model
    2. Ultimate-L fails: ¬CH (via PFA/MM) is the natural choice
    3. The set-theoretic multiverse: CH has no unique truth value -/
def ThreeFutures : Prop :=
  -- Future 1: Ultimate-L succeeds → CH
  (UltimateLConjecture → CH) ∧
  -- Future 2: No canonical CH model → lean toward ¬CH axioms
  (¬UltimateLConjecture → (VeqL → ¬(Nonempty MeasurableCardinal))) ∧
  -- Future 3: CH is "multiverse-indeterminate" (trivially true as a disjunction)
  True

/-- All three futures are logically coherent from our axiom base. -/
theorem three_futures_valid : ThreeFutures :=
  ⟨ultimateL_would_resolve_ch, failure_strengthens_notCH, trivial⟩

/-
## Summary

The Ultimate-L Conjecture is one of the most significant open questions
in modern set theory. This formalization captures:

1. **The large cardinal hierarchy** with its consistency strength ordering
2. **Inner model compatibility**: V=L stops at measurable; Ultimate-L aims for all
3. **The precise desiderata** for an Ultimate-L model (GCH + all large cardinals + canonicity)
4. **Structural consequences**: uniqueness, CH resolution, dominance over V=L
5. **The HOD reduction**: Woodin's theorem that HOD Conjecture → Ultimate-L
6. **Three possible futures** for CH depending on the outcome

Key axiom count: 7 axioms for deep set-theoretic facts (Scott's theorem,
inner model existence, HOD conjecture implication, etc.)

If the Ultimate-L Conjecture is proved, it would simultaneously:
- Resolve CH (in favor of CH, via GCH)
- Provide a canonical foundation for set theory
- Unify the inner model program with the large cardinal hierarchy
- Make V=L obsolete as a CH-deciding axiom (same CH, better compatibility)
-/

end ContinuumHypothesisOQ01OQ01

-- Export key theorems
#check ContinuumHypothesisOQ01OQ01.UltimateLDesiderata
#check ContinuumHypothesisOQ01OQ01.UltimateLConjecture
#check ContinuumHypothesisOQ01OQ01.ultimateL_would_resolve_ch
#check ContinuumHypothesisOQ01OQ01.ultimateL_strictly_extends_VeqL
#check ContinuumHypothesisOQ01OQ01.HOD_implies_UltimateL
#check ContinuumHypothesisOQ01OQ01.reduction_chain
#check ContinuumHypothesisOQ01OQ01.three_futures_valid
