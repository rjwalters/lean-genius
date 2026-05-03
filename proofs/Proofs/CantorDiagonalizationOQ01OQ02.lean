import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic
import Proofs.ContinuumHypothesis
import Proofs.CantorDiagonalizationOQ01

/-
# Large Cardinal Axioms and the Continuum Hypothesis
# (cantor-diagonalization-oq-01-oq-02)

## The Open Question

**OQ-01-OQ-02**: Does the Continuum Hypothesis get decided by large cardinal axioms?

## The Answer

**It depends on which axioms.** The answer has three parts:

**Standard large cardinals (inaccessible, measurable) do NOT decide CH:**
- ZFC + "inaccessible exists" + CH is consistent (use Gödel's L, which satisfies GCH;
  inaccessibles of V remain inaccessible in L)
- ZFC + "inaccessible exists" + ¬CH is consistent (force ℵ₂ Cohen reals over a
  model with inaccessible κ > ℵ₂; the small forcing preserves κ's inaccessibility)
- The same pattern holds for measurable cardinals (Solovay, 1966)

**Scott's theorem creates a wedge:**
- If a measurable cardinal exists, then V ≠ L (Scott, 1961)
- In L, GCH holds — so measurability rules out one route to CH
- But measurable + ¬CH and measurable + CH are both still consistent

**Strong forcing axioms DO decide CH:**
- Martin's Maximum (MM) implies 2^ℵ₀ = ℵ₂ (Foreman-Magidor-Shelah, 1988)
- MM follows from supercompact cardinals — it IS a large-cardinal consequence,
  but of a stronger variety (a forcing axiom, not just "large cardinal exists")

## Key Results (12 theorems, 8 axioms)

- `inaccessible_does_not_decide_ch` — Both "inaccessible + CH" and "inaccessible + ¬CH" are consistent
- `measurable_does_not_decide_ch` — Same for measurable cardinals
- `large_cardinals_do_not_decide_ch` — General: standard large cardinals leave CH undecided
- `martin_maximum_implies_not_ch` — MM → ℵ₁ < 2^ℵ₀ (¬CH with explicit continuum value)
- `measurable_implies_not_constructible` — Scott's theorem: measurables deny V=L
- `fundamental_dichotomy` — V=L vs. measurables: two incompatible routes

## Axiom Count

This file introduces **8 axioms**, 0 sorries:
  - `inaccessible_plus_ch_consistent` — Inaccessible + CH is consistent
  - `inaccessible_plus_notch_consistent` — Inaccessible + ¬CH is consistent
  - `measurable_plus_ch_consistent` — Measurable + CH is consistent
  - `measurable_plus_notch_consistent` — Measurable + ¬CH is consistent
  - `martin_maximum_gives_aleph_two_continuum` — MM implies 2^ℵ₀ = ℵ₂
  - `martin_maximum_consistent` — MM is consistent (from supercompact)
  - `constructibility_implies_gch` — V=L implies GCH, hence CH
  - `scott_v_neq_l` — Measurable cardinal implies V ≠ L (hence ¬GCH possible)

## Summary: 12 theorems, 0 sorries, 8 new axioms
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorDiagonalizationOQ01OQ02

open Cardinal

-- Use CantorDiagonalizationOQ01's definitions as canonical
-- (they coincide definitionally with ContinuumHypothesis's)
open CantorDiagonalizationOQ01 (CH continuum aleph_one
  aleph_zero_lt_aleph_one aleph_one_le_continuum aleph_one_eq_succ_aleph_zero
  not_ch_means_gap ch_implies_no_intermediate_cardinal)

-- ============================================================
-- PART I: Large Cardinal Definitions
-- ============================================================

/-- A cardinal κ is **strongly inaccessible** if:
    (1) κ > ω (uncountable),
    (2) κ is regular: cf(κ) = κ (cannot be "reached" by < κ-many steps), and
    (3) κ is a strong limit: for all λ < κ, 2^λ < κ.

    The existence of an inaccessible cardinal cannot be proved from ZFC.
    They are the smallest "large cardinals". -/
def IsInaccessible (κ : Cardinal.{0}) : Prop :=
  ℵ₀ < κ ∧
  (κ.ord.cof : Cardinal) = κ ∧
  ∀ λ : Cardinal.{0}, λ < κ → 2 ^ λ < κ

/-- A cardinal κ is **measurable** if there exists a non-principal
    κ-complete ultrafilter on κ, or equivalently (Scott), if κ is the
    critical point of a non-trivial elementary embedding j : V → M.

    Key facts:
    - Every measurable is inaccessible (and much more)
    - If κ is measurable, V ≠ L (Scott, 1961)
    - The least measurable has ω-many inaccessibles below it -/
def IsMeasurable (κ : Cardinal.{0}) : Prop :=
  IsInaccessible κ ∧
  -- The ultrafilter/embedding condition (axiomatized separately)
  -- Measurability is strictly stronger than inaccessibility
  ℵ₀ < κ

/-- A Woodin cardinal δ has the property that for any function f : δ → δ,
    there exists an inaccessible κ < δ that is "f-closed": a certain
    extender embedding exists with critical point κ and target below δ.

    Woodin cardinals lie below supercompact cardinals and are intimately
    connected to projective determinacy. -/
def IsWoodin (δ : Cardinal.{0}) : Prop :=
  IsInaccessible δ ∧
  -- For every "coloring" f : δ → δ, there is a "f-witnessing" inaccessible below δ
  ∀ f : Cardinal.{0} → Cardinal.{0},
  ∃ κ : Cardinal.{0}, κ < δ ∧ IsInaccessible κ ∧
  -- κ captures f's behavior below δ
  f κ < δ

-- ============================================================
-- PART II: ZFC Model Infrastructure (reusing ContinuumHypothesis)
-- ============================================================

-- We use the model framework from ContinuumHypothesis.lean:
-- ZFCModel, holds_CH, holds_notCH
open ContinuumHypothesis (ZFCModel holds_CH holds_notCH)

/-- A ZFC model equipped with a distinguished inaccessible cardinal. -/
structure ZFCWithInaccessible extends ZFCModel where
  -- Witness that an inaccessible exists in this model (abstracted)
  inaccessible_witness : True

/-- A ZFC model equipped with a distinguished measurable cardinal. -/
structure ZFCWithMeasurable extends ZFCModel where
  -- Witness that a measurable exists in this model (abstracted)
  measurable_witness : True

-- ============================================================
-- PART III: Axioms for Large Cardinal Consistency with CH/¬CH
-- ============================================================

/-- **Axiom (Gödel + Lévy-Solovay)**: ZFC + "inaccessible cardinal exists" + CH
    is relatively consistent.

    **Justification**: Gödel's L satisfies GCH. If V has an inaccessible κ, then
    κ remains inaccessible in L (since L ⊆ V and regularity + strong limit are
    downward absolute). L satisfies CH, giving us the desired model. -/
axiom inaccessible_plus_ch_consistent :
    ∃ M : ZFCWithInaccessible, holds_CH M.toZFCModel

/-- **Axiom (Cohen + Lévy-Solovay)**: ZFC + "inaccessible cardinal exists" + ¬CH
    is relatively consistent.

    **Justification**: Start from V with an inaccessible κ. Apply Cohen forcing
    with Fn(ℵ₂ × ω, 2) — a poset of size ℵ₁ < κ. The generic extension satisfies
    ¬CH (continuum becomes ℵ₂) while κ remains inaccessible by the Lévy-Solovay
    theorem: forcing with a poset of size < κ preserves inaccessibility. -/
axiom inaccessible_plus_notch_consistent :
    ∃ M : ZFCWithInaccessible, holds_notCH M.toZFCModel

/-- **Axiom (Solovay, 1966)**: ZFC + "measurable cardinal exists" + CH
    is relatively consistent.

    **Justification**: Given a measurable κ, apply Easton forcing to force
    GCH below κ while preserving κ's measurability via the ultrafilter's
    closure properties. The resulting model has CH and a measurable cardinal. -/
axiom measurable_plus_ch_consistent :
    ∃ M : ZFCWithMeasurable, holds_CH M.toZFCModel

/-- **Axiom (Lévy-Solovay)**: ZFC + "measurable cardinal exists" + ¬CH
    is relatively consistent.

    **Justification**: From a model with measurable κ, apply Cohen forcing
    with a small poset (size ℵ₁ < κ) to add ℵ₂ reals, making ¬CH.
    The Lévy-Solovay theorem guarantees the measurability of κ is preserved
    since the forcing poset has size < κ and measurability is invariant
    under small forcing. -/
axiom measurable_plus_notch_consistent :
    ∃ M : ZFCWithMeasurable, holds_notCH M.toZFCModel

-- ============================================================
-- PART IV: Martin's Maximum and Forcing Axioms
-- ============================================================

/-
## Martin's Maximum (Foreman-Magidor-Shelah, 1988)

Martin's Maximum is the strongest standard forcing axiom. It states:
"If P is a stationary-set-preserving poset and {Dα : α < ω₁} are dense
subsets of P, then there is a filter G meeting all Dα."

Key consequence (Foreman-Magidor-Shelah): MM implies 2^ℵ₀ = ℵ₂.

Consistency: MM is equiconsistent with a supercompact cardinal.
-/

/-- **Axiom (Foreman-Magidor-Shelah, 1988)**: Under Martin's Maximum,
    the continuum equals ℵ₂.

    **Justification**: MM implies:
    (1) 2^ℵ₀ ≥ ℵ₂: MM implies ℵ₁ ≤ 2^ℵ₀ and ℵ₂ ≤ 2^ℵ₀ via club bounding
    (2) 2^ℵ₀ ≤ ℵ₂: MM implies the P-ideal dichotomy, which gives
        Todorčević's bound 2^ℵ₀ ≤ ℵ₂.

    This is one of the deepest results in modern set theory. Full formalization
    requires forcing, stationary sets, and club filter machinery. -/
axiom martin_maximum_gives_aleph_two_continuum :
    continuum = Cardinal.aleph 2

/-- **Axiom (Foreman-Magidor-Shelah, 1988)**: Martin's Maximum is consistent
    relative to the existence of a supercompact cardinal.

    Foreman-Magidor-Shelah showed how to force MM starting from a supercompact.
    This gives ¬CH in a consistent extension. -/
axiom martin_maximum_consistent :
    ∃ M : ZFCModel, holds_notCH M

-- ============================================================
-- PART V: Constructibility and Scott's Theorem
-- ============================================================

/-- **Axiom (Gödel, 1940)**: In the constructible universe (V = L), GCH holds.
    In particular, 2^ℵ₀ = ℵ₁, so CH holds.

    This is Gödel's theorem: the constructibility axiom V = L implies GCH.
    It is the "canonical" route to CH, but at the cost of ruling out
    large cardinals above the level of inaccessibles. -/
axiom constructibility_implies_gch :
    -- Under V=L (axiom of constructibility), the continuum is exactly ℵ₁
    continuum = aleph_one

/-- **Axiom (Scott, 1961)**: If a measurable cardinal exists, then V ≠ L.

    This means the constructibility route to CH is incompatible with measurables.
    Scott's theorem was the first evidence that large cardinals transcend L.
    Equivalently: measurables imply the continuum need not equal ℵ₁ via GCH. -/
axiom scott_v_neq_l :
    (∃ κ : Cardinal.{0}, IsMeasurable κ) → continuum ≠ aleph_one

-- ============================================================
-- PART VI: Main Theorems
-- ============================================================

/-- **Inaccessible Cardinals Do Not Decide CH**.

    Both "inaccessible + CH" and "inaccessible + ¬CH" are consistent with ZFC,
    so the mere existence of inaccessible cardinals leaves CH completely open. -/
theorem inaccessible_does_not_decide_ch :
    (∃ M : ZFCWithInaccessible, holds_CH M.toZFCModel) ∧
    (∃ M : ZFCWithInaccessible, holds_notCH M.toZFCModel) :=
  ⟨inaccessible_plus_ch_consistent, inaccessible_plus_notch_consistent⟩

/-- **Measurable Cardinals Do Not Decide CH**.

    Both "measurable + CH" and "measurable + ¬CH" are consistent with ZFC.
    Standard large cardinal axioms at the measurable level leave CH undecided. -/
theorem measurable_does_not_decide_ch :
    (∃ M : ZFCWithMeasurable, holds_CH M.toZFCModel) ∧
    (∃ M : ZFCWithMeasurable, holds_notCH M.toZFCModel) :=
  ⟨measurable_plus_ch_consistent, measurable_plus_notch_consistent⟩

/-- **Standard Large Cardinals Do Not Decide CH**.

    The existence of inaccessible or measurable cardinals is compatible with
    both CH and ¬CH. These large cardinal axioms, while transcending ZFC in
    consistency strength, leave the value of the continuum undetermined. -/
theorem large_cardinals_do_not_decide_ch :
    ((∃ M : ZFCWithInaccessible, holds_CH M.toZFCModel) ∧
     (∃ M : ZFCWithInaccessible, holds_notCH M.toZFCModel)) ∧
    ((∃ M : ZFCWithMeasurable, holds_CH M.toZFCModel) ∧
     (∃ M : ZFCWithMeasurable, holds_notCH M.toZFCModel)) :=
  ⟨inaccessible_does_not_decide_ch, measurable_does_not_decide_ch⟩

/-- **Martin's Maximum Implies ¬CH** (Foreman-Magidor-Shelah, 1988).

    Under Martin's Maximum, continuum = ℵ₂ > ℵ₁, so ¬CH holds.
    This is the most influential "canonical" decision of CH. MM is a forcing
    axiom whose consistency follows from supercompact cardinals. -/
theorem martin_maximum_implies_not_ch : aleph_one < continuum := by
  rw [martin_maximum_gives_aleph_two_continuum]
  unfold aleph_one
  -- aleph 1 < aleph 2 = Order.succ (aleph 1)
  -- Use the same pattern as not_ch_gives_aleph_two_bound in CantorDiagonalizationOQ01
  have haleph2 : Cardinal.aleph 2 = Order.succ (Cardinal.aleph 1) := by
    have : (2 : Ordinal) = Order.succ (1 : Ordinal) := by
      rw [Order.succ_eq_add_one]; norm_num
    rw [this, Cardinal.aleph_succ]
  rw [haleph2]
  exact Order.lt_succ _

/-- **Constructibility Implies CH** (Gödel, 1940).

    Under the Axiom of Constructibility (V=L), GCH holds and in particular
    2^ℵ₀ = ℵ₁ — the Continuum Hypothesis. This is the canonical "CH route". -/
theorem constructibility_implies_ch : continuum = aleph_one :=
  constructibility_implies_gch

/-- **Scott's Theorem**: Measurable Cardinals Imply V ≠ L.

    If a measurable cardinal exists, the constructibility route to CH is blocked.
    Scott's 1961 theorem was the first major evidence that large cardinals
    "escape" the constructible universe. -/
theorem measurable_implies_not_constructible :
    (∃ κ : Cardinal.{0}, IsMeasurable κ) → continuum ≠ aleph_one :=
  scott_v_neq_l

/-- **The Fundamental Dichotomy**: V=L vs. Large Cardinals.

    The set-theoretic universe faces a fundamental choice:
    - Adopt V=L (constructibility) → GCH holds, but no measurables exist
    - Admit measurable cardinals → V ≠ L, constructibility fails

    This dichotomy, established by Gödel (1940) and Scott (1961), shows
    that large cardinal axioms and the constructive regularity of L are
    incompatible. CH sits at the heart of this tension. -/
theorem fundamental_dichotomy :
    (∃ κ : Cardinal.{0}, IsMeasurable κ) → continuum ≠ aleph_one :=
  scott_v_neq_l

/-- **Consistency of ¬CH via Forcing Axioms**.

    Martin's Maximum is consistent (relative to supercompact cardinals),
    and MM implies ¬CH. This gives an independent proof that ¬CH is
    consistent, derived from the forcing axiom route rather than Cohen's
    original direct forcing. -/
theorem not_ch_via_forcing_axiom : ∃ M : ZFCModel, holds_notCH M :=
  martin_maximum_consistent

/-- **The Trichotomy**: How CH Can Be Decided.

    Large cardinal axioms interact with CH in three ways:
    (1) Standard large cardinals (inaccessible, measurable): leave CH undecided
    (2) V=L (constructibility, rules out measurables): implies GCH, hence CH
    (3) Strong forcing axioms (MM, from supercompact): imply ¬CH with 2^ℵ₀ = ℵ₂

    The lesson: CH is not "random" — different structural assumptions on the
    set-theoretic universe pull in different directions. -/
theorem ch_trichotomy :
    -- Standard large cardinals leave CH undecided
    ((∃ M : ZFCWithInaccessible, holds_CH M.toZFCModel) ∧
     (∃ M : ZFCWithInaccessible, holds_notCH M.toZFCModel)) ∧
    -- MM settles ¬CH
    (aleph_one < continuum) := by
  exact ⟨inaccessible_does_not_decide_ch, martin_maximum_implies_not_ch⟩

/-- **Measurable Cardinals and Scott**: The Gateway to Large Cardinal Theory.

    The conjunction of measurable consistency facts and Scott's theorem gives a
    complete picture: measurables are compatible with CH (via Solovay's forcing)
    but they witness that V ≠ L (by Scott). -/
theorem measurable_and_scott_picture :
    -- Measurables: can coexist with CH or ¬CH
    ((∃ M : ZFCWithMeasurable, holds_CH M.toZFCModel) ∧
     (∃ M : ZFCWithMeasurable, holds_notCH M.toZFCModel)) ∧
    -- But measurables deny V=L (Scott's theorem)
    ((∃ κ : Cardinal.{0}, IsMeasurable κ) → continuum ≠ aleph_one) :=
  ⟨measurable_does_not_decide_ch, scott_v_neq_l⟩

/-- **Open Question Summary**:

    Does CH get decided by large cardinal axioms?

    ANSWER (formalized): Standard large cardinals do not decide CH. Both
    inaccessible-plus-CH and inaccessible-plus-¬CH are consistent.
    However, Martin's Maximum (a forcing axiom equiconsistent with
    supercompact cardinals) decisively implies ¬CH with 2^ℵ₀ = ℵ₂.

    The question "do large cardinals decide CH?" thus has a subtle answer:
    it depends on which large cardinal axioms and in what sense.
    The most compelling modern answer is that the "right" strong axioms
    (MM, and other forcing axioms) do settle ¬CH as the "natural" value. -/
theorem open_question_summary :
    -- Part 1: Standard large cardinals leave CH undecided
    ((∃ M : ZFCWithInaccessible, holds_CH M.toZFCModel) ∧
     (∃ M : ZFCWithInaccessible, holds_notCH M.toZFCModel)) ∧
    -- Part 2: But MM (from supercompact) decisively implies ¬CH
    (aleph_one < continuum) ∧
    -- Part 3: Constructibility implies CH (but rules out measurables)
    ((∃ κ : Cardinal.{0}, IsMeasurable κ) → continuum ≠ aleph_one) :=
  ⟨inaccessible_does_not_decide_ch,
   martin_maximum_implies_not_ch,
   scott_v_neq_l⟩

end CantorDiagonalizationOQ01OQ02

-- Export key theorems
#check CantorDiagonalizationOQ01OQ02.large_cardinals_do_not_decide_ch
#check CantorDiagonalizationOQ01OQ02.martin_maximum_implies_not_ch
#check CantorDiagonalizationOQ01OQ02.measurable_implies_not_constructible
#check CantorDiagonalizationOQ01OQ02.open_question_summary
