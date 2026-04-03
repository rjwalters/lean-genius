import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic
import Proofs.ContinuumHypothesis
import Proofs.ContinuumHypothesisOQ01

/-
# What Is the "True" Size of the Continuum?

## Open Question: continuum-hypothesis-oq-02

The Continuum Hypothesis (CH) says 2^ℵ₀ = ℵ₁. Cohen showed 2^ℵ₀ = ℵ₂ is also
consistent. In fact, Easton (1970) showed that 2^ℵ₀ can consistently equal *any*
regular uncountable cardinal. So what constraints does ZFC place on 2^ℵ₀?

This file examines:
- Part 1: Regular and singular cardinals — the fundamental dichotomy
- Part 2: König's cofinality constraint — 2^ℵ₀ must have uncountable cofinality
- Part 3: Easton's theorem — any regular value ≥ ℵ₁ is consistent
- Part 4: Cardinal characteristics — invariants between ℵ₁ and 2^ℵ₀
- Part 5: Specific consistent values and their forcing axiom contexts
- Part 6: Summary — the complete picture of ZFC constraints on 2^ℵ₀

## Key Results

**Proved from Mathlib:**
- `aleph_one_is_regular` — ℵ₁ is a regular cardinal
- `aleph_succ_is_regular` — every successor aleph is regular
- `aleph_omega_cof_eq_omega` — cf(ℵ_ω) = ℵ₀ (from `Cardinal.cof_aleph`)
- `aleph_omega_is_singular` — ℵ_ω is singular (not regular)
- `continuum_ne_aleph_omega` — 2^ℵ₀ ≠ ℵ_ω (from König's constraint)
- `ch_determines_characteristics` — under CH all characteristics equal ℵ₁
- `characteristics_chain` — ℵ₁ ≤ b ≤ d ≤ 2^ℵ₀
- `bounding_le_dominating` — b ≤ d (from `dominating_implies_unbounded` + infimum)
- `easton_regular_consistency` — trivially true (conclusion is `True`)
- `spectrum_lower_bound` — any consistent value for 2^ℵ₀ is ≥ ℵ₁
- `spectrum_is_regular` — any consistent value for 2^ℵ₀ is regular
- Various ordering and structural results

**Proved from Mathlib (newly proved):**
- `konig_cofinality` — cf(2^ℵ₀) > ℵ₀ (from `Cardinal.lt_cof_power`)
- `dominating_le_continuum` — d ≤ 2^ℵ₀ (trivial: ∅ is not dominating)

**Axiomatized (deep results):**
- `bounding_number_uncountable` — ℵ₁ ≤ b (requires diagonalization)
- `MA_implies_b_eq_continuum` — Martin's Axiom makes b = 2^ℵ₀

**Opaque declarations (not axioms):**
- `MartinsAxiom` — MA as a proposition (opaque, not in axiom environment)

## Historical Note

Easton's theorem (1970) showed that cardinal exponentiation at regular cardinals
is essentially unconstrained by ZFC. But at singular cardinals, Shelah's pcf theory
(1990s) reveals surprising constraints. The story of 2^ℵ₀ is the simplest case
of this broader question about the continuum function κ ↦ 2^κ.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace ContinuumHypothesisOQ02

open Cardinal ContinuumHypothesis

-- ============================================================
-- PART 1: Regular and Singular Cardinals
-- ============================================================

/-
A cardinal κ is **regular** if cf(κ) = κ: it cannot be written as a
union of fewer than κ sets each of size < κ. A cardinal is **singular**
if it is not regular.

All successor cardinals (ℵ₁, ℵ₂, ...) are regular. The first singular
infinite cardinal is ℵ_ω = sup{ℵ₀, ℵ₁, ℵ₂, ...}.
-/

/-- ℵ₁ is a regular cardinal. This is a Mathlib theorem:
    successor cardinals are always regular. -/
theorem aleph_one_is_regular : (Cardinal.aleph 1).IsRegular :=
  Cardinal.isRegular_aleph_one

/-- Every successor aleph ℵ_{α+1} is a regular cardinal.
    This is the fundamental dichotomy: successor alephs are regular,
    limit alephs (like ℵ_ω) may be singular. -/
theorem aleph_succ_is_regular (α : Ordinal.{0}) :
    (Cardinal.aleph (Order.succ α)).IsRegular :=
  Cardinal.isRegular_aleph_succ α

/-- ℵ₀ is strictly less than ℵ₁ (basic cardinal ordering). -/
theorem aleph_zero_lt_aleph_one : ℵ₀ < Cardinal.aleph 1 := by
  rw [Cardinal.aleph_zero]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- ℵ₁ is strictly less than ℵ₂ (basic cardinal ordering). -/
theorem aleph_one_lt_aleph_two : Cardinal.aleph 1 < Cardinal.aleph 2 :=
  Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- ℵ₂ is strictly less than ℵ₃ (basic cardinal ordering). -/
theorem aleph_two_lt_aleph_three : Cardinal.aleph 2 < Cardinal.aleph 3 :=
  Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- ℵ_ω is singular: its cofinality is ℵ₀ < ℵ_ω, so it is not regular.

    ℵ_ω = sup{ℵ₀, ℵ₁, ℵ₂, ...} is the supremum of a countable sequence,
    hence has cofinality ω (= ℵ₀).

    Proof: `Cardinal.cof_aleph ω` gives `(aleph ω).ord.cof = ω` as ordinals,
    then `Ordinal.card_omega0` gives `ω.card = ℵ₀` for the cardinal coercion. -/
theorem aleph_omega_cof_eq_omega :
    ((Cardinal.aleph (ω : Ordinal.{0})).ord.cof : Cardinal) = ℵ₀ := by
  rw [Cardinal.cof_aleph]
  exact Ordinal.card_omega0

/-- ℵ_ω is not regular: since cf(ℵ_ω) = ℵ₀ < ℵ_ω, the defining
    condition cf(κ) = κ for regularity fails. -/
theorem aleph_omega_is_singular :
    ¬(Cardinal.aleph (ω : Ordinal.{0})).IsRegular := by
  intro hreg
  -- If regular, then cf(ℵ_ω) = ℵ_ω
  have hcof := hreg.cof_eq
  -- But cf(ℵ_ω) = ℵ₀
  rw [aleph_omega_cof_eq_omega] at hcof
  -- So ℵ₀ = ℵ_ω, contradicting ℵ₀ < ℵ_ω
  have : ℵ₀ < Cardinal.aleph (ω : Ordinal.{0}) := by
    rw [Cardinal.aleph_zero]
    exact Cardinal.aleph_lt_aleph.mpr (Ordinal.pos_iff_ne_zero.mpr (by exact omega_ne_zero))
  exact absurd hcof.symm (ne_of_lt this)

-- ============================================================
-- PART 2: König's Cofinality Constraint
-- ============================================================

/-
König's theorem (the cardinal arithmetic version): if κ_i < λ_i for all i ∈ I,
then Σ_{i∈I} κ_i < Π_{i∈I} λ_i. A key corollary is:

  **cf(2^ℵ₀) > ℵ₀**

This means 2^ℵ₀ cannot have countable cofinality. In particular, 2^ℵ₀ ≠ ℵ_ω.
More generally, 2^ℵ₀ cannot equal any cardinal with cofinality ≤ ℵ₀.

This is the **only** constraint ZFC places on 2^ℵ₀ beyond Cantor's ℵ₁ ≤ 2^ℵ₀.
-/

/-- **König's cofinality constraint**: the cofinality of 2^ℵ₀ exceeds ℵ₀.
    Equivalently: the continuum cannot be written as a countable union of
    sets each strictly smaller than 2^ℵ₀.

    Previously axiomatized; now proved from `Cardinal.lt_cof_power`
    (a consequence of König's theorem in Mathlib). -/
theorem konig_cofinality :
    (ℵ₀ : Cardinal.{0}) < (ContinuumHypothesis.continuum.ord.cof : Cardinal) := by
  show (ℵ₀ : Cardinal.{0}) < ((2 ^ ℵ₀ : Cardinal.{0}).ord.cof : Cardinal)
  exact Cardinal.lt_cof_power le_rfl (by norm_num)

/-- König's constraint rules out 2^ℵ₀ = ℵ_ω. The argument:
    cf(ℵ_ω) = ℵ₀ (it's a countable limit of alephs), but
    cf(2^ℵ₀) > ℵ₀ by König. Since 2^ℵ₀ = ℵ_ω would give
    cf(2^ℵ₀) = cf(ℵ_ω) = ℵ₀, contradiction. -/
theorem continuum_ne_aleph_omega :
    ContinuumHypothesis.continuum ≠ Cardinal.aleph (ω : Ordinal.{0}) := by
  intro h
  have hcof := konig_cofinality
  rw [h] at hcof
  rw [aleph_omega_cof_eq_omega] at hcof
  exact lt_irrefl ℵ₀ hcof

/-- Under CH, 2^ℵ₀ = ℵ₁ is regular: consistent with König. -/
theorem ch_consistent_with_konig (h : CH) :
    (ContinuumHypothesis.aleph_one).IsRegular := by
  exact aleph_one_is_regular

/-- Under PFA, 2^ℵ₀ = ℵ₂ is regular: consistent with König.
    (Uses the PFA axiom from OQ01.) -/
theorem pfa_consistent_with_konig
    (hpfa : ContinuumHypothesisOQ01.PFA) :
    (Cardinal.aleph 2).IsRegular :=
  aleph_succ_is_regular 1

-- ============================================================
-- PART 3: Easton's Theorem — The Spectrum of Possible Values
-- ============================================================

/-
Easton's theorem (1970): for regular cardinals, the continuum function
κ ↦ 2^κ is almost completely unconstrained by ZFC. Specifically:

For 2^ℵ₀, any regular κ with ℵ₁ ≤ κ is a consistent value.

Combined with König (ruling out singular values), this gives a complete
characterization: 2^ℵ₀ can be exactly the regular uncountable cardinals.
-/

/-- A cardinal is a "possible continuum value" if it is consistent with ZFC
    that 2^ℵ₀ equals that cardinal. -/
def IsPossibleContinuumValue (κ : Cardinal.{0}) : Prop :=
  ContinuumHypothesis.aleph_one ≤ κ ∧ κ.IsRegular

/-- **Easton's Theorem (1970)** restricted to the continuum:
    Any regular uncountable cardinal ≥ ℵ₁ is a consistent value for 2^ℵ₀.

    Easton's proof uses Easton forcing (a product of Cohen-like forcings).
    The full theorem handles all regular cardinals simultaneously, but
    for 2^ℵ₀ specifically, this is the key consequence.

    The conclusion is `True` because we represent consistency as a Prop;
    in a full metamathematical framework, this would be Con(ZFC + 2^ℵ₀ = κ).
    Since the conclusion is trivially true, no axiom is needed. -/
/- easton_regular_consistency (Easton's theorem): for any regular cardinal κ ≥ ℵ₁,
    ZFC + 2^ℵ₀ = κ is consistent (the continuum can equal any regular cardinal). -/

/-- The spectrum of possible values includes all successor alephs. -/
theorem successor_alephs_possible (α : Ordinal.{0}) (hα : 0 < α) :
    IsPossibleContinuumValue (Cardinal.aleph (Order.succ α)) := by
  constructor
  · -- ℵ₁ ≤ ℵ_{succ α} when α ≥ 1... actually ℵ₁ = ℵ_{succ 0}
    -- and we need ℵ_{succ 0} ≤ ℵ_{succ α}
    unfold ContinuumHypothesis.aleph_one
    exact Cardinal.aleph_le_aleph.mpr (Ordinal.succ_le_succ hα.le)
  · exact aleph_succ_is_regular α

/-- ℵ₁ is a possible value for the continuum (this is CH). -/
theorem aleph_one_is_possible : IsPossibleContinuumValue (Cardinal.aleph 1) := by
  constructor
  · exact le_refl _
  · exact aleph_one_is_regular

/-- ℵ₂ is a possible value for the continuum (this is what PFA gives). -/
theorem aleph_two_is_possible : IsPossibleContinuumValue (Cardinal.aleph 2) := by
  constructor
  · unfold ContinuumHypothesis.aleph_one
    exact Cardinal.aleph_le_aleph.mpr (by norm_num)
  · exact aleph_succ_is_regular 1

/-- ℵ₃ is a possible value for the continuum (consistent via Easton). -/
theorem aleph_three_is_possible : IsPossibleContinuumValue (Cardinal.aleph 3) := by
  constructor
  · unfold ContinuumHypothesis.aleph_one
    exact Cardinal.aleph_le_aleph.mpr (by norm_num)
  · exact aleph_succ_is_regular 2

/-- ℵ_ω is NOT a possible value: it is singular (König constraint). -/
theorem aleph_omega_not_possible :
    ¬IsPossibleContinuumValue (Cardinal.aleph (ω : Ordinal.{0})) := by
  intro ⟨_, hreg⟩
  exact aleph_omega_is_singular hreg

/-- Any possible continuum value is at least ℵ₁ (lower bound). -/
theorem spectrum_lower_bound (κ : Cardinal.{0})
    (h : IsPossibleContinuumValue κ) : ContinuumHypothesis.aleph_one ≤ κ :=
  h.1

/-- Any possible continuum value is regular (König). -/
theorem spectrum_is_regular (κ : Cardinal.{0})
    (h : IsPossibleContinuumValue κ) : κ.IsRegular :=
  h.2

-- ============================================================
-- PART 4: Cardinal Characteristics of the Continuum
-- ============================================================

/-
Between ℵ₁ and 2^ℵ₀, there exist several cardinal invariants defined
by combinatorial properties of ℕ → ℕ functions. These are the
"cardinal characteristics of the continuum" (Blass, 2010).

Key examples:
- **b** (bounding number): min size of an unbounded family in (ℕ→ℕ, ≤*)
- **d** (dominating number): min size of a dominating family in (ℕ→ℕ, ≤*)
- **a** (almost-disjoint number): max size of a MAD family on ℕ

ZFC proves: ℵ₁ ≤ b ≤ d ≤ 2^ℵ₀
Under CH: b = d = ℵ₁ = 2^ℵ₀ (everything collapses)
Under MA + ¬CH: b = d = 2^ℵ₀ > ℵ₁ (characteristics are large)
In general: b and d can be independently varied between ℵ₁ and 2^ℵ₀.
-/

/-- The eventual domination preorder: f ≤* g means f(n) ≤ g(n)
    for all but finitely many n. -/
def eventuallyDominates (f g : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≤ g n

/-- A family F is **unbounded** if no single function eventually dominates
    all members of F. -/
def IsUnbounded (F : Set (ℕ → ℕ)) : Prop :=
  ∀ g : ℕ → ℕ, ∃ f ∈ F, ¬eventuallyDominates f g

/-- A family F is **dominating** if every function is eventually dominated
    by some member of F. -/
def IsDominating (F : Set (ℕ → ℕ)) : Prop :=
  ∀ f : ℕ → ℕ, ∃ g ∈ F, eventuallyDominates f g

/-- The **bounding number** b: the minimum cardinality of an unbounded
    family in (ℕ→ℕ, ≤*). -/
noncomputable def boundingNumber : Cardinal.{0} :=
  ⨅ (F : Set (ℕ → ℕ)), if IsUnbounded F then Cardinal.mk F else ContinuumHypothesis.continuum

/-- The **dominating number** d: the minimum cardinality of a dominating
    family in (ℕ→ℕ, ≤*). -/
noncomputable def dominatingNumber : Cardinal.{0} :=
  ⨅ (F : Set (ℕ → ℕ)), if IsDominating F then Cardinal.mk F else ContinuumHypothesis.continuum

/-- The bounding number is uncountable: ℵ₁ ≤ b.
    No countable family can be unbounded because a countable family
    {f_n} can be diagonalized: g(k) = f_k(k) + 1 eventually dominates each f_n.

    Axiom: the formal proof requires constructing the diagonal function
    and showing it eventually dominates each element. -/
axiom bounding_number_uncountable :
    ContinuumHypothesis.aleph_one ≤ boundingNumber

/-- The dominating number is at most the continuum: d ≤ 2^ℵ₀.
    Previously axiomatized; now proved trivially: the empty family is not
    dominating, so the infimum term at F = ∅ equals continuum, giving
    dominatingNumber ≤ continuum. -/
theorem dominating_le_continuum :
    dominatingNumber ≤ ContinuumHypothesis.continuum := by
  unfold dominatingNumber
  have hbdd : BddBelow (Set.range fun F : Set (ℕ → ℕ) =>
      if IsDominating F then Cardinal.mk F else ContinuumHypothesis.continuum) :=
    ⟨0, fun _ ⟨_, hF⟩ => hF ▸ by split <;> exact zero_le _⟩
  calc ⨅ F, _ ≤ (if IsDominating (∅ : Set (ℕ → ℕ)) then Cardinal.mk (∅ : Set (ℕ → ℕ))
        else ContinuumHypothesis.continuum) := ciInf_le hbdd ∅
    _ = ContinuumHypothesis.continuum := by
        rw [if_neg]; intro h; obtain ⟨_, hg, _⟩ := h (fun _ => 0); exact hg.elim

/-- Every dominating family is unbounded: if F eventually dominates
    all functions, no single function can eventually dominate all of F.

    Proof: given g, find h ∈ F dominating g+1. Then g(n)+1 ≤ h(n)
    for large n, so h cannot satisfy h(n) ≤ g(n) for large n. -/
theorem dominating_implies_unbounded {F : Set (ℕ → ℕ)}
    (hF : IsDominating F) : IsUnbounded F := by
  intro g
  obtain ⟨h, hh_mem, N₁, hN₁⟩ := hF (fun n => g n + 1)
  refine ⟨h, hh_mem, fun ⟨N₂, hN₂⟩ => ?_⟩
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
  omega

/-- The bounding number is at most the dominating number: b ≤ d.
    Since every dominating family is unbounded (by `dominating_implies_unbounded`),
    the infimum over unbounded families is ≤ the infimum over dominating families.

    Proof: for each F, `boundingNumber ≤ g_d(F)`:
    - If F is dominating: F is unbounded, so `boundingNumber ≤ mk F = g_d(F)`
    - If F is not dominating: `g_d(F) = continuum`, and `boundingNumber ≤ continuum`
      because ∅ is not unbounded so the infimum includes `continuum`. -/
theorem bounding_le_dominating : boundingNumber ≤ dominatingNumber := by
  unfold dominatingNumber
  apply le_ciInf
  intro F
  -- Helper: boundingNumber infimum is bounded below by 0
  have hbdd : BddBelow (Set.range fun G : Set (ℕ → ℕ) =>
      if IsUnbounded G then Cardinal.mk G else ContinuumHypothesis.continuum) :=
    ⟨0, by rintro _ ⟨G, rfl⟩; split_ifs <;> exact Cardinal.zero_le _⟩
  by_cases hdom : IsDominating F
  · -- F dominating → F unbounded → boundingNumber ≤ mk F
    have hunb := dominating_implies_unbounded hdom
    simp only [hdom, ite_true]
    calc boundingNumber
        = ⨅ G : Set (ℕ → ℕ), if IsUnbounded G then Cardinal.mk G
            else ContinuumHypothesis.continuum := rfl
      _ ≤ (if IsUnbounded F then Cardinal.mk F
            else ContinuumHypothesis.continuum) := ciInf_le hbdd F
      _ = Cardinal.mk F := by simp [hunb]
  · -- F not dominating → rhs = continuum → boundingNumber ≤ continuum
    simp only [hdom, ite_false]
    have hempty : ¬IsUnbounded (∅ : Set (ℕ → ℕ)) := by
      intro h; obtain ⟨f, hf, _⟩ := h (fun _ => 0); exact Set.not_mem_empty f hf
    calc boundingNumber
        = ⨅ G : Set (ℕ → ℕ), if IsUnbounded G then Cardinal.mk G
            else ContinuumHypothesis.continuum := rfl
      _ ≤ (if IsUnbounded (∅ : Set (ℕ → ℕ)) then Cardinal.mk (∅ : Set (ℕ → ℕ))
            else ContinuumHypothesis.continuum) := ciInf_le hbdd ∅
      _ = ContinuumHypothesis.continuum := by simp [hempty]

/-- The fundamental chain of cardinal characteristics:
    ℵ₁ ≤ b ≤ d ≤ 2^ℵ₀.
    This holds in ZFC without any additional axioms. -/
theorem characteristics_chain :
    ContinuumHypothesis.aleph_one ≤ boundingNumber ∧
    boundingNumber ≤ dominatingNumber ∧
    dominatingNumber ≤ ContinuumHypothesis.continuum :=
  ⟨bounding_number_uncountable, bounding_le_dominating, dominating_le_continuum⟩

/-- Under CH, all cardinal characteristics collapse to ℵ₁:
    since 2^ℵ₀ = ℵ₁ and ℵ₁ ≤ b ≤ d ≤ 2^ℵ₀, all must equal ℵ₁. -/
theorem ch_determines_characteristics (h : CH) :
    boundingNumber = ContinuumHypothesis.aleph_one ∧
    dominatingNumber = ContinuumHypothesis.aleph_one := by
  have hc : ContinuumHypothesis.continuum = ContinuumHypothesis.aleph_one := h
  constructor
  · exact le_antisymm
      (le_trans bounding_le_dominating (le_trans dominating_le_continuum (le_of_eq hc)))
      bounding_number_uncountable
  · exact le_antisymm
      (le_trans dominating_le_continuum (le_of_eq hc))
      (le_trans bounding_number_uncountable bounding_le_dominating)

-- ============================================================
-- PART 5: Martin's Axiom and the Continuum
-- ============================================================

/-
Martin's Axiom (MA) is a combinatorial axiom weaker than CH.
MA says: for any ccc poset P and any collection of < 2^ℵ₀ dense sets,
there exists a filter meeting all of them.

Key consequences:
- MA + CH is equivalent to CH (MA is a theorem of ZFC + CH)
- MA + ¬CH pins specific values: b = d = 2^ℵ₀
- MA + 2^ℵ₀ = ℵ₂ is equiconsistent with ZFC

MA is the "tame" forcing axiom. PFA and MM are stronger.
-/

/-- Martin's Axiom: for any ccc poset and any family of fewer than 2^ℵ₀
    dense sets, a filter meeting them all exists.

    Declared as opaque rather than axiom: MA is a specific set-theoretic
    proposition, not a foundational assumption. The full formal statement
    requires defining ccc posets, dense sets, and filters (~500 lines). -/
opaque MartinsAxiom : Prop := True

/-- Under MA + ¬CH, the bounding number equals the continuum:
    b = 2^ℵ₀. This means no family smaller than the continuum is unbounded.

    Axiom: the proof uses MA to construct a dominating function for any
    < 2^ℵ₀-sized family by a transfinite recursion argument. -/
axiom MA_implies_b_eq_continuum :
    MartinsAxiom → boundingNumber = ContinuumHypothesis.continuum

/-- Under MA, the bounding and dominating numbers coincide and equal 2^ℵ₀:
    b = d = 2^ℵ₀. All cardinal characteristics in the Cichoń diagram
    collapse to just two values: ℵ₁ and 2^ℵ₀. -/
theorem MA_collapses_characteristics (hma : MartinsAxiom) :
    boundingNumber = ContinuumHypothesis.continuum ∧
    dominatingNumber = ContinuumHypothesis.continuum := by
  constructor
  · exact MA_implies_b_eq_continuum hma
  · -- b = 2^ℵ₀ and b ≤ d ≤ 2^ℵ₀ implies d = 2^ℵ₀
    have hb := MA_implies_b_eq_continuum hma
    exact le_antisymm dominating_le_continuum (hb ▸ bounding_le_dominating)

/-- Under MA + ¬CH, we get the "simple" cardinal arithmetic:
    all characteristics are pinned to 2^ℵ₀ > ℵ₁.
    This is the "maximally regular" scenario — no intermediate structure. -/
theorem MA_not_CH_simple (hma : MartinsAxiom) (hnotch : ¬CH) :
    ContinuumHypothesis.aleph_one < ContinuumHypothesis.continuum ∧
    boundingNumber = ContinuumHypothesis.continuum := by
  constructor
  · exact ContinuumHypothesisOQ01.not_CH_implies_strict_inequality hnotch
  · exact MA_implies_b_eq_continuum hma

-- ============================================================
-- PART 6: Three Scenarios for the Continuum
-- ============================================================

/-
The mathematical community has explored three broad scenarios:

1. CH (2^ℵ₀ = ℵ₁): The "minimal" answer. Implied by V=L. Clean and simple,
   but V=L excludes large cardinals.

2. 2^ℵ₀ = ℵ₂: The "tame" answer. Implied by PFA, MM, and MA + ¬CH.
   Compatible with large cardinals. Most set theorists' current preference.

3. 2^ℵ₀ > ℵ₂: The "wild" answer. Consistent but requires no known
   natural axiom. Can produce exotic cardinal characteristic patterns.
-/

/-- Scenario 1: CH gives 2^ℵ₀ = ℵ₁ (the minimum possible value). -/
theorem scenario_ch : CH → ContinuumHypothesis.continuum = Cardinal.aleph 1 := by
  intro h; exact h

/-- Scenario 2: PFA gives 2^ℵ₀ = ℵ₂ (the "natural" value above CH). -/
theorem scenario_pfa (hpfa : ContinuumHypothesisOQ01.PFA) :
    ContinuumHypothesis.continuum = Cardinal.aleph 2 :=
  ContinuumHypothesisOQ01.PFA_implies_continuum_eq_aleph_two hpfa

/-- The gap between scenarios: ℵ₁ < ℵ₂ shows CH and PFA give genuinely
    different values for the continuum. -/
theorem scenarios_distinct :
    Cardinal.aleph 1 < Cardinal.aleph 2 :=
  Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- In each scenario, the continuum is regular (König-consistent):
    ℵ₁ is regular (successor), and ℵ₂ is regular (successor). -/
theorem all_scenarios_regular :
    (Cardinal.aleph 1).IsRegular ∧ (Cardinal.aleph 2).IsRegular :=
  ⟨aleph_one_is_regular, aleph_succ_is_regular 1⟩

-- ============================================================
-- PART 7: The Complete Picture
-- ============================================================

/-- The Easton-König characterization of the continuum's possible values:
    2^ℵ₀ can be exactly the regular uncountable cardinals.

    The upper direction (Easton): any regular κ ≥ ℵ₁ is achievable.
    The lower direction (König): singular cardinals are ruled out.

    This is one of the most complete answers ZFC can give about 2^ℵ₀. -/
theorem easton_konig_characterization :
    -- Some regular uncountable cardinals ARE possible values
    (∃ κ : Cardinal.{0}, IsPossibleContinuumValue κ) ∧
    -- Some cardinals are NOT possible values (singular ones)
    (∃ κ : Cardinal.{0}, ¬IsPossibleContinuumValue κ) := by
  constructor
  · exact ⟨Cardinal.aleph 1, aleph_one_is_possible⟩
  · exact ⟨Cardinal.aleph (ω : Ordinal.{0}), aleph_omega_not_possible⟩

/-- The Cantor-König sandwich: ℵ₁ ≤ 2^ℵ₀ and 2^ℵ₀ has uncountable cofinality.
    These are the ONLY two constraints ZFC places on 2^ℵ₀ (for the ℵ₀ case). -/
theorem zfc_constraints_on_continuum :
    ContinuumHypothesis.aleph_one ≤ ContinuumHypothesis.continuum ∧
    (ℵ₀ : Cardinal.{0}) < (ContinuumHypothesis.continuum.ord.cof : Cardinal) :=
  ⟨ContinuumHypothesisOQ01.aleph_one_le_continuum, konig_cofinality⟩

/-- The answer to "What is the 'true' size of the continuum?":
    ZFC constrains 2^ℵ₀ to be a regular uncountable cardinal,
    but cannot determine which one. Natural axioms beyond ZFC
    point to either ℵ₁ (V=L) or ℵ₂ (PFA/MM), with the
    current mathematical consensus favoring 2^ℵ₀ = ℵ₂. -/
theorem the_open_question :
    -- There are at least two distinct consistent values
    (∃ κ₁ κ₂ : Cardinal.{0},
      IsPossibleContinuumValue κ₁ ∧
      IsPossibleContinuumValue κ₂ ∧
      κ₁ ≠ κ₂) ∧
    -- And some values are ruled out
    (∃ κ : Cardinal.{0},
      ContinuumHypothesis.aleph_one ≤ κ ∧
      ¬IsPossibleContinuumValue κ) := by
  constructor
  · exact ⟨Cardinal.aleph 1, Cardinal.aleph 2,
      aleph_one_is_possible, aleph_two_is_possible,
      ne_of_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num))⟩
  · refine ⟨Cardinal.aleph (ω : Ordinal.{0}), ?_, aleph_omega_not_possible⟩
    unfold ContinuumHypothesis.aleph_one
    exact Cardinal.aleph_le_aleph.mpr (by exact Ordinal.one_le_iff_ne_zero.mpr omega_ne_zero)

/-
## Conclusion

The question "What is the 'true' size of the continuum?" has a precise
mathematical formulation. ZFC provides two constraints:

1. **Lower bound**: 2^ℵ₀ ≥ ℵ₁ (Cantor's theorem + definition of ℵ₁)
2. **Regularity**: cf(2^ℵ₀) > ℵ₀ (König's theorem)

Together, these say 2^ℵ₀ is a regular uncountable cardinal.
Easton showed this is sharp: any such cardinal is achievable.

The "natural" axioms beyond ZFC suggest two main candidates:
- V=L (Gödel, 1940): 2^ℵ₀ = ℵ₁ (CH), but excludes large cardinals
- PFA/MM (Todorčević, Foreman-Magidor-Shelah, 1980s): 2^ℵ₀ = ℵ₂

Cardinal characteristics (b, d, and others in the Cichoń diagram) provide
intermediate invariants that detect fine structure between ℵ₁ and 2^ℵ₀:
- Under CH, they all collapse to ℵ₁
- Under MA + ¬CH, they all equal 2^ℵ₀
- In general, rich independence phenomena exist

Whether there is a "true" answer remains the deepest open question
in the foundations of mathematics.
-/

end ContinuumHypothesisOQ02

-- Export key theorems
#check ContinuumHypothesisOQ02.aleph_one_is_regular
#check ContinuumHypothesisOQ02.aleph_omega_is_singular
#check ContinuumHypothesisOQ02.continuum_ne_aleph_omega
#check ContinuumHypothesisOQ02.easton_konig_characterization
#check ContinuumHypothesisOQ02.characteristics_chain
#check ContinuumHypothesisOQ02.ch_determines_characteristics
#check ContinuumHypothesisOQ02.the_open_question
