/-
  Königsberg… no — Algebraic Numbers Countable, OQ-02 OQ-05:
  Definable Reals are Countable (First-Order Base Case)

  ## Open Question (algebraic-numbers-countable-oq-02-oq-05)

  The parent chain establishes that ℝ is uncountable (Cantor 1874) while the
  "nameable" subfamilies sit below it in cardinality:

      ℚ  ⊊  algebraic  ⊊  computable  ⊊  ℝ
      ↑          ↑            ↑        ↑
      ℵ₀         ℵ₀           ℵ₀       𝔠

  Sibling OQ-04 added the *computable* reals (countable, named by Turing-machine
  codes). The natural next layer is the **definable** reals: the raw open
  question asks whether *each level of the analytical hierarchy of definable
  reals is countable*.

  ## What is proved here (and what is deferred — read this honestly)

  The literal open question is about the **analytical hierarchy** — Σ¹ₙ
  definability in *second-order* arithmetic (quantifying over sets of naturals /
  reals). Mathlib currently has no formalization of second-order logic or the
  analytical hierarchy, so that statement is genuinely blocked (it would require
  building the second-order syntax, satisfaction, and the Σ¹ₙ stratification from
  scratch — well over a thousand lines of foundational logic). See the
  `## Deferred` note at the end.

  What *is* fully formalizable today — and is the honest **base case** of that
  hierarchy — is the **first-order** (arithmetical-flavoured) definability layer,
  using Mathlib's `FirstOrder.Language` model theory. This file proves, for an
  **arbitrary countable first-order language** `L` and **any** `L`-structure on
  ℝ:

  1. `Countable (L.Formula (Fin 1))` — a countable language has only countably
     many one-variable formulas (derived from `BoundedFormula.encoding`).

  2. `foDefinable_reals_countable` — the set of reals that are ∅-definable
     (uniquely pinned down by a single one-variable formula) is countable.
     The proof is a pure counting argument: distinct definable reals need
     distinct defining formulas, so the definable reals inject into the
     countable formula set.

  3. `exists_non_foDefinable_real` / `non_foDefinable_reals_uncountable` — the
     cardinality punchline: since ℝ is uncountable, *most* reals are **not**
     first-order definable. This is the definability analogue of "most reals are
     transcendental" (parent OQ-03) and a concrete face of the Skolem/Tarski
     observation that a countable language cannot name a continuum of points.

  ## Why this is the right general statement

  The theorem is deliberately stated for an *arbitrary* countable language and an
  *arbitrary* structure on ℝ, because that is the uniform engine behind every
  entry in the hierarchy above:

  * Instantiated at the language of ordered rings, Tarski's quantifier
    elimination identifies the ∅-definable reals with the **real algebraic
    numbers**, so this theorem *subsumes* the parent result
    "algebraic reals are countable".
  * Any countable expansion of the language (adding exp, a truth predicate for a
    fixed countable set of constants, …) still yields only countably many
    definable reals — the same one-line counting argument.

  So rather than re-proving one instance, we isolate the single reason all such
  levels are countable: **countable syntax ⟹ countably many definitions**.

  ## Deferred (the genuinely open remainder)

  The full analytical hierarchy (Σ¹ₙ, second-order definability) is *not* proved
  here and is blocked pending a Mathlib formalization of second-order logic. The
  recommended path is exactly the argument above lifted to second-order syntax:
  once the Σ¹ₙ formula sets are shown countable, the identical injection gives
  countability of each analytical-hierarchy level. This file supplies the
  first-order base case and the reusable counting lemma.

  References:
  - Tarski (1951): quantifier elimination for real closed fields.
  - Skolem (1922): the Löwenheim–Skolem observations on countable languages.
  - Cantor (1874): ℝ is uncountable (parent, algebraic-numbers-countable-oq-02).
-/

import Mathlib.ModelTheory.Encoding
import Mathlib.ModelTheory.Semantics
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic

open FirstOrder Language

namespace AlgebraicNumbersCountableOQ02OQ05

variable (L : Language)
  [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]

/-
══════════════════════════════════════════════════════════════
PART I: A COUNTABLE LANGUAGE HAS COUNTABLY MANY ONE-VARIABLE FORMULAS
══════════════════════════════════════════════════════════════

  `BoundedFormula.encoding` encodes each bounded formula as a finite list over
  the alphabet `Γ = (Σ k, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ)`.
  When the language is countable, `Γ` is countable, hence so is the list type,
  and the injectivity of the encoding transports countability back to formulas.
-/

/-- All bounded formulas over one free variable (of every nesting depth) form a
    countable type, for a countable language. -/
instance instCountableSigmaBoundedFormula :
    Countable (Σ n, L.BoundedFormula (Fin 1) n) := by
  -- Register `Countable Γ` at the (definitionally equal) explicit sum type so the
  -- `Countable (List Γ)` instance the encoding needs can be synthesised.
  haveI hΓ : Countable (BoundedFormula.encoding (L := L) (α := Fin 1)).Γ :=
    (inferInstance :
      Countable ((Σ k, L.Term ((Fin 1) ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ)))
  exact (BoundedFormula.encoding (L := L) (α := Fin 1)).encode_injective.countable

/-- **Countably many one-variable formulas.** A countable first-order language
    has only countably many `Formula (Fin 1)`s (the depth-`0` bounded formulas). -/
instance instCountableFormulaFinOne : Countable (L.Formula (Fin 1)) :=
  Function.Injective.countable
    (f := fun φ : L.Formula (Fin 1) =>
      (⟨0, φ⟩ : Σ n, L.BoundedFormula (Fin 1) n))
    (fun _ _ h => by simpa using h)

/-
══════════════════════════════════════════════════════════════
PART II: DEFINABLE REALS ARE COUNTABLE
══════════════════════════════════════════════════════════════ -/

variable [L.Structure ℝ]

/-- A real `r` is **(∅-)definable** over the structure `(ℝ, L)` if some single
    one-variable formula is satisfied by `r` and by `r` alone. This is the
    first-order (arithmetical-style) definability whose analytical-hierarchy
    generalisation is the raw open question. -/
def FODefinable (r : ℝ) : Prop :=
  ∃ φ : L.Formula (Fin 1), ∀ x : ℝ, φ.Realize ![x] ↔ x = r

/-- **Main theorem: the ∅-definable reals are countable.**

    Counting argument: each definable real carries (by choice) a formula that it
    uniquely satisfies; two reals sharing such a formula would each be its unique
    realiser and hence be equal. The definable reals therefore inject into the
    countable set of one-variable formulas. -/
theorem foDefinable_reals_countable : {r : ℝ | FODefinable L r}.Countable := by
  rw [← Set.countable_coe_iff]
  apply Function.Injective.countable
    (f := fun x : ↥{r : ℝ | FODefinable L r} => x.2.choose)
  intro a b hf
  simp only [] at hf
  have ha := a.2.choose_spec        -- ∀ x, (φₐ).Realize ![x] ↔ x = a
  have hb := b.2.choose_spec         -- ∀ x, (φ_b).Realize ![x] ↔ x = b
  rw [← hf] at hb                    -- φ_b = φₐ, so hb is now about φₐ
  refine Subtype.ext ?_
  have h1 := ha a.1                  -- (φₐ).Realize ![a] ↔ a = a
  have h2 := hb a.1                  -- (φₐ).Realize ![a] ↔ a = b
  rw [h1] at h2                      -- a = a ↔ a = b
  simpa using h2.mp rfl

/-
══════════════════════════════════════════════════════════════
PART III: MOST REALS ARE NOT FIRST-ORDER DEFINABLE
══════════════════════════════════════════════════════════════

  ℝ is uncountable, but only countably many reals are definable, so definability
  cannot exhaust ℝ. This is the definability analogue of the parent's
  "the transcendental reals are uncountable".
-/

/-- **There is an undefinable real.** No countable language can name every real. -/
theorem exists_non_foDefinable_real : ∃ r : ℝ, ¬ FODefinable L r := by
  by_contra h
  push_neg at h
  have huniv : {r : ℝ | FODefinable L r} = Set.univ :=
    Set.eq_univ_of_forall h
  have hcount := foDefinable_reals_countable L
  rw [huniv, Set.countable_univ_iff] at hcount
  exact (not_countable (α := ℝ)) hcount

/-- **The undefinable reals are uncountable.** Sharpening
    `exists_non_foDefinable_real`: definability misses not just one real but a
    full continuum's worth. -/
theorem non_foDefinable_reals_uncountable :
    ¬ {r : ℝ | ¬ FODefinable L r}.Countable := by
  intro h
  have hcov : {r : ℝ | FODefinable L r} ∪ {r : ℝ | ¬ FODefinable L r} = Set.univ := by
    ext r; by_cases hr : FODefinable L r <;> simp [hr]
  have huniv : (Set.univ : Set ℝ).Countable := by
    rw [← hcov]; exact (foDefinable_reals_countable L).union h
  rw [Set.countable_univ_iff] at huniv
  exact (not_countable (α := ℝ)) huniv

end AlgebraicNumbersCountableOQ02OQ05
