import Proofs.GodelSecondIncompletenessOQ02Companion
import Proofs.GodelSecondIncompletenessOQ02GLSyntax

/-!
# Gödel's Second Incompleteness — S10 ACT: GL→PA translate (realization function)

This companion file is the **S15 ACT** (formerly named "S10 ACT") for the
`godel-second-incompleteness-oq02-oq-02` research slug (Solovay's arithmetical
completeness for GL). It defines the **realization function**
`translate : (PropAtom → Formula) → GLFormula → Formula` bridging GL syntax
(`GodelSecondGLSyntax.GLFormula`, S8 ACT #19146) to PA syntax
(`GodelFirst.Formula`, parent + S2-α Companion #19037).

The realization is parametrized by a propositional atom assignment
`ρ : PropAtom → Formula`. Solovay's arithmetical completeness theorem
universally quantifies over `ρ` (Boolos 1993, §3).

## Purpose

This file unblocks the next two downstream stages without adding any axiom:

- **S7 ACT** (arithmetical soundness of GL): the five-case induction
  `GL_proves φ → ∀ ρ, ⊢ translate ρ φ` dispatches on the `GL_proves`
  constructors (`taut`, `k`, `lob`, `mp`, `nec`). Each case becomes a
  goal in terms of `translate`-applied formulas (see S10 PREP #18678 §3.4).
- **S5 ACT** (Kripke semantics for GL): the predicate
  `forces : KripkeModel → World → GLFormula → Prop` is defined directly on
  `GLFormula` and does not consume `translate`, but the soundness/completeness
  triangle (Solovay 1976) ties Kripke completeness to arithmetical completeness
  via `translate`.

## Per S10 PREP #18678 §3.3

The four recursive cases (atom / falsum / impl / box) map onto the existing
gallery operations:

| GL constructor   | translate clause                                              |
|------------------|---------------------------------------------------------------|
| `.atom n`        | `ρ n`                                                         |
| `.falsum`        | `GodelSecond.falsum` (parent's ⊥, code 0)                     |
| `.impl φ ψ`      | `impl_formula (translate ρ φ) (translate ρ ψ)` (S2-α Companion)|
| `.box φ`         | `Prov (godelNum (translate ρ φ))` (D1 from First)             |

The `box` case unfolds to a `Prov ∘ godelNum`-application, which is exactly
the shape that the parent's `d1_representability` axiom (line 123 of
`GodelSecondIncompletenessOQ02.lean`) addresses. So the `nec` case of
arithmetical soundness reduces to D1 + `translate` unfolding (no new axiom).

## What this file does NOT do

- **Does not state or prove arithmetical soundness.** That is S7 ACT scope.
  The five-case induction over `GL_proves` (`taut`, `k`, `lob`, `mp`, `nec`)
  will each invoke this file's `translate` and its equation lemmas (§2 below).
- **Does not redefine `GLFormula.not`-style derived connectives.** The single
  derived `translate_not` simp-lemma (§3 below) is included as a sanity check
  that the simp normal form composes through `GLFormula.not = .impl _ .falsum`.
- **Does not introduce any new axioms.** All four cases reduce to existing
  gallery defs (`impl_formula`, `Prov`, `godelNum`, `falsum`).

## Status

- **0 sorries**
- **0 new axioms** (this is the key axiom-integrity win — it consumes the
  S2-α Companion's `impl_formula` def without introducing fresh assumptions)
- **5 derived theorems** (4 equation simp-lemmas + 1 sanity `translate_not`)
- Unblocks S7 ACT (arithmetical soundness induction); orthogonal to S4 ACT
  (Löb's theorem, +1 axiom).

## References

- Boolos, G. (1993). *The Logic of Provability*. Cambridge University Press.
  Chs. 1–3 (esp. §3, Solovay's completeness).
- Solovay, R. (1976). "Provability interpretations of modal logic". *Israel J. Math.*
- S10 PREP #18678 (researcher, 2026-05-13) §3.3 — proposed design.
- S2-α ACT #19037 (researcher, merged 2026-05-19) — defines `impl_formula`.
- S8 ACT #19146 (researcher, merged 2026-05-14) — defines `GLFormula`.
- S14 STATE-SYNC #20656 (researcher-1, merged 2026-05-25) — top-3 priority
  reorder elevating this S10 ACT to #1 on axiom-integrity grounds.
-/

open GodelFirst GodelSecond GodelSecondGLSyntax

namespace GodelSecondTranslate

-- ============================================================
-- PART 1: The realization function
-- ============================================================

/-- The realization function bridging propositional modal logic GL to
    Peano-Arithmetic-style provability syntax.

    Parametrized by a propositional atom assignment `ρ : PropAtom → Formula`,
    `translate ρ` recursively maps a `GLFormula` to a `GodelFirst.Formula`:

    | GL constructor   | translate clause                                              |
    |------------------|---------------------------------------------------------------|
    | `.atom n`        | `ρ n`                                                         |
    | `.falsum`        | `GodelSecond.falsum`                                          |
    | `.impl φ ψ`      | `impl_formula (translate ρ φ) (translate ρ ψ)`                |
    | `.box φ`         | `Prov (godelNum (translate ρ φ))`                             |

    Per S10 PREP #18678 §3.3. -/
def translate (ρ : PropAtom → Formula) : GLFormula → Formula
  | .atom n      => ρ n
  | .falsum      => GodelSecond.falsum
  | .impl φ ψ    => impl_formula (translate ρ φ) (translate ρ ψ)
  | .box φ       => Prov (godelNum (translate ρ φ))

-- ============================================================
-- PART 2: Equation simp-lemmas
-- ============================================================

/-- `translate` on an atom is just the assignment. -/
@[simp] theorem translate_atom (ρ : PropAtom → Formula) (n : PropAtom) :
    translate ρ (.atom n) = ρ n := rfl

/-- `translate` of GL's `falsum` is the parent's `falsum`. -/
@[simp] theorem translate_falsum (ρ : PropAtom → Formula) :
    translate ρ .falsum = GodelSecond.falsum := rfl

/-- `translate` distributes over `impl` via `impl_formula`. -/
@[simp] theorem translate_impl (ρ : PropAtom → Formula) (φ ψ : GLFormula) :
    translate ρ (.impl φ ψ) =
      impl_formula (translate ρ φ) (translate ρ ψ) := rfl

/-- `translate` of `box φ` is `Prov` applied to the Gödel code of `translate ρ φ`.

    This is the clause that bridges to D1 (`d1_representability` in the parent
    file): when `GL_proves φ`, applying D1 to `translate ρ φ` gives a proof of
    `Prov (godelNum (translate ρ φ))`, which by this equation equals
    `translate ρ (.box φ)`. -/
@[simp] theorem translate_box (ρ : PropAtom → Formula) (φ : GLFormula) :
    translate ρ (.box φ) =
      Prov (godelNum (translate ρ φ)) := rfl

-- ============================================================
-- PART 3: Sanity / derived theorems
-- ============================================================

/-- The derived `GLFormula.not` is mapped to `impl_formula _ falsum` (i.e.,
    `_ →ᶠ falsum`). Sanity check that the simp normal form composes through
    `GLFormula.not = .impl _ .falsum` (from `GodelSecondGLSyntax` line 63). -/
@[simp] theorem translate_not (ρ : PropAtom → Formula) (φ : GLFormula) :
    translate ρ φ.not = impl_formula (translate ρ φ) GodelSecond.falsum := rfl

end GodelSecondTranslate
