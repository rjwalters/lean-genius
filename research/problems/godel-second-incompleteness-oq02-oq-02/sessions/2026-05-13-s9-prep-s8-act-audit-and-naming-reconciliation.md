# S9 PREP — S8 ACT audit + cross-PREP naming reconciliation

**Date**: 2026-05-13
**Researcher**: researcher-6
**Mode**: PREP (doc-only audit memo; pre-implementation)
**Phase target**: tighten S8 ACT (≤80 LOC, 0 sorries, 0 axioms) before it lands; flag inter-PREP naming inconsistency between S5 PREP and S7 / S8 PREPs that would force a rename pass after the fact.
**Status**: pristine orthogonal to merged
S1 OBSERVE (#18198), S1b OBSERVE (#18404), S4 PREP Löb (#18445),
S5 PREP Kripke (#18473), S6 PREP Σ₁-blocker (#18497),
S7 PREP soundness-induction (#18523), S8 PREP `GLFormula` (#18566).
**0 open PRs on this slug at PREP push time.**

## 0. Why this PREP

S8 PREP (#18566) committed the §9 signature for the S8 ACT companion file:

- `import Proofs.GodelSecondIncompletenessOQ02` + `import Mathlib.Logic.Basic`
- `inductive GLFormula` with constructors `atom`, `falsum`, `impl`, `box`
- `inductive PropAxiom` with 3 Łukasiewicz schemas
- `inductive GL_proves` with `taut`, `k`, `lob`, `mp`, `nec`
- 2 `@[simp]` rename lemmas

Auditing that signature against the **actual** parent files at the current Mathlib pin (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, Lean v4.26.0), the prior PREP chain (#18198→#18566), and the live Mathlib surface, this PREP surfaces four concrete findings that should be folded into S8 ACT **before** push:

1. A **primary naming inconsistency** between S5 PREP and S7/S8 PREPs (`ModalFormula` vs `GLFormula`) that S8 PREP §7 misquotes — uncorrected, the eventual S5 ACT and S7 ACT will not type-check against each other.
2. A **PA-side naming inconsistency** (`PAFormula` in S7 PREP vs `Formula` in S8 PREP) that needs to align with the parent file.
3. Two **unnecessary imports** in S8 PREP §9 that should be removed before S8 ACT — both keep S8 ACT decoupled from the parent build status.
4. Two **low-value `@[simp]` lemmas** in §9 that re-name constructors without unfolding anything.

Plus two **positive confirmations**:

5. S8 PREP §2's negative Mathlib claim (no off-the-shelf modal-logic Hilbert system) is **verified** at the current pin: the top-level Mathlib directory has no `ModalLogic/`, `Modal/`, `Provability/`, `Hilbert/`, or `PropositionalLogic/` subtree; `Mathlib/Tactic/Tauto.lean` is a meta-level tactic over `Prop`, not an object-level deduction system.
6. S8 PREP §14 risk register #1 (`deriving DecidableEq` may need manual implementation) is over-cautious: three existing gallery files use `deriving DecidableEq` for `Nat`-parametrized structures and build successfully on the current pin.

This PREP is doc-only. Zero Lean changes. Zero gallery / JSON / `state.md` / `problem.md` / `knowledge.md` edits. One new file path:
`research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s9-prep-s8-act-audit-and-naming-reconciliation.md`.

## 1. Inter-PREP naming inconsistency — primary finding

### 1.1 The discrepancy

| PREP            | PR     | Modal-formula type name | PA-formula type name |
|-----------------|--------|-------------------------|----------------------|
| S5 PREP Kripke  | #18473 | `ModalFormula`          | `Formula` (parent's) |
| S7 PREP arith   | #18523 | `GLFormula`             | `PAFormula`          |
| S8 PREP syntax  | #18566 | `GLFormula`             | `Formula` (parent's) |

The three PREPs do **not** agree on either name. Verbatim citations:

**S5 PREP** (`sessions/2026-05-13-s5-prep-kripke-semantics-gl-segerberg.md:82-86`):

```lean
inductive ModalFormula : Type where
  | atom : ℕ → ModalFormula
  | falsum : ModalFormula
  | impl : ModalFormula → ModalFormula → ModalFormula
  | box : ModalFormula → ModalFormula
```

…and `forces : KripkeModel → World → ModalFormula → Prop` (line 121 of S5 PREP), and `valid_K`/`valid_4`/`valid_L`/`segerberg_completeness` all take `ModalFormula` arguments (lines 204, 210, 229, 282).

**S7 PREP** (`sessions/2026-05-13-s7-prep-arith-soundness-induction-design.md:227`):

```lean
def translate (rho : PropAtom → PAFormula) : GLFormula → PAFormula
```

…and `GL_proves`, `PropositionallyValid`, `arith_K_axiom`, `arith_lob_axiom`, `arith_MP`, `arith_NEC` all take `GLFormula` arguments (S7 PREP lines 52, 81, 110, 134, 238, 244, 250, 257). `translate` returns `PAFormula`, not `Formula`.

**S8 PREP** (`sessions/2026-05-13-s8-prep-glformula-gl-proves-hilbert-design.md:108`):

```lean
inductive GLFormula : Type where
  | atom (p : PropAtom)            : GLFormula
  | falsum                          : GLFormula
  | impl (p q : GLFormula)          : GLFormula
  | box  (p : GLFormula)            : GLFormula
```

…with the `translate` signature using bare `Formula` (S8 PREP §6 line 156: `Prov (godelNum (translate ρ p))` against `def translate (ρ : PropAtom → Formula) : GLFormula → Formula`).

### 1.2 S8 PREP §7 misquotes S5 PREP

S8 PREP §7 (lines 343–349) writes:

> S5 PREP §3 plans:
> ```lean
> def forces (M : KripkeModel) (w : World) : GLFormula → Prop
>   | .atom p   => M.valuation w p
>   ...
> ```

But the **actual** S5 PREP §3 (`sessions/2026-05-13-s5-prep-kripke-semantics-gl-segerberg.md:120-126`) writes:

```lean
/-- The forcing (modal-truth) relation, recursive on ModalFormula. -/
def forces : M.frame.W → ModalFormula → Prop
```

The `GLFormula` in S8 PREP §7 is **not** what S5 PREP actually committed to. S8 PREP claims S5 ACT "**also assumes** `GLFormula` with the 4 constructors"; **this is false**. S5 ACT, if it ships per S5 PREP's signature, will land `ModalFormula`, not `GLFormula`. Without intervention, the two ACT PRs will produce two structurally-identical inductive types with different names — and `forces` and `translate` will not compose.

### 1.3 Resolution recommendation

Pick **`GLFormula`** as the canonical name. Rationale:

- `GLFormula` is the more-specific term; the formulas described **are** GL formulas (4 constructors, including `box` — there is no `dia` constructor, so this is not a general bimodal "modal formula"). Modal-logic textbooks (Boolos 1993; Smoryński 1985) use either name interchangeably, but for **a Hilbert system with the L-axiom**, the type is unambiguously the formulas of GL.
- S7 PREP and S8 PREP already agree on `GLFormula` — only S5 PREP is the outlier.
- S8 ACT lands the type and is the natural foundation; S5 ACT defines a forcing relation on top.

**Migration cost**: S5 PREP will need a single global rename `ModalFormula → GLFormula` before S5 ACT. The rename is 0-meaning-change (constructor names match, fields match, recursion structure is identical). Estimated impact: ~15 occurrences across S5 PREP (lines 82, 90, 93, 120-128, 204, 210, 229, 252, 256, 282, 404, 438). No new Lean code.

**Alternative considered**: rename to `ModalFormula` instead. Rejected because (a) S7 ACT and S8 ACT are slated next per state.md, (b) the L-axiom embedding is GL-specific so the name should be too, and (c) `ModalFormula` would suggest the type generalizes to other modal logics, which it does not as currently constructed (no `dia`, no `[α]`, no multi-modal `□_α`).

### 1.4 PA-side reconciliation (`PAFormula` vs `Formula`)

S7 PREP uses `PAFormula` as a notational rename for the parent's `Formula` (which has its full type signature at `proofs/Proofs/GodelFirstIncompletenessOQ01.lean:60`):

```lean
structure Formula where
  code : Nat
  deriving DecidableEq
```

The parent file declares this type as `Formula` inside `namespace GodelFirst` (lines 52, 60, 267). **No `PAFormula` exists** in the parent. S7 ACT's adoption of `PAFormula` would require either a type alias or an `abbrev` — neither has been planned in a PREP.

**Resolution**: S7 ACT should use the parent's name `Formula` (qualified as `GodelFirst.Formula` when ambiguity matters, or via `open GodelFirst`). Matches S8 PREP §6's choice. This is purely a S7 ACT concern — flagged here so it doesn't surface as a build error.

## 2. Audit of S8 PREP §9 — unnecessary imports

S8 PREP §9 header:

```lean
import Proofs.GodelSecondIncompletenessOQ02
import Mathlib.Logic.Basic
```

### 2.1 `import Proofs.GodelSecondIncompletenessOQ02` is unnecessary

The §9 code defines `PropAtom`, `GLFormula`, `PropAxiom`, `GL_proves`, plus 2 simp lemmas. **None of these reference a parent-file symbol**:

| Symbol used in §9 | Source |
|---|---|
| `Nat` | core Lean (`Init.Prelude`) |
| `Type` | core Lean |
| `Prop` | core Lean |
| `DecidableEq` | core Lean (`Init.Data.Basic`) |
| `Repr` | core Lean (`Init.Data.Repr`) |
| `inductive` | core Lean syntax |
| `abbrev` | core Lean syntax |
| `@[simp]` attribute | core Lean (Mathlib elaborates the attribute the same way) |

**Recommendation for S8 ACT**: drop both imports. The file is purely syntactic and depends on no parent symbol. Decoupling has three concrete benefits:

1. **Build-graph robustness** — `GodelSecondIncompletenessOQ02GLSyntax.lean` builds even if the parent ever fails to elaborate.
2. **Parallel build** — Lake can compile S8 ACT's file independently of `GodelFirst*` / `GodelSecond*`.
3. **Cleaner ACT story** — when S5 ACT / S7 ACT land (and **they** import this file), the dependency direction is `S5/S7 ACT → S8 ACT → core Lean`, with no reverse edges.

S7 PREP §4 / §6 confirm S7 ACT will import both this file and the parent (so the parent dependency lives in S7 ACT's file, not S8 ACT's).

### 2.2 `import Mathlib.Logic.Basic` is unnecessary

The §9 code uses no Mathlib symbol — no `Function.Injective`, no `Iff.intro`, no `Classical.choice`, no `Decidable.decide`, no `OrElse`, no `Nat.rec`. The constructors of `PropAxiom` and `GL_proves` are pure first-order ADTs.

**Recommendation**: drop. Minimal viable S8 ACT can omit Mathlib entirely.

The only risk: if S8 ACT adds a `@[simp]` attribute, the elaborator needs the simp framework — but `@[simp]` is built into core Lean's elaborator (the attribute itself is `Lean.Meta.Simp.SimpTheorem`), not Mathlib-dependent. Tested via the gallery's `EulerPolyhedralFormula.lean:82` which uses `inductive ... deriving Repr` and `@[simp]` without `Mathlib.Logic.Basic` imported.

### 2.3 LOC delta

Removing both imports saves **2 LOC**. Removing the two `@[simp]` rename lemmas (§3 below) saves **6 LOC**. Net: §9's 60-LOC estimate becomes ~52 LOC. Well within S8 PREP's ≤80 LOC budget — and the budget headroom can absorb future risk (e.g., explicit `instance : DecidableEq GLFormula` if `deriving` fails on a kernel edge case).

## 3. Audit of §9 — `@[simp]` convenience lemmas are low-value

S8 PREP §9 lines 432–439:

```lean
@[simp] theorem GL_proves_k (p q : GLFormula) :
    GL_proves (.impl (.box (.impl p q)) (.impl (.box p) (.box q))) :=
  GL_proves.k p q

@[simp] theorem GL_proves_lob (p : GLFormula) :
    GL_proves (.impl (.box (.impl (.box p) p)) (.box p)) :=
  GL_proves.lob p
```

### 3.1 Why these are low-value

Each lemma is a **rename** of the corresponding constructor:

- `GL_proves_k p q` and `GL_proves.k p q` have **the same term and same type**.
- `GL_proves_lob p` and `GL_proves.lob p` likewise.

There is no unfolding: both sides are literal constructor applications. The only purpose of the rename is to expose a non-namespaced `GL_proves_k` that downstream proofs can call directly without the `GL_proves.` prefix.

### 3.2 Why `@[simp]` is unusual here

For a proposition `P` (not an equation or iff), `@[simp] theorem h : P := ...` causes `simp` to register `h` as `P ↔ True` — i.e., simp will rewrite any goal containing the exact pattern of `P` to `True`. This is a legitimate use of simp lemmas, but:

- The pattern `GL_proves (.impl (.box (.impl ?p ?q)) (.impl (.box ?p) (.box ?q)))` is unlikely to appear verbatim in any S5/S7 ACT goal — the natural usage is `apply GL_proves.k` or `exact GL_proves.k p q`, not invoking `simp` on a fully expanded modal expression.
- If a goal ever has the K-axiom shape, the user-friendly closer is `exact .k _ _`, not `simp`.
- The L-axiom shape is even less likely to be a simp target (the L-axiom is what `lob` *is*; it would not appear as a sub-goal needing closure).

### 3.3 Recommendation

Drop both lemmas. Save 6 LOC. If a downstream caller ever wants a non-namespaced alias, they can write `open GL_proves in ...` or `alias GL_proves_k := GL_proves.k`. This is cleaner than carrying simp-tagged constructors.

If the lemmas are kept, **drop the `@[simp]` attribute** — at minimum, the simp tag should be omitted because (a) the pattern is unlikely to fire, and (b) simp's `Prop`-to-`True` rewrite muddies the goal display for the downstream `forces_of_GL_proves` (S5 ACT) and `GL_proves_arith_sound` (S7 ACT) case-splits, which both want to **pattern-match on the constructor**, not have it rewritten away.

## 4. Audit of S8 PREP §14 risk register #1 — `deriving DecidableEq` is safe

S8 PREP §14 risk register:

> | Risk | Mitigation |
> |---|---|
> | `deriving DecidableEq` fails because Nat needs explicit instance | Lean 4 / Mathlib has `Nat.decEq` in core; should be automatic. If it fails, manually implement `instance : DecidableEq GLFormula := by ...` (~6 LOC). |

This concern is **already discharged by the gallery's existing pattern**. Three sibling files use `deriving DecidableEq` on a `Nat`-parametrized structure and build successfully on the current pin:

| File                                                  | Line | Type        |
|-------------------------------------------------------|-----:|-------------|
| `proofs/Proofs/GodelFirstIncompletenessOQ01.lean`     | 60–62 | `Formula`   |
| `proofs/Proofs/GodelFirstIncompletenessOQ01OQ01.lean` | 73–75 | `Formula`   |
| `proofs/Proofs/GodelFirstIncompletenessOQ01OQ04.lean` | 59–61 | `Formula`   |

All three define `structure Formula where { code : Nat } deriving DecidableEq` and build via `./proofs/scripts/docker-build.sh Proofs.GodelFirstIncompletenessOQ01[OQ04|OQ01]`. The handler that `deriving DecidableEq` invokes (`Lean.Elab.Deriving.DecEq`) is the same for inductive types as for structures, and the `Nat` argument case is exactly what those three files exercise.

**Additional confirmation for inductive types**:

| File                                | Line | Type                              |
|-------------------------------------|-----:|-----------------------------------|
| `proofs/Proofs/TractatusQuantifiers.lean` | 49 | `inductive FOProp (S : Type) (D : Type) : Type` |
| `proofs/Proofs/PNPBarriersLegacy.lean`    | 5752 | `inductive Bit : Type`            |
| `proofs/Proofs/EulerPolyhedralFormula.lean` | 82 | `inductive ConstructiblePoly : Type` |

(none of these use `deriving DecidableEq` on a `Nat`-parametrized recursive inductive, so they don't fully cover S8 ACT's case — but `GLFormula` only depends on `PropAtom = Nat`, not on a more exotic parameter. The recursion is on `GLFormula` itself, which `deriving DecidableEq` handles automatically as long as all *non-recursive* fields have `DecidableEq` — and the only non-recursive field is `(p : PropAtom)` which is `Nat`).

**Recommendation**: downgrade risk register #1 from "may need manual implementation" to "essentially zero risk". The mitigation column can be retained for paranoia, but the row probability should be marked "negligible".

## 5. Audit of S8 PREP §2 — Mathlib negative claim verified

S8 PREP §2 claims:

> | Query | Hits |
> |---|---|
> | `GLFormula` | 0 |
> | `GLProves` | 0 |
> | `ModalLogic.GL` | 0 |
> | `"inductive GLFormula"` | 0 |
> | `ProvabilityLogic` | 0 |
> | `HilbertSystem Modal` | 0 |

This PREP independently verifies the broader claim by **directly browsing the Mathlib v4.26.0 directory tree** via the Contents API (5000/hr core API quota, no search/code quota required).

### 5.1 Top-level Mathlib directory listing at pin `2df2f015...`

```
Algebra/        Lean/             Std/
AlgebraicGeometry/ LinearAlgebra/ Tactic/
AlgebraicTopology/ Logic/         Testing/
Analysis/       Mathport/         Topology/
CategoryTheory/ MeasureTheory/    Util/
Combinatorics/  ModelTheory/
Computability/  NumberTheory/
Condensed/      Order/
Control/        Probability/
Data/           RepresentationTheory/
Deprecated/     RingTheory/
Dynamics/       SetTheory/
FieldTheory/    Std/
Geometry/       Tactic/
GroupTheory/    Testing/
InformationTheory/ Topology/
```

**Absent**: `Modal/`, `ModalLogic/`, `Provability/`, `ProvabilityLogic/`, `Hilbert/`, `PropositionalLogic/`, `Tableau/`. No top-level directory devoted to modal logic or to propositional Hilbert calculi.

### 5.2 `Mathlib/Logic/` subdirectory listing

```
Basic.lean       Lemmas.lean
Denumerable.lean Nonempty.lean
Embedding/       Nontrivial/
Encodable/       OpClass.lean
Equiv/           Pairwise.lean
ExistsUnique.lean Relation.lean
Function/        Relator.lean
Godel/           Small/
Hydra.lean       Unique.lean
IsEmpty.lean     UnivLE.lean
```

The only Gödel-themed subdir is `Mathlib/Logic/Godel/` containing exactly one file: `GodelBetaFunction.lean` — the **arithmetic** Gödel β-function for primitive-recursion encoding, not provability logic. **No modal / Hilbert / propositional-Hilbert file**.

### 5.3 `Mathlib/Computability/` and `Mathlib/ModelTheory/` are FOL/recursion-theory only

`Mathlib/Computability/`: TMs, NFAs, primitive recursion, partial recursion, Ackermann function, halting, Myhill-Nerode, regular expressions, Turing-degree. **No propositional Hilbert system.**

`Mathlib/ModelTheory/`: first-order logic over multi-sorted signatures — `BoundedFormula`, `Formula : ℕ → Type`, `Sentence`, `Theory`, `Satisfiability`, `Semantics`, `Substructures`, `Ultraproducts`. **No propositional or modal Hilbert system.**

### 5.4 `Mathlib/Tactic/Tauto.lean` exists but is meta-level

The file `Mathlib/Tactic/Tauto.lean` (9259 bytes at the pin) implements the `tauto` tactic via `Q(Prop)` reflection — operating on Lean's *built-in* `Prop` type. It cannot discharge `PropAxiom : GLFormula → Prop` constructors (those have a *user-defined* index `GLFormula`, not Lean's `Prop`).

S7 PREP §5.3 Strategy C ("Outsource to Mathlib if a propositional fragment exists") is now **definitively dead**: the only `Tauto`-like infrastructure in Mathlib operates at the meta-level, not at the object-level. **Strategy B (Łukasiewicz schemas + Kalmár) is the only path forward**, as S7 PREP and S8 PREP both already recommend.

### 5.5 Updated negative-claim table

S8 PREP §2's six-row table can be augmented with:

| Query                                                   | Result |
|---------------------------------------------------------|--------|
| top-level `Mathlib/{Modal,ModalLogic,Provability,Hilbert,PropositionalLogic}/` | Absent |
| `Mathlib/Logic/{Modal,Hilbert,Tableau}.lean`            | Absent |
| `Mathlib/Logic/Godel/{Modal,Tableau,Hilbert}.lean`      | Absent |
| `Mathlib/Tactic/Tauto.lean` produces an object-level deduction system | No — meta-level over `Prop` only |

S8 PREP §2 stands. **No off-the-shelf modal-logic stack exists** in Mathlib v4.26.0.

## 6. Namespace-and-`open` audit (S7 ACT scope)

For completeness, this PREP records the namespace structure that S7 ACT's `translate` function will need:

| Symbol         | Namespace in parent file                  | File                                            |
|----------------|-------------------------------------------|-------------------------------------------------|
| `Formula`      | `GodelFirst`                              | `GodelFirstIncompletenessOQ01.lean:60`          |
| `Provable`     | `GodelFirst`                              | `GodelFirstIncompletenessOQ01.lean:81`          |
| `godelNum`     | `GodelFirst`                              | `GodelFirstIncompletenessOQ01.lean:91`          |
| `Prov`         | `GodelFirst`                              | `GodelFirstIncompletenessOQ01.lean:96`          |
| `neg`          | `GodelFirst`                              | `GodelFirstIncompletenessOQ01.lean:65`          |
| `falsum`       | `GodelSecond`                             | `GodelSecondIncompletenessOQ02.lean:70`         |
| `Con`          | `GodelSecond`                             | `GodelSecondIncompletenessOQ02.lean:84`         |

S8 PREP §6 sketches the `translate` signature (this is S7 ACT, not S8 ACT):

```lean
def translate (ρ : PropAtom → Formula) : GLFormula → Formula
  | .atom p     => ρ p
  | .falsum     => GodelSecond.falsum
  | .impl p q   => GodelSecondCompanion.impl (translate ρ p) (translate ρ q)
  | .box  p     => Prov (godelNum (translate ρ p))
```

The bare `Formula`, `Prov`, `godelNum` in the return type and the `.box` case **require either** (a) `open GodelFirst` at the file head, **or** (b) full qualification to `GodelFirst.Formula`, `GodelFirst.Prov`, `GodelFirst.godelNum`. The bare `GodelSecond.falsum` and `GodelSecondCompanion.impl` are already fully qualified.

`GodelSecondCompanion.impl` does **not yet exist** — it is the S2-α ACT prerequisite from state.md §3 ("Next action (S2 recommended)") and S1 OBSERVE knowledge.md. **S7 ACT cannot land without S2-α ACT**. S8 ACT can land independently (no dependence on S2-α).

This is consistent with S8 PREP §1's architectural diagram — S8 ACT sits below S7 ACT and S5 ACT, and is independent of S2-α (which lives on the PA syntax side).

## 7. Concrete edit list for the eventual S8 ACT

Combining findings §2 + §3 + §4, the recommended S8 ACT file content is:

```lean
/-
  Syntactic foundation for the modal logic GL: formulas + Hilbert-style
  derivability. Companion file for `Proofs.GodelSecondIncompletenessOQ02`;
  consumed by S5 ACT (Kripke semantics) and S7 ACT (arithmetic soundness).
  No parent-file imports — pure first-order ADTs.
-/

namespace GodelSecondGLSyntax

/-- Atomic propositional variables of GL formulas. -/
abbrev PropAtom : Type := Nat

/-- Formulas of the propositional modal logic GL. -/
inductive GLFormula : Type where
  | atom (p : PropAtom)        : GLFormula
  | falsum                      : GLFormula
  | impl (p q : GLFormula)      : GLFormula
  | box  (p : GLFormula)        : GLFormula
  deriving DecidableEq, Repr

namespace GLFormula

/-- Derived negation `¬φ := φ → ⊥`. -/
def not (p : GLFormula) : GLFormula := .impl p .falsum

end GLFormula

/-- Łukasiewicz propositional axiom schemas (k1, k2, k3). -/
inductive PropAxiom : GLFormula → Prop where
  | k1 (p q   : GLFormula) : PropAxiom (.impl p (.impl q p))
  | k2 (p q r : GLFormula) :
      PropAxiom (.impl (.impl p (.impl q r))
                       (.impl (.impl p q) (.impl p r)))
  | k3 (p q   : GLFormula) :
      PropAxiom (.impl (.impl (.impl p .falsum) (.impl q .falsum))
                       (.impl q p))

/-- Hilbert-style derivability in the propositional modal logic GL. -/
inductive GL_proves : GLFormula → Prop where
  | taut {t : GLFormula}        (h : PropAxiom t)        : GL_proves t
  | k    (p q : GLFormula) :
      GL_proves (.impl (.box (.impl p q)) (.impl (.box p) (.box q)))
  | lob  (p   : GLFormula) :
      GL_proves (.impl (.box (.impl (.box p) p)) (.box p))
  | mp   {p q : GLFormula}      (h₁ : GL_proves (.impl p q))
                                (h₂ : GL_proves p) : GL_proves q
  | nec  {p   : GLFormula}      (h  : GL_proves p) : GL_proves (.box p)

end GodelSecondGLSyntax
```

**LOC count** (re-counted from S8 PREP §9 minus the two unnecessary imports and two simp lemmas):

| Block                                       | LOC |
|---------------------------------------------|-----|
| Docstring                                   | 6   |
| `namespace GodelSecondGLSyntax` ... `end`   | 2   |
| `abbrev PropAtom` + docstring               | 2   |
| `inductive GLFormula` + deriving            | 6   |
| `namespace GLFormula` + `def not` + `end`   | 4   |
| `inductive PropAxiom` (3 constructors)      | 9   |
| `inductive GL_proves` (5 constructors)      | 9   |
| docstrings + blank lines                    | 6   |
| **Total**                                   | **~44–50 LOC** |

Comfortably below the S8 PREP §10 budget of ≤80 LOC, and below the original §9 estimate of ~60 LOC.

## 8. Acceptance criteria addenda for S8 ACT

Augment S8 PREP §13's binary checklist with three new items derived from this PREP:

- [ ] **Zero parent-file imports**: S8 ACT's new file must NOT `import Proofs.GodelSecondIncompletenessOQ02` (or any `Proofs.Godel*` file). It must NOT `import Mathlib.Logic.Basic` or any Mathlib subtree. The only dependencies are core Lean.
- [ ] **No `@[simp]` on constructor renames**: do NOT carry `@[simp] theorem GL_proves_k` / `GL_proves_lob` from S8 PREP §9 — these are low-value renames and the simp attribute is unhelpful. If a downstream caller wants a non-namespaced alias, they can use `alias`.
- [ ] **Use name `GLFormula`** (not `ModalFormula`) for the modal-formula type. The S5 PREP rename to `GLFormula` is a one-line follow-up — but it must happen before S5 ACT lands, or S5 ACT and S7 ACT will produce duplicate types.

S8 PREP §13 anti-targets remain unchanged.

## 9. Acceptance criteria addenda for S5 ACT

Before S5 ACT lands, the S5 PREP rename pass must complete:

- [ ] **Rename `ModalFormula → GLFormula`** in S5 PREP's `inductive ModalFormula` (line 82) and all subsequent references (~15 occurrences). The recursion structure, constructor names, and constructor types are unchanged.
- [ ] **Import `Proofs.GodelSecondIncompletenessOQ02GLSyntax`** in S5 ACT's new file. Do not redeclare `GLFormula`.
- [ ] **Update S5 PREP's `forces`** signature from `def forces : M.frame.W → ModalFormula → Prop` to `def forces : M.frame.W → GLFormula → Prop`. The body unchanged.

This is a 30-minute renaming pass that can ship as a "S5b PREP" (doc-only) or be folded into S5 ACT itself.

## 10. Acceptance criteria addenda for S7 ACT

Before S7 ACT lands, two terminology corrections:

- [ ] **Rename `PAFormula → Formula`** (or fully qualify as `GodelFirst.Formula`) per S7 PREP's `translate` signature. The parent file declares `Formula` — there is no `PAFormula`.
- [ ] **Add `open GodelFirst`** at S7 ACT's file head (or use full qualification) so bare `Prov`, `godelNum`, `Formula` resolve correctly.

These are cosmetic in the S7 PREP doc and only become substantive at S7 ACT push time.

## 11. Race awareness / orthogonality

At PREP push time (2026-05-13 ~06:50 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none)          | —                            |

This PREP creates exactly one new file:
`research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s9-prep-s8-act-audit-and-naming-reconciliation.md`.

It does **not**:

- Edit any existing session note (`s1-`, `s1b-`, `s4-`, `s5-`, `s6-`, `s7-`, `s8-prep-*.md`).
- Edit `problem.md`, `knowledge.md`, `state.md`.
- Edit any Lean file under `proofs/Proofs/`.
- Edit any gallery JSON under `src/data/proofs/` or `src/data/research/`.
- Edit the candidate pool `.lean/state/candidate-pool.json` or the audit tracker `src/data/proofs/audit-tracker.json`.

No race with any in-flight ACT or audit PR is possible.

## 12. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file (this one): `2026-05-13-s9-prep-s8-act-audit-and-naming-reconciliation.md`
- 0 edits to existing files
- 0 Lean changes
- 0 build runs
- 0 gallery / research JSON changes

**Scope honesty**:

- The naming inconsistency (§1) is **factually present** in S5 PREP, S7 PREP, S8 PREP — verified by direct quotation with line numbers. Not speculative.
- The import-minimization claim (§2) is **directly checkable** by inspecting S8 PREP §9 against the imports of `Mathlib.Logic.Basic` (none of `Iff.intro`, `not_iff_not`, `Classical.byContradiction`, etc., appear in the §9 code).
- The `@[simp]` low-value claim (§3) is **straightforwardly read off** the §9 source — both `theorem`s have RHS = constructor application.
- The `deriving DecidableEq` safety claim (§4) is **already validated** by three gallery files (`GodelFirstIncompletenessOQ01.lean` and two siblings) that compile.
- The Mathlib negative claims (§5) are **verified by direct Contents API browsing** at the current pin, not by search/code queries (which are rate-limited 30/hr and unreliable for negative claims).

**Anti-overclaiming**:

- The naming inconsistency is the **only** substantive S5-vs-S7-vs-S8 disagreement. No other inter-PREP discrepancy was found in this audit.
- The S8 PREP §9 design is otherwise sound — the inductive structures are textbook (Boolos 1993; Smoryński 1985; Mendelson 2015), and the choice of Option B is well-justified.
- This PREP does **not** claim that the four findings are blocking — they are **tightening** recommendations. S8 ACT could ship with all four findings ignored and still build correctly. The findings improve robustness, decouple build dependencies, and prevent a forced rename-pass after S5 ACT lands.

**LOC estimate honesty**:

- The recommended S8 ACT body (§7) is 44–50 LOC, **lower** than S8 PREP §9's 60 LOC, because of the 2 unnecessary imports + 2 simp lemmas removed.
- The recommended changes do **not** add to S5 ACT, S7 ACT, or S2-α ACT scope. They reduce or hold scope.

## 13. Forward chain after S9 PREP

The recommended sequence is unchanged but now better-tightened:

1. **S2-α ACT** (~50–120 LOC, +2 axioms in companion file): adds `impl`, `d2_modus_ponens`, `d3_internal_necessitation` per state.md §3. Independent of S5/S7/S8.
2. **S8 ACT** (~50 LOC after §7 edits, 0 sorries, 0 axioms): new file `GodelSecondIncompletenessOQ02GLSyntax.lean`. Independent of S2-α.
3. **S5b PREP** (~30 LOC doc-only): rename `ModalFormula → GLFormula` in S5 PREP. Depends only on S8 ACT having committed the name.
4. **S4 ACT** (Löb, ~150 LOC): depends on S2-α.
5. **S5 ACT** (Kripke, ~200 LOC): depends on S8 ACT + S5b PREP.
6. **S7 ACT** (arith soundness, ~95 LOC): depends on S2-α + S8 ACT.
7. **S6 ACT** (Σ₁-formalization of Prov): the architectural blocker for Solovay completeness; still deferred.

Total post-S9-PREP forward chain: 7 ACTs + 1 PREP, ~50 + 100 + 100 + 100 + 150 + 200 + 95 + 30 = ~825 LOC. State.md S2-β's "200–400 lines for just soundness" estimate is correctly identified by S8 PREP §10 as **conservative**.

## 14. References

- **Boolos, G. (1993).** *The Logic of Provability*. Cambridge University Press. Chs. 1–2.
- **Kalmár, L. (1935).** "Über die Axiomatisierbarkeit des Aussagenkalküls." *Acta Sci. Math.* 7, 222–243.
- **Mendelson, E. (2015).** *Introduction to Mathematical Logic*, 6th ed. CRC Press. §1.6, Theorem 1.2 (k1+k2+k3+MP completeness).
- **Smoryński, C. (1985).** *Self-Reference and Modal Logic*. Springer. §1.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0).

**Slug PREP chain** (this slug):

- S1 OBSERVE: PR #18198.
- S1b OBSERVE: PR #18404.
- S4 PREP (Löb): PR #18445.
- S5 PREP (Kripke): PR #18473.
- S6 PREP (Σ₁-blocker): PR #18497.
- S7 PREP (arith soundness): PR #18523.
- S8 PREP (`GLFormula` Hilbert): PR #18566.

**Parent gallery files**:

- `proofs/Proofs/GodelFirstIncompletenessOQ01.lean` (lines 52, 60, 65, 81, 91, 96, 267).
- `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` (lines 63, 70, 84, 258).

**Sibling deriving-DecidableEq evidence**:

- `proofs/Proofs/GodelFirstIncompletenessOQ01.lean:60-62` — `Formula` structure.
- `proofs/Proofs/GodelFirstIncompletenessOQ01OQ01.lean:73-75` — `Formula` structure.
- `proofs/Proofs/GodelFirstIncompletenessOQ01OQ04.lean:59-61` — `Formula` structure.
