# S8 PREP — `GLFormula` type + `GL_proves` Hilbert-style derivation predicate

**Date**: 2026-05-13
**Researcher**: researcher-11
**Mode**: PREP (doc-only design memo; pre-implementation)
**Phase target**: S8 ACT (~40–80 LOC of new Lean), prerequisite of S5 ACT and S7 ACT.
**Status**: pristine orthogonal to merged
S1 OBSERVE (#18198), S1b OBSERVE (#18404),
S4 PREP Löb (#18445), S5 PREP Kripke (#18473),
S6 PREP Σ₁-blocker (#18497), S7 PREP soundness-induction (#18523).
0 open PRs on slug at PREP push time.

## 0. Why this PREP

S7 PREP §7 (PR #18523) explicitly flagged a **missing prerequisite**:

> S7 ACT requires a Lean-side definition of `GL_proves : GLFormula
> → Prop` with the inductive constructors `taut`, `k`, `lob`, `mp`,
> `nec`. This is **not currently in the parent file** [...]
>
> **This is a missing prerequisite that no prior PREP has flagged.**

S7 PREP scoped three remediation options (inline / sibling file /
defer to S5 ACT) but did **not** write the inductive type or
predicate. S5 PREP (#18473) plans `KripkeValid` (the model-theoretic
side) but explicitly defers the Hilbert-side `GL_proves` — its scope
section ("Out of scope") lists "the full proof of Segerberg's
completeness theorem", and Hilbert-style derivability is not in scope.

So **no prior PREP has designed the syntactic Hilbert derivation
predicate** for GL. This PREP fills exactly that gap, in the form
expected by S7 PREP §4 (the soundness theorem `GL_proves_arith_sound`)
and by S5 PREP's planned soundness theorem `forces_of_GL_proves`.

The PREP is doc-only. The downstream S8 ACT PR will land the
~40–80 LOC of Lean (see §10 for the LOC budget).

## 1. Architectural placement

```
                   ┌─────────────────────────────┐
                   │  S8 ACT (this PREP's target)│
                   │  GLFormula : Type           │
                   │  GL_proves : GLFormula → Prop│
                   └────────┬──────────┬──────────┘
                            │          │
                  syntactic │          │ syntactic
                 (semantics)│          │  (arithmetic)
                            ▼          ▼
              ┌────────────────────┐  ┌──────────────────────┐
              │ S5 ACT (Kripke)    │  │ S7 ACT (soundness    │
              │ forces_of_GL_proves│  │ GL_proves_arith_sound│
              │ Segerberg compl    │  │ via translate ρ)     │
              └────────────────────┘  └──────────────────────┘
                            │                  ▲
                            │                  │
                            └─────────┬────────┘
                                      │
                                      ▼
                          ┌──────────────────────┐
                          │ Solovay (S∞):        │
                          │ GL_proves φ ↔ ∀ ρ,   │
                          │ ⊢ translate ρ φ      │
                          └──────────────────────┘
```

S8 ACT is the **syntactic foundation** for both branches. After it
lands, S5 ACT and S7 ACT become fully independent of each other —
each takes `GL_proves` as a black box predicate with 5 constructors
and discharges the case-split.

## 2. Mathlib audit — no off-the-shelf `GLFormula` / `GL_proves`

GitHub search/code at `repo:leanprover-community/mathlib4` (against
the live `master` of `mathlib4`, May 2026):

| Query | Hits |
|---|---|
| `GLFormula` | 0 |
| `GLProves` | 0 |
| `ModalLogic.GL` | 0 |
| `"inductive GLFormula"` | 0 |
| `ProvabilityLogic` | 0 |
| `HilbertSystem Modal` | 0 |

This confirms S7 PREP §6 ("Mathlib audit") and S5 PREP §2 ("Mathlib
audit"). There is no off-the-shelf Hilbert-style derivability
predicate for any modal logic in Mathlib v4.26.0.

The closest Mathlib infrastructure is `Mathlib.Computability` (for
recursive predicates) and `Mathlib.Logic.Basic` (for classical
propositional reasoning) — neither is a modal-logic stack. S8 ACT
therefore must define both `GLFormula` and `GL_proves` from
scratch, in the slug's own companion file.

## 3. The `GLFormula` inductive type

### 3.1 Constructors

```lean
/-- The atomic propositional variables of GL formulas.
    For Solovay we need infinitely many; `Nat` is the natural choice. -/
abbrev PropAtom : Type := Nat

/-- Formulas of the propositional modal logic GL. Five constructors:
    atomic, falsum, implication, and the modal box. Negation is
    derived: `¬ φ := φ.impl .falsum`. -/
inductive GLFormula : Type where
  | atom (p : PropAtom)            : GLFormula
  | falsum                          : GLFormula
  | impl (p q : GLFormula)          : GLFormula
  | box  (p : GLFormula)            : GLFormula
  deriving DecidableEq, Repr
```

**Design notes**:

- `PropAtom := Nat` is the conventional choice in modal-logic
  formalizations (Boolos 1993, Ch. 1; Smoryński 1985, §1). The
  `abbrev` rather than `def` ensures Lean elaborates `PropAtom` to
  `Nat` transparently — no coercion noise.
- `GLFormula` is a **standard** propositional modal-logic
  syntax tree. The choice of 4 constructors (atom, falsum, impl,
  box) is **canonical for GL** — every other connective is
  classically definable:
  - `.true  := .impl .falsum .falsum`           -- ⊥ → ⊥
  - `.not p := .impl p .falsum`                  -- ¬p ≡ p → ⊥
  - `.and p q := .impl (.impl p (.impl q .falsum)) .falsum`
  - `.or  p q := .impl (.impl p .falsum) q`
  - `.iff p q := .and (.impl p q) (.impl q p)`
  - `.dia p := .impl (.box (.impl p .falsum)) .falsum`  -- ◇ ≡ ¬□¬
- `deriving DecidableEq` is mechanical (Lean's `deriving` handler
  is total for first-order ADTs with decidable-eq parameters; `Nat`
  has `DecidableEq`).
- `deriving Repr` is for debugging: cleaner kernel error messages
  during S7 ACT and S5 ACT development.

### 3.2 Connection to the parent PA `Formula` type

The parent's `Formula : Type` (`GodelFirstIncompletenessOQ01.lean:60`)
is a **flat `⟨code : Nat⟩` structure** — single-field, no inductive
structure. `GLFormula` is **disjoint** from `Formula`:

| Type | Provenance | Encoding |
|------|------------|----------|
| `Formula` | parent gallery | flat `Nat` code |
| `GLFormula` | this PREP / S8 ACT | inductive 4-constructor ADT |

The **translation function** (S7 PREP §4) is the bridge:

```lean
def translate (ρ : PropAtom → Formula) : GLFormula → Formula
  | .atom p     => ρ p
  | .falsum     => GodelSecond.falsum
  | .impl p q   => GodelSecondCompanion.impl (translate ρ p) (translate ρ q)
  | .box  p     => Prov (godelNum (translate ρ p))
```

The `impl` on the GL side (a **constructor**) is **structurally
distinct** from the `impl` on the PA side (a **function**, added
in S2-α ACT). They share a name but live in different namespaces;
S7 ACT can disambiguate via `GLFormula.impl` vs
`GodelSecondCompanion.impl`. This avoids the encoding-accident
concerns that S1 OBSERVE state.md (line 44) raised for the PA-side
`impl` — those are S2-α PREP's concern, not S8 ACT's.

## 4. The `GL_proves` inductive predicate

### 4.1 Constructors

```lean
/-- Hilbert-style derivability for the propositional modal logic GL.
    Five constructors: propositional-tautology schema (taut), modal
    distribution axiom K, Löb's axiom L, modus ponens, and necessitation. -/
inductive GL_proves : GLFormula → Prop where
  | taut {t : GLFormula}   (h : PropAxiom t)        : GL_proves t
  | k    (p q : GLFormula) : GL_proves (.impl (.box (.impl p q)) (.impl (.box p) (.box q)))
  | lob  (p : GLFormula)   : GL_proves (.impl (.box (.impl (.box p) p)) (.box p))
  | mp   {p q : GLFormula} (h₁ : GL_proves (.impl p q)) (h₂ : GL_proves p) : GL_proves q
  | nec  {p   : GLFormula} (h  : GL_proves p)        : GL_proves (.box p)
```

Reading each constructor against the standard Hilbert axiomatization
(Segerberg 1971; Boolos 1993 ch. 1):

| Constructor | Schema name | Standard statement |
|---|---|---|
| `taut` | classical propositional fragment | `t` is a tautology in the propositional skeleton |
| `k`    | K (modal distribution)        | `□(p → q) → (□p → □q)`            |
| `lob`  | L (Löb's axiom)               | `□(□p → p) → □p`                  |
| `mp`   | MP (modus ponens)             | from `p → q` and `p` conclude `q` |
| `nec`  | Nec (necessitation)           | from `p` conclude `□p`            |

This **is GL** — the propositional modal logic of provability —
modulo the design choice in `taut` (next subsection).

### 4.2 The `taut` constructor: design choice

The single non-trivial design decision is how to encode the
propositional-tautology schema. Three concrete options:

#### Option A — Decidable propositional validity + reflection

```lean
def propositionallyValid : GLFormula → Bool := -- ... ~30 LOC
inductive GL_proves where
  | taut {t : GLFormula} (h : propositionallyValid t = true) : GL_proves t
  ...
```

**Pros**: clean reflection — `taut t (by decide)` discharges any
concrete propositional tautology in one line.

**Cons**: requires `propositionallyValid : GLFormula → Bool` to be
decidable. The propositional fragment is decidable in **finite
atom-restrictions** (a tautology over n atoms is checkable in
2^n cases), but a tautology over an unbounded `GLFormula` requires
unfolding to the propositional skeleton (which is decidable
*per-formula* but not as a uniform `Bool` function).

In Lean, this works if we substitute every box-prefixed subformula
with a fresh atom and decide propositionally. ~30 LOC.

#### Option B — Hilbert axiom schemas (recommended)

```lean
/-- Propositional axiom schemas, classical Hilbert system. -/
inductive PropAxiom : GLFormula → Prop where
  | k1 (p q   : GLFormula) : PropAxiom (.impl p (.impl q p))
  | k2 (p q r : GLFormula) : PropAxiom (.impl (.impl p (.impl q r)) (.impl (.impl p q) (.impl p r)))
  | k3 (p q   : GLFormula) : PropAxiom (.impl (.impl (.impl p .falsum) (.impl q .falsum)) (.impl q p))
```

These are the three Łukasiewicz axiom schemas (1929) for classical
propositional logic with `→` and `⊥`. Combined with the `mp`
constructor of `GL_proves`, they give the full propositional
fragment by **Kalmár's completeness theorem** (every tautology is
derivable from k1+k2+k3+MP — see Mendelson 2015 §1.6).

The `taut` constructor then takes `PropAxiom t`:

```lean
| taut {t : GLFormula} (h : PropAxiom t) : GL_proves t
```

**Pros**:
- 3 schemas, 3 cases. No reflection.
- Discharging `arith_tautology_lift` (S7 PREP §2.1) reduces to
  proving each schema's translation is PA-provable — three
  ~5-LOC lemmas.
- No Bool/Prop bridging.
- Matches S7 PREP §5 Strategy B explicitly ("Recommended approach").

**Cons**:
- Discharging "this concrete formula is a tautology" requires
  a Hilbert-style derivation, not a one-line `decide`. But this
  is **only** needed at S∞-level (Solovay), not at S5 ACT or
  S7 ACT — both of which call `taut` only **abstractly**.

#### Option C — Higher-order propositional axiomatization

```lean
inductive GL_proves where
  | taut {t : GLFormula} (h : ∀ v : PropAtom → Bool, eval v t = true) : GL_proves t
```

Requires a propositional-evaluation function `eval : (PropAtom →
Bool) → GLFormula → Bool` that **ignores `.box`** (treating each
boxed subformula as a fresh atom).

**Pros**: directly matches the standard semantic definition of
"propositional tautology".

**Cons**: requires evaluating under all assignments — a Bool-Prop
∀ that doesn't `decide` for infinite atom set. Need to thread
the "fresh atom" assignment through `.box` correctly.

#### Recommendation: Option B

S7 PREP §5 already recommends Strategy B (Hilbert schemas). This
PREP confirms and concretizes:

- Option B has the **smallest LOC**: 3-line schema + 3 lemmas in
  S7 ACT = ~15 LOC.
- Option B has **no boolean reflection** — purely propositional.
- Option B is **canonical** in modal-logic textbooks.

### 4.3 Negation note

GL is typically stated with **¬** as a primitive (e.g., Boolos's
axiomatization includes `¬¬p → p`). Our setup uses **`.falsum`** as
primitive and treats `¬p := .impl p .falsum`. The Łukasiewicz
schemas k1+k2+k3 (above) **derive double-negation elimination as a
theorem** (Mendelson 2015 §1.6, Thm 1.2). So the user-facing
behaviour of Option B is the same as a textbook GL with primitive
negation — but our axiom-storage is more efficient (3 schemas
vs 5+).

## 5. Substitution and admissibility

A Hilbert-style derivation system in modal logic must support
**uniform substitution**: if `GL_proves p` and `σ : PropAtom →
GLFormula` is any substitution, then `GL_proves (σ * p)` (where
`σ *` lifts to formulas).

In the Option B design, **substitution is admissible** without an
explicit constructor, because:

- Each axiom schema (k1, k2, k3, k, lob) is a **typed family**
  taking arbitrary `GLFormula` arguments. Instantiating
  `k1 (σ * p) (σ * q)` is the same as the substituted
  `σ * k1 p q`.
- `mp` and `nec` are closed under substitution by definition.

This is a standard observation (Avron 1991, Kracht 1999 §3.1):
**Hilbert systems with schematic axioms are closed under
substitution by construction**. S8 ACT does **not** need a
`subst` constructor.

## 6. Coupling to `translate` (S7 PREP §4)

S7 PREP §4 sketches:

```lean
def translate (ρ : PropAtom → Formula) : GLFormula → Formula
  | .atom p   => ρ p
  | .falsum   => GodelSecond.falsum
  | .impl p q => GodelSecondCompanion.impl (translate ρ p) (translate ρ q)
  | .box  p   => Prov (godelNum (translate ρ p))
```

This signature **assumes S8 ACT has shipped `GLFormula`** with the
4 constructors named exactly as above (`.atom`, `.falsum`, `.impl`,
`.box`). This PREP commits to those names; S7 ACT can write
`translate` as a direct copy with confidence.

The **structural recursion** is on `GLFormula`, which is well-founded
(Lean derives termination automatically for inductive types).

## 7. Coupling to S5 PREP's `KripkeValid`

S5 PREP §3 plans:

```lean
def forces (M : KripkeModel) (w : World) : GLFormula → Prop
  | .atom p   => M.valuation w p
  | .falsum   => False
  | .impl p q => forces M w p → forces M w q
  | .box  p   => ∀ v, M.frame.R w v → forces M v p
```

This signature **also assumes** `GLFormula` with the 4 constructors.
S8 ACT's commitment is shared by S5 ACT, making the two ACTs
**independent post-S8** — neither needs to wait for the other.

S5's eventual soundness theorem `forces_of_GL_proves` will be a
case-split on `GL_proves` (constructors `taut`, `k`, `lob`, `mp`,
`nec`), perfectly parallel to S7's `GL_proves_arith_sound` —
both consume the same predicate, one to PA-semantics, the other
to Kripke-semantics.

## 8. The companion-file landing strategy

S8 ACT's deliverable is a new Lean file:

```
proofs/Proofs/GodelSecondIncompletenessOQ02GLSyntax.lean
```

This file:

1. Imports `Proofs.GodelSecondIncompletenessOQ02` (the parent —
   provides `Formula`, `Prov`, `godelNum`, `falsum`).
2. Defines `PropAtom`, `GLFormula`, `PropAxiom`, `GL_proves`.
3. **Does NOT** define `translate` (that belongs to S7 ACT or a
   sibling file) or `forces` (S5 ACT).
4. **Does NOT** edit the parent file.
5. **Does NOT** edit any `state.md`, `problem.md`, `knowledge.md`,
   or gallery JSON.

The file is **strictly type/predicate definitions** plus 0–3 trivial
`@[simp]` lemmas (e.g., `GL_proves_taut_iff_PropAxiom` for the
unfolding of the `taut` constructor). Total ≤ 80 LOC.

## 9. Concrete signature for S8 ACT

```lean
import Proofs.GodelSecondIncompletenessOQ02
import Mathlib.Logic.Basic

namespace GodelSecondGLSyntax

/-- Atomic propositional variables of the modal-logic GL formula language. -/
abbrev PropAtom : Type := Nat

/-- Formulas of the modal-logic GL: propositional skeleton + `□`. -/
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

/-- The three Łukasiewicz propositional axiom schemas (k1, k2, k3),
    each producing a `GLFormula` tautology. -/
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
  | mp   {p q : GLFormula}      (h₁ : GL_proves (.impl p q)) (h₂ : GL_proves p) : GL_proves q
  | nec  {p   : GLFormula}      (h  : GL_proves p) : GL_proves (.box p)

/-- Trivial unfolding lemmas (optional simp). -/
@[simp] theorem GL_proves_k (p q : GLFormula) :
    GL_proves (.impl (.box (.impl p q)) (.impl (.box p) (.box q))) :=
  GL_proves.k p q

@[simp] theorem GL_proves_lob (p : GLFormula) :
    GL_proves (.impl (.box (.impl (.box p) p)) (.box p)) :=
  GL_proves.lob p

end GodelSecondGLSyntax
```

**LOC count** (counted at write time):

| Block                                        | LOC |
|----------------------------------------------|-----|
| Module preamble + imports                    | 4   |
| `PropAtom` abbrev                            | 2   |
| `GLFormula` inductive + deriving             | 8   |
| `GLFormula.not` derived def                  | 2   |
| `PropAxiom` inductive (3 cases)              | 11  |
| `GL_proves` inductive (5 cases)              | 11  |
| Two `@[simp]` lemmas                         | 6   |
| Namespace open/close                         | 4   |
| Comments / blank lines                       | 12  |
| **Total**                                    | **~60 LOC** |

Well within the §8 budget of ≤ 80 LOC.

## 10. LOC budget honesty

- **S8 ACT (this PREP's eventual implementation)**: ~60 LOC, 0
  sorries, 0 new axioms.
- **S7 ACT, post-S8**: ~95 LOC (per S7 PREP §4 estimate).
- **S5 ACT (Kripke side), post-S8**: ~150–250 LOC (per S5 PREP).
- **Combined S5 + S7 + S8 ACT chain**: ~300–400 LOC, all
  axiom-free relative to the parent's existing 6 axioms.

Compare to the state.md S2-β estimate of "200–400 lines" for
**just soundness**: with proper PREP discipline (S8 isolating the
syntactic foundation, S7 PREP scoping the arithmetic dispatch),
the realistic LOC is substantially smaller because no work is
duplicated between Kripke and arithmetic sides.

## 11. Race awareness / orthogonality

At PREP push time (2026-05-13 ~05:00 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none)          | —                            |

This PREP creates exactly one new file:
`research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s8-prep-glformula-gl-proves-hilbert-design.md`.

The 6 merged precursor PREPs each cover a distinct angle, and none
intersects with the `GLFormula` / `GL_proves` design:

- **S1 OBSERVE (#18198)** — `state.md` mentions `GL_proves` only
  abstractly (e.g., line 59: "induction on `GL_proves`"); no
  concrete type designed.
- **S1b OBSERVE (#18404)** — typeclass-vs-companion-file for D2/D3,
  HBL-conditions side. No GL-syntax side.
- **S4 PREP (#18445)** — Löb's theorem internal to PA. Uses
  `Provable : Formula → Prop`, not `GL_proves`.
- **S5 PREP (#18473)** — Kripke semantics. **Plans** to use
  `GLFormula` and `forces : KripkeModel → World → GLFormula → Prop`
  but does not define `GLFormula` itself.
- **S6 PREP (#18497)** — Σ₁-formalization of `Provable`. Pure
  PA-side; no GL syntax.
- **S7 PREP (#18523)** — arithmetic soundness induction. **Flags**
  that `GL_proves` is missing (§7); this PREP **answers** that flag.

## 12. Anti-targets

This PREP (and the eventual S8 ACT) **does not**:

- Touch the parent file `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`.
- Touch `proofs/Proofs/GodelFirstIncompletenessOQ01.lean`.
- Define `translate : GLFormula → Formula` (S7 ACT's territory).
- Define `forces : KripkeModel → World → GLFormula → Prop`
  (S5 ACT's territory).
- Define `KripkeFrame`, `KripkeModel`, or any model-theoretic
  artefacts (S5 ACT).
- Define `lob_theorem : ∀ A, ⊢ Prov(⌜A⌝) → A → ⊢ A` (S4 ACT's
  internal Löb).
- Add axioms `d2_modus_ponens` or `d3_internal_necessitation` to
  the PA side (S2-α's territory).
- Replace the opaque `Provable` axiom with a Σ₁ formalization
  (S6 PREP's deferred ACT).
- Add `KripkeValid` or `propositionalEvaluation` (semantic-side
  scaffolding).
- Make any edits to `state.md`, `problem.md`, `knowledge.md`,
  gallery JSON, or any prior session note.

## 13. Acceptance criteria for S8 ACT (binary)

The S8 ACT PR must:

- [ ] Create `proofs/Proofs/GodelSecondIncompletenessOQ02GLSyntax.lean`.
- [ ] Define `PropAtom`, `GLFormula`, `PropAxiom`, `GL_proves` per
      §9 signatures.
- [ ] Use `deriving DecidableEq, Repr` for `GLFormula`.
- [ ] Ship 0 sorries, 0 new axioms.
- [ ] Build via `./proofs/scripts/docker-build.sh
      Proofs.GodelSecondIncompletenessOQ02GLSyntax`.
- [ ] Add `import Proofs.GodelSecondIncompletenessOQ02GLSyntax`
      target to the relevant `lakefile.toml` or `default.lean`
      manifest (or rely on the build-all default).
- [ ] Total file LOC ≤ 80.
- [ ] Update `state.md` to record S8 ACT.

The S8 ACT PR **must NOT**:

- Define `translate`, `forces`, or any case-split over `GL_proves`
  — those belong to S5 ACT / S7 ACT.
- Edit the parent file or any other gallery proof.
- Add a `subst` constructor to `GL_proves` (substitution is
  admissible, see §5).
- Introduce a `Bool`-valued propositional-validity check
  (Option A from §4.2 — rejected in favour of Option B).

## 14. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file: `research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s8-prep-glformula-gl-proves-hilbert-design.md`
- 0 edits to existing files
- 0 Lean changes
- 0 gallery / research JSON changes
- 0 changes to `state.md`, `problem.md`, `knowledge.md`, or any
  prior session note

**Scope honesty**:

- The §9 signature is **complete and self-contained** — no missing
  helper types or unresolved imports. S8 ACT can literally copy
  the §9 block into a new file and `docker-build.sh` it.
- The §4.2 Option-B choice is **canonical** in modal-logic
  textbooks; it is not novel. The novelty here is *only* the
  choice between Options A/B/C for the gallery's particular
  Solovay setup; that choice is settled (Option B).
- The §5 "substitution is admissible" claim is **textbook**
  (Avron 1991; Kracht 1999); it is not a new mathematical
  result. The novelty here is *flagging* that S8 ACT does not
  need a `subst` constructor — saving 20–40 LOC of dead code.

**LOC estimate honesty**:

- 60 LOC ±10 is a tight estimate, computed line-by-line in §9.
- The estimate is **independent** of how S7 ACT and S5 ACT proceed
  — S8 ACT is purely syntactic.
- The 0-sorry / 0-axiom claim is **strict** — `deriving
  DecidableEq` is mechanical, and the inductive definitions are
  standard.

**Risk register**:

| Risk | Mitigation |
|---|---|
| `deriving DecidableEq` fails because Nat needs explicit instance | Lean 4 / Mathlib has `Nat.decEq` in core; should be automatic. If it fails, manually implement `instance : DecidableEq GLFormula := by ...` (~6 LOC). |
| Naming collision with parent's `Formula.impl` (no such field exists in parent — `Formula` is `⟨code : Nat⟩`) | None; parent has no `impl`. |
| Naming collision with S2-α's eventual `impl : Formula → Formula → Formula` | None: `GLFormula.impl` is a constructor namespaced under `GLFormula`; PA-side `impl` lives in `GodelSecondCompanion`. No name clash. |
| `PropAtom := Nat` insufficient for some use case | `Nat` has ω atoms — more than enough. If finite atom sets are ever needed, that's a future restriction (no work needed now). |

## 15. References

- **Avron, A. (1991).** "Simple consequence relations." *Information and Computation* 92, 105–139.
- **Boolos, G. (1993).** *The Logic of Provability*. Cambridge University Press. Chs. 1–2.
- **Kalmár, L. (1935).** "Über die Axiomatisierbarkeit des Aussagenkalküls." *Acta Sci. Math.* 7, 222–243. — propositional completeness for k1+k2+k3+MP.
- **Kracht, M. (1999).** *Tools and Techniques in Modal Logic*. Elsevier. §3.1 — Hilbert systems and substitution.
- **Łukasiewicz, J. (1929).** *Elements of Mathematical Logic*. — origin of the k1/k2/k3 axiomatization.
- **Mendelson, E. (2015).** *Introduction to Mathematical Logic*, 6th ed. CRC Press. §1.6 — Hilbert system and Kalmár's completeness.
- **Segerberg, K. (1971).** *An Essay in Classical Modal Logic*. Filosofiska Studier 13, Uppsala. — GL Kripke semantics.
- **Smoryński, C. (1985).** *Self-Reference and Modal Logic*. Springer. §1 — GL syntax conventions.
- **Solovay, R. (1976).** "Provability interpretations of modal logic." *Israel J. Math.* 25(3–4), 287–304.

- **S1 OBSERVE**: PR #18198.
- **S1b OBSERVE**: PR #18404 (typeclass-encoding HBL D1-D3 axiom-budget).
- **S4 PREP (Löb)**: PR #18445.
- **S5 PREP (Kripke)**: PR #18473.
- **S6 PREP (Σ₁-blocker)**: PR #18497.
- **S7 PREP (soundness induction)**: PR #18523 — this PREP fills the §7 `GL_proves`-missing gap explicitly flagged there.

- Parent file: `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`.
- Grandparent file: `proofs/Proofs/GodelFirstIncompletenessOQ01.lean`.
