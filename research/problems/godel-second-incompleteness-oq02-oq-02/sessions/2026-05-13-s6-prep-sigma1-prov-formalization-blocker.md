# S6 PREP — Σ_1-formalization of `Provable` (architectural-blocker scoping)

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only architectural-blocker scoping)
**Phase target**: S6 / S7+ multi-iteration ACT chain
**Status**: pristine, orthogonal to all four prior doc-only PRs.

## Why this PREP

The S1 OBSERVE (`state.md` § "Architectural flag") explicitly flags:

> **The opaque `Provable : Formula → Prop` axiom (from
> `GodelFirstIncompletenessOQ01`) is incompatible with Solovay's
> completeness construction**, which requires a concrete
> Σ_1-formalization of provability. This is a fundamental
> architectural mismatch that should be flagged before any
> completeness-direction S3 work begins.

and

> **Architectural blocker for S3+ completeness direction:** the
> opaque `Provable` axiom must be replaced with a concrete
> Σ_1-formalization. This is a major restructuring and should be
> a separate proposal (not a single session).

This PREP **is that separate proposal**. It scopes:

1. **What the current placeholder actually is** (§1).
2. **Why the placeholder breaks Solovay completeness** (§2).
3. **What a Σ_1-formalization of `Provable` must provide** (§3).
4. **Three replacement strategies, ranked by effort × infrastructure cost** (§4).
5. **Mathlib v4.26.0 first-order logic API audit** (§5).
6. **A 6-step decomposition** of the replacement into smaller ACT deliverables (§6).
7. **Honest LOC + axiom-count projections** for each strategy (§7).
8. **Anti-targets and the orthogonality story** to the four prior PREPs (§8).

The four prior PREPs cover:

| PR | Direction | Stage | This PREP overlap? |
|----|-----------|-------|--------------------|
| #18198 (S1 OBSERVE) | full slug survey | S1 | This PREP refines the architectural blocker the survey flagged. |
| #18404 (S1b OBSERVE) | typeclass-encoding axiom-budget for HBL D1-D3 | S2-α prep | **No overlap** — HBL D1-D3 are *modal logic axioms over* `Provable`; this PREP replaces `Provable` itself. |
| #18445 (S4 PREP) | Löb's theorem formalization design | S4 | **No overlap** — Löb operates within the existing axiomatic framework. |
| #18473 (S5 PREP, OPEN) | Kripke semantics for GL + Segerberg soundness | S5 | **No overlap** — pure modal logic, no arithmetization. |

This PREP is the **arithmetic-formalization** angle, complementary
to S5's **modal-logic** angle and orthogonal to S4's HBL angle.

## 1. The current placeholder

`Proofs/GodelIncompleteness.lean:78`:

```lean
def Provable : Formula → Prop := fun _ => False
```

This is **definitionally `False`** — every "provability" claim is
vacuous. The file's docstring at `:42` is explicit:

> 0 sorries, 0 axioms (derivability_conditions removed:
> inconsistent with `Provable := fun _ => False`)

and at `:75`:

> For this illustrative formalization, we use this placeholder. The
> theorems below demonstrate the **structure** of Gödel's argument;
> a complete formalization would require extensive foundational work
> (see e.g., Paulson's Gödel proof in Isabelle, which spans
> ~15,000 lines).

The downstream consequence: `first_incompleteness`,
`second_incompleteness`, and `con_implies_G` all become trivially
true because their conclusions are `¬ Provable _ = ¬ False = True`.
The gallery's `status: verified` claim is technically correct for
the **structural** form of Gödel's argument; it is **not** a claim
about a real provability predicate.

## 2. Why the placeholder breaks Solovay completeness

Solovay's theorem (the OQ-02 target):

> `GL ⊢ φ ⟺ ∀ realizations *, PA ⊢ φ*`

requires interpreting `□` as a **specific arithmetical predicate**
`Prov_PA(⌜·⌝)` and showing the **biconditional** holds. Two
obstructions:

1. **Vacuity**: with `Provable := fun _ => False`, the right-hand
   side `PA ⊢ φ*` is `False` for every realisation, hence the
   biconditional reduces to `GL ⊢ φ ⟺ False` — equivalent to "GL
   proves nothing", which is patently wrong (e.g., GL proves all
   propositional tautologies).
2. **No arithmetisation**: even if `Provable` were upgraded to a
   non-vacuous predicate, the *content* of Solovay's proof requires
   `Provable` to satisfy:
   - **Σ_1-completeness**: `Provable φ → PA ⊢ Prov(⌜φ⌝)`
     (formalized provability mirrors meta-provability).
   - **HBL D1-D3** as object-language theorems (not informal axioms).
   - **Diagonal lemma** as a Lean theorem (currently the parent
     stubs it as `theorem diagonal_lemma … := by exact ⟨⟨0⟩, trivial⟩`
     — a trivial witness, not the real construction).

The current parent therefore lacks **all four** prerequisites for
Solovay. A "drop-in replacement" of `Provable` with a non-vacuous
predicate is not enough — the surrounding infrastructure must come
along.

## 3. What a Σ_1-formalization must provide

A concrete Σ_1-formalization of `Provable` must supply:

### 3.1 First-order syntax for PA

- A type `LFormula` of first-order formulas in the language of PA
  (constants `0`, function `S`, `+`, `×`, equality `=`,
  quantifiers `∀ ∃`, connectives `→ ¬`).
- Term type, formula type, free-variable and substitution operations.
- Gödel numbering: an injection `code : LFormula ↪ ℕ` with a
  decidable inverse.

### 3.2 Decidable proof checker

- A formal proof type `PAProof` (a finite list of formulas, each
  either a logical axiom, a PA axiom, or derivable from earlier
  steps via modus ponens / generalisation).
- A decidable predicate `IsValidProof : PAProof → Prop`.
- The concluding formula extractor `Conclusion : PAProof → LFormula`.

### 3.3 Provability as Σ_1 quantification

```lean
def Provable (φ : LFormula) : Prop :=
  ∃ π : PAProof, IsValidProof π ∧ Conclusion π = φ
```

The `∃` over `PAProof` (whose elements are encoded as natural
numbers) makes `Provable` a **Σ_1-predicate** in the meta-theory.
The decidability of `IsValidProof` is what gives Σ_1 rather than
just `∃`.

### 3.4 Internal provability predicate

`Prov : ℕ → LFormula` returning an object-language formula
"the formula with Gödel number n is provable in PA". This formula
must be **a Σ_1-formula in the language of PA**, encoding the
decidable predicate `IsValidProof` over `ℕ`-coded proofs.

### 3.5 Σ_1-completeness of PA

A theorem (NOT an axiom):

```lean
theorem sigma1_completeness (φ : LFormula) (hΣ : IsSigma1 φ)
    (h_true : LSat φ) : Provable φ
```

This is the "PA proves all true Σ_1-formulas" result — Robinson 1952,
restated and proved formally. Approximately 200-400 LOC in a
dedicated module.

### 3.6 The four HBL conditions as theorems

D1: `Provable φ → Provable (Prov ⌜φ⌝)` (provability implies
formalised provability — Σ_1-completeness applied to the Σ_1
formula `Provable`).

D2: `Provable (impl φ ψ) → Provable φ → Provable ψ` (modus ponens
internalised — straightforward from the proof system).

D3: `Provable (Prov ⌜φ⌝) → Provable (Prov ⌜Prov ⌜φ⌝⌝)` (Σ_1
internal necessitation — a syntactic consequence of D1 applied
internally).

D4 (sometimes separated): `Provable (impl (impl φ ψ) (impl (Prov ⌜φ⌝)
(Prov ⌜ψ⌝)))` — internal distribution of `Prov` over `→`.

## 4. Three replacement strategies

### Strategy A — Direct Mathlib FirstOrder framework

Use `Mathlib.ModelTheory.Language` to encode PA, then construct
`Provable` via Mathlib's `Theory.Provable` or equivalent.

**Pros**:

- Reuses a battle-tested library; no in-project syntax/semantics duplication.
- `Mathlib.ModelTheory` is actively maintained; bug-fixes propagate.
- Reduces our local code footprint.

**Cons**:

- Mathlib `FirstOrder.Language.Theory` defines provability via
  `LCompleteness.theorems` or `Theory.Provable` — but these are
  *meta-level* sets, not Σ_1-predicates inside the object language.
- The bridge "Mathlib `Provable` = our Σ_1 `Prov(⌜·⌝)`" is a
  separate result (~500 LOC).
- PA itself is not currently in Mathlib as a built-in theory
  (status of `Mathlib.ModelTheory.PeanoArithmetic` at v4.26.0
  needs verification — see §5).

**Effort estimate**: 1,500-2,500 LOC + Mathlib API bridge.

### Strategy B — Local Σ_1-formalization

Build a minimal PA-arithmetization in-project, modelled after
existing Lean/Isabelle Gödel formalisations (Paulson 2014 in
Isabelle; Carneiro 2018 sketch in Lean 3).

**Pros**:

- Total control over the encoding (tailored to gallery's needs).
- No Mathlib API drift risk.
- Easier to audit for the Axiom Integrity Policy (every assumption
  is locally declared).

**Cons**:

- ~3,000-5,000 LOC of foundational work.
- Bug surface is local — fewer eyes than Mathlib's.
- Cannot easily share with downstream slugs that might want PA
  formalization (locked into this OQ).

**Effort estimate**: 3,000-5,000 LOC.

### Strategy C — Hybrid (Mathlib syntax + local proof checker)

Use `Mathlib.ModelTheory` for the **syntax** (formulas, terms,
substitution, Gödel numbering) but write a **local proof checker**
that fits the gallery's `Theorem ⊢` style.

**Pros**:

- Best of both: free syntax + tailored proof system.
- Smaller local footprint than Strategy B.
- Local proof checker is the "Σ_1-providing" piece; everything else
  is reused.

**Cons**:

- Hybrid interfaces have integration risk (Mathlib's term
  representation vs. local proof checker's substitution).
- Locking in to Mathlib's `FirstOrder.Language` means tracking
  Mathlib breaking changes (cf. `feedback_researcher_mathlib_v4_26_drift`
  for the project's history of v4.26.0 drift).

**Effort estimate**: 2,000-3,500 LOC.

### Recommended: Strategy C (Hybrid)

Three considerations tilt to Strategy C:

1. **Solovay's proof structure** is largely syntactic: it manipulates
   proof codes, applies the diagonal lemma, and reasons about
   provability of Σ_1-formulas. Mathlib's syntactic framework
   provides this; the local proof checker provides Σ_1.
2. **The 4 HBL conditions** are local to the proof checker's
   structural axioms (a 50-100 LOC declaration once the checker
   exists). No Mathlib bridging needed for these.
3. **Future-proofing**: if Solovay's theorem is later ported to use
   Mathlib's syntactic upgrade (or to a polymodal extension like
   GLP), the hybrid file is easy to refactor — the local proof
   checker can be swapped without touching syntax.

## 5. Mathlib v4.26.0 first-order logic API audit

At pinned Mathlib v4.26.0, the relevant declarations:

| Decl | Module | Use | Status (PREP guess) |
|------|--------|-----|---------------------|
| `FirstOrder.Language` | `Mathlib.ModelTheory.Language` | language of PA | likely present |
| `FirstOrder.Language.Term` | `Mathlib.ModelTheory.Syntax` | terms | likely present |
| `FirstOrder.Language.Formula` | `Mathlib.ModelTheory.Syntax` | formulas | likely present |
| `FirstOrder.Language.Sentence` | `Mathlib.ModelTheory.Syntax` | closed formulas | likely present |
| `FirstOrder.Language.Theory` | `Mathlib.ModelTheory.Theory` | theory as set of sentences | likely present |
| `FirstOrder.Language.Theory.Provable` / similar | `Mathlib.ModelTheory.Theory` or `.Satisfiability` | meta-level provability | **unclear v4.26.0 status** |
| `Mathlib.ModelTheory.PeanoArithmetic` | (dedicated PA module) | PA axioms | **may not exist** |
| `Mathlib.ModelTheory.Encoding` | (Gödel numbering / arithmetization) | encoding bridge | **likely absent** |
| `Decidable` instance for term/formula equality | core | proof checker decidability | likely present (via `DecidableEq`) |

**Action item for S6 ACT**: Before committing to Strategy C, verify

```bash
gh api -X GET search/code \
  -F q="PeanoArithmetic repo:leanprover-community/mathlib4" \
  --jq '.items[].path' | head
```

and

```bash
gh api -X GET search/code \
  -F q="Theory.Provable repo:leanprover-community/mathlib4" \
  --jq '.items[].path' | head
```

If `PeanoArithmetic` and a usable `Theory.Provable` exist, Strategy
A may become viable (lower local LOC). If not, Strategy C remains
the recommendation.

The **outcome of this audit** should land as an addendum to this
PREP or as a separate S6 PREP-2 — the audit is itself a doc-only
deliverable.

## 6. Six-step ACT decomposition

The Σ_1-formalization replacement decomposes into:

### S6 ACT — Mathlib audit (this iteration's natural follow-up)

Run the `gh api` queries above. Verify `Mathlib.ModelTheory.Language`
v4.26.0 surface. Decide A vs B vs C definitively. **Deliverable**:
single PREP-2 file with audit results. ~150 LOC doc-only.

### S7 ACT — Local proof checker (Strategy C, step 1)

Create `Proofs/Sigma1ProvabilityCore.lean` with:

- Import of Mathlib `FirstOrder.Language`.
- Local definition of PA's language (`PALanguage`).
- Local `PAProof`, `IsValidProof`, `Conclusion`.
- `Provable_v2 : LFormula → Prop` via `∃ π, IsValidProof π ∧ …`.

**Deliverable**: ~600-1000 LOC, 0 sorries, 0 axioms.

### S8 ACT — Σ_1-completeness

Prove `∀ φ : Σ_1, LSat φ → Provable_v2 φ`. Robinson 1952; ~300 LOC.

### S9 ACT — HBL D1-D4 as theorems

Replace the typeclass-encoded HBL axioms (from #18404) with proofs
in the new framework. ~400 LOC.

### S10 ACT — Diagonal lemma (real version)

Prove `∀ P : ℕ → LFormula, ∃ γ : LFormula, Provable_v2 (γ ↔ P ⌜γ⌝)`.
~300 LOC.

### S11 ACT — Bridge to gallery's `Provable`

Either (a) replace gallery's `Provable` with `Provable_v2` (parent-edit
+ re-prove first / second incompleteness), or (b) prove a
correspondence theorem `Provable ↔ Provable_v2` (keep parent
immutable). ~200-400 LOC.

### S∞ — Solovay completeness

With S6-S11 in place, Solovay's completeness direction becomes a
finite (multi-thousand LOC) but well-scoped target.

**Total Σ_1-replacement scope**: ~3,000-4,000 LOC across S6-S11,
spanning several months of work. Comparable to Paulson's Isabelle
~15,000 lines but smaller because Mathlib's syntax is reused.

## 7. LOC + axiom-count projection

| Strategy | New LOC | New axioms | Removes existing axioms? |
|---------|---------|-----------|--------------------------|
| A (Mathlib) | 1,500-2,500 | 0-1 (if Mathlib bridge needs one) | `Provable` placeholder + `con_implies_G` axiom: removed |
| B (Local) | 3,000-5,000 | 0 | (same removals) |
| C (Hybrid) | 2,000-3,500 | 0 | (same removals) |

In all three strategies, the **first-incompleteness and
second-incompleteness theorems are re-proved** from a non-vacuous
`Provable` predicate. The gallery's status improves from
"structural argument with placeholder predicate" to **"verified
first/second incompleteness on a concrete arithmetisation"**.

The five HBL-related typeclass axioms from PR #18404 are also
**removed** — they become theorems in the new framework.

## 8. Orthogonality story — four prior PREPs

| Prior PR | Subject | Overlap with this S6 PREP? | Why |
|----------|---------|----------------------------|-----|
| #18198 (S1 OBSERVE) | Survey | This PREP refines its "architectural blocker" flag | Survey scoped the problem; this PREP scopes the solution |
| #18404 (S1b OBSERVE) | HBL typeclass-encoding | **No overlap** | HBL axioms operate over `Provable`; this PREP replaces `Provable` itself (HBL becomes theorems post-replacement, see §6 S9) |
| #18445 (S4 PREP) | Löb's theorem within existing framework | **No overlap** | Löb works with HBL-as-axioms; this PREP replaces the foundation under HBL |
| #18473 (S5 PREP, OPEN) | Kripke semantics for GL | **No overlap** | S5 PREP is pure modal logic (no arithmetic); this PREP is pure arithmetic (no modal semantics). They meet at the *Solovay biconditional*, far downstream. |

This S6 PREP is the **5th orthogonal angle** on the slug. The five
form a coherent design space:

```
                  Solovay's theorem
                 (multi-month ACT chain)
                 /                      \
       Soundness (←−)         Completeness (−→)
       /    |    \                /    |    \
      D1    D2    D3         Σ_1     Kripke  Diagonal
   (HBL    (HBL  (HBL      (this    (S5     (S6 step 4
   #18404) #18445) #18404)  PREP)  PREP)    of this PREP)
```

Soundness uses HBL D1-D3 (covered by PRs #18404, #18445).
Completeness uses Σ_1-formalization (this PREP), Kripke
semantics (#18473), and a real diagonal lemma (a deliverable
inside this PREP's S10 step).

## 9. Honest framing

This PREP does NOT solve Solovay's theorem. It explicitly maps the
**architectural prerequisite work**, with effort estimates that are
deliberately pessimistic. The S∞ Solovay completeness deliverable
remains a multi-month, multi-thousand-LOC contribution comparable
in scope to a small Mathlib library.

Three caveats:

1. **Effort estimates are rough**. Paulson's 15K-line Isabelle
   formalization is the upper bound; Mathlib reuse may reduce by
   3-5x; but our local complications (e.g., bridge to gallery's
   existing `Formula` type, parent-edit decisions, audit
   requirements) may increase by 2x. Honest range: ~3,000-8,000
   LOC for the full replacement.
2. **The PREP recommends Strategy C without doing the Mathlib audit
   first**. The recommendation is a starting position based on
   structural reasoning; the §5 audit is the natural S6 ACT
   follow-up.
3. **Solovay's completeness direction has additional content not
   covered here**: the actual completeness proof requires the
   Solovay fixed-point construction (a clever iteration over
   pre-models that converges to a Kripke-style countermodel for any
   non-GL-provable formula). The completeness ACT chain is S∞ in §6;
   this PREP focuses on the prerequisite Σ_1-machinery (S6-S11).

## 10. Race awareness

At PREP-push time (2026-05-13, ~03:30 UTC):

- **Open PRs for this slug**: PR #18473 (S5 PREP Kripke +
  Segerberg). Disjoint subject (modal logic vs. arithmetic). Zero
  file overlap (different `sessions/` filenames).
- **Recent merged PRs**:
  - PR #18445 (S4 PREP Löb formalization), merged 2026-05-13T02:06:28Z.
  - PR #18404 (S1b OBSERVE typeclass-encoding), merged
    2026-05-13T02:09:30Z.
  - PR #18198 (S1 OBSERVE Solovay survey), merged 2026-05-12T23:20:28Z.
- **Latest `origin/main`**: `0c84ce40fd1` (general-quartic-oq-02
  S4 PREP, unrelated slug).
- **Conflict surface**: zero. Strictly additive single-file PR.

## 11. No-edit guarantee

Confirmed via design: this PREP adds **exactly one new file**:

```
research/problems/godel-second-incompleteness-oq02-oq-02/sessions/
    2026-05-13-s6-prep-sigma1-prov-formalization-blocker.md
```

(Reuses the `sessions/` subdirectory created by prior PRs.)

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
  - `proofs/Proofs/GodelIncompleteness.lean` (parent, in main)
  - `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` (gallery
    entry, in main)
  - `proofs/Proofs/GodelFirstIncompletenessOQ01.lean` (sibling)
- ✗ No edits to any `.json` file
- ✗ No edits to the existing `sessions/` memos (S1b OBSERVE, S4 PREP)

## 12. Anti-targets (out of scope for this PREP)

1. **Solovay's completeness proof.** Even sketched, the construction
   is multi-thousand LOC. Out of scope.
2. **Choosing between Strategy A vs B vs C definitively.** §5 flags
   the Mathlib audit as the natural follow-up; this PREP recommends
   Strategy C as a starting position only.
3. **Implementing any of S6-S11 ACT steps.** This PREP is pure
   scoping.
4. **Editing the parent `GodelIncompleteness.lean`.** Any
   modification to `Provable` is an S11 deliverable, not a PREP item.
5. **Adding new axioms.** This PREP recommends 0 new axioms across
   all three strategies; specific bridge axioms (e.g., Mathlib's
   `Theory.Provable ↔ local Provable_v2`) may be needed and would
   be flagged at S7 ACT time.
6. **Cross-OQ refactoring** (e.g., propagating Σ_1-formalization to
   `godel-first-incompleteness-oq01`). Deferred to a sibling slug
   or a deliberate refactoring PR.
7. **Resolution of the Wiedijk-100-list status claim.** The current
   `GodelIncompleteness.lean` is marked as a Wiedijk #56 entry
   ("Gödel's incompleteness theorems"). With Σ_1-replacement
   complete, the verification claim becomes substantially stronger.
   This is an enrichment-phase task, not a research-phase task.

## 13. Mathlib API audit checklist for S6 ACT

When the S6 ACT iteration runs the audit (per §5), it should record:

- [ ] `Mathlib.ModelTheory.Language` exists at v4.26.0 — confirmed (audit-verify).
- [ ] `Mathlib.ModelTheory.Syntax` `Formula`, `Term`, `Sentence` — confirmed (audit-verify).
- [ ] `Mathlib.ModelTheory.Theory.Provable` (or equivalent) — flag whether present.
- [ ] `Mathlib.ModelTheory.PeanoArithmetic` (or `.Arithmetic`) — flag whether present.
- [ ] `Mathlib.ModelTheory.Encoding` (or `.Godel` / `.Arithmetization`) — flag whether present.
- [ ] `DecidableEq` instances for terms / formulas — confirmed (audit-verify).
- [ ] `Function.Bijective` / `Encodable` for proof-code injection — confirmed (audit-verify).
- [ ] Existing `Sigma1` / `Pi1` arithmetic-hierarchy definitions — flag whether present.
- [ ] Mathlib's policy on `ℕ`-encoded proofs vs. inductive proof types — record convention.

Based on the audit outcome, the S6 ACT iteration recommends
Strategy A / B / C definitively.

## 14. References

- Gödel, K. (1931). *Über formal unentscheidbare Sätze der Principia
  Mathematica und verwandter Systeme I.* Monatshefte für Mathematik
  und Physik **38**, 173-198.
- Hilbert, D. & Bernays, P. (1939). *Grundlagen der Mathematik II.*
  Springer. (HBL conditions D1-D4.)
- Löb, M. H. (1955). *Solution of a problem of Leon Henkin.* J.
  Symbolic Logic **20**(2), 115-118.
- Solovay, R. M. (1976). *Provability interpretations of modal
  logic.* Israel J. Math. **25**, 287-304.
- Paulson, L. C. (2015). *A mechanised proof of Gödel's
  incompleteness theorems using Nominal Isabelle.* J. Automated
  Reasoning **55**, 1-37. (~15,000 lines; cited in parent
  `GodelIncompleteness.lean:77`.)
- Smoryński, C. (1985). *Self-Reference and Modal Logic.* Springer.
  (GL's modal axiom system; chapter 2 covers Solovay.)
- Boolos, G. (1993). *The Logic of Provability.* Cambridge UP. (GL
  textbook; Σ_1-completeness in chapter 1.)
- Robinson, R. M. (1952). *An essentially undecidable axiom system.*
  Proc. Intl. Congr. Math. Cambridge MA **1**, 729-730. (Σ_1
  representability.)
- Mathlib v4.26.0:
  - `Mathlib.ModelTheory.Language` — first-order languages.
  - `Mathlib.ModelTheory.Syntax` — terms, formulas, substitution.
  - `Mathlib.ModelTheory.Semantics` — satisfaction.
  - `Mathlib.ModelTheory.Theory` — theories and provability.
- This repo:
  - `proofs/Proofs/GodelIncompleteness.lean:75-78` — `Provable`
    placeholder definition and docstring caveat.
  - `proofs/Proofs/GodelIncompleteness.lean:131-134` —
    `diagonal_lemma` trivial-witness stub.
  - `proofs/Proofs/GodelSecondIncompletenessOQ02.lean:120-153` —
    `con_implies_G` axiom (replacable post-S11).
  - `research/problems/godel-second-incompleteness-oq02-oq-02/state.md:32-33` —
    explicit architectural-blocker flag.
  - `research/problems/godel-second-incompleteness-oq02-oq-02/sessions/`:
    - `2026-05-13-s1b-observe-typeclass-encoding-axiom-budget.md` (S1b OBSERVE).
    - `2026-05-13-s4-prep-lob-theorem-design.md` (S4 PREP).

## 15. Honesty statement

This document is **doc-only PREP**. It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in any current `.lean` file
- 0 axiom changes
- 0 changes to any other markdown file or to the gallery JSON
- 1 new design document (this file) in the existing `sessions/`
  subdirectory

The value is **architectural-scoping**: a future S6 ACT can run the
Mathlib audit per §5 in ~30 min and produce a definitive
Strategy A / B / C recommendation. Subsequent S7-S11 ACT iterations
implement the chosen strategy as a multi-iteration chain
(~3,000-5,000 LOC total over several weeks).

The PREP iteration does NOT discharge any open goal. Status
remains `in-progress` for the slug.

The "complete" Σ_1-formalization, once delivered (S∞), would
upgrade the gallery's `GodelIncompleteness` and
`GodelSecondIncompletenessOQ02` from "structural illustration"
to **fully verified Gödel-Löb provability theory on PA**, unlocking
the Solovay-completeness OQ-02 target as a downstream consequence.

---

**End of S6 PREP — no Lean changes, no gallery changes, no axiom
changes. New entry in the `sessions/` subdirectory.**
