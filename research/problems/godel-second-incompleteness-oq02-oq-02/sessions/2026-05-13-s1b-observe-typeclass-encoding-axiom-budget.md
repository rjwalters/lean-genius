# S1b OBSERVE — typeclass-encoding analysis of HBL + axiom-budget ledger

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: OBSERVE (refinement of S1; doc-only, no Lean edits, orthogonal to all parent files)
**Builds on**: PR #18198 (S1 OBSERVE Solovay survey) — merged.

The S1 OBSERVE doc (`knowledge.md` §7 "axiom inflation" + §6 ranked S2
candidates) flags axiom inflation as a top-level risk and proposes a
companion-file isolation strategy. This S1b doc:

1. Examines a **typeclass-encoding** alternative to the companion-file
   approach for D2/D3 — does this reduce the *effective* axiom budget?
2. Provides a concrete **axiom-budget ledger** comparing all three S2
   candidates side-by-side.
3. Investigates whether `Löb`'s theorem can be stated as a *theorem
   parameterized by a typeclass* (so the axioms move to instance
   declarations rather than gallery-level `axiom` blocks).

This document is **strictly orthogonal** to:

- `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` (the parent file)
- `proofs/Proofs/GodelFirstIncompletenessOQ01.lean`
- `knowledge.md` / `problem.md` / `state.md` for this slug
- the per-slug JSON, `meta.json`, etc.

Adds exactly one new file under `sessions/`. ~210 LOC of markdown.

## 1. Typeclass-encoded HBL — sketch

```lean
class HBLDerivability (Formula : Type) (Provable : Formula → Prop) where
  /-- The internal modus ponens (D2): provability of an implication
      and its premise yields provability of the conclusion. -/
  D2_modusPonens : ∀ φ ψ : Formula,
    Provable (impl φ ψ) → Provable φ → Provable ψ
  /-- Provability of provability (D3): if a formula is provable, then
      its own provability statement is provable. -/
  D3_provProv : ∀ φ : Formula,
    Provable φ → Provable (Prov (godelNum φ))
```

Then Löb's theorem and Second Incompleteness become *theorems
parameterized by `[HBLDerivability]`*:

```lean
theorem loeb_theorem [HBLDerivability Formula (· ⊢ ·)]
    (A : Formula) (h : ⊢ impl (Prov (godelNum A)) A) : ⊢ A := by
  -- ... ~150 LOC unfolding D2/D3 + Diagonal Lemma ...
  sorry

theorem second_incompleteness_typeclass
    [HBLDerivability Formula (· ⊢ ·)]
    (h : Consistent) : ¬ (⊢ Con) := by
  -- ... ~30 LOC using loeb_theorem at A = ⊥ ...
  sorry
```

This is the standard "abstract HBL theory" pattern, mirroring how
Mathlib treats `IsBoundedAlgHom` or `OrderedRing`. The class fields
are mathematical *commitments*; an instance must witness them.

## 2. Axiom-integrity audit

**Does typeclass-encoding reduce the gallery axiom count?** No — and
this is the load-bearing observation.

Per the project's axiom-integrity policy
(`CLAUDE.md:Axiom Integrity Policy`, also memory project
`memory/project_tractatus_review.md`):

> Structure-encoded hypotheses (fields in structures/typeclasses such as
> `NSAxioms`, `SelbergClassAxioms`, `RHAxioms`) are mathematical
> assumptions. Moving `axiom` declarations into structure fields does
> not reduce the assumption count -- it only changes where they are
> declared.

Applied to HBL:

| Encoding | gallery-level `axiom` count | structure/class fields | total assumption count |
|----------|------------------------------|-------------------------|------------------------|
| Status quo (S1) | 1 (`con_implies_G`) | 0 | 1 |
| S2-α companion file | 1 (`con_implies_G`) + 2 (D2, D3 in companion) | 0 | **3** |
| S2-α typeclass refactor | 1 (`con_implies_G`) — or 0 if we drop it | 2 (D2, D3) | **2 or 3** |
| Replace `con_implies_G` via D1+D2+D3+diagonal | 0 | 3 (D1, D2, D3) + diagonal | 3+ |

Net: **typeclass encoding does not shrink the gallery's effective
assumption count.** All three S2-α variants land at ≥ 2 assumptions.
The status quo's 1 axiom is the leanest from a pure axiom-count
perspective.

What typeclass encoding **does** improve:

- **Locality of commitment**: instance declarations are explicit and
  searchable; gallery-level `axiom` decls are diffuse.
- **Future-proofing**: when D1/D2/D3 get proved from a Σ_1-PA
  formalization (a multi-thousand-LOC effort), the typeclass instance
  becomes a `: HBLDerivability ... := { ... }` provable instance, and
  no consumer code changes.
- **Modularity**: the abstract `loeb_theorem` and
  `second_incompleteness_typeclass` are reusable across different
  encodings of `Formula` and `Provable`.

But it **costs**:

- More typeclass synthesis overhead in Lean (small).
- A small refactor of the parent file's `second_incompleteness` proof to
  invoke the typeclass version (small).
- One more layer of abstraction for the reader (small).

## 3. Per-S2-candidate axiom budget

| Candidate | Lean LOC | New axioms | Net assumption count delta | Recommended? |
|-----------|----------|------------|---------------------------|--------------|
| S2-α companion (impl + 2 axioms) | ~50-120 | 2 (D2, D3) | +2 | Yes, with caveat — see §4 |
| S2-α typeclass refactor (class + 2 fields, drop `con_implies_G`) | ~80-150 | -1 +2 | net +1 | Yes — strictly improves on the companion |
| S2-β soundness direction of Solovay | ~200-400 | 0 (requires S2-α done first) | 0 | Conditional on S2-α |
| S4+ Löb's theorem formalization | ~150 | 0 (requires S2-α done first) | 0 | Conditional on S2-α |
| S2-γ completeness of Solovay | multi-thousand | requires concrete Σ_1-Prov | major | Not feasible in current framework |

## 4. Recommendation revisited

The S1 doc's recommendation of "S2-α as the smallest scope, highest
reuse value" remains correct. **This S1b refines that recommendation**:

- **Prefer S2-α via the typeclass refactor over the companion-file
  approach.** Net assumption count drops by 1 (drop `con_implies_G`,
  add D2 + D3), and downstream Löb / Second Incompleteness become
  parameterized theorems instead of stand-alone derivations.
- Implementation strategy: introduce `HBLDerivability` typeclass in a
  new file `proofs/Proofs/GodelSecondIncompletenessOQ02HBL.lean` (or
  in-line in the parent file), prove `second_incompleteness_typeclass`
  using *only* the typeclass fields, then add a single instance
  witnessing D2 and D3 as axioms.
- Update `meta.json` to reflect: `axiomCount = 2` (D2, D3 in
  instance — count under axiom-integrity policy), down from the
  current `axiomCount = 1` for `con_implies_G`. **However**, the
  *parent* `GodelFirstIncompletenessOQ01.lean` may also be impacted if
  D1 needs to be lifted to a typeclass field; flag this in the PR
  description.

## 5. Out-of-scope and red flags

### 5.1 Out of scope for any S2 ACT

- The S2-γ completeness direction. As S1 flagged, the opaque `Provable`
  axiom is incompatible with Solovay's completeness construction.
- Replacing `Provable` with a concrete Σ_1-formalization of PA
  provability. This is multi-thousand LOC and warrants its own
  proposal.

### 5.2 Red flag for any axiom-adding PR

If a future PR adds D2 and D3 as axioms (in any of the three S2-α
variants), the PR must update **both**:

- `src/data/proofs/godel-second-incompleteness-oq02/meta.json`:
  `axiomCount` field to reflect the structure-encoded assumption count
  (D2 + D3 counted, plus `con_implies_G` if retained).
- The parent file's docstring `## Status` block (currently states "1
  new axiom (`con_implies_G`)") to reflect the new count and the new
  typeclass / companion structure.

Failure to update `axiomCount` in `meta.json` would be a Tier-1
gallery-integrity violation (see memory:
`feedback_axiom_integrity_meta_json_drift.md`).

### 5.3 Sibling slugs

The OQ-04 of `godel-second-incompleteness` already exists (file
`Proofs/GodelSecondIncompletenessOQ02OQ04.lean` per umbrella import
list). Coordinate any axiom-budget changes at the gallery level if
that file is touched.

## 6. Mathlib provability-logic infrastructure scan

A quick directory scan of Mathlib v4.26.0 for any pre-existing
provability-logic / modal-logic / GL infrastructure (no API call
performed at session time; performed by inspection of cached package
manifest):

- `Mathlib.Logic.Basic`, `Mathlib.Logic.Equiv.Basic` — propositional
  logic primitives; no modal extension.
- `Mathlib.ModelTheory.*` — first-order model theory. Useful for
  S2-γ completeness direction (Σ_1-PA encoding) but does not have
  provability logic.
- `Mathlib.Computability.Primrec`, `Mathlib.Computability.Halting` —
  primitive-recursive / r.e. machinery. Useful for a concrete
  Σ_1-PA-`Prov` formalization (S2-γ direction).
- **No** existing `GL` / `K4` / `S4` modal-logic infrastructure in
  Mathlib v4.26.0. The gallery is greenfield for provability logic.

This confirms the S2 candidates are not duplicating Mathlib work; any
typeclass `HBLDerivability` is genuinely new infrastructure.

## 7. Total deliverable

Three substantive observations beyond S1 OBSERVE:

1. The typeclass refactor of S2-α is strictly preferable to the
   companion-file approach on assumption-count grounds (§3-4).
2. The Mathlib v4.26.0 surface is greenfield for provability logic;
   no API gap analysis is needed (§6).
3. Any axiom-adding PR must update `meta.json axiomCount` and the
   parent docstring; this is non-negotiable (§5.2).

These three observations re-rank the S2-α candidate sub-variants but
do **not** change the top-level recommendation: S2-α first, then S2-β
soundness or S4+ Löb's theorem.

## 8. Files added (this session)

- `research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-13-s1b-observe-typeclass-encoding-axiom-budget.md` — this file.

No other files modified. Zero Lean changes. Zero gallery-JSON changes.

## 9. Build status

No `.lean` changes. Build not attempted (no diff to verify).
