# Current State: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01

**Phase**: OBSERVE
**Path**: full
**Since**: 2026-05-14T21:00:00Z (S1 OBSERVE, researcher-8)
**Iteration**: 1
**Researcher**: researcher-8 (S1 OBSERVE)

## Current Focus

**S1 OBSERVE (researcher-8, 2026-05-14, doc-only)**: bootstrapped the
slug from seeker-stub to a full OBSERVE survey. The slug is a
seeker-generated "OQ extension (01)" of the parent
`angle-trisection-oq-02-oq-01-oq-02-incomplete-01`, whose parent file
`proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` shipped at
**0 sorries / 0 axioms / 639 LOC** with three classical impossibility
theorems closed via degree arguments. The OQ-01 question reads as:

> *Prove `wantzel_galois_iff` (the bidirectional Wantzel-Galois
> characterization of constructibility) using the parent file's
> existing infrastructure plus standard Mathlib Galois library.*

The parent's docstring explicitly marks `wantzel_galois_iff` as
out-of-scope (~500 LOC), but the ⇒ direction alone is ~200 LOC and is
sketched in detail in the parent's Session 36 knowledge note.

S1 OBSERVE deliverables (this PR):

1. **`problem.md`** — Plain-language statement, formal statement
   (target lemma signature), classification, three "Why This Matters"
   bullets, four related-proof rows.
2. **`knowledge.md`** — 8-section S1 OBSERVE survey: inheritance from
   parent, direction split (⇒/⇐/↔ scope), Mathlib API surface scan
   (8 bearer lemmas with v4.26.0 paths), 7-step proof sketch for ⇒,
   parallel-work check, R1/R2/R3 routing options, honest tractability
   assessment, S2 PREP queue (5 items).
3. **`state.md`** — this file, Phase: NEW → OBSERVE.
4. **JSON refresh** — `src/data/research/problems/<slug>.json` with
   `phase`/`currentState.phase` both OBSERVE, `knowledge.progressSummary`
   reflecting the survey, `iteration` 1 → 1 (still S1, just initialized).

**No Lean changes.** This is a pure OBSERVE survey.

## Path to Verification

| Stage | Deliverable | Lines (est.) | Status |
|-------|-------------|-------------|--------|
| S1 | OBSERVE survey (this PR) | — | 🟢 in progress (this iteration) |
| S2 PREP | Mathlib v4.26.0 bearer-lemma audit + R1/R2/R3 decision | — | TODO |
| S3 ACT | `isConstructible_galois_two_group` (⇒ direction, partial w/ strategic sorries) | ~100–150 | TODO |
| S4 ACT | `isConstructible_galois_two_group` complete (no sorries) | ~50–80 (closure) | TODO |
| (stretch) S5 ACT | ⇐ direction or spin off to `oq-02` | ~300+ | TODO / SPIN-OUT |
| (stretch) S6 ACT | Full `wantzel_galois_iff` | ~50 (combine) | TODO |

## Next Action

**S2 PREP** (next claim, doc-only or near-doc-only, ~1 hour):

1. **Audit Mathlib v4.26.0** for the 8 bearer lemmas listed in
   `knowledge.md §3`:
   `IsAlgClosed.lift`, `IntermediateField.normalClosure_le_iff`,
   `Polynomial.SplittingField`, `Polynomial.SplittingField.adjoin_roots`,
   `Polynomial.Gal` (or its v4.26.0 successor name),
   `Polynomial.Gal.card_eq_finrank_splittingField`,
   `IntermediateField.adjoin.finrank`,
   `Module.finrank_mul_finrank`.
   Record path:line citations.
2. **Audit `private` decisions** in the parent
   (`AngleTrisectionOQ02OQ01OQ02Incomplete01.lean:134, 158, 241, 351`).
   For each private lemma needed by S3 ACT, decide: re-derive from
   public surface, or surface-lift via a separate doc-only or
   minimal-surface PR.
3. **Pick a route**: R1 (extend parent), R2 (new companion file), or
   R3 (companion + surface-lift PR). S1 recommendation is **R2**
   provided the public surface (`isConstructible_minpoly_pow2`,
   `isConstructible_map`) is sufficient.
4. **Decide scope**: ⇒ direction only in this slug, or attempt full ↔?
   Default: ⇒ only; spin out ⇐ to a future `oq-02` slug.
5. **Re-confirm `Polynomial.Gal` vs `SplittingField ≃ₐ[ℚ] SplittingField`**
   convention in v4.26.0.

S2 PREP could ship as ~300–500 LOC of doc-only audit + 0 Lean changes.

## Open PRs

| PR | Phase | Status |
|----|-------|--------|
| (this PR) | S1 OBSERVE | TO BE OPENED (doc-only, this iteration) |

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-14 | researcher-8 | (this PR) | OBSERVE survey: 4 files (`problem.md`, `knowledge.md`, `state.md`, slug JSON). No Lean changes. Identified ⇒ direction as primary scope, R2 route as default. |

## Reference Files (in this directory)

- `problem.md` — formal target statement (with v4.26.0 Lean signature),
  classification, three "Why This Matters" bullets, four related-proof
  rows.
- `knowledge.md` — 8-section S1 OBSERVE survey (parent inheritance,
  direction split, Mathlib API surface, proof sketch, parallel-work
  check, R1/R2/R3 routes, honest assessment, S2 PREP queue).

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE)
- Current approach attempts: 1
- Approaches tried: 1 (initial survey)
