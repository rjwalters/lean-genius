# Current State

**Phase**: PREP (S2 complete; S3 ACT pending)
**Since**: 2026-05-14T03:05:23Z (S2 PREP merge UTC)
**Iteration**: 2 (S1 OBSERVE, S2 PREP per-row API sketches)
**Researcher**: researcher-3 (S1); researcher-10 (S2 PREP); researcher-4 (S2b body+JSON sync, this PR)

## Current Focus

S2 PREP (PR #18946) operationalised §2 of `knowledge.md` (the 9-row
solvable-subgroup table) into concrete Lean signatures + Mathlib lemma
chains for the **three easier rows**:

| Row | Realization | LOC est | Axioms |
|-----|-------------|---------|--------|
| ℤ/n (n ≤ 4) | wrapper of `OQ-05-OQ-01.cyclic_realizable` | ≤10 | 0 |
| V₄ | cyclotomic ζ₁₂ via `IsCyclotomicExtension.Rat.aut_equiv_pow` | 40–60 | 0 |
| S₃ | `X³ − 2` + Eisenstein + `Polynomial.Gal.galActionHom` cardinality | 80–120 | 0 |

D₄ / A₄ / S₄ are **explicitly deferred** — each requires a resolvent-cubic
Mathlib helper namespace that does not currently exist (potentially its
own Mathlib PR). Overpromising on those rows in markdown without buildable
Lean infrastructure would inflate the slug's perceived progress.

Distinguishing this slug from siblings remains the S1 framing:
`abel-ruffini-galois-extensions-oq-05` (full Shafarevich axiom),
`abel-ruffini-galois-extensions-oq-05-oq-01` (cyclic + coprime abelian
proved). OQ-04-OQ-09 carves out the axiom-free `n ≤ 4` slice that closes
the parent's threshold theorem constructively.

## Active Approach

**S1 deliverable** (PR pending merge — see Session Log): OBSERVE scaffold.
- `problem.md`: full statement, classification, scope.
- `knowledge.md`: Mathlib API survey + per-row realization menu.
- `state.md`: this file.
- `src/data/research/problems/abel-ruffini-oq-04-oq-09.json`: registry
  updates (phase OBSERVE, problem statement, knownResults, related proofs).

**S2 PREP deliverable** (PR #18946 merged 2026-05-14 03:05Z): doc-only
expansion of `knowledge.md` §4.5 with per-row Mathlib API paths for the
three easier rows + session memo. State.md header bumped; body refresh
deferred to S2b (this PR).

**S2b STATE-SYNC** (this PR): refresh state.md body + JSON registry to
match S2 PREP header. Explicitly NOT touching Lean (none exists yet),
knowledge.md (already current via PR #18946), or problem.md (unchanged).

**No Lean changes yet.** First Lean work is S3 ACT (recommended: cyclic
wrapper as smallest probe).

## Findings (cumulative S1+S2)

1. **The OQ-04-OQ-09 slug is NOT a duplicate of OQ-05.** OQ-05
   axiomatizes the full theorem; OQ-04-OQ-09 carves out the axiom-free
   `n ≤ 4` slice that closes the parent's threshold theorem
   constructively.

2. **9 distinct group structures** appear as transitive Galois groups of
   irreducible polynomials of degree ≤ 4 over ℚ: `{e}, ℤ/2, ℤ/3, ℤ/4,
   V₄, S₃, D₄, A₄, S₄`. All 9 are solvable (matches parent's threshold
   theorem) and all 9 admit explicit ℚ-realizations using Mathlib's
   cyclotomic + splitting-field infrastructure.

3. **Mathlib gaps**: none for cyclic + V₄ rows; S₃/D₄/A₄/S₄ each require
   ~80-300 lines of polynomial-Galois-group identification (no missing
   infrastructure for S₃; D₄/A₄/S₄ need a resolvent-cubic helper
   namespace not currently in Mathlib).

4. **Sibling reuse**: OQ-05-OQ-01's `cyclic_realizable` already handles
   `ℤ/n` for `n ∈ {2, 3, 4}`. The new gallery entry imports that lemma
   and adds the non-abelian cases incrementally.

5. **S2 PREP findings** (new): three concrete Lean signatures + Mathlib
   lemma chains identified for cyclic / V₄ / S₃. Each cited Mathlib
   symbol verified at lake-pinned rev `2df2f015...` (Mathlib v4.26.0)
   against in-repo precedent (`InverseGalois.lean`,
   `NthRootIrrationalOQ01.lean`, `AbelRuffiniGaloisExtensions.lean`).
   No new mathematical claims — content cribbed from Conrad's notes,
   Jensen–Ledet–Yui, and existing OQ-05-OQ-01 patterns.

## Blockers

For S3+:
- Broken `proofs/.lake` symlink → ~45 min cold-build cycles (see
  `feedback_researcher_lake_symlink_broken.md`). Plan build budget
  accordingly: batch cyclic + V₄ + S₃ into one Docker cycle if possible.

### Risks

- **Sibling drift**: if a parallel session updates
  `AbelRuffiniGaloisExtensionsOQ05` to remove the Shafarevich axiom
  (e.g. by importing a Mathlib PR), OQ-04-OQ-09's "axiom-free n ≤ 4
  slice" framing becomes less novel. Re-check at S3 start.
- **V₄ path B-2 `decide` step**: `(ℤ/12)× ≅ ℤ/2 × ℤ/2` is asserted as a
  1-line `decide` in S2 PREP §4.5.B, but `decide` on `Equiv.Perm` may
  involve elaborator gymnastics requiring an explicit construction
  (~5-20 extra LOC). S3 ACT should budget for this contingency.
- **S₃ cardinality argument LOC**: S2 PREP §4.5.C estimates 80-120 LOC
  for S₃; the `IntermediateField.adjoin_finrank` chain
  `[ℚ(∛2, ζ₃) : ℚ] = [L : ℚ(∛2)] · [ℚ(∛2) : ℚ] = 2 · 3 = 6` has no
  pre-packaged wrapper. May need an interleaved `have hζ ∉ ℝ` block.
- **D₄/A₄/S₄ deferred indefinitely**: the resolvent-cubic helper
  namespace is its own research scope. The slug ships with rows 1-6
  (cyclic + V₄ + S₃) as a first cut; rows 7-9 wait for a later
  iteration or a Mathlib PR.

## Next Action

**S3 ACT — implement the cyclic/V₄/S₃ trio in Lean.**

Create `proofs/Proofs/AbelRuffiniOQ04OQ09.lean` (~150 LOC, 0 axioms
beyond `Classical.choice`). Recommended order:

1. **Cyclic wrapper** (≤10 LOC, lowest risk). Re-exports
   `AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` specialised
   to `n ∈ {2, 3, 4}`. First buildable target.
2. **V₄** (40-60 LOC). Path B-2: cyclotomic `ζ₁₂`, Galois group
   `(ℤ/12)× ≅ ℤ/2 × ℤ/2` via `IsCyclotomicExtension.Rat.aut_equiv_pow`.
3. **S₃** (80-120 LOC). `X³ − 2` Eisenstein at 2; splitting field
   `ℚ(∛2, ζ₃)` of degree 6; `Polynomial.Gal.galActionHom` injective +
   cardinality 6 forces surjective into `S₃`.

Plan: batch all three before the first Docker build to amortise the
~45 min cold start. If V₄ `decide` step balloons, ship cyclic + S₃
first, defer V₄ to S3b.

**Alternative S3 ACT — single-row probe**: ship cyclic wrapper only as a
10-LOC API-surface confirmation, defer V₄ + S₃ to S3b/S3c. Lower risk
per PR but slower aggregate progress.

**Anti-target (S3)**: do NOT start D₄/A₄/S₄. Wait until a separate
researcher session packages the resolvent-cubic helper namespace.

## Attempt Counts

- Total attempts: 0 (S1 and S2 are documentation-only)
- Current approach attempts: 0
- Approaches tried: 0

## Session Log

- **S1** (2026-05-12, researcher-3, PR #17764) — OBSERVE scaffold.
  Identified the three sibling gallery entries (OQ-05, OQ-05-OQ-01,
  InverseGalois) that already touch Shafarevich and narrowed
  OQ-04-OQ-09's scope to the axiom-free `n ≤ 4` slice. Surveyed
  Mathlib API surface for cyclotomic Galois groups, splitting fields,
  and `Polynomial.Gal`. Catalogued the 9 target group structures.
  **No Lean code; no build.**
- **S2 PREP** (2026-05-13, researcher-10, PR #18946) — doc-only
  per-row Mathlib API path sketches for cyclic / V₄ / S₃. Added
  `knowledge.md §4.5` (+93 LOC), bumped state.md header
  `OBSERVE → S2 PREP complete`, shipped session memo (+165 LOC).
  Explicitly deferred D₄/A₄/S₄ (need resolvent-cubic helper). Each
  cited Mathlib symbol cross-checked against in-repo precedent at
  lake-pinned rev. **No Lean code; no build.** JSON sync deferred.
- **S2b STATE-SYNC** (2026-05-14, researcher-4, this PR) — refresh
  state.md body (Focus/Approach/Findings/NextAction/SessionLog) and
  JSON registry (`phase`, `currentState.{phase,since,iteration,focus,
  nextAction}`, `knowledge.{progressSummary,builtItems,nextSteps}`,
  top-level `lastUpdate`) to match the S2 PREP header. No Lean, no
  knowledge.md, no problem.md edits. **Doc-only sync.**

## Honest Calibration (S2b)

This S2b STATE-SYNC:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify the S2 PREP API path sketches (S3 ACT will).

It does:

- Align `state.md` body with the `S2 PREP complete` header.
- Update the JSON registry's top-level `phase` and `lastUpdate` so
  `research-listings.json` (via `scripts/research/build.ts`) and the
  `ResearchPage` gallery reflect post-S2 reality. (Per memory
  `feedback_researcher_state_sync_misses_top_level_phase`.)
- Update `currentState.{phase, since, iteration, focus, nextAction}`
  and `knowledge.{progressSummary, builtItems, nextSteps}` so any
  subsequent agent reading the JSON sees the correct iteration and
  next-action target.
- Set a concrete S3 ACT plan (three-row Lean implementation, recommended
  ordering, anti-target).

The S2 PREP author explicitly deferred this JSON sync to a separate PR
(see PR #18946 §5 "Out of scope"); this S2b is that separate PR.
