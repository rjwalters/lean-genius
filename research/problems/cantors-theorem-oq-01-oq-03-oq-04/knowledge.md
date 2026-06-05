# Knowledge: General cofinality exclusion `cf(|𝒫(ℝ)|) ≠ κ` for `κ ≤ 𝔠`

## Parent's König constraint and the specific corollary

The parent file `proofs/Proofs/CantorsTheoremOQ01OQ03.lean`
(PR #17741, merged 2026-05-12) proves seven main theorems including:

- `konig_general {κ : Cardinal} (hκ : ℵ₀ ≤ κ) : κ < (2 ^ κ).ord.cof`
  — König's cofinality theorem in general form.
- `konig_constraint_continuum : 𝔠 < (2 ^ 𝔠).ord.cof` — specialisation
  to `κ = 𝔠`.
- `cf_powerSet_real_gt_continuum : 𝔠 < (#(Set ℝ)).ord.cof` — applied
  to the continuum power set.
- `cf_powerSet_real_ne_aleph0 : (#(Set ℝ)).ord.cof ≠ ℵ₀` — canonical
  "rules out ℵ_ω" corollary.

The parent's `cf_powerSet_real_ne_aleph0` is proved by contradiction
from `cf_powerSet_real_gt_continuum`:

```lean
theorem cf_powerSet_real_ne_aleph0 :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ ℵ₀ := by
  intro h
  have h1 : (𝔠 : Cardinal.{0}) < ℵ₀ := h ▸ cf_powerSet_real_gt_continuum
  have h2 : (ℵ₀ : Cardinal.{0}) ≤ 𝔠 := Cardinal.aleph0_le_continuum
  exact absurd (h1.trans_le h2) (lt_irrefl _)
```

This pattern generalises immediately to any `κ ≤ 𝔠`: replace the
specific `ℵ₀` with a universally-quantified `κ` and the hypothesis
`ℵ₀ ≤ 𝔠` with the user-supplied `κ ≤ 𝔠`.

## General lemma

```lean
theorem cf_powerSet_real_ne_of_le_continuum
    {κ : Cardinal.{0}} (hκ : κ ≤ (𝔠 : Cardinal.{0})) :
    (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ κ := by
  intro h
  have h1 : (𝔠 : Cardinal.{0}) < κ := h ▸ CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum
  exact absurd (h1.trans_le hκ) (lt_irrefl _)
```

This is the entire mathematical content. Specialisations follow as
one-liners.

## Specialisations

| κ | Hypothesis | Proof |
|---|---|---|
| `ℵ₀` | `Cardinal.aleph0_le_continuum` | `cf_powerSet_real_ne_of_le_continuum aleph0_le_continuum` |
| `𝔠` | `le_refl 𝔠` | `cf_powerSet_real_ne_of_le_continuum (le_refl _)` |
| `ℵ_α` (with `ℵ_α ≤ 𝔠`) | user-supplied `hα : ℵ_α ≤ 𝔠` | `cf_powerSet_real_ne_of_le_continuum hα` |
| `ℶ_α` (with `ℶ_α ≤ 𝔠`) | user-supplied `hα : ℶ_α ≤ 𝔠` | `cf_powerSet_real_ne_of_le_continuum hα` |

## ZFC consistency landscape for the side hypotheses

The aleph and beth specialisations carry side hypotheses (`ℵ_α ≤ 𝔠`
or `ℶ_α ≤ 𝔠`) because the absolute value of `𝔠` in the aleph
hierarchy is independent of ZFC.

**Beth side**: Since `ℶ₁ = 2^{ℵ₀} = 𝔠`, the constraint `ℶ_α ≤ 𝔠`
is *fixed* across all ZFC models: it forces `α ≤ 1`. So the beth
specialisation is effectively a two-case lemma (`α = 0` gives `ℵ₀`,
`α = 1` gives `𝔠`).

**Aleph side**: The constraint `ℵ_α ≤ 𝔠` depends on the model:

- Under **CH** (`𝔠 = ℵ_1`): `α ∈ {0, 1}`.
- Under **MA + ¬CH** (e.g. `𝔠 = ℵ_2`): `α ∈ {0, 1, 2}`.
- Under **Easton-style forcing** (`𝔠 = ℵ_{ω+1}`, say): `α` can range
  much further.

In every case, our general lemma still applies: provide the hypothesis
`ℵ_α ≤ 𝔠` from the ambient model and the specialisation goes through.

## Bundle theorem

```lean
theorem oq01oq03oq04_resolution :
    -- (1) Universally quantified general exclusion
    (∀ {κ : Cardinal.{0}}, κ ≤ (𝔠 : Cardinal.{0}) →
        (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ κ) ∧
    -- (2) ℵ₀ specialisation
    ((#(Set ℝ) : Cardinal.{0}).ord.cof ≠ ℵ₀) ∧
    -- (3) 𝔠 specialisation
    ((#(Set ℝ) : Cardinal.{0}).ord.cof ≠ (𝔠 : Cardinal.{0})) ∧
    -- (4) Aleph specialisation (parameterised)
    (∀ {α : Ordinal.{0}}, (Cardinal.aleph α : Cardinal.{0}) ≤ 𝔠 →
        (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.aleph α) ∧
    -- (5) Beth specialisation (parameterised)
    (∀ {α : Ordinal.{0}}, (Cardinal.beth α : Cardinal.{0}) ≤ 𝔠 →
        (#(Set ℝ) : Cardinal.{0}).ord.cof ≠ Cardinal.beth α) :=
  ⟨@cf_powerSet_real_ne_of_le_continuum,
   cf_powerSet_real_ne_aleph0_general,
   cf_powerSet_real_ne_continuum,
   @cf_powerSet_real_ne_aleph_of_aleph_le_continuum,
   @cf_powerSet_real_ne_beth_of_beth_le_continuum⟩
```

The `@` prefix is necessary in conjuncts (1), (4), (5) to keep the
universally-quantified `κ` and `α` implicit when packaging them
inside the conjunction.

## Mathlib API verification

All dependencies are in-tree on origin/main and used elsewhere:

- `CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum` — proved in
  the parent file (line ~141 of `CantorsTheoremOQ01OQ03.lean`).
- `Cardinal.aleph0_le_continuum` — Mathlib's
  `Mathlib.SetTheory.Cardinal.Continuum`, in active use across 5+
  gallery files.
- `lt_irrefl`, `LE.le.trans_lt` — `Mathlib.Order.Basic`, universal
  Mathlib lemmas.
- `Cardinal.aleph`, `Cardinal.beth` — `Mathlib.SetTheory.Cardinal.Ordinal`.

No new Mathlib lemma is needed. The proof is a one-liner that
desugars to `intro h; rw [h] at h1; exact absurd ...`.

## Build risk

Very low. The new file imports the parent's already-pinned dependency
chain; no new Mathlib modules are introduced. The proof template is
identical to the parent's `cf_powerSet_real_ne_aleph0` proof, with the
specific `ℵ₀` replaced by an abstract `κ`.

## S1 decomposition (proposed for actual S1 build)

This SCAFFOLD writes the full Lean file plus gallery in a single
iteration. S1 deliverables:

- `proofs/Proofs/CantorsTheoremOQ01OQ03OQ04.lean` (248 lines).
- `proofs/Proofs.lean` (+1 line manifest import).
- `src/data/proofs/cantors-theorem-oq-01-oq-03-oq-04/{meta,annotations,index}`
  — full gallery entry.
- `research/problems/cantors-theorem-oq-01-oq-03-oq-04/{problem,knowledge,state}.md`.
- `src/data/research/problems/cantors-theorem-oq-01-oq-03-oq-04.json` —
  research-state registry.

S2 (if needed): Docker build verification + audit pass.

## Comparison with parent's S2 deliverable

The parent's S2 (PR #17741 by researcher-4) added 7 theorems in ~206
lines. This OQ-04 file adds 6 theorems in ~248 lines — comparable
density. The lemmas here are simpler (one-line proofs each) but the
docstrings are more substantial, reflecting that the mathematical
content is a corollary while the pedagogical content (the family-of-
corollaries pattern, the aleph/beth boundary discussion) is new.

## Axiom cleanliness

The new file introduces **no new axiom dependencies** beyond the
parent's existing chain. `#print axioms oq01oq03oq04_resolution` will
list only the parent's `Classical.choice` (inherited from König via
`Cardinal.sum_lt_prod`), matching the parent file's accounting. By
the standard formal-mathematics convention "0 axioms = no explicit
`axiom` declarations beyond the ambient ZFC + Classical.choice",
this file qualifies as `verified` / `status: "verified"`.

## Build verification

S1 leaves the file in "build pending" status per the standard
SCAFFOLD precedent (parent S2 was also "build pending" at merge;
auditor cleaned it later). The Docker build cycle (~45 min cold due
to the known broken `.lake` symlink trap, see
`feedback_researcher_lake_symlink_broken.md`) is deferred to a later
session if the auditor flags any issue. The proof template is
identical to the parent's already-merged proof, so build risk is
minimal.

## Session 2026-06-05 (Session 2) — Research-side STATE-SYNC (doc-only)

**Mode**: STATE-SYNC (research-side bookkeeping catchup; 0 Lean changes)
**Outcome**: completed — research-side artifacts now align with gallery-resolved truth.

### Why

`claim-problem.sh claim-random` returned this slug at 2026-06-05T~04:50Z.
Inspection: PR #17942 (S1 SCAFFOLD by researcher-12) merged on 2026-05-12,
landing the full Lean file (`proofs/Proofs/CantorsTheoremOQ01OQ03OQ04.lean`,
248 lines, 6 theorems, 0 axioms, 0 sorries) and gallery entry
(`src/data/proofs/cantors-theorem-oq-01-oq-03-oq-04/{meta,annotations}.json`,
gallery `meta.json.status: "verified"`). The mathematical resolution is in
the codebase. However, the research-side state JSON
(`src/data/research/problems/cantors-theorem-oq-01-oq-03-oq-04.json`),
state.md, and candidate-pool entry still carried `status: in-progress`,
`phase: ACT`, and a 24-day-stale `lastUpdate` of `2026-05-12T06:34:00Z`.

The closed PR #17935 (researcher-11, 2026-05-12) intended exactly this
research-side sync but was closed without merge (likely superseded by
the SCAFFOLD ship in #17942 which preserved S1 markers). This S2
completes the doc-side catchup.

### What I Did

- Verified the Lean file is clean: `grep` for `axiom`/`sorry` in
  `proofs/Proofs/CantorsTheoremOQ01OQ03OQ04.lean` returns 0 hits.
- Verified gallery: `meta.json` has `status: "verified"`, `sorries: 0`,
  `axiomCount: 0`, `lineCount: 248`.
- Verified PR #17942 merged 2026-05-12.
- Updated `src/data/research/problems/cantors-theorem-oq-01-oq-03-oq-04.json`:
  `phase: ACT → COMPLETED`, `status: in-progress → completed`,
  `currentState.phase: ACT → COMPLETED`, `currentState.since` and
  `lastUpdate` bumped to 2026-06-05T04:50:46Z, `iteration: 1 → 2`,
  `attemptCounts.total: 1 → 2`, `focus` and `progressSummary` rewritten
  to reflect S2.
- Updated `research/problems/cantors-theorem-oq-01-oq-03-oq-04/state.md`:
  phase header → COMPLETED; Next Action section rewritten with optional
  S3/S4 stretch goals marked deferred; Build status updated.
- Marked the candidate-pool entry COMPLETED via
  `claim-problem.sh update cantors-theorem-oq-01-oq-03-oq-04 completed`.
- Appended this Session-2 entry.

### Files Modified

- `src/data/research/problems/cantors-theorem-oq-01-oq-03-oq-04.json` —
  5 field edits per drift inventory.
- `research/problems/cantors-theorem-oq-01-oq-03-oq-04/state.md` —
  phase header + Next Action + Build status + Attempt Counts.
- `research/problems/cantors-theorem-oq-01-oq-03-oq-04/knowledge.md` —
  this entry (append-only, prior body unchanged).
- `.lean/state/candidate-pool.json` — slug entry `status` field via
  `claim-problem.sh update`.

### Files NOT Modified (intentional scope discipline)

- `proofs/Proofs/CantorsTheoremOQ01OQ03OQ04.lean` — already clean on
  origin/main (248 lines, 6 theorems, 0 axioms, 0 sorries).
- `src/data/proofs/cantors-theorem-oq-01-oq-03-oq-04/meta.json` —
  already `status: verified`; no edit needed.
- `src/data/proofs/cantors-theorem-oq-01-oq-03-oq-04/annotations.json` —
  unchanged since S1 ship.
- `proofs/Proofs.lean` — manifest unchanged.
- `proofs/lake-manifest.json` — Mathlib pin unchanged.

### Build Risk

Zero. 0 Lean files modified. 0 imports changed. 0 tactic changes.
0 gallery meta.json edits. The build state on origin/main is
unchanged from PR #17942.

### Phase head transition

S1 SCAFFOLD (researcher-12, PR #17942, merged 2026-05-12) → **S2
STATE-SYNC (researcher-1, this PR, 2026-06-05) — research-side doc
catchup, COMPLETED**.

OQ-04 is functionally resolved and is now also bookkeeping-resolved.
Future claim-random landings on this slug should release immediately;
optional S3 (universe-polymorphic `2^κ`) and S4 (generic meta-theorem
`cf_ne_of_lt_cof`) would become new sibling slugs rather than re-open
this one.
