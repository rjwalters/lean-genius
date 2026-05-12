# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12T20:30:00Z
**Iteration**: 1
**Last update**: 2026-05-12 (S1 OBSERVE by researcher-1)

## Current Focus

S1 OBSERVE — survey of the local `IsClubBelow` / `IsStationaryBelow` /
`diagInter` infrastructure in `proofs/Proofs/FodorPressingDown.lean`,
alignment with Mathlib's existing ordinal-topology API
(`Mathlib.SetTheory.Ordinal.Topology`, `Cardinal.Cofinality`,
`Cardinal.Regular`), naming convention lock, and a four-phase
refactor plan to lift the infrastructure into a standalone
`Proofs/Club/Basic.lean` module.

## Active Approach

**Doc-only S1 OBSERVE.** No Lean changes in this iteration. The
deliverable is three markdown files + one JSON gallery entry:

- `problem.md` — formal signature targets (5 defs + 3 theorems),
  acceptance criteria, related slugs.
- `knowledge.md` — inventory of current local API, Mathlib alignment
  survey, naming-convention decision lock (Option A: `Ordinal`
  namespace), file-path decision lock (Option 1: `proofs/Proofs/Club/
  Basic.lean`), four-phase migration plan, risk register, sister-slug
  compatibility design (`fodor-pressing-down-oq-04` Solovay
  splitting).
- `state.md` (this file).
- `src/data/research/problems/fodor-pressing-down-oq-01.json` —
  gallery entry, status `in-progress`, phase `OBSERVE`, knowledge
  payload summarising the survey.

## S1 Summary

### Locked design decisions

1. **Naming.** `Ordinal.IsUnboundedBelow`, `Ordinal.IsClubBelow`
   (structure with three fields), `Ordinal.IsStationaryBelow`,
   `Ordinal.diagInter`, `Ordinal.IsRegressive` — all in the `Ordinal`
   namespace, matching `Ordinal.IsAcc` (existing in Mathlib).
2. **File path.** `proofs/Proofs/Club/Basic.lean`. New directory
   `proofs/Proofs/Club/` introduced for future siblings
   (`DiagonalIntersection.lean`, `Galvin.lean`, etc.).
3. **Universe polymorphism.** Definitions stay universe-polymorphic
   in the new module; combinatorial lemmas (`diagInter_isClubBelow`,
   `fodor`) remain pinned at `Cardinal.{0}` until a downstream
   request appears.
4. **Structure vs Prop.** `IsClubBelow` is a `structure` (three
   fields), matching the local file. `IsUnboundedBelow`,
   `IsStationaryBelow`, `IsRegressive`, `diagInter` are
   `def`-bindings returning `Prop` / `Set Ordinal`.

### Migration plan (committed)

- **S2 ACT**: ship `proofs/Proofs/Club/Basic.lean` with the five
  definitions + three mechanical lemmas (~80 Lean LOC, 0 sorries).
  Add `import Proofs.Club.Basic` to `proofs/Proofs.lean`. Build-
  pending tolerable.
- **S3 ACT**: move `diagInter_isClosedBelow` from parent to new
  module (~28 LOC migration, parent decreases by 28).
- **S4 ACT**: trim `proofs/Proofs/FodorPressingDown.lean` — remove
  the five moved definitions and three moved lemmas; add `import
  Proofs.Club.Basic`. Update `meta.json` `lineCount` /
  `theoremCount` for `fodor-pressing-down-oq-04`. Net parent
  delta ≈ –150 LOC.
- **S5 (optional)**: doc-only update to `fodor-pressing-down-oq-04`'s
  `problem.md` recording the new dependency path.

### Mathlib alignment summary

- **In Mathlib already**: `IsClosedBelow`, `Ordinal.IsAcc`,
  `Cardinal.cof`, `Cardinal.IsRegular`, `Cardinal.IsRegular.aleph0_le_cof`.
- **New code required**: `IsUnboundedBelow`, `IsClubBelow`,
  `IsStationaryBelow`, `diagInter`, `IsRegressive` plus their
  mechanical and combinatorial supporting lemmas.

### Sister-slug compatibility

`fodor-pressing-down-oq-04` (Solovay splitting, NEW phase since
2026-05-12 14:35 UTC) is the primary downstream consumer. Its
eventual Lean file will start with `import Proofs.Club.Basic` and
use `Ordinal.IsStationaryBelow` directly. Without OQ-01 lifted,
OQ-04 either inlines duplicate predicates or depends on the entire
parent `FodorPressingDown.lean`. The plan unblocks OQ-04 once S4
lands.

## Blockers

None mathematical. The refactor is mechanical; the only operational
risk is parent-file `build pending` during the S2 → S4 sequence,
mitigated by ordering the commits as additive-first
(S2 introduces, S3 moves trivia, S4 cuts parent).

**Operational:** worktree `proofs/.lake` symlink is recursive
(`feedback_researcher_lake_symlink_broken.md`); local docker build is
~25–45 min. S1 OBSERVE is doc-only — no build needed.

## Next Action

**S2 ACT — any researcher.** Create `proofs/Proofs/Club/Basic.lean`
with the locked-naming API:

```lean
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Tactic

namespace Ordinal

open Set Order

/-- A set S is unbounded below ordinal o. -/
def IsUnboundedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ α < o, ∃ β ∈ S, α < β ∧ β < o

/-- A club (closed unbounded) set below ordinal o. -/
structure IsClubBelow (S : Set Ordinal) (o : Ordinal) : Prop where
  subset_Iio : S ⊆ Iio o
  closed     : IsClosedBelow S o
  unbounded  : IsUnboundedBelow S o

/-- A set S is stationary below o if it meets every club below o. -/
def IsStationaryBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty

/-- Diagonal intersection of an ordinal-indexed family below o. -/
def diagInter (f : Ordinal → Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {γ | γ < o ∧ ∀ β < γ, γ ∈ f β}

/-- Regressiveness: f α < α for every nonzero α ∈ S. -/
def IsRegressive (f : Ordinal → Ordinal) (S : Set Ordinal) : Prop :=
  ∀ ⦃α⦄, α ∈ S → α ≠ 0 → f α < α

theorem IsClubBelow.mem_lt {S : Set Ordinal} {o : Ordinal}
    (hS : IsClubBelow S o) {α : Ordinal} (hα : α ∈ S) : α < o :=
  hS.subset_Iio hα

theorem IsClubBelow.mem_of_isAcc {S : Set Ordinal} {o : Ordinal}
    (hS : IsClubBelow S o) {α : Ordinal} (hα : α < o) (hAcc : α.IsAcc S) : α ∈ S :=
  hS.closed.forall_lt α hα hAcc

theorem mem_diagInter {f : Ordinal → Set Ordinal} {o γ : Ordinal} :
    γ ∈ diagInter f o ↔ γ < o ∧ ∀ β < γ, γ ∈ f β := Iff.rfl

theorem diagInter_subset_Iio (f : Ordinal → Set Ordinal) (o : Ordinal) :
    diagInter f o ⊆ Iio o :=
  fun _ h => h.1

theorem isClubBelow_Iio_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) :
    IsClubBelow (Iio o) o where
  subset_Iio := fun _ h => h
  closed := by rw [isClosedBelow_iff]; intro p pltq _hacc; exact pltq
  unbounded := fun α hα => by
    have h1 : α + 1 < o := ho.succ_lt hα
    exact ⟨α + 1, h1, lt_add_one α, h1⟩

end Ordinal
```

Then update `proofs/Proofs.lean` with the alphabetical `import
Proofs.Club.Basic` line. Build-pending acceptable.

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE)
- Current approach attempts: 1
- Approaches tried: 1 (library refactor with `Ordinal`-namespace
  naming and `Proofs/Club/Basic.lean` placement)

## Open files

- `problem.md` — formal scope and signature targets (this PR).
- `knowledge.md` — Mathlib alignment survey and migration plan (this PR).
- `state.md` (this file).
- (downstream) `proofs/Proofs/FodorPressingDown.lean` — the source
  file from which definitions will be lifted; **not touched** in S1.

## Race awareness

OQ-01 has zero open PRs at S1 push time (verified 2026-05-12 20:30
UTC via `gh pr list --search "fodor-pressing-down-oq-01 in:title"`).
The slug was seeker-selected (added 2026-05-12 14:35 UTC same batch
as oq-04) and currently has 0 prior merges (no `Enrich
fodor-pressing-down-oq-01`, no `audit`-tracker line). The sister slug
`fodor-pressing-down-oq-04` is NEW and has zero recent PR activity
either. Re-entry risk: a parallel researcher attempting the same S1
OBSERVE during the ~5 min between PR draft and PR creation. Mitigated
by writing a doc-only PR with full migration plan locked in; any
parallel attempt would either duplicate the survey (waste) or
disagree on naming (rejected at review).
