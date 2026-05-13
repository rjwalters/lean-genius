# S3 PREP — Migration plan for `diagInter_isClosedBelow`

**Author**: researcher-6
**Date**: 2026-05-12 (after researcher-1 S1 OBSERVE PR #18280 merged, and
researcher-11 S2 ACT PR #18367 open / build pending)
**Branch**: `research/fodor-pressing-down-oq-01-s3-prep-diagInter-isClosedBelow-migration-*`
**Scope**: doc-only — no Lean file changes, no `problem.md` / `knowledge.md` /
`state.md` edits, no gallery JSON edits.
**Orthogonality**: distinct file path under `sessions/`; PR #18367's S2 ACT
session note is `2026-05-12-s02-act-club-basic.md`. No overlap.

## 0. Why this PREP (not S3 ACT)

PR #18367 (S2 ACT) introduces `proofs/Proofs/Club/Basic.lean` with the
`Ordinal`-namespace API (5 defs + 5 mechanical lemmas, ~98 LOC, build
pending). Until #18367 lands AND its build is verified by docker, any
S3 ACT that adds `Ordinal.diagInter_isClosedBelow` to Basic.lean
inherits the merge-conflict risk from any rebase, and races with a
parallel S3 attempt that picks the same anchor location.

This session note locks the **mechanical migration plan** so the next
researcher who picks up S3 (after #18367 merges and its build clears
docker) can transfer the lemma verbatim with namespace rewrite and zero
proof-state re-derivation. The plan is fully build-pending tolerable in
the additive-first style of S2.

## 1. Parent-file source range

The migration target is the single theorem `diagInter_isClosedBelow` in
`proofs/Proofs/FodorPressingDown.lean`. Exact slice (anchored at HEAD =
`bf0339915c6`, parent file 385 LOC):

```
lines 102-107  docstring (6 lines)
lines 108-109  signature  (2 lines)
lines 110-124  proof body (15 lines)
total          23 LOC including docstring
```

For reference, the signature reads (parent file, `FodorPressingDown`
namespace, line numbers preserved):

```lean
/-- **Diagonal Intersection is Closed** (0 sorries).

    Proof: Given γ < o an acc point of Δ(f β),
    for each β < γ and each p < γ, pick δ ∈ Δ ∩ (max p β, γ).
    Then β < δ → δ ∈ f β, so f β ∩ (p,γ) ≠ ∅.
    Hence γ is an acc point of f β → γ ∈ f β (by closure). -/
theorem diagInter_isClosedBelow {f : Ordinal → Set Ordinal} {o : Ordinal}
    (hf : ∀ β < o, IsClubBelow (f β) o) : IsClosedBelow (diagInter f o) o := by
  rw [isClosedBelow_iff]
  intro γ γlto γAcc
  simp only [mem_diagInter]
  refine ⟨γlto, fun β βltγ => ?_⟩
  apply (hf β (βltγ.trans γlto)).closed.forall_lt γ γlto
  rw [isAcc_iff]
  refine ⟨γAcc.pos.ne', fun p pltγ => ?_⟩
  obtain ⟨δ, hδ_mem⟩ := γAcc.forall_lt (max p β) (max_lt pltγ βltγ)
  simp only [mem_inter_iff, mem_diagInter, mem_Ioo] at hδ_mem
  obtain ⟨⟨_, hδ_mem2⟩, hδ_lo, hδ_hi⟩ := hδ_mem
  have hβδ : β < δ := lt_of_le_of_lt (le_max_right p β) hδ_lo
  exact ⟨δ, hδ_mem2 β hβδ, lt_of_le_of_lt (le_max_left p β) hδ_lo, hδ_hi⟩
```

Note the parent's `IsClubBelow`, `diagInter`, `mem_diagInter` resolve
to `FodorPressingDown.X` (the parent's own namespace, opened by
`namespace FodorPressingDown` at line 39); `isClosedBelow_iff`,
`isAcc_iff`, `IsAcc.pos`, `IsAcc.forall_lt`, `IsClosedBelow.forall_lt`
resolve to Mathlib (the parent has `open Cardinal Order Ordinal Set`
at line 41 so the unqualified names work).

## 2. Dependency inventory (Mathlib + post-S2 Basic.lean)

S3 ACT will add `Ordinal.diagInter_isClosedBelow` to the **end** of
`proofs/Proofs/Club/Basic.lean` (after `isClubBelow_Iio_of_isSuccLimit`,
inside the existing `namespace Ordinal`). Required symbols, all already
in scope at the insertion point given the imports declared by PR
#18367 (`Mathlib.SetTheory.Ordinal.Topology` + `Mathlib.Tactic`):

| Symbol                       | Source                                                | In scope after #18367 |
|------------------------------|-------------------------------------------------------|-----------------------|
| `IsClubBelow`                | `Proofs.Club.Basic` (PR #18367)                       | yes                   |
| `IsClubBelow.closed`         | structure field projection                            | yes                   |
| `diagInter`                  | `Proofs.Club.Basic` (PR #18367)                       | yes                   |
| `mem_diagInter`              | `Proofs.Club.Basic` (PR #18367, marked `@[simp]`?)    | yes — but see §6.1    |
| `isClosedBelow_iff`          | `Mathlib.SetTheory.Ordinal.Topology` v4.26 line 233   | yes                   |
| `IsClosedBelow.forall_lt`    | `Mathlib.SetTheory.Ordinal.Topology` v4.26 line 238   | yes — alias of `iff`  |
| `isAcc_iff`                  | `Mathlib.SetTheory.Ordinal.Topology` v4.26 line 184   | yes                   |
| `IsAcc.pos`                  | `Mathlib.SetTheory.Ordinal.Topology` v4.26 line 210   | yes                   |
| `IsAcc.forall_lt`            | `Mathlib.SetTheory.Ordinal.Topology` v4.26 line 207   | yes                   |
| `Set.mem_inter_iff`          | Mathlib core                                          | yes                   |
| `Set.mem_Ioo`                | Mathlib core                                          | yes                   |
| `max_lt`, `le_max_left/right`| Mathlib core                                          | yes                   |
| `lt_of_le_of_lt`             | Mathlib core / Order                                  | yes                   |

The Mathlib references were confirmed against the live Mathlib v4.26.0
source on 2026-05-12 (researcher-6) via the GitHub Contents API on
`Mathlib/SetTheory/Ordinal/Topology.lean`; line numbers above are
relative to that revision. The alias

```
alias ⟨IsClosedBelow.forall_lt, _⟩ := isClosedBelow_iff
```

is a definitional alias of the forward direction, so it takes
`IsClosedBelow S o → ∀ p < o, IsAcc p S → p ∈ S`. The argument order
matches the parent body's usage at the line `apply (hf β …).closed.forall_lt γ γlto`.

## 3. Verbatim transfer with namespace rewrite

The S3 ACT diff against post-#18367 Basic.lean is purely additive —
append the following at the bottom of `namespace Ordinal`, just before
the `end Ordinal` closer:

```lean
/-- **Diagonal Intersection is Closed** (0 sorries).

    Proof: Given γ < o an acc point of Δ(f β),
    for each β < γ and each p < γ, pick δ ∈ Δ ∩ (max p β, γ).
    Then β < δ → δ ∈ f β, so f β ∩ (p,γ) ≠ ∅.
    Hence γ is an acc point of f β → γ ∈ f β (by closure). -/
theorem diagInter_isClosedBelow {f : Ordinal → Set Ordinal} {o : Ordinal}
    (hf : ∀ β < o, IsClubBelow (f β) o) : IsClosedBelow (diagInter f o) o := by
  rw [isClosedBelow_iff]
  intro γ γlto γAcc
  simp only [mem_diagInter]
  refine ⟨γlto, fun β βltγ => ?_⟩
  apply (hf β (βltγ.trans γlto)).closed.forall_lt γ γlto
  rw [isAcc_iff]
  refine ⟨γAcc.pos.ne', fun p pltγ => ?_⟩
  obtain ⟨δ, hδ_mem⟩ := γAcc.forall_lt (max p β) (max_lt pltγ βltγ)
  simp only [mem_inter_iff, mem_diagInter, mem_Ioo] at hδ_mem
  obtain ⟨⟨_, hδ_mem2⟩, hδ_lo, hδ_hi⟩ := hδ_mem
  have hβδ : β < δ := lt_of_le_of_lt (le_max_right p β) hδ_lo
  exact ⟨δ, hδ_mem2 β hβδ, lt_of_le_of_lt (le_max_left p β) hδ_lo, hδ_hi⟩
```

Body is **character-identical** to lines 110-124 of the parent file.
The renaming is entirely implicit: `IsClubBelow`, `diagInter`,
`mem_diagInter` now refer to the `Ordinal.X` names defined upstream in
the same `namespace Ordinal` block. Mathlib symbols
(`isClosedBelow_iff`, `IsAcc.forall_lt`, etc.) require `open Set Order`
at file scope (already present in Basic.lean per PR #18367 line ~6:
`open Set Order`) or unqualified resolution through the Mathlib
`open Cardinal Order Ordinal Set` chain.

**Important — the parent file is not edited in S3.** The existing
`FodorPressingDown.diagInter_isClosedBelow` keeps compiling using the
parent's own local `IsClubBelow` / `diagInter` / `mem_diagInter`.
Removal of the parent copy is deferred to S4 (trim).

## 4. Order of operations

Pre-conditions before S3 ACT can ship:

1. **PR #18367 merged into `main`.** Verifiable via
   `gh pr view 18367 --repo rjwalters/lean-genius --json mergedAt`
   returning a non-null `mergedAt`.

2. **#18367's docker build clears.** This is the *only* hard blocker,
   because if `Proofs.Club.Basic` fails to build, S3's addition
   inherits the failure. Verifiable via
   `./proofs/scripts/docker-build.sh Proofs.Club.Basic` returning
   exit 0 against `Ordinal.IsClubBelow`, `Ordinal.diagInter`, etc.

3. **No concurrent S3 PR is open.** Check
   `gh pr list --repo rjwalters/lean-genius --search "diagInter_isClosedBelow" --state open`
   and
   `gh pr list --repo rjwalters/lean-genius --search "fodor-pressing-down-oq-01 s3" --state open`
   return an empty array.

S3 ACT itself is one-commit, one-file (Basic.lean) plus an optional
new session note. Build-pending tolerable per S2's precedent (no
proof-state changes elsewhere).

## 5. Aliasing strategy (optional, deferred to S4)

A judgment call: should S3 (or S4) emit a deprecated alias

```lean
@[deprecated Ordinal.diagInter_isClosedBelow (since := "2026-05-12")]
alias FodorPressingDown.diagInter_isClosedBelow := Ordinal.diagInter_isClosedBelow
```

inside the parent file, to soften downstream-rename churn?

**Recommendation: no.** This slug's parent file
(`FodorPressingDown.lean`) has only one caller of
`diagInter_isClosedBelow`: the definition of
`diagInter_isClubBelow.closed` at line 245. After S4 the parent file
will simply `import Proofs.Club.Basic` and refer to
`Ordinal.diagInter_isClosedBelow` directly. No gallery proof outside
the parent uses the name, so an alias would be carrying maintenance
debt for no consumer. Drop the alias and grep-and-replace `FodorPressingDown.`
→ `Ordinal.` at S4 time.

## 6. Tactical risks (sorted by likelihood)

### 6.1 `mem_diagInter` simp-attribute drift

The parent's `mem_diagInter` is marked `@[simp]` (line 90 of the
parent file). PR #18367's introduced `Ordinal.mem_diagInter` reads
`theorem mem_diagInter … := Iff.rfl` — verify before S3 whether the
PR-as-merged carries the `@[simp]` attribute. If it does not, the
`simp only [mem_diagInter]` calls inside the migrated body will still
work (because the lemma is named in the simp set explicitly), but the
*usability* of `Ordinal.mem_diagInter` from downstream sites drops
slightly. **Mitigation**: read the merged Basic.lean line for
`theorem mem_diagInter` at S3 time; if missing the attribute, S3 can
re-add it in the same PR (one extra line) without scope creep.

### 6.2 `Mathlib.Tactic` vs explicit imports

PR #18367 imports `Mathlib.Tactic`, which is sufficient for the
tactics used (`rw`, `simp only`, `refine`, `obtain`, `apply`,
`exact`). If a Mathlib upstream split lands between #18367's
build-pending state and S3 ACT, narrow imports may be needed. Low
risk: the migrated tactics are all elementary.

### 6.3 `IsClubBelow` field projection naming

The parent's `IsClubBelow.closed` is a `structure` field. PR #18367
(per its body) declares `IsClubBelow` as a structure with three
fields: `subset_Iio`, `closed`, `unbounded`. The `.closed` projection
will exist under exactly that name. Confirmed against state.md §2.4
("Structure vs Prop. IsClubBelow is a structure (three fields),
matching the local file").

### 6.4 `Ordinal.IsAcc.forall_lt` argument order

Mathlib v4.26.0 line 207 declares:

```
theorem IsAcc.forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    ∀ p < o, (S ∩ Ioo p o).Nonempty
```

The migrated body calls `γAcc.forall_lt (max p β) (max_lt pltγ βltγ)`.
Argument order is `(p, h_p_lt_o)` and the return is
`(S ∩ Ioo p o).Nonempty` — `S` is `f β` here (no, wait, `S` is the
type-variable in `γAcc : IsAcc γ S`, and `S` is `diagInter f o`
because `γAcc : IsAcc γ (diagInter f o)`). The `obtain` then
destructs the nonempty membership against `diagInter ∩ Ioo (max p β) γ`,
which matches the subsequent `simp only [mem_inter_iff, mem_diagInter,
mem_Ioo]` rewrite. Body is internally self-consistent. No risk.

### 6.5 `simp only [mem_diagInter]` after rewrite to `Ordinal.diagInter`

When the lemma is moved to `namespace Ordinal`, the unqualified
`mem_diagInter` inside the `simp only [mem_diagInter]` call resolves
to `Ordinal.mem_diagInter` (correct) because the body is inside
`namespace Ordinal`. If a future refactor moves the body outside the
namespace, the call must become `simp only [Ordinal.mem_diagInter]`.
S3 keeps the body inside `namespace Ordinal`; no risk this PR.

### 6.6 `open Set` at Basic.lean file scope

The migrated body uses `Set.Ioo` (unqualified `mem_Ioo`) and
`Set.mem_inter_iff` (unqualified). PR #18367 declares `open Set Order`
in Basic.lean (per its file scaffold). If a future PR removes
`open Set`, the migrated body breaks at the `simp only`. Low risk:
the open chain matches the parent file's `open Cardinal Order Ordinal
Set` at line 41.

## 7. Anti-targets (S3 PREP & S3 ACT)

1. **Do NOT edit `problem.md`.** Lock state from S1 remains
   authoritative.
2. **Do NOT edit `knowledge.md`.** The Mathlib alignment survey is
   still accurate at v4.26.0 (verified §2).
3. **Do NOT edit `state.md`.** Phase remains OBSERVE/SCAFFOLD pending
   #18367 merge; a parallel "S3 prep landed" note belongs in
   `sessions/`.
4. **Do NOT edit the gallery JSON** (`src/data/research/problems/fodor-pressing-down-oq-01.json`).
   Knowledge fields are part of the S1 OBSERVE payload.
5. **Do NOT introduce Lean changes** in this PREP PR (no
   `proofs/Proofs/**`).
6. **Do NOT edit `proofs/Proofs.lean`.** That edit already lives in
   #18367.
7. **Do NOT edit `proofs/Proofs/FodorPressingDown.lean`** even
   speculatively. Parent trim is the S4 deliverable, after S3 has
   build-verified the migrated lemma in Basic.lean.

## 8. Acceptance criteria for the eventual S3 ACT

When a future researcher picks up S3 ACT, the deliverable is binary:

1. `proofs/Proofs/Club/Basic.lean` gains exactly one new theorem,
   `Ordinal.diagInter_isClosedBelow`, with signature equal to the §3
   block above and body character-identical to lines 110-124 of the
   parent file at #18367-merge time.
2. No other file in `proofs/Proofs/**` is modified.
3. The migrated theorem has **0 sorries**, **0 axioms**, and uses
   only the symbols inventoried in §2.
4. Docker build of `Proofs.Club.Basic` clears (≥1 successful run);
   non-clearing is acceptable for the PR-pending state per S2's
   precedent.
5. PR title: `research(fodor-pressing-down-oq-01): S3 ACT — add
   Ordinal.diagInter_isClosedBelow to Proofs.Club.Basic`.
6. PR body references this PREP and #18367.
7. Optional: add a one-line session note
   `sessions/2026-05-12-s03-act-diagInter-isClosedBelow.md` mirroring
   the S2 ACT note style.

## 9. Verification log (this PREP — read-only, no edits)

| Check                                                                          | Outcome |
|--------------------------------------------------------------------------------|---------|
| `grep -n diagInter_isClosedBelow proofs/Proofs/FodorPressingDown.lean`         | hits lines 18, 108, 245, 364 (def at 108, ref at 245) |
| Parent file size at HEAD `bf0339915c6`                                         | 385 LOC |
| Parent imports include `Mathlib.SetTheory.Ordinal.Topology` (Mathlib API host) | yes (line 36) |
| Parent uses `IsClubBelow.closed.forall_lt` (the alias)                         | yes (line 114) |
| PR #18367 introduces `Ordinal.IsClubBelow` as a structure with `.closed`       | yes (per body summary) |
| PR #18367 introduces `Ordinal.mem_diagInter`                                   | yes (per body summary) |
| Mathlib v4.26 `IsAcc.forall_lt` signature                                      | line 207, `Mathlib/SetTheory/Ordinal/Topology.lean` |
| Mathlib v4.26 `IsClosedBelow.forall_lt` alias                                  | line 238, same file |
| Mathlib v4.26 `isAcc_iff`                                                      | line 184, same file |
| Mathlib v4.26 `IsAcc.pos`                                                      | line 210, same file |
| Race check: open PRs on `fodor-pressing-down-oq-01 s3`                         | 0 open as of 2026-05-12 ~00:30 UTC |
| Race check: open PRs on `diagInter_isClosedBelow`                              | 0 open |

## 10. Honesty / no-edit guarantee

This PR is **doc-only**:

- 1 new file: `research/problems/fodor-pressing-down-oq-01/sessions/2026-05-12-s03-prep-diagInter-isClosedBelow-migration.md`
- 0 edits to existing files
- 0 edits to Lean files
- 0 edits to gallery JSON
- 0 edits to `meta.json` of any proof

Diff against #18367 is empty (mutually orthogonal — that PR adds
Basic.lean and a different session note; this PR adds only a third
session note under the same slug). Rebase risk: zero, because no file
edited here is touched by #18367.
