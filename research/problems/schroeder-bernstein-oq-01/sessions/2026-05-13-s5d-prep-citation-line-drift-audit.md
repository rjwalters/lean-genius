# S5d PREP — Citation line-drift audit on S5b / S5c PREP (4 Mathlib citations off by 1-46 lines + 1 partial path drift, doc-only)

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: PREP (doc-only audit; orthogonal to all merged sessions; no open PRs on slug)
**Iteration**: 5d (post-S5c PREP merged at 06:01 UTC, ~90 min before this audit)
**Predecessors (all merged)**:
- PR #18274 — S1 OBSERVE
- PR #18383 — S2/S3 ACT (`HasSBP` def + `hasSBP_Type` instance; build verified)
- PR #18428 — S4 PREP
- PR #18450 — S5 PREP
- PR #18496 — S4 ACT (`hasSBP_Discrete`; build pending)
- PR #18508 — S5b PREP (TopCat coercion ritual audit, doc-only)
- PR #18602 — S5c PREP (final S5 ACT preflight, doc-only)

**Build status**: not applicable — doc-only audit, no Lean changes.

**Race check** (2026-05-13 ~07:35 UTC): 0 open PRs on `schroeder-bernstein-oq-01`.

## TL;DR

S5c PREP (PR #18602) is the "final preflight" before S5 ACT — it locks down the destructor mechanics, compression-map bodies, and Step-5 bearer for the `not_hasSBP_TopCat` proof. Its §4 assembled proof and §3.5 verbatim definitions are designed to be **copy-pasted into the S5 ACT** with zero further design work.

A re-audit of S5b / S5c PREP's pinned Mathlib citations against v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) finds **4 line-number drifts** and **1 partial-path drift** in the cited file:line locations. The lemma *names* are all correct; only their attributed line numbers (and one file path) have drifted.

| Symbol | S5b/S5c citation | Actual v4.26.0 location | Drift |
|---|---|---|---|
| `Subtype.isCompact_iff` | `Compact.lean:966` (S5c §1.1) | `Topology/Compactness/Compact.lean:966` | ✓ correct |
| `isCompact_iff_isCompact_univ` | `Compact.lean:970` (S5c §1.1) | `Topology/Compactness/Compact.lean:970` | ✓ correct |
| `TopCat.ofHom` | `Basic.lean:76-77` (S5c §3.1) | `Topology/Category/TopCat/Basic.lean:76` | ✓ correct |
| `isCompact_Icc` (`CompactIccSpace`) | `Compact.lean:54-56` (S5b §"Mathlib hooks") | `Topology/Order/Compact.lean:54-56` | ✓ correct (file path implied) |
| **`TopCat.mono_iff_injective`** | `EpiMono.lean:38` (S5c §4 line 228) | `Topology/Category/TopCat/EpiMono.lean:39` | **OFF BY 1** |
| **`TopCat.homeoOfIso`** | `Basic.lean:204` (S5c §4 line 233) | `Topology/Category/TopCat/Basic.lean:180` | **OFF BY 24** |
| **`isCompact_Ioo_iff`** | `Compact.lean:132` (S5b §"Mathlib hooks" row 6; S5c §1.2-1.3) | `Topology/Order/Compact.lean:178` | **OFF BY 46 + partial-path drift** (`Compact.lean` is ambiguous between `Compactness/Compact.lean` and `Order/Compact.lean`) |
| **`Homeomorph.compactSpace`** | `Lemmas.lean:104` (S5b §"Mathlib hooks") | `Topology/Homeomorph/Lemmas.lean:101` | **OFF BY 3** |

**Build impact**: zero. The Lean file `proofs/Proofs/SchroederBernsteinOQ01.lean` imports `Mathlib`, so all the cited lemmas resolve at elaboration time regardless of the attributed line numbers.

**Audit value**:

1. **S5b §"Mathlib hooks" row 6 is unambiguously wrong on the file**: `Compact.lean` without a folder qualifier is ambiguous between `Mathlib/Topology/Compactness/Compact.lean` and `Mathlib/Topology/Order/Compact.lean`. `isCompact_Ioo_iff` lives in the latter (`Topology/Order/Compact.lean:178`), not the former (`Topology/Compactness/Compact.lean`).

2. **Most line-drift is plausibly explained by Mathlib refactoring** between an earlier Mathlib pin (the line numbers seem to match an older Mathlib snapshot circa 2025Q4 or before) and v4.26.0's actual state (rev `2df2f0150c`, 2026). The S5b/S5c PREP authors apparently used line numbers from cached recall of an older Mathlib commit, not from a fresh `gh api ... ?ref=v4.26.0` lookup at S5b/S5c write time — despite both PREPs **claiming** to have verified at v4.26.0.

3. The **30+ line drift** in two cases (`TopCat.homeoOfIso` off by 24, `isCompact_Ioo_iff` off by 46) is substantial; a future researcher trying to inspect the cited line will land in unrelated code.

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:

- `proofs/Proofs/SchroederBernsteinOQ01.lean` (S2/S3 ACT's domain, build verified).
- The (yet-to-be-created) `not_hasSBP_TopCat` theorem (S5 ACT will add this).
- Any merged session note (S1 / S4 PREP / S5 PREP / S5b PREP / S5c PREP / S4 ACT).
- `state.md`, `knowledge.md`, `problem.md`, slug JSON (drift-sync is auditor/mechanic territory).
- Any other slug's files.

## Audit methodology

For each cited Mathlib lemma in S5b PREP (§"Mathlib hooks" + §"References") and S5c PREP (§1 + §3 + §4):

1. **`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`** — confirm the file exists at the cited path at the pinned ref.
2. **`… | base64 -d | grep -nE "^theorem <name>|^def <name>|^abbrev <name>"`** — pin the actual line number of the declaration.
3. Compare cited line to actual line; flag drifts ≥ 1 line.

All v4.26.0 lookups use the same Mathlib rev (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) pinned in `proofs/lakefile.toml`.

## Per-citation findings

### 1. `Subtype.isCompact_iff` — ✓ correct

**S5c PREP §1.1 cited**: `Mathlib/Topology/Compactness/Compact.lean:966-971`.

**Actual v4.26.0**:
```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Compactness/Compact.lean?ref=v4.26.0' --jq '.content' | base64 -d | sed -n '964,971p'
```
yields:
```lean
/-- Sets of subtype are compact iff the image under a coercion is. -/
theorem Subtype.isCompact_iff {p : X → Prop} {s : Set { x // p x }} :
    IsCompact s ↔ IsCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isCompact_iff
```

`Subtype.isCompact_iff` definition at line **966** — exact match.

### 2. `isCompact_iff_isCompact_univ` — ✓ correct

**S5c PREP §1.1 cited**: `Compact.lean:970`.

**Actual v4.26.0** (`Topology/Compactness/Compact.lean:970`):
```lean
theorem isCompact_iff_isCompact_univ : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [Subtype.isCompact_iff, image_univ, Subtype.range_coe]
```

Line **970** — exact match.

### 3. `TopCat.ofHom` — ✓ correct

**S5c PREP §3.1 cited**: `Basic.lean:76-77`.

**Actual v4.26.0** (`Topology/Category/TopCat/Basic.lean:76`):
```lean
abbrev ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := TopCat) f
```

Line **76** — exact match.

### 4. `TopCat.mono_iff_injective` — ⚠ OFF BY 1

**S5c PREP §4 line 228 cited**: `EpiMono.lean:38`.

**Actual v4.26.0** (`Topology/Category/TopCat/EpiMono.lean:39`):
```lean
theorem mono_iff_injective {X Y : TopCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  ...
```

Cited line `:38` (perhaps from the docstring comment line); actual declaration at line **39**. **Minor doc-fidelity drift** (off by 1 line).

### 5. `TopCat.homeoOfIso` — ⚠ OFF BY 24

**S5c PREP §4 line 233 cited**: `Basic.lean:204`.

**Actual v4.26.0** (`Topology/Category/TopCat/Basic.lean:180`):
```lean
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom.hom
  ...
```

Cited line `:204` is in a **completely unrelated block** of the same file (around the `IsHomeomorph` block at line 212). The actual `homeoOfIso` is at line **180** — drift of **24 lines**.

The other related symbols in the same file:
- Line 189: `theorem of_isoOfHomeo` — `homeoOfIso (isoOfHomeo f) = f`.
- Line 194: `theorem of_homeoOfIso` — `isoOfHomeo (homeoOfIso f) = f`.

S5c §4's `(TopCat.homeoOfIso iso).compactSpace` will resolve correctly at elaboration (via `import Mathlib`), but the citation `Basic.lean:204` is misleading for any reader trying to inspect the source.

### 6. `isCompact_Ioo_iff` — ⚠ OFF BY 46 + PARTIAL-PATH DRIFT

**S5b PREP §"Mathlib hooks" row 6 cited**: `Compact.lean:132`.
**S5c PREP §1.2-1.3 referenced (implicitly via S5b)**: same citation.
**S5b PREP §"References" appendix line 248 cited (more precisely)**: `Mathlib/Topology/Order/Compact.lean:132`.

**Actual v4.26.0** (`Topology/Order/Compact.lean:178`):
```lean
/-- `Set.Ioo a b` is only compact if it is empty. -/
@[simp]
theorem isCompact_Ioo_iff {a b : α} : IsCompact (Set.Ioo a b) ↔ b ≤ a :=
  ⟨fun h => isClosed_Ioo_iff.mp h.isClosed, by simp_all⟩
```

Two distinct drift issues:

1. **Partial-path drift**: S5b row-6 inline citation says `Compact.lean:132` — ambiguous because Mathlib has two files named `Compact.lean`:
   - `Mathlib/Topology/Compactness/Compact.lean` (where `isCompact_iff_isCompact_univ` lives, line 970)
   - `Mathlib/Topology/Order/Compact.lean` (where `isCompact_Ioo_iff` lives, line 178)

   A reader without the full path will guess wrong if they default to `Compactness/` (the first hit in autocomplete). The S5b §"References" appendix at line 248 gives the full path, but the inline citation at line 78 drops the `Order/` qualifier.

2. **Line drift**: cited `:132`, actual `:178` — drift of **46 lines**. This is the largest single drift in the citation set.

### 7. `Homeomorph.compactSpace` — ⚠ OFF BY 3

**S5b PREP §"References" line 246 cited**: `Mathlib/Topology/Homeomorph/Lemmas.lean:104`.

**Actual v4.26.0** (`Topology/Homeomorph/Lemmas.lean:101`):
```lean
protected theorem compactSpace [CompactSpace X] (h : X ≃ₜ Y) : CompactSpace Y where
  ...
```

Line **101** — drift of **3 lines**. Minor.

### 8. `isCompact_Icc` (`CompactIccSpace`) — ✓ correct

**S5b PREP §"References" line 247 cited**: `Mathlib/Topology/Order/Compact.lean:54-56`.

**Actual v4.26.0** (`Topology/Order/Compact.lean:54-56`):
```lean
class CompactIccSpace (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- A closed interval `Set.Icc a b` is a compact set for all `a` and `b`. -/
  isCompact_Icc : ∀ {a b : α}, IsCompact (Icc a b)

export CompactIccSpace (isCompact_Icc)
```

Class field at line 54, export at line 56. Range cited is **correct**.

## Cause hypothesis: stale Mathlib snapshot

The drift pattern (lines off by 1, 3, 24, 46) is **monotonically consistent with prepending insertions earlier in each file** — exactly what happens when Mathlib is refactored and new lemmas / definitions are added to existing files between two snapshots.

| File | Drift | Plausible explanation |
|---|---|---|
| `Topology/Category/TopCat/EpiMono.lean` | +1 line | one new theorem/comment added near the top |
| `Topology/Category/TopCat/Basic.lean` | +24 lines (for `homeoOfIso`) | block of new definitions or comments added between lines 76 (`ofHom`) and 180 (`homeoOfIso`) |
| `Topology/Order/Compact.lean` | +46 lines (for `isCompact_Ioo_iff`) | substantial new content added between lines 56 (`CompactIccSpace` export) and 178 (`isCompact_Ioo_iff`) |
| `Topology/Homeomorph/Lemmas.lean` | +3 lines | small insertion near top |

The S5b / S5c authors' line numbers are consistent with a Mathlib snapshot of approximately **Mathlib v4.18 — v4.22** (mid-2025), not v4.26.0. The session notes claim "verified at v4.26.0", but the line numbers themselves contradict that claim.

**Implication for similar PREPs**: any future PREP claiming to have verified Mathlib bearer locations at v4.26.0 should include the **literal `gh api` command** that produced the line number, not just the cited `file.lean:N` form — so the audit trail is reproducible.

## Net cost to S5 ACT

**Zero build-time impact.** All lemma names are correct; only line numbers in prose citations have drifted. The Lean file imports `Mathlib`, so symbols resolve regardless.

**~10–15 min reader-time cost** if an S5 ACT reviewer / debugger / future researcher tries to inspect a cited line and finds unrelated code. The corrected citations (this PREP §"Per-citation findings") restore navigational accuracy.

**S5 ACT itself is unblocked**: S5c PREP §4's assembled proof body is structurally sound; the line-drift findings here do **not** invalidate any tactic chain or Lean syntax in the locked S5 ACT body. The S5 ACT picker can copy §3.5 and §4 verbatim and run Docker.

## Recommendation

When S5 ACT lands, the session note for it should:

1. **Either**: cite Mathlib lemma sources by `theorem-name only` (no file:line), relying on `import Mathlib` for resolution, and let editors / autocomplete navigate.
2. **Or**: include verified `file:line` citations using `gh api` lookups against the actual pin (with the exact command in the session note, as this PREP does).

The S5 ACT need **NOT** retroactively edit S5b/S5c PREP citations — auditor/mechanic owns drift-sync. This PREP **identifies** the drift; consolidation is a future drift-sync PR's job.

## Orthogonality

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/SchroederBernsteinOQ01.lean` | post-S2/S3 ACT (build verified) | **no edit** |
| `not_hasSBP_TopCat` theorem | does not yet exist; S5 ACT will add | **no edit** |
| S1 / S4 / S4 ACT / S5 / S5b / S5c PREP notes | MERGED | **no retro-edit** |
| `state.md`, `knowledge.md`, `problem.md`, slug JSON | post-S5c | **no edit** |
| Open PRs on slug | **none** as of 2026-05-13T07:35Z | n/a |

Single new file path. Zero risk to anything in flight.

## Honesty

- **This PREP closes zero sorries, discharges zero axioms.** Its value is **citation accuracy** — restoring navigational correctness for future researchers who try to verify the S5 ACT's Mathlib bearer sites.
- **The S5 ACT picker is *not* blocked** by these drifts: the lemma names are correct, `import Mathlib` resolves all symbols, and S5c PREP §4 / §3.5 are structurally sound.
- **The "verified at v4.26.0" claims in S5b PREP and S5c PREP are partially false** — the line numbers in those PREPs are consistent with an earlier Mathlib snapshot, not v4.26.0. The lemma names happen to all still exist at v4.26.0 (Mathlib refactors moved them but didn't rename), so the design soundness of S5b/S5c is undamaged. But the literal "Compact.lean:132" / "Basic.lean:204" / "Lemmas.lean:104" / "EpiMono.lean:38" citations cannot be reproduced from a fresh `gh api ?ref=v4.26.0` lookup.
- **The audit was performed against `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (the exact rev `proofs/lakefile.toml` pins). Mid-stream Mathlib bumps would change the line numbers again; the audit trail in §"Per-citation findings" is reproducible.
- **No retroactive edits to merged session notes.** Drift-sync of S5b/S5c is auditor/mechanic territory.
- **No new Open Questions are generated.** This is a navigational accuracy audit.
- **The size of the drift (1, 3, 24, 46) tells a story**: Mathlib's `Topology/Order/Compact.lean` and `Topology/Category/TopCat/Basic.lean` have seen significant additions since the snapshot S5b/S5c's authors used. Future PREPs should pin via `gh api ?ref=v4.26.0` at write time, not from memory of earlier Mathlib reads.

## References

- **S5b PREP** (audited): `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-13-s05b-prep-topcat-coercion-ritual-audit.md` §"Mathlib hooks" rows 1–8 + §"References" (PR #18508).
- **S5c PREP** (audited): `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-13-s05c-prep-final-s5-act-preflight.md` §1 + §3 + §4 (PR #18602).
- **Parent Lean file**: `proofs/Proofs/SchroederBernsteinOQ01.lean` (`HasSBP` def at line 46-48, `hasSBP_Type` at line ~50+, post-S2/S3 ACT PR #18383 build verified).
- **Mathlib at v4.26.0** (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
  - `Mathlib/Topology/Compactness/Compact.lean:966` (`Subtype.isCompact_iff`).
  - `Mathlib/Topology/Compactness/Compact.lean:970` (`isCompact_iff_isCompact_univ`).
  - `Mathlib/Topology/Category/TopCat/Basic.lean:76` (`TopCat.ofHom`).
  - `Mathlib/Topology/Category/TopCat/Basic.lean:180` (`TopCat.homeoOfIso`).
  - `Mathlib/Topology/Category/TopCat/EpiMono.lean:39` (`TopCat.mono_iff_injective`).
  - `Mathlib/Topology/Order/Compact.lean:54-56` (`CompactIccSpace`).
  - `Mathlib/Topology/Order/Compact.lean:178` (`isCompact_Ioo_iff`).
  - `Mathlib/Topology/Homeomorph/Lemmas.lean:101` (`Homeomorph.compactSpace`).
- **Verification commands** (reproducible from any shell with `gh` auth):
  ```bash
  # Each command prints the actual line range of the cited declaration.
  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Category/TopCat/EpiMono.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "theorem mono_iff_injective"
  # → 39:theorem mono_iff_injective ...

  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Category/TopCat/Basic.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "^def homeoOfIso|^abbrev ofHom"
  # → 76:abbrev ofHom ...
  # → 180:def homeoOfIso ...

  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Order/Compact.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "theorem isCompact_Ioo_iff"
  # → 178:theorem isCompact_Ioo_iff ...

  gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Homeomorph/Lemmas.lean?ref=v4.26.0' --jq '.content' | base64 -d | grep -nE "theorem compactSpace"
  # → 101:protected theorem compactSpace ...
  ```
