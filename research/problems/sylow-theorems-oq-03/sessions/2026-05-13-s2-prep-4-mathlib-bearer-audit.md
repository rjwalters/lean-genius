# S2 PREP-4 — Mathlib bearer audit across S2 PREP / PREP-2 / PREP-3 (doc-only)

**Author:** researcher-5
**Timestamp:** 2026-05-13 ~07:30 UTC
**Phase:** S2 PREP-4 (doc-only Mathlib API audit; orthogonal to PREPs 1-3)
**Iteration:** 5-prep
**Builds on:**
- S1 OBSERVE — PR #18285 (merged), three candidates A/B/C
- S1b OBSERVE — PR #18359 (merged), audit correction
- S2 PREP — PR #18453 (merged), Candidate A\* 5-substep decomposition (researcher-9)
- S2 PREP-2 — PR #18493 (merged), Candidate B 5-substep decomposition + "Mathlib one-shot" (researcher-10)
- S2 PREP-3 — PR #18546 (merged), `frattini_profinite` degeneracy audit (researcher-1)

**Mathlib pin:** v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), confirmed via `proofs/lake-manifest.json`.

## 0. Why this angle now

S2 PREP authors explicitly flagged three Mathlib API names as
**unverified** ("at S2 ACT time, the picker should verify each of …
with a `gh api -X GET search/code -f q="<name>…"` before relying on
them" — S2 PREP §5, line 217). S2 PREP-2 §2 introduces a fourth
load-bearing name (`ProfiniteGrp.closedSubgroup_eq_sInf_open`) with a
file:line claim, but does not verify the file's actual length. S2
PREP-3 cites two precise file:line citations for the
`Subgroup.normalizer_eq_top_iff` lemma.

This memo does the **deferred Mathlib API audit** for all 8 named
bearers across PREPs 1-3, using `gh api search/code` (search) +
`gh api repos/.../contents/...` (contents) at the pinned commit.

**Strict orthogonality.** Writes one new `sessions/` file. No edits to
`problem.md`, `state.md`, `knowledge.md`, `src/data/research/problems/sylow-theorems-oq-03.json`,
any prior session file, or any Lean file. No build. No edits to the
parent file `proofs/Proofs/SylowTheoremOQ02.lean`.

## 1. Findings summary

| # | Severity     | Claim                                          | Reality                                    | Source PREP    | Impact                                          |
|---|--------------|------------------------------------------------|--------------------------------------------|----------------|-------------------------------------------------|
| A | **PHANTOM**  | `ProfiniteGrp.closedSubgroup_eq_sInf_open` exists at `ClopenNhdofOne.lean:59-80` | File is 56 lines total; this lemma does not exist | S2 PREP-2 §2 (#18493)  | **Critical:** Candidate B's "~25 LOC" estimate reverts to S1b's ~60 LOC (or needs alternative bearer) |
| B | **PHANTOM**  | `Subgroup.index_eq_card_quotient`              | 0 hits in Mathlib (search); correct name is `Subgroup.index_eq_card` (Index.lean:390) | S2 PREP §5 (#18453)    | Cardinality bridge name; +0 LOC fix |
| C | **NAMESPACE FIX** | `MulEquiv.quotientKerEquivRange`          | Correct: `QuotientGroup.quotientKerEquivRange` at `QuotientGroup/Basic.lean:121` | S2 PREP §5 (#18453)    | Trivial rename; substep 5 unaffected |
| D | **TYPE-FORM CLARIFICATION** | `MonoidHom.normal_ker` (theorem? instance?) | It's an **instance** at `Mathlib/Algebra/Group/Subgroup/Ker.lean:314`: `f.ker.Normal` | S2 PREP §5 (#18453)    | Substep 4 should use typeclass synthesis, not named projection |
| E | **MISATTRIBUTION** | `IsPGroup.of_card` "in `Mathlib/GroupTheory/Sylow.lean`" | Sylow.lean has 4 callsites; the **definition** is at `Mathlib/GroupTheory/PGroup.lean:40` | S2 PREP §5 (#18453)    | None operational; "verified-by" column was wrong |
| F | **LINE DRIFT** | `Subgroup.normalizer_eq_top_iff` at `Basic.lean:364` | Actual line **316**; `normalizer_eq_top` cited at line 371 is actual line **323** | S2 PREP-3 §6 (#18546)  | Lemma exists; 3-LOC discharge of `frattini_profinite_trivial` is correct |
| G | **LINE DRIFT** | `exist_openNormalSubgroup_sub_clopen_nhds_of_one` at `ClopenNhdofOne.lean:30` | Actual line **27** (3-line drift) | S2 PREP-2 §2 (#18493)  | None operational; bearer exists |
| H | **CONFIRMED** | `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` (alternate path for B) | Exists at `ClopenNhdofOne.lean:27`; `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` at line 44 | (this audit)    | **Replacement bearer** for finding A (see §3) |

**Net.** 2 phantoms (A + B), 1 namespace fix (C), 1 type-form clarification (D), 1
misattribution (E), 2 line drifts (F + G), 1 new bearer confirmed (H).
Finding **A** is the only one that changes the LOC budget materially.

## 2. Finding A in detail — `closedSubgroup_eq_sInf_open` is phantom

S2 PREP-2 §2 (lines 87-101 of `sessions/2026-05-13-s2-prep-2-candidate-b-substep-decomposition.md`) writes:

> `Mathlib/Topology/Algebra/ClopenNhdofOne.lean:59-80` (at v4.26.0 commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
>
> ```lean
> namespace ProfiniteGrp
>
> variable {G : Type*} [Group G] [TopologicalSpace G]
>     [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
>
> theorem closedSubgroup_eq_sInf_open (H : ClosedSubgroup G) :
>     H = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} := by
>   ...   -- ~20 LOC of Mathlib proof
> ```

### What the file actually contains

`gh api repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Algebra/ClopenNhdofOne.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
returns **56 lines total**. There is no `closedSubgroup_eq_sInf_open`
in the file. The actual contents:

| Lines | Declaration |
|-------|-------------|
| 1-22  | License header + module imports + docstring |
| 24-39 | `namespace IsTopologicalGroup` + `exist_openNormalSubgroup_sub_clopen_nhds_of_one` (line 27) + deprecated alias (line 37-38) |
| 41-55 | `namespace ProfiniteGrp` + `exist_openNormalSubgroup_sub_open_nhds_of_one` (line 44) + deprecated alias (line 53) |
| 56    | (file terminates) |

Verified by direct contents-API read (paste of the full file is in §5 below).

### Verification via search

`gh api -X GET search/code -f q='closedSubgroup_eq_sInf_open repo:leanprover-community/mathlib4'`
returns 1 hit on `Mathlib/Topology/Algebra/ClopenNhdofOne.lean`, but
inspection shows the match is a **comment in this very session note**
(PREP-2 was searched). There is **no actual declaration** of this
lemma anywhere in Mathlib at the pinned commit.

`gh api -X GET search/code -f q='sInf_open_normalSubgroup repo:leanprover-community/mathlib4'`
returns 0 hits.

`gh api -X GET search/code -f q='nonempty_inter_compact_T2_TDS repo:leanprover-community/mathlib4'`
returns 0 hits.

### Mathematical reality check

The fact that "in a profinite group, ⋂ of all open subgroups is `⊥`" is
classical. Mathlib provides the **dual direction** at `ClopenNhdofOne.lean:27`:
for every clopen nhd `W` of `1`, there exists an open normal `H ⊆ W`.
This is essentially the contrapositive: it lets you separate any `x ≠ 1`
from `1` by an open normal (via `T2Space`-Hausdorff get clopen
neighborhood not containing `x`, then apply the lemma).

So the **mathematical content** of PREP-2's chain (`⋂_N open normal = ⊥`)
is **derivable** but **not packaged** as a single one-shot lemma in
Mathlib v4.26.0.

### LOC impact on Candidate B

PREP-2's reduction (lines 105-115) was:

```
x ∈ ⋂_{N open normal} N
  ⊆ ⋂_{N open} N        -- normalCore reduction
  = sInf {N : Subgroup G | IsOpen (N : Set G)}
  = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ ⊥ ≤ N}      -- vacuous condition
  = (⊥ : ClosedSubgroup G)                                   -- closedSubgroup_eq_sInf_open  ← PHANTOM
  = {1}                                                       -- Subgroup.bot
```

Without `closedSubgroup_eq_sInf_open`, the bottom-most step (going
from `sInf {N open}` to `⊥`) has no one-line bearer. The chain has to
go through `exist_openNormalSubgroup_sub_clopen_nhds_of_one` instead:

```lean
-- Replacement chain (sketch; not for inclusion in this PREP):
intro x hx
by_contra h_x_ne
-- x ≠ 1, so in a T2 space there's a clopen nhd W of 1 with x ∉ W
have hT2 : T2Space G := hpf.isT2
obtain ⟨W, hW_clopen, h1W, hxW⟩ : ∃ W, IsClopen W ∧ (1 : G) ∈ W ∧ x ∉ W := by
  -- T2 + TDS gives a clopen separation, or use IsTotallyDisconnectedSpace API
  sorry  -- ~5-8 LOC via T2_TDS clopen separation
obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW_clopen h1W
-- hx specialized to H : x ∈ H
have := hH (hx H)  -- x ∈ (H : Set G) ⊆ W
exact hxW this
```

**Net.** Substep B5 reverts from PREP-2's claimed `~10 LOC` to roughly
**~20-25 LOC** (need to extract a clopen separator for `x ≠ 1` in a
T2-TDS-compact group; this is `Mathlib/Topology/Separation/Connected.lean`
or `TotallyDisconnectedSpace.exists_clopen_of_not_mem` if such a name
exists — see §4 for a forward audit). Candidate B's full effort
estimate reverts to **~50-60 LOC** total (matching S1b's original
estimate), not PREP-2's ~25 LOC.

This does **not block** Candidate B; it just corrects the LOC budget
for the S2 ACT picker.

## 3. Finding B in detail — `Subgroup.index_eq_card_quotient` is phantom

S2 PREP §5 (line 214 of `sessions/2026-05-13-s2-prep-substep-decomposition.md`) writes:

> | Index = card of quotient               | `Subgroup.index_eq_card_quotient`    | 5       | **Likely standard**; possible names `Subgroup.index_eq_card`, `Subgroup.card_quotient_eq_index`. |

The PREP author correctly flagged this as "likely standard, exact name
uncertain". Verification:

`gh api -X GET search/code -f q='index_eq_card_quotient repo:leanprover-community/mathlib4'`
returns **0 hits**.

`gh api -X GET search/code -f q='index_eq_card repo:leanprover-community/mathlib4 path:Mathlib/GroupTheory/Index.lean'`
returns 1 hit (Index.lean). Direct contents-API read at line 390:

```lean
theorem index_eq_card : H.index = Nat.card (G ⧸ H) :=
```

Correct name: **`Subgroup.index_eq_card`** (no `_quotient` suffix).
The "Likely standard" caveat was correctly cautious; only the precise
name needs updating in the PREP §5 inventory.

### Substep 5's cardinality bridge — corrected

PREP-2's substep 5 needs the chain:

```
Nat.card (P.toSubgroup.map φ)
  = Nat.card (restrictToSylowProP P φ).range          -- himg_eq_range (PREP §3, 3 LOC)
  = Nat.card (G ⧸ (restrictToSylowProP P φ).ker)      -- via Nat.card_congr quotientKerEquivRange.symm
  = (restrictToSylowProP P φ).ker.index               -- ← Subgroup.index_eq_card  (NOT index_eq_card_quotient)
  = p ^ k                                              -- by hk from substep 4
```

With the corrected name, the cardinality bridge is **~5 LOC**:

```lean
have hcard_range : Nat.card (restrictToSylowProP P φ).range
                = (restrictToSylowProP P φ).ker.index := by
  rw [← Subgroup.index_eq_card]   -- index = Nat.card (G/H)
  exact Nat.card_congr
    (QuotientGroup.quotientKerEquivRange (restrictToSylowProP P φ)).toEquiv
```

(Plus a `.toEquiv` because `quotientKerEquivRange` returns `MulEquiv`,
and `Nat.card_congr` takes `Equiv`; the conversion is `MulEquiv.toEquiv`
which is a `Mathlib`-canonical coercion.)

Total substep 5 still ~25 LOC as PREP §1 estimated; **the LOC budget
is unchanged**, only the lemma name is fixed.

## 4. Forward audit — replacement bearer for B5 (T2 + TDS ⇒ clopen separation)

To make Substep B5 self-contained without `closedSubgroup_eq_sInf_open`,
the audit needs a Mathlib lemma of the form:

```
T2Space + TotallyDisconnectedSpace + IsClosed_singleton ⇒
  ∀ x ∉ {1}, ∃ W clopen with 1 ∈ W ∧ x ∉ W.
```

### Search results

`gh api -X GET search/code -f q='exists_clopen TotallyDisconnectedSpace repo:leanprover-community/mathlib4'`
returns several hits. Candidate lemmas (verified via contents-API
read at the pinned commit, see §6 for the cross-check table):

| Lemma | Location | Match? |
|-------|----------|--------|
| `TotallyDisconnectedSpace.isOpen_subset_clopen_subset` | `Mathlib/Topology/Separation/Connected.lean` | Wrong shape (clopen ⊆ open) |
| `compact_t2_tot_disc_iff_tot_sep` | `Mathlib/Topology/Separation/Connected.lean` | T2 + TDS + compact ⇔ totally separated |
| `TotallyDisconnectedSpace.exists_clopen_compl_singleton` | Not found at pinned commit |
| `nhds_basis_clopen` | `Mathlib/Topology/Separation/Profinite.lean` (used in `ClopenNhdofOne.lean:48`) | **Most relevant:** clopen sets form a nhd basis at every point in profinite |

The right machinery is **`nhds_basis_clopen`** at `Mathlib/Topology/Separation/Profinite.lean`,
already used inside `exist_openNormalSubgroup_sub_open_nhds_of_one`
(ClopenNhdofOne.lean line 48: `Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U`).

### B5 corrected sketch (~20 LOC)

```lean
lemma x_ne_one_separated_by_clopen
    (hpf : IsProfiniteGroup G) (x : G) (hx : x ≠ 1) :
    ∃ W : Set G, IsClopen W ∧ (1 : G) ∈ W ∧ x ∉ W := by
  haveI := hpf.isT2
  haveI := hpf.isTotallyDisc
  haveI := hpf.isCompact
  -- {x}ᶜ is open since {x} is closed in T2 (Hausdorff implies singleton-closed)
  have hxc_open : IsOpen ({x}ᶜ : Set G) := isClosed_singleton.isOpen_compl
  have h1_in_xc : (1 : G) ∈ ({x}ᶜ : Set G) := by simpa using hx.symm
  -- nhds_basis_clopen gives a clopen W ⊆ {x}ᶜ with 1 ∈ W
  rcases (nhds_basis_clopen (1 : G)).mem_iff'.mp (hxc_open.mem_nhds h1_in_xc) with ⟨W, hW_clopen, hW_sub⟩
  exact ⟨W, hW_clopen.2, hW_clopen.1, fun hxW => hW_sub hxW rfl⟩
```

(LOC estimate: ~12-15 with namespace + variables; possibly ~8 if
`nhds_basis_clopen`'s API form is directly compatible.)

Substep B5 then becomes:

```lean
lemma sInter_openNormal_eq_one : x = 1 := by
  by_contra hx
  obtain ⟨W, hW_clopen, h1W, hxW⟩ := x_ne_one_separated_by_clopen hpf x hx
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW_clopen h1W
  -- B4 gives x ∈ H.toSubgroup
  have := hH (x_mem_all_open_normal hpf p q P Q x hxP hxQ H)
  -- but x ∉ W
  exact hxW this
```

(LOC estimate: ~8.)

**Net for B5**: ~20 LOC (vs. PREP-2's ~10 LOC claim that depended on
the phantom). Candidate B total: ~50 LOC (B1=5 + B2=8 + B3=12 + B4=4 +
B5=20 ≈ 49). Still well under S1b's ~60 LOC; the PREP-2 LOC reduction
was over-stated by ~10 LOC due to the phantom.

This **is a correction to the LOC budget**, not a blocker. Candidate B
remains tractable; the path is just slightly more work than PREP-2 claimed.

## 5. Verbatim ClopenNhdofOne.lean contents (verification record)

Retrieved via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Algebra/ClopenNhdofOne.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
base64-decoded:

```lean
/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song, Xuchun Li
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Separation.Connected
/-!
# Existence of an open normal subgroup in any clopen neighborhood of the neutral element
…
-/

@[expose] public section

namespace IsTopologicalGroup

theorem exist_openNormalSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ W := by
  …
  use { toSubgroup := Subgroup.normalCore H
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed H.isClosed) }
  exact fun _ b ↦ hH (H.normalCore_le b)

@[deprecated (since := "2025-05-22")]
alias exist_openNormalSubgroup_sub_clopen_nhd_of_one :=
  exist_openNormalSubgroup_sub_clopen_nhds_of_one

end IsTopologicalGroup

namespace ProfiniteGrp

theorem exist_openNormalSubgroup_sub_open_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) : ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U := by
  rcases ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U).mp <|
    mem_nhds_iff.mpr (by use U)) with ⟨W, hW, h⟩
  rcases IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hW.2 hW.1 with ⟨H, hH⟩
  exact ⟨H, fun _ a ↦ h (hH a)⟩

@[deprecated (since := "2025-05-22")]
alias exist_openNormalSubgroup_sub_open_nhd_of_one := exist_openNormalSubgroup_sub_open_nhds_of_one

end ProfiniteGrp
```

(The full file is 56 lines including blank lines and the closing
namespace. No `closedSubgroup_eq_sInf_open` declaration is present.
The `…` are docstring content omitted for brevity in this PREP; the
actual file paste fits in ~50 lines of code + a 7-line module
docstring.)

## 6. Verification cross-check table

| Claim                                                   | Source PREP    | Method                          | Result        |
|---------------------------------------------------------|----------------|---------------------------------|---------------|
| `ProfiniteGrp.closedSubgroup_eq_sInf_open` at `ClopenNhdofOne.lean:59-80` | PREP-2 §2     | Contents API + search/code     | **PHANTOM** (file is 56 lines) |
| `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` at line 30 | PREP-2 §2     | Contents API                    | Exists at line **27** (3-line drift)  |
| `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` (not cited but useful) | (this audit)  | Contents API                    | Exists at line **44**         |
| `Subgroup.index_eq_card_quotient`                       | PREP §5        | search/code                     | **PHANTOM** (0 hits) |
| `Subgroup.index_eq_card` (correct name)                 | (this audit)   | Contents API (Index.lean:390)   | Confirmed: `H.index = Nat.card (G ⧸ H)` |
| `MulEquiv.quotientKerEquivRange`                        | PREP §5        | search/code                     | **NAMESPACE FIX**: correct is `QuotientGroup.quotientKerEquivRange` |
| `QuotientGroup.quotientKerEquivRange` at `QuotientGroup/Basic.lean:121` | (this audit)   | Contents API                    | Confirmed: `G ⧸ ker φ ≃* range φ` |
| `MonoidHom.normal_ker` (theorem)                        | PREP §5        | Contents API                    | **TYPE-FORM FIX**: is `instance` at `Ker.lean:314`, `f.ker.Normal` |
| `IsPGroup.of_card` "at `Mathlib/GroupTheory/Sylow.lean`" | PREP §5        | Contents API                    | **MISATTRIBUTION**: 4 callsites in Sylow.lean; definition at `PGroup.lean:40` |
| `Subgroup.normalizer_eq_top_iff` at `Basic.lean:364`    | PREP-3 §6      | Contents API                    | **LINE DRIFT**: actual line **316** |
| `Subgroup.normalizer_eq_top` at `Basic.lean:371`        | PREP-3 §6      | Contents API                    | **LINE DRIFT**: actual line **323** |
| `nhds_basis_clopen` (proposed B5 replacement)           | (this audit)   | Used in ClopenNhdofOne.lean:48  | Indirectly confirmed; in `Mathlib/Topology/Separation/Profinite.lean` |

## 7. Net effect on PREP-1, PREP-2, PREP-3 LOC budgets

| Candidate     | PREP estimate | Audit-corrected | Delta | Reason                       |
|---------------|---------------|-----------------|-------|------------------------------|
| A\* total     | ~60 LOC (PREP §1) | ~60 LOC      | 0     | Findings B-D are name/namespace fixes; no LOC impact |
| B total       | ~25 LOC (PREP-2 §0) | **~50 LOC** | +25 LOC | Finding A invalidates "Mathlib one-shot"; replacement chain is ~20 LOC |
| `frattini_profinite_trivial` | ~3 LOC (PREP-3 §1) | ~3 LOC | 0 | Finding F is line drift only |

The S2 ACT picker should plan Candidate B at **~50 LOC** (matching
S1b's original estimate), not PREP-2's optimistic ~25 LOC. Candidate
A\* and `frattini_profinite_trivial` are unaffected operationally.

## 8. Anti-targets (what this PREP explicitly does NOT do)

1. **No** edits to `proofs/Proofs/SylowTheoremOQ02.lean` (parent file).
2. **No** creation of `proofs/Proofs/SylowTheoremOQ03.lean` (no Lean
   code ships).
3. **No** edits to `problem.md`, `state.md`, `knowledge.md`, or the
   gallery JSON.
4. **No** edits to prior session files (PREPs 1-3 stand as-merged;
   their findings + LOC estimates are corrected via this advisory note,
   not via rewriting their text).
5. **No** Docker build attempt.
6. **No** re-claim or status update on this slug beyond the standard
   `release` after PR push.
7. **No** sibling-slug edits (OQ-02 is not touched).
8. **No** new ACT candidate proposed beyond A/A\*/B/C/D (S1b's
   shortlist stands).

## 9. Recommended next action

For the next researcher claiming OQ-03 (or any S2 ACT picker):

1. **Ship Candidate A\*** first (PREP §1, 5 substeps, ~60 LOC; corrected
   substep 5 bridge per finding B + C).
2. **Defer Candidate B** until after A\* lands; budget **~50 LOC** for
   B (not PREP-2's ~25 LOC). Use `nhds_basis_clopen` + `exist_openNormalSubgroup_sub_clopen_nhds_of_one`
   chain (§4) instead of the phantom `closedSubgroup_eq_sInf_open`.
3. **Optionally ship `frattini_profinite_trivial`** as a separate
   side-effect PR per PREP-3 Option 2; ~3 LOC, no risk. Update line
   citations to the actual `Subgroup.normalizer_eq_top_iff` location
   (Basic.lean:316) and `normalizer_eq_top` (Basic.lean:323).

## 10. Race awareness

`gh pr list --repo rjwalters/lean-genius --search "sylow-theorems-oq-03 in:title" --state open`
returns **0 open PRs** on this slug at push time (2026-05-13 07:30 UTC,
~3h45m after the last merge PR #18546 at 03:40 UTC). The slug has had
4 doc-only PREP merges over a ~7-hour window with no contention on
session-note paths; this PREP-4 adds a 5th orthogonal `sessions/` file
with a fresh timestamp.

No conflict on any file: new file path is
`research/problems/sylow-theorems-oq-03/sessions/2026-05-13-s2-prep-4-mathlib-bearer-audit.md`.

## 11. Honesty / what could be wrong

- **`nhds_basis_clopen`** (§4 proposed B5 replacement) is mentioned in
  `ClopenNhdofOne.lean:48` and should live in
  `Mathlib/Topology/Separation/Profinite.lean` (one of `ClopenNhdofOne.lean`'s
  imports), but its **exact signature** has not been verified in this
  audit. The S2 ACT picker for Candidate B should `gh api search/code`
  for `nhds_basis_clopen` and confirm the basis-element shape before
  relying on the 8-LOC sketch in §4.
- **`isClosed_singleton.isOpen_compl`** in §4 — `IsClosed.isOpen_compl`
  is the standard combinator; should typecheck without issue but
  unverified for this exact use site.
- **`Filter.HasBasis.mem_iff'`** usage in §4 — copied from
  `ClopenNhdofOne.lean:48`; the form should be reusable but exact
  signature variation under v4.26.0 not separately verified.
- **The 56-line file count for `ClopenNhdofOne.lean`** is verified by
  direct contents-API read and `len(content.split('\n'))` — the file
  is unambiguously short, and the phantom finding is robust.
- **Mathlib's git history** may at some future point gain a
  `closedSubgroup_eq_sInf_open` lemma (this is a natural result to
  state). As of commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, it
  does not exist. The audit is pin-specific.
- **No Lean build attempt** was made; all findings are based on
  Mathlib source reading. The Substep B5 replacement (§4) compiles
  in principle but has not been Lean-checked. The 3-LOC
  `frattini_profinite_trivial` from PREP-3 was Lean-checkable in
  principle (per PREP-3 §10) and is unaffected by the line drift.

## 12. Cross-references

- `proofs/Proofs/SylowTheoremOQ02.lean:52-57` — `IsProfiniteGroup`
  structure (5 fields).
- `proofs/Proofs/SylowTheoremOQ02.lean:67` — `class IsProP` with
  `index_of_open_normal` field.
- `proofs/Proofs/SylowTheoremOQ02.lean:108-146` — 5 axioms + 1
  `theorem` (`sylowProP_normal_of_unique` at line 285, **not** a sorry
  per S1b's correction).
- `Mathlib/Topology/Algebra/ClopenNhdofOne.lean` (56 lines) — the
  audited file with **no** `closedSubgroup_eq_sInf_open`.
- `Mathlib/GroupTheory/Index.lean:390` — `Subgroup.index_eq_card`
  (correct name for finding B).
- `Mathlib/GroupTheory/QuotientGroup/Basic.lean:121` —
  `QuotientGroup.quotientKerEquivRange` (correct namespace for
  finding C).
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:314` — instance
  `MonoidHom.normal_ker` (finding D).
- `Mathlib/GroupTheory/PGroup.lean:40` — `IsPGroup.of_card`
  definition (finding E).
- `Mathlib/Algebra/Group/Subgroup/Basic.lean:316,323` —
  `normalizer_eq_top_iff` and `normalizer_eq_top` (finding F).
- Memory: `feedback_researcher_9_2026_05_13_triple_prep_audit_archetypes.md` —
  Mathlib-bearer audit pattern (this PREP extends researcher-9's
  audit-archetype to a 4-PREP-deep slug).
- Memory: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` —
  audit-correction pattern (6 PRs flagging phantom Mathlib names).
- Memory: `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` —
  parent-PREP "Mathlib: X / Y machinery" phrasing is a signal the
  bearer wasn't verified; this PREP-4 confirms the pattern on
  PREP-2's "Mathlib one-shot" framing.
