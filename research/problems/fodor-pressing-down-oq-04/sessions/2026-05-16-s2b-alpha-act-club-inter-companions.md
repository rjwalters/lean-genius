# S2-β-α ACT — Club ∩ Club + Stationary ∩ Club companions (Solovay Step 2 foundations)

**Date**: 2026-05-16
**Researcher**: researcher-6 (Claude Opus 4.7)
**Mode**: ACT (Docker-verified Lean delta in `proofs/Proofs/FodorPressingDown.lean`,
**+115 LOC** to a new `§ Part VIII`; 0 sorries, 0 axioms; 3062-job clean build)
**Status**: post-#19365 (S3c PREP — bearer drift recheck) — does not depend on
#19365 merging (Lean source is line-stable; this ACT touches only the file's
trailing region between Part VII and the Summary docstring)

## 0. Why S2-β-α ACT (not full S2-β ACT)

The S3 PREP (#19207) and S3b PREP (#19251) drain-wave-merged design points to an
S2-β ACT at ~200-270 LOC with three deliverables:

1. **`IsStationaryBelow.inter_isClubBelow`** — companion (~20-30 LOC).
2. **`fodor_anti_constant`** — companion (~60-80 LOC), requires
   `Ordinal.IsFundamentalSequence` cofinal-sequence picking.
3. **`stationary_splits_binary`** — main theorem (~80-100 LOC).

The cofinal-sequence picking infrastructure in #2 carries the bulk of the
technical risk: `IsFundamentalSequence` at Mathlib SHA `2df2f015...` uses an
`∀ {i j} (hi hj)` binder form (S3c PREP §3.3) plus `blsub.{u, u}` with explicit
universes, plus the `Classical.choose` lifting through a binary product of
ordinal indices.

This **S2-β-α ACT** ships ONLY companion #1 + a chained corollary, in a strictly
build-verified path independent of the cofinal-sequence machinery. The full S2-β
ACT can now stack atop this PR by importing the two ready-to-use Part VIII
theorems instead of inlining them.

**Deliverables (this PR)**:

| # | Theorem | LOC | Status |
|---|---|---:|---|
| 1 | `IsClubBelow.inter` | ~70 | NEW (companion) |
| 2 | `IsStationaryBelow.inter_isClubBelow` | ~13 | NEW (companion) |
| 3 | `IsStationaryBelow.inter_isLimitOrdinals` | ~6 | NEW (corollary) |
| ─ | Section header + docstrings | ~26 | NEW |
| ─ | Summary-list bullets (Key results) | ~3 | EDITED |

Total **+115 LOC** to `proofs/Proofs/FodorPressingDown.lean`. 0 sorries, 0
axioms. Docker build: **3062 jobs successful in 7.2s** (incremental).

## 1. State at S2-β-α claim time

### 1.1 Slug PR queue at claim (2026-05-16 ~01:55Z)

| PR | Title (short) | Status | Surface |
|---|---|---|---|
| **#19365** | S3c PREP — post-merge bearer drift recheck (doc-only) | OPEN/CLEAN | sessions + state.md append |

One open PR on this slug at claim time. #19365 ships `sessions/` + a 32-line
state.md append only (no Lean changes); this S2-β-α ACT ships `.lean` + a new
`sessions/` file + a `state.md` append. **Surface-disjoint** from #19365 (the
file is identical on `proofs/Proofs/FodorPressingDown.lean` and the state.md
appends do not overlap; sessions/ files are different).

Repo HEAD at claim: `8a3cda556b6` (audit tracker sync #19328, merged
2026-05-16T00:14Z). Mathlib pinned SHA in `proofs/lake-manifest.json:8`:
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — **unchanged** since S3 PREP
§3.1 + S3b PREP §2 + S3c PREP §3 pin.

### 1.2 Why pivot to S2-β-α now (post-ship triage)

Post-ship triage from the immediately preceding cycle:

- Researcher-6 just shipped PR #19364 (S16 PREP angle-trisection-oq-05-oq-04,
  doc-only) at 2026-05-16T01:50:31Z.
- Claim-random landed on `fodor-pressing-down-oq-04` (depth-first tier:
  MODERATE+, knowledge score 19/RICH).
- #19365 (S3c PREP) shipped at 01:57:27Z (~6 min before claim), absorbed all
  the post-merge bearer drift recheck work + state.md narrative refresh +
  catalogue of section-header anchors.
- The natural next deliverable in the sequence is the S2-β ACT itself.

Per the memory archetype variant "post-ship pivot lands on slug with just-merged
sibling PREP whose §11 honesty note named ~30-60min owed pencil work" — except
#19365's §8 honesty note flags "0 new companion lemmas identified beyond S3b's
two — the bearer chain for the S2-β ACT is unchanged" (no §11 owed pencil work).
The owed work is the S2-β ACT itself, the next-iteration deliverable.

Rather than (a) release + 1-skip exit or (b) attempt the full S2-β ACT in one
cycle (risk: cofinal-sequence machinery + multiple Docker build iterations on
top of a still-open S3c PREP whose state.md append narrates "stable post-#19052
baseline"), this cycle commits to (c) **the S2-β-α subset**: companion-only
ACT, build-verified, atop `origin/main` (not #19365's branch). This is the
narrowest tractable Lean delta that meaningfully advances the slug.

## 2. Mathematical content

### 2.1 `IsClubBelow.inter` (binary intersection of clubs is a club)

The S3b PREP §5.1 flagged that Mathlib at SHA does NOT have a packaged
"intersection of two clubs is a club" lemma in the form needed here
(`IsClubBelow` is the gallery's own predicate, distinct from Mathlib's
`Set.IsStationary`). The S3b PREP §5.2 sketched a companion at ~20-30 LOC
**assuming** a separate binary-intersection-of-clubs result. This ACT
combines both into one ~70-LOC theorem.

**Statement**:
```lean
theorem IsClubBelow.inter {C D : Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hC : IsClubBelow C κ.ord) (hD : IsClubBelow D κ.ord) :
    IsClubBelow (C ∩ D) κ.ord
```

**Proof architecture** (matches S3b §5.2 sketch but extends with the
unboundedness reduction):

- **Closure** (~13 LOC): an `IsAcc`-point of `C ∩ D` is an `IsAcc`-point of
  both `C` and `D` (the `IsAcc` witnesses project through the intersection),
  so it lies in both by closure. Two parallel `apply hC.closed.forall_lt …`
  / `apply hD.closed.forall_lt …` branches.

- **Unboundedness** (~50 LOC): reduce to `diagInter_isUnboundedBelow` (line
  138) via the 2-element family `f β = (if β = 0 then C else D)`. Apply the
  diagonal-intersection-of-clubs unboundedness with starting point
  `max α 1` (chosen so that the result is **strictly** above both `0` and
  `1`, witnessing membership in both `f 0 = C` and `f 1 = D`):

  ```
  obtain ⟨γ, hγdiag, hmγ, hγκ⟩ :=
    diagInter_isUnboundedBelow hκ hκ_unc hf_club (max α 1) hmaxκ
  ```

  From `hmγ : max α 1 < γ`, derive `1 < γ` (so `f 1 = D ∋ γ`) and `α < γ`,
  and use the diagonal-intersection membership unfold to project out
  `γ ∈ f 0 = C`.

### 2.2 `IsStationaryBelow.inter_isClubBelow` (stationary ∩ club preserves stationary)

**Statement**:
```lean
theorem IsStationaryBelow.inter_isClubBelow {S C : Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hS : IsStationaryBelow S κ.ord) (hC : IsClubBelow C κ.ord) :
    IsStationaryBelow (S ∩ C) κ.ord
```

**Proof** (~6 LOC): given a club `D`, the binary `IsClubBelow.inter`
shows `C ∩ D` is itself a club, so `S` meets it (by stationarity); rearrange
to `(S ∩ C) ∩ D` nonempty.

### 2.3 `IsStationaryBelow.inter_isLimitOrdinals` (WLOG-restrict to limits)

**Statement**:
```lean
theorem IsStationaryBelow.inter_isLimitOrdinals {S : Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hS : IsStationaryBelow S κ.ord) :
    IsStationaryBelow (S ∩ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α}) κ.ord
```

**Proof** (~3 LOC): direct corollary, `hS.inter_isClubBelow hκ hκ_unc
(isLimitOrdinals_isClubBelow hκ hκ_unc)`. This is the directly-callable form
the S2-β / Solovay Step 2 ACT writer needs at the top of their proof —
restricts any stationary `S ⊆ κ.ord` to its limit-ordinal part, so the
subsequent cofinal-sequence picking has the `IsSuccLimit α` precondition
available element-wise.

## 3. Lean lemma-naming pitfalls discovered (Mathlib v4.26.0 surface)

Three v4.26.0 Mathlib naming surface deltas surfaced during Docker-build
iterations. None affect the mathematical content; all are name/form fixes:

| # | Designed | v4.26.0 actual | Resolution |
|---|---|---|---|
| 1 | `Ordinal.zero_lt_one` (for `(0 : Ordinal) < 1`) | Not present at that name | Use `one_pos` (generic, instance-resolved for `Ordinal`) |
| 2 | `Ordinal.succ_pos α` + `rwa [zero_add]` | `succ` shows in goal as `succ` not `+ 1`; pattern miss | Replaced with `one_pos`-based derivation (avoids the `succ`-form mismatch) |
| 3 | `have h1ne0 : (1 : Ordinal) ≠ 0 := one_ne_zero` | "failed to infer universe levels" — `Ordinal.{u}` polymorphic | Replaced with `simpa [f] using h` (let `simp` discover `1 ≠ 0` automatically) |

The `(1 : Ordinal) ≠ 0` universe-inference failure (item 3) is the most
non-obvious — `one_ne_zero` is universe-polymorphic but Lean cannot fix the
`Ordinal.{u}` parameter from a bare type ascription. The `simpa [f] using h`
form sidesteps by unfolding `f` to `if (1 : Ordinal) = 0 then C else D` in
context where the universe is fixed by `f`'s definition.

## 4. Build verification

### 4.1 Docker build

```
$ LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh Proofs.FodorPressingDown
...
⚠ [3062/3062] Built Proofs.FodorPressingDown (7.2s)
warning: Proofs/FodorPressingDown.lean:261:5: unused variable `hS_pos`
warning: Proofs/FodorPressingDown.lean:344:34: unused variable `hTS`
Build completed successfully (3062 jobs).

=== Build succeeded ===
```

Both warnings are **pre-existing** in unrelated theorems (`fodor` and
`IsStationaryBelow.of_subset`), already noted in #19052's body (S2-α ACT) at
the same line numbers post-#19052 — **no new warnings** introduced by this
ACT.

### 4.2 File stats

| Metric | Pre (HEAD `8a3cda556b6`) | Post (this ACT) | Δ |
|---|---:|---:|---:|
| LOC | 453 | **568** | +115 |
| `theorem` / `def` / `structure` declarations | 18 | **21** | +3 |
| `sorry` | 0 | **0** | 0 |
| `axiom` | 0 | **0** | 0 |
| Sections (`§ Part …`) | VII (last) | **VIII** (last) | +1 |

### 4.3 Iteration count

3 Docker build iterations (each ~7-13s for the FodorPressingDown target,
plus ~2-3min cache download/decompress on cold start; subsequent rebuilds
are incremental). Iteration log:

| # | Result | Fix |
|---|---|---|
| 1 | Fail: `Unknown constant Ordinal.zero_lt_one` | Renamed to `one_pos` |
| 2 | Fail: `rw [zero_add]` did not find pattern `0 + ?a` in `0 < succ 0` | Replaced with `lt_of_lt_of_le one_pos (le_of_lt hγ_gt_1)` |
| 3 | **PASS** (3062 jobs, 0 new warnings) | Replaced `if_neg`-based `simp` with `simpa [f]` to bypass universe inference on `(1 : Ordinal) ≠ 0` |

## 5. Cross-PR conflict surface

| Target | #19052 (S2-α ACT, merged) | #19207 (S3 PREP, merged) | #19251 (S3b PREP, merged) | #19365 (S3c PREP, OPEN) | This S2-β-α ACT |
|---|---:|---:|---:|---:|---:|
| `proofs/Proofs/FodorPressingDown.lean` | ✓ +68/-0 | ─ | ─ | ─ | **✓ +115/-0** |
| `state.md` | ✓ +105/-42 | ─ | ─ | ✓ +32/-0 (append) | **✓ append** |
| `JSON` (`fodor-pressing-down-oq-04.json`) | ✓ +25/-21 | ─ | ─ | ─ | **✓ refresh** |
| `sessions/2026-05-14-s2a-act-…` | ✓ NEW | ─ | ─ | ─ | ─ |
| `sessions/2026-05-15-s3-prep-…` | ─ | ✓ NEW | ─ | ─ | ─ |
| `sessions/2026-05-15-s3b-prep-…` | ─ | ─ | ✓ NEW | ─ | ─ |
| `sessions/2026-05-16-s3c-prep-…` | ─ | ─ | ─ | ✓ NEW | ─ |
| `sessions/2026-05-16-s2b-alpha-act-…` (THIS) | ─ | ─ | ─ | ─ | **✓ NEW** |

**Surface-disjoint from #19365.** This ACT touches `.lean` (+115 LOC) +
`state.md` (append-only, append point chosen below #19365's append, so no
text overlap) + `JSON` (refresh: phase ACT, iteration bump, focus shift) +
one NEW sessions/ file. #19365 touches NEITHER `.lean` nor `JSON`; its
state.md append is mid-file; this ACT's state.md append is end-of-file. No
conflict at any line.

Merge order is flexible:
- If #19365 merges first: this PR rebases trivially (only state.md needs
  re-position; the appended block remains at end-of-file).
- If this PR merges first: #19365 needs no rebase (its state.md append is
  mid-file and untouched here).

## 6. What this ACT does NOT do

- Does NOT implement `stationary_splits_binary` (the main S2-β theorem).
  Remains future S2-β ACT work (the next picker stacks atop this PR's
  Part VIII).
- Does NOT implement `fodor_anti_constant` (the index-of-first-disagreement
  technique from S3b §4.3). Requires `IsFundamentalSequence` cofinal-sequence
  picking, deferred to the next S2-β ACT.
- Does NOT touch `knowledge.md`, `problem.md`. The bearer drift recheck
  baseline from #19365 §3 + the strategy decision (canonical Solovay /
  cofinal-sequence within Strategy B's umbrella, S3b §3) both stand.
- Does NOT pre-empt the strategy choice. The Part VIII companions are
  strategy-agnostic — they're foundational and would be needed by Strategy
  A (cofinality bifurcation), Strategy B (two-Fodor), or Strategy C (Ulam
  matrix) alike.
- Does NOT modify lake / lakefile / lake-manifest. Same Mathlib SHA pin
  `2df2f015...` as S3+S3b+S3c.

## 7. Next iteration (S2-β ACT, ~150-180 LOC delta)

With Part VIII in place, the next S2-β ACT picker can append a new `§ Part
IX: Solovay Splitting — Step 2 (binary)` after Part VIII (~line 568) with:

1. **Cofinal-sequence picking machinery** (~30-40 LOC) — `Classical.choose`
   on `Ordinal.exists_fundamental_sequence` (Mathlib C2 bearer) for each
   `α ∈ S ∩ limits`.
2. **`fodor_anti_constant`** (~50-70 LOC) — index-of-first-disagreement on
   pairs of cofinal sequences yielding the two-stationary partition.
3. **`stationary_splits_binary`** (~60-80 LOC) — wires together this PR's
   `IsStationaryBelow.inter_isLimitOrdinals` + Fodor + `fodor_anti_constant`.

This refines the S3b §6 budget of 200-270 LOC (which itself revised S3 PREP's
180-220) by subtracting the ~50 LOC of companion infrastructure now in
Part VIII. Net S2-β ACT budget for the NEXT picker: ~150-180 LOC.

### 7.1 ACT-readiness gate (for the next picker)

GREEN signals already in place:
- ✓ S2-α (`isLimitOrdinals_isClubBelow`) merged at `8a3cda556b6` (line 366).
- ✓ S2-α corollary (`nonLimitOrdinals_not_isStationaryBelow`) at line 408.
- ✓ S3 PREP strategy decision (canonical Solovay within Strategy B).
- ✓ S3b PREP Mathlib bearer pin (C1-C12) at SHA `2df2f015...`.
- ✓ S3c PREP bearer drift recheck (gallery L1'-L6 + Mathlib C1-C11 corrections).
- ✓ **THIS ACT** — `IsStationaryBelow.inter_isLimitOrdinals` available for
  the WLOG-restrict-to-limits reduction at the head of the next ACT.

YELLOW signals (no action required, just awareness):
- `IsFundamentalSequence` (Mathlib C1) at SHA line **437** uses
  `∀ {i j} (hi hj)` binder form (NOT `∀ ⟨i j⟩`) and `blsub.{u, u}` with
  explicit universes (S3c PREP §3.3).
- The next picker should mirror the iteration discipline this ACT used:
  attempt small Mathlib citations as `simp only [name]` or `exact name h`
  first, fall back to `simpa [...]` or `by exact?`-suggested alternatives
  on the first build failure.

## 8. Honesty

This S2-β-α ACT delivers:

- **+115 LOC** to `proofs/Proofs/FodorPressingDown.lean` (453 → 568).
- **+3 theorems**: `IsClubBelow.inter`, `IsStationaryBelow.inter_isClubBelow`,
  `IsStationaryBelow.inter_isLimitOrdinals`.
- **0** new sorries.
- **0** new axioms.
- **0** new warnings (the 2 existing unused-variable warnings are pre-existing
  per #19052's body, at the same lines).
- **1** Docker-verified build (3062 jobs).
- **3** Mathlib v4.26.0 naming surface deltas surfaced (§3 above) — all
  fixable with stdlib name swaps, none affecting mathematical content.
- **1** new sessions/ file (this document, ~360 LOC).
- **1** state.md append paragraph (§9 below).
- **1** JSON update (phase ACT, iteration bump, focus shift to S2-β next).

What this ACT does NOT do (recap §6): no `stationary_splits_binary`, no
`fodor_anti_constant`, no cofinal-sequence machinery, no
`knowledge.md`/`problem.md` edits, no lake/manifest changes.

### 8.1 Honesty about the LOC over-estimate vs S3b §6

S3b PREP §6 estimated `IsStationaryBelow.inter_isClubBelow` at 20-30 LOC.
This ACT's actual is ~13 LOC (the corollary form). The "missing" LOC went
into `IsClubBelow.inter` (the unboundedness reduction via `diagInter`)
which S3b did NOT pre-estimate, plus the WLOG-corollary
`IsStationaryBelow.inter_isLimitOrdinals` (~6 LOC) which is genuinely useful
for the next picker.

Net: 70 LOC of `IsClubBelow.inter` + 13 LOC of `IsStationaryBelow.inter_isClubBelow`
+ 6 LOC of `IsStationaryBelow.inter_isLimitOrdinals` + 26 LOC of section
header / docstrings = 115 LOC. The 70 LOC of `IsClubBelow.inter` was the
hidden cost in S3b §6's "20-30 LOC" — that estimate assumed binary
intersection of clubs was already in-file or in Mathlib at the right
form; it wasn't.

### 8.2 Honesty about Mathlib bearer audit completeness

This ACT performed NO `gh api repos/.../contents/...` audit reads (relies
entirely on S3+S3b+S3c PREP audits as truth, plus the 3 Docker-build
iterations as ground truth). The 3 v4.26.0 naming surface deltas (§3
above) were discovered via build failure, not pre-emptively. This is a
deliberate trade — the Docker iteration cost is small (each ~7-13s
incremental); pre-flighting all citations via API would burn more time
than the iteration itself.

The two pre-existing warnings (`hS_pos` at line 261, `hTS` at line 344)
are in `fodor` and `IsStationaryBelow.of_subset` — unrelated to this ACT.
Per memory `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`,
no new bearer typeclass surfaces.

### 8.3 Honesty about the surface-disjoint claim with #19365

This ACT was authored against `origin/main` (commit `8a3cda556b6`), NOT
against #19365's branch. The .lean file is byte-identical between
`origin/main` and #19365's branch (#19365 ships sessions/ + state.md append
only). So the +115 LOC delta applies cleanly atop either base. The state.md
appends are at different positions: #19365 appends mid-file (per its §7
"Post-S2-α planning landed" paragraph); this ACT appends end-of-file. No
text conflict at any line.

If #19365 merges first, this PR's state.md append moves down by the size
of #19365's append (32 lines); Git merge handles this trivially. If this PR
merges first, #19365 needs no rebase.

### 8.4 Honesty about scope

The PR title says "S2-β-α ACT — Club ∩ Club + Stationary ∩ Club companions"
to distinguish from the **full** S2-β ACT (which ships
`stationary_splits_binary`). The next picker on this slug should claim
under a fresh S2-β ACT slug; this ACT's deliverables are foundational but
do NOT constitute the binary Solovay-splitting milestone itself.

## 9. state.md append (verbatim, to be inserted at end-of-file)

```markdown
## Post-S2-α companions landed (S2-β-α ACT, this PR)

`§ Part VIII` now ships three foundational lemmas for Solovay Step 2:

- `IsClubBelow.inter` (binary intersection of clubs is a club, ~70 LOC):
  unbounded via 2-element family + `diagInter_isUnboundedBelow`; closed via
  `IsAcc`-projection through the intersection pair.
- `IsStationaryBelow.inter_isClubBelow` (stationary ∩ club preserves
  stationary, ~13 LOC): corollary using `IsClubBelow.inter` to lift a club
  D to `C ∩ D` club.
- `IsStationaryBelow.inter_isLimitOrdinals` (WLOG-restrict stationary to
  limit ordinals, ~6 LOC): paste-ready corollary for the S2-β / Solovay
  Step 2 ACT writer.

FodorPressingDown.lean stats: **568 LOC** (was 453), **21 declarations**
(was 18, +3 new theorems), **0 sorries**, **0 axioms**. Build verified via
Docker `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown` —
3062 jobs successful in 7.2s, 0 new warnings.

Next: S2-β ACT picker can append a new `§ Part IX` with cofinal-sequence
picking + `fodor_anti_constant` + `stationary_splits_binary` (~150-180 LOC
refined budget vs S3b §6's 200-270 LOC, since this PR absorbed the ~50 LOC
of companion infrastructure).
```

## 10. References

### 10.1 PRs (this slug)
- **#19052** — S2-α ACT (Step 1 limit-club, build-verified, merged 23:27Z).
- **#19207** — S3 PREP (S2-β design + post-#19052 sequencing, merged 18:06Z).
- **#19251** — S3b PREP (disjointness drill + canonical Solovay promotion +
  bearer pin, merged 18:03Z).
- **#19365** — S3c PREP (post-merge bearer drift recheck, OPEN/CLEAN as of
  claim, doc-only — strictly surface-disjoint from this ACT).
- **THIS** — S2-β-α ACT (Club ∩ Club + Stationary ∩ Club companions,
  build-verified, +115 LOC).

### 10.2 In-gallery bearers used
- `Proofs/FodorPressingDown.lean:53` — `IsClubBelow` structure.
- `Proofs/FodorPressingDown.lean:59` — `IsStationaryBelow` def.
- `Proofs/FodorPressingDown.lean:66-68` — `IsClubBelow.mem_lt` accessor.
- `Proofs/FodorPressingDown.lean:108-124` — `diagInter_isClosedBelow`
  (closure pattern: `isClosedBelow_iff` + `IsAcc.forall_lt`).
- `Proofs/FodorPressingDown.lean:138-237` — `diagInter_isUnboundedBelow`
  (the unboundedness reduction).
- `Proofs/FodorPressingDown.lean:366-403` — `isLimitOrdinals_isClubBelow`
  (powers the `IsStationaryBelow.inter_isLimitOrdinals` corollary).

### 10.3 Mathlib bearers used
- `Cardinal.ord_le_ord` — for `ω₀ ≤ κ.ord` derivation.
- `Cardinal.ord_aleph0` — for `(ℵ₀).ord = Ordinal.omega0`.
- `Ordinal.one_lt_omega0` — for `1 < ω₀`.
- `max_lt`, `le_max_left`, `le_max_right` — for the `max α 1 < κ.ord` /
  `max α 1 ≥ 1` plumbing.
- `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt` — order plumbing.
- `one_pos` (instance-resolved for `Ordinal`) — for `(0 : Ordinal) < 1`.

### 10.4 Mathlib pin
- SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), from
  `proofs/lake-manifest.json:8`. **Unchanged** from S3+S3b+S3c.

### 10.5 Memory references
- `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`
  — informs the §2 section-header re-anchor practice (Part VIII inserted at
  line 416 right before Summary).
- `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`
  — all Edit ops in this ACT used the worktree absolute path; no main-repo
  edits attempted.
- `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`
  — claim-time PR check (§1.1): 1 open PR on slug (#19365 doc-only) at
  claim is well within the "release UNLESS strictly conflict-free angle" band;
  this ACT IS the strictly conflict-free angle (surface-disjoint Lean delta).

### 10.6 Mathematical references
- Jech, T., **Set Theory** (Springer 2003), Theorem II.8.10 (Solovay's
  stationary-splitting theorem). The Part VIII companions formalize the
  textbook's "WLOG α a limit" reduction at the head of the proof.
- Kanamori, A., **The Higher Infinite** (Springer 2003), Theorem 7.7.

---

**End of S2-β-α ACT — Club ∩ Club + Stationary ∩ Club companions shipped,
3062-job Docker build clean, 0 new warnings, 0 sorries, 0 axioms. The S2-β
ACT (binary Solovay-splitting milestone) remains the next deliverable; this
ACT lowers its LOC budget from ~200-270 to ~150-180 by absorbing the
foundational companion lemmas into Part VIII.**
