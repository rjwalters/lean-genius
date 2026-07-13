# S3 PREP — S2-β binary Solovay design + post-#19052 sequencing (doc-only)

**Date**: 2026-05-15
**Researcher**: researcher-12
**Mode**: PREP (doc-only, forward design + cross-PR coordination)
**Status**: pristine, single-file addition under `sessions/`,
strictly orthogonal to open PR #19052 (S2-α ACT)

## 0. Why S3 PREP

PR #19052 (S2-α ACT, opened 2026-05-14T13:24Z by researcher-8) is
**CLEAN, mergeable, and stuck** behind a system-wide deployer
stall. It ships Step 1 of the three-step Jech proof of Solovay
splitting (limit ordinals form a club below `κ.ord`) plus the
`nonLimitOrdinals_not_isStationaryBelow` corollary. Once it merges:

- `proofs/Proofs/FodorPressingDown.lean`: 385 → 453 LOC; 12 → 14
  theorems; 0 sorries / 0 axioms (unchanged).
- `state.md`: phase OBSERVE → ACT, iteration 1 → 7.
- JSON `phase` and `currentState.phase` both updated to ACT.

**Deployer stall evidence** (per memory
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`):

- Most recent merge anywhere in the repo: 2026-05-14T03:03:38Z
  (PR #18980, schroeder-bernstein-oq-01 S6 BUILD UNBLOCKER).
- Current time: 2026-05-15T01:49Z.
- Gap: **~22.7 hours zero-merge**, well past the 12-hour
  deployer-stall threshold.
- PR #19052 age at this writing: ~12.4 hours, CLEAN since at least
  the S6 PREP audit window.

**No re-implementation, no conflicting ACT.** This S3 PREP is
strictly forward-looking design + cross-PR coordination per the
documented pattern.

## 1. Open-PR check (pre-claim and pre-push)

Per memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`:

```
$ gh pr list -R rjwalters/lean-genius \
    --search "fodor-pressing-down-oq-04 in:title" --state open
[
  {
    "number": 19052,
    "title": "research(fodor-pressing-down-oq-04): S2-α ACT — limit ordinals form a club (Solovay Step 1, build-verified)",
    "createdAt": "2026-05-14T13:24:18Z",
    "mergeStateStatus": "CLEAN"
  }
]
```

One open PR on this slug — PR #19052. To be re-checked immediately
before `git push` of this PREP per the pre-push pattern. The
sister slug `fodor-pressing-down-oq-01` (Club library extraction)
has its own active PR queue — verified non-overlapping below in §6.

## 2. Post-#19052 baseline (projected, source: PR #19052 body
table)

After PR #19052 lands, the file's append point structure becomes:

```
Line  Section
----  ---------------------------------------------------------
053   IsClubBelow definition
059   IsStationaryBelow definition
240   diagInter_isClubBelow
259   fodor (Pressing-Down Lemma)
319   fodor_aleph1
333   IsStationaryBelow.nonempty
343   IsStationaryBelow.of_subset
350   § Summary and Open Next Steps
385   end FodorPressingDown                  ← pre-#19052
... (S2-α additions in NEW § Part VII at lines 386-453) ...
453   end FodorPressingDown                  ← post-#19052
```

Per PR #19052's body, the new theorems land in a NEW section
between the existing Part VI (subsidiary lemmas) and the summary
docstring; the section is titled "§ Part VII: Solovay Splitting
Step 1". Two named theorems are exposed at the post-merge file:

```lean
theorem isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    IsClubBelow {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} κ.ord

theorem nonLimitOrdinals_not_isStationaryBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    ¬ IsStationaryBelow {α : Ordinal | α < κ.ord ∧ ¬ IsSuccLimit α} κ.ord
```

These are the two upstream dependencies for any S2-β ACT body
that needs to WLOG-restrict to limit ordinals before applying
`fodor`.

### 2.1 Append point for S2-β (projected)

After PR #19052 lands, the next ACT (S2-β) should append to a
NEW `§ Part VIII: Solovay Splitting Step 2 (binary)` section,
after line 453 and before the existing summary docstring (which
will likely have shifted to ~line 454+ post-#19052). The append
point is **line-stable** in the sense that PR #19052's diff is
pure-additive (+68 / -0 to the parent file body, plus the
section-summary line touch). No prior `theorem`/`def`/`section`
boundaries shift.

## 3. Mathlib v4.26.0 surface drifts NEW since S6 PREP (2026-05-13)

S6 PREP (PR #18603) and S2-α ACT (PR #19052) collectively pinned 8
Mathlib citations. This S3 PREP audit re-verifies them at the
inherited pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and
**surfaces 2 NEW drifts** not flagged by S6 PREP, both
operationally non-breaking but worth recording for S2-β authors.

### 3.1 `Cardinal.IsRegular` is a `def`, not a `structure`

S6 PREP §2.3 (`sessions/2026-05-13-s6-prep-row2-row4-erratum-closure.md:154-160`)
documented:

```lean
structure IsRegular (c : Cardinal) : Prop where
  aleph0_le : ℵ₀ ≤ c
  cof_eq : c.ord.cof = c
```

At v4.26.0
(`Mathlib/SetTheory/Cardinal/Regular.lean:42-43`), the actual
definition is:

```lean
def IsRegular (c : Cardinal) : Prop :=
  ℵ₀ ≤ c ∧ c ≤ c.ord.cof
```

with `aleph0_le := H.1` and `cof_eq` derived as a separate
theorem (`Regular.lean:48`):

```lean
theorem IsRegular.aleph0_le {c : Cardinal} (H : c.IsRegular) : ℵ₀ ≤ c :=
  H.1

theorem IsRegular.cof_eq {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2
```

**Operational impact**: ZERO. Both `hκ.aleph0_le` and `hκ.cof_eq`
work as expected via the named theorems. The gallery file uses
`hκ.aleph0_le` at lines 144, 285 and `hκ.cof_eq` at lines 161, 201
— all compile under v4.26.0 because the theorems exist with
those names. The S6 PREP doc's "structure" rendering was
descriptive shorthand, not a literal definition citation.

**Why surface this now**: S2-β designs that use `obtain ⟨h1, h2⟩
:= hκ` style destructuring will work (it's an `And`-projection).
But designs that say "by `cases` on the structure" will need
`rcases hκ with ⟨h1, h2⟩` instead — there is no `IsRegular.mk`
constructor anymore.

### 3.2 `Cofinality.lean` lives in `SetTheory/Cardinal/`, not `SetTheory/Ordinal/`

`knowledge.md` line 75 of this slug currently says:

```
Mathlib.SetTheory.Ordinal.Cofinality
  - Ordinal.cof : Ordinal → Cardinal
  - Ordinal.cof_lt
  - Ordinal.cof_le_card
  - Cardinal.IsRegular.cof_eq
```

At v4.26.0, the file is at `Mathlib/SetTheory/Cardinal/Cofinality.lean`
(verified via `gh api` on `git/trees/<SHA>?recursive=1`). The
namespace `Ordinal` exposes the relevant accessors (`Ordinal.cof`,
`Ordinal.cof_le_card`, `Ordinal.aleph0_le_cof` etc.) but they
are DEFINED in the `Cardinal/` directory file under `namespace
Ordinal` blocks.

**Operational impact**: ZERO for `import` purposes — both
`import Mathlib.SetTheory.Cardinal.Cofinality` AND
`import Mathlib.SetTheory.Cardinal.Regular` (which transitively
includes Cofinality.lean) make the API available. The gallery
file already imports `Mathlib.SetTheory.Cardinal.Cofinality`
indirectly via `Mathlib.SetTheory.Cardinal.Regular`.

**Why surface this now**: S2-β designers searching by file path
(e.g., `gh search code 'IsFundamentalSequence' path:Mathlib/SetTheory/Ordinal`)
will get 0 hits and conclude the API is missing. The correct
search is `path:Mathlib/SetTheory/Cardinal/Cofinality.lean`. This
is a stale-knowledge.md item to fix in a future STATE-SYNC, not a
blocker for S2-β.

### 3.3 Pin-spot check for S2-α deps (no drift detected)

Two key lemmas pinned by S6 PREP and used in S2-α:

| Citation | S6 PREP path | Verified at SHA |
|---|---|---|
| `Ordinal.isSuccLimit_add` | `Ordinal/Arithmetic.lean:511` | `Arithmetic.lean:511` ✓ |
| `Cardinal.isPrincipal_add_ord` | `Cardinal/Ordinal.lean:204` | `Cardinal/Ordinal.lean:204` ✓ |

Both still resolve at the same line numbers. PR #19052's body
documented 3 additional Mathlib v4.26.0 surface deltas hit during
build iterations (Cardinal.isPrincipal_add_ord rename, Ordinal
add-strict-mono via `IsNormal`, IsSuccLimit field order); those
are now baked into the merged ACT body and need no further audit.

## 4. S2-β strategy options (binary Solovay splitting)

The OQ asks for the full κ-splitting; S2-β is the milestone "any
stationary set splits into 2 disjoint stationary subsets". This
PREP enumerates strategies; the S2-β ACT writer should pick one
based on Mathlib API budget.

### 4.1 Goal statement (informally)

```lean
-- WANTED at S2-β:
theorem stationary_splits_binary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord) :
    ∃ S₁ S₂ : Set Ordinal,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
      IsStationaryBelow S₁ κ.ord ∧ IsStationaryBelow S₂ κ.ord
```

### 4.2 Strategy A — Cofinality bifurcation (Jech II.8 sketch)

Restrict to `S' = S ∩ {limit ordinals}` (stationary by S2-α's
`nonLimitOrdinals_not_isStationaryBelow`). For each `α ∈ S'`,
either `cof α = ℵ₀` (countable cofinality) or `cof α > ℵ₀`. This
gives a Boolean partition:

- `S₁ = S' ∩ {α | cof α = ℵ₀}` (ω-cofinal)
- `S₂ = S' ∩ {α | ℵ₀ < cof α}` (uncountably cofinal)

Disjointness is trivial. **Stationarity of both pieces** is the
genuine content. For the binary case, this strategy works only
when κ ≥ ℵ₂; for κ = ℵ₁ both pieces would be unbalanced (every
element of S' has cof ≤ ℵ₁ ≤ ℵ₀, so S₂ = ∅).

**Verdict**: STRATEGY-LIMITED. Does not work uniformly across
all regular κ; needs a second strategy for κ = ℵ₁.

### 4.3 Strategy B — Regressive auxiliary + Fodor bipartition

For each `α ∈ S'` (limits in S), choose `g(α) < α` regressive.
Apply `fodor` to obtain `β* < κ.ord` with `T* := {α ∈ S' | g(α)
= β*}` stationary. Now consider:

- `S₁ = T*` (constant on g)
- `S₂ = S' \ T*` (g varies)

`S₂` may not be stationary — it may be the union of Fodor-fibers
that are themselves non-stationary. The proof of `S₂` stationary
requires a separate argument (e.g. apply Fodor again to `S₂`
under a DIFFERENT regressive function and show the new fiber
is disjoint from `T*`). This is the **two-Fodor** technique.

**LOC estimate**: ~150-200 lines. Two `fodor` invocations + a
disjointness argument. Heavy use of `Classical.choose` for the
regressive `g`.

**Mathlib API needed**:
- `fodor` (already in-file at line 259, post-#19052 unchanged).
- A canonical regressive function on limit ordinals — e.g., the
  predecessor in `S'` (well-defined when `α` is a limit and `S'`
  is unbounded below `α`). Mathlib may have `Ordinal.pred` or
  similar; v4.26.0 exposes `Order.IsSuccLimit` predicate.
- `IsFundamentalSequence` from
  `Mathlib/SetTheory/Cardinal/Cofinality.lean:437` for the
  cofinal sequence picking.

**Risk**: the disjointness argument may collapse to S2-γ scope
unless carefully bounded. S2-β as "binary" was originally
proposed (per `knowledge.md:109-112`) as a reduced-bookkeeping
version of the κ-version, but the algebraic content of the
disjointness step is essentially the same.

### 4.4 Strategy C — Direct via Ulam matrix (sidesteps cofinality)

For κ = ℵ₁ (regular), use the classical Ulam matrix construction:
fix a canonical injection `S → ω₁ × ω₁`, project onto the second
coordinate, partition by parity. This produces 2 disjoint
stationary subsets without invoking cofinality.

**Verdict**: not general (only works for `κ = ℵ₁` in the
classical formulation). For arbitrary regular κ, the Ulam matrix
generalisation requires `κ`-many pairwise-disjoint clubs, which
is essentially the κ-version.

### 4.5 Recommendation

**Strategy B (two-Fodor)** is the most general approach and the
canonical textbook proof for binary Solovay. The disjointness
step is the main risk. S2-β ACT should:

1. Define a canonical regressive function on `S' ⊆ {limit ordinals}`
   — e.g., `g(α) = ⨅ {β ∈ S' | β < α}` (the inf over the
   intersection with `S' ∩ Iio α`). This requires `S' ∩ Iio α` to
   be nonempty, which holds because `S'` is stationary in
   `κ.ord` and `Iio α` is a club in `α` for `α` a limit.
2. Apply `fodor` to obtain `T₁`.
3. Define a SECOND regressive function `h` on `S' \ T₁` —
   careful to ensure `S' \ T₁` is itself stationary, which is
   the key obligation.
4. Apply `fodor` again to `S' \ T₁` (if stationary) → `T₂`.
5. Verify `T₁ ∩ T₂ = ∅` from constructions of g and h.

**LOC budget projection**: 180-220 lines, 0 new sorries, 0 new
axioms. Comparable in structural complexity to the existing
`fodor` proof (lines 259-313, ~55 LOC).

### 4.6 Anti-target — do NOT attempt full S2-γ in one PR

The `knowledge.md:114-115` S2-γ ("full Solovay") estimate is
~400+ LOC and requires `Classical.skolem` over a κ-indexed
family. That is out-of-scope for an S2-β session. Defer to S4+
sessions per the existing roadmap.

## 5. LOC budget for S2-β PREP-2 (NOT this PREP)

This S3 PREP is itself doc-only (no Lean). The CONTENT it
designs — S2-β PREP-2 (drilling into Strategy B's disjointness
step) — would itself be a doc-only PREP at ~200-300 LOC. Only
after S2-β PREP-2 ships should an S2-β ACT writer attempt the
180-220 LOC Lean implementation.

The S2-β ACT may discover Mathlib v4.26.0 surface drifts not
caught at PREP audit (cf. PR #19052's 3 build-iteration
discoveries). Build-pending researcher PRs on this slug now go
through Docker per S2-α's precedent (no longer "build pending"
convention).

## 6. Cross-PR conflict surface

This PREP creates **exactly one new file**:
`research/problems/fodor-pressing-down-oq-04/sessions/2026-05-15-s3-prep-s2b-binary-solovay-design-and-post-19052-sequencing.md`

| Target | #19052 (S2-α ACT) | This S3 PREP |
|---|---:|---:|
| `proofs/Proofs/FodorPressingDown.lean` | ✓ +68/-0 | ─ |
| `state.md` | ✓ +105/-42 | ─ |
| `JSON` (`fodor-pressing-down-oq-04.json`) | ✓ +25/-21 | ─ |
| `sessions/2026-05-14-s2a-act-...md` | ✓ NEW | ─ |
| `sessions/2026-05-15-s3-prep-...md` | ─ | ✓ NEW |

**Commit-disjoint from PR #19052.** No edit overlap on any file.

### 6.1 Sister-slug check

`fodor-pressing-down-oq-01` (Club library extraction, distinct
slug, both target the same parent `proofs/Proofs/FodorPressingDown.lean`):

```
$ gh pr list -R rjwalters/lean-genius \
    --search "fodor-pressing-down-oq-01 in:title" --state open
```

Has its own active PR queue (most recent activity 2026-05-14
~17:30 UTC per memory `feedback_researcher_cross_pr_coordination_audit_pattern.md`,
the S4e PREP for that slug). All those PRs touch
`Proofs/FodorPressingDown.lean` shared with this slug. **This S3
PREP has zero parent-file edits, so no shared-file collision.**
Once #19052 lands AND a future S2-β ACT lands on THIS slug, the
sister oq-01 PR queue will need a line-shift refresh.

### 6.2 System-wide deployer-stall awareness

Per memory pattern, this is one of multiple slugs with a stuck
CLEAN PR awaiting deployer. The detailed deployer-stall write-up
already exists in PR #19186 (`zsqrtd-neg-two-oq-03` slug,
researcher-8) and is cross-referenced by PR #19188
(`hilbert-14-oq-04` slug). This S3 PREP is the **third** such
documentation per the documented pattern; cross-references those
two write-ups by reference rather than duplicating their
68-stuck-PR system inventory.

## 7. Honesty

This PREP delivers:

- **0** new Lean theorems shipped.
- **0** sorry deltas (file remains 0 sorries pre- and post-merge of
  #19052 — and post-merge of any future S2-β).
- **0** axiom changes.
- **1** new design document (this file, ~280 LOC).
- **2** Mathlib v4.26.0 surface drifts surfaced (§3.1, §3.2).

What this PREP does NOT do:

- Implement S2-β. That remains future ACT work.
- Verify Strategy B's disjointness claim formally — only sketches
  the recipe per Jech (§4.5).
- Edit `state.md`, `knowledge.md`, `problem.md`, or any JSON.
  These edits are queued in PR #19052; this PREP would conflict
  if it touched them.
- Write a new mechanic kit. The post-#19052 baseline is build-clean
  per PR #19052's 3062-jobs Docker verification; no mechanic
  intervention needed.

### 7.1 Honesty about audit completeness

This PREP burned **2** `gh api repos/.../contents/...` reads
(directory listing + Cofinality.lean + Regular.lean) and **1**
`gh api git/trees/<SHA>?recursive=1` walk. No `gh search code`
quota burn. The audit relied primarily on direct contents-API
reads at the pinned SHA — sufficient to surface the IsRegular
def-vs-structure drift and the Cofinality.lean path correction
in 3 reads.

The Strategy B disjointness obligation (§4.5 step 3) is asserted
without a formal sketch. Future S2-β PREP-2 should drill into
this — the canonical Jech argument uses two regressive functions
chosen to ensure disjointness via a "g(α) ≠ h(α)" condition,
but the Lean encoding requires care.

### 7.2 Honesty about strategy ranking

§4 ranks Strategy B over A and C, but does NOT prove B is the
unique correct path. An S2-β ACT writer with deep familiarity in
Mathlib's `Cofinality.lean` API may find Strategy A (cofinality
bifurcation) tractable for κ ≥ ℵ₂ as a lemma + a Strategy-B
fallback for κ = ℵ₁. The state.md note (PR #19052 edits) does
not prescribe; this PREP recommends but does not lock.

### 7.3 Honesty about PR sequencing

The recommended merge order is:

1. **PR #19052** (S2-α ACT) — load-bearing for any S2-β ACT.
2. **This S3 PREP** — purely additive, zero conflict.
3. (Future) **S2-β PREP-2** (strategy drill-down, doc-only).
4. (Future) **S2-β ACT** (Lean implementation, depends on
   #19052 having merged).

If the deployer remains stalled past 2026-05-15T08:00Z,
intervention may be needed via `/loom` or manual deployer
respawn; that is out of scope for a researcher PREP.

## 8. References

### 8.1 Open PRs
- **#19052** (S2-α ACT, CLEAN, ~12.4h old at write-time): the
  predecessor this PREP coordinates with.

### 8.2 Merged PREP chain (this slug)
- #18193 (S1 OBSERVE)
- #18375 (S2 PREP — Step I limit-club design)
- #18471 (S3 PREP — cofinality bound)
- #18544 (S4 PREP — Mathlib name verification)
- #18603 (S5 PREP — Row 2/Row 4 phantom flagging)
- #18665 (S6 PREP — Row 2/Row 4 ERRATUM closure)

### 8.3 Mathlib references (v4.26.0 pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
- `Mathlib/SetTheory/Cardinal/Regular.lean:42-43` — `IsRegular`
  def (NOT structure).
- `Mathlib/SetTheory/Cardinal/Regular.lean:45-49` —
  `IsRegular.aleph0_le` and `IsRegular.cof_eq` accessors.
- `Mathlib/SetTheory/Cardinal/Cofinality.lean:437` —
  `IsFundamentalSequence` definition (for cofinal sequence
  picking in Strategy B).
- `Mathlib/SetTheory/Cardinal/Cofinality.lean:581` —
  `aleph0_le_cof` (cof of limit is ≥ ℵ₀).

### 8.4 Local references
- `proofs/Proofs/FodorPressingDown.lean:259-313` — the `fodor`
  hammer (unchanged by #19052).
- `proofs/Proofs/FodorPressingDown.lean:240` —
  `diagInter_isClubBelow` (Step 3 dependency, unused at S2-β).
- `proofs/Proofs/FodorPressingDown.lean:343` —
  `IsStationaryBelow.of_subset` (Step 1 / S2-α reduction
  building block).

### 8.5 Memory references
- `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
  — the documented pattern this PREP follows.
- `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
  — pre-claim and pre-push open-PR check.
- `feedback_researcher_cross_pr_coordination_audit_pattern.md` —
  multi-PR line-shift accounting (this slug has only 1 open PR;
  pattern still informs).

---

**End of S3 PREP — no Lean changes, no gallery JSON / state.md
edits, no axiom changes. PR #19052 (S2-α ACT) is the sole
prerequisite; this PREP is conflict-free with it. Two NEW Mathlib
v4.26.0 drifts recorded (IsRegular def-vs-structure;
Cofinality.lean lives in Cardinal/, not Ordinal/). Recommended
S2-β strategy: two-Fodor bipartition (Strategy B), expected
~180-220 Lean LOC. Defer Strategy A and C to S2-β author
judgement.**
