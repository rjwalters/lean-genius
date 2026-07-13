# Session S4f PREP — Dot-Notation Resolution Audit (Part VIII / Part IX)

**Date**: 2026-06-05
**Researcher**: researcher-1
**Phase**: PREP (doc-only; no Lean changes)
**Predecessors**: S4 PREP (PR #18441), S4b PREP (#18519), S4c PREP (#18585),
S4d PREP (#18733), S4e PREP (#18891), S5 STATE-SYNC (#18905)

## TL;DR

The S4 ACT cut plan in S4c/S4d/S4e PREPs and S5 STATE-SYNC predates two
parent-file additions (Solovay Step 2 companions in §Part VIII at
`FodorPressingDown.lean` lines 502–527, and the Solovay Step 2 head in
§Part IX lines 602–608) that introduce **dot-notation calls** on
`IsStationaryBelow` values. After the S4 ACT cut deletes the parent-local
`def IsStationaryBelow`, those dot-notation calls **break**: the type of
the receiver becomes `Ordinal.IsStationaryBelow`, and Lean 4 dot notation
on `hS : Ordinal.IsStationaryBelow ...` looks up
`Ordinal.IsStationaryBelow.inter_isClubBelow` (which does not exist).

This session memo audits the two problematic callsites and prescribes the
**minimal mechanical fix** for the S4 ACT writer: convert the two dot-
notation calls to fully-qualified function calls. No additional Lean
definitions are lifted; no design change is needed.

## Background: what changed after the S4c/d/e PREPs

The S4c PREP audit (PR #18585, 2026-05-13) was authored against parent
file state ≈ 385 LOC, before the oq-04 sister slug shipped its
S2-β-α ACT (PR #19378, 2026-05-15, adding §Part VIII at +115 LOC) and
its S2-β-β ACT (PR #20621, 2026-05-25, adding §Part IX at +86 LOC).
S5 STATE-SYNC (PR #18905, 2026-05-16) recorded the existence of the new
Part VIII theorems and added 5 names to the S4 ACT re-anchoring scope,
but did not drill into the **dot-notation resolution semantics** because
the parent's `def IsStationaryBelow` was still in place at that point.

The remaining 3 theorems added in S2-β-β (cofHead-cohort, Part IX) were
recorded in S6 ACT's state.md update (2026-05-31) but again the re-
anchoring details were left to S4 ACT writer.

## The Issue: Lean 4 dot-notation namespace resolution

In Lean 4, when `hS : Ordinal.IsStationaryBelow S κ.ord` and the writer
calls `hS.inter_isClubBelow ...`, the elaborator looks up the constant
`Ordinal.IsStationaryBelow.inter_isClubBelow`. It does **not** fall back
to searching opened namespaces or the current `FodorPressingDown`
namespace. If the constant is not found, elaboration fails with
"unknown constant" or "no field inter_isClubBelow".

Currently the parent file has:

```
-- parent line 50 (still on origin/main):
def IsStationaryBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty
```

so the type `IsStationaryBelow S κ.ord` resolves to
`FodorPressingDown.IsStationaryBelow S κ.ord`, and the dot-notation calls
at lines 526 and 608 resolve to `FodorPressingDown.IsStationaryBelow.{inter_isClubBelow,inter_isLimitOrdinals}`,
both of which are declared in the parent file.

After S4 ACT deletes the parent-local `def IsStationaryBelow`, types of
`hS` parameters declared with `IsStationaryBelow S κ.ord` in their
signatures resolve to `Ordinal.IsStationaryBelow` (via the parent's
`open Ordinal`). At that point both dot-notation calls break.

## The Two Affected Callsites

### Callsite 1: parent line 526 (inside `IsStationaryBelow.inter_isLimitOrdinals`)

```
-- parent file, lines 522–527 (origin/main):
theorem IsStationaryBelow.inter_isLimitOrdinals {S : Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hS : IsStationaryBelow S κ.ord) :
    IsStationaryBelow (S ∩ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α}) κ.ord :=
  hS.inter_isClubBelow hκ hκ_unc (isLimitOrdinals_isClubBelow hκ hκ_unc)
                                                                          --  ^^^^^^^^^^^^^^^^^
                                                                          --  dot-notation call
```

### Callsite 2: parent line 608 (inside `exists_cofHead_constant_stationary_of_stationary`)

```
-- parent file, lines 602–608 (origin/main):
theorem exists_cofHead_constant_stationary_of_stationary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord) :
    ∃ β < κ.ord, IsStationaryBelow
      (S ∩ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} ∩ cofHead ⁻¹' {β}) κ.ord :=
  exists_cofHead_constant_stationary hκ hκ_unc
    (hS.inter_isLimitOrdinals hκ hκ_unc) (fun _ hα => hα.2)
   --  ^^^^^^^^^^^^^^^^^^^^^^^^
   --  dot-notation call
```

## The Fix: convert to qualified function calls

The minimal change is to call the theorems by their fully-qualified
**defined** name. After the S4 ACT cut, the theorems `IsStationaryBelow.
inter_isClubBelow` and `IsStationaryBelow.inter_isLimitOrdinals` REMAIN in
the parent file (they are NOT deleted by S4 ACT — they live in
`namespace FodorPressingDown` and are not redundant with anything in
`Proofs/Club/Basic.lean`). Their fully-qualified names are
`FodorPressingDown.IsStationaryBelow.inter_isClubBelow` and
`FodorPressingDown.IsStationaryBelow.inter_isLimitOrdinals`.

Inside `namespace FodorPressingDown` they are reachable as
`IsStationaryBelow.inter_isClubBelow` (no prefix needed because we are in
the namespace). So the mechanical rewrite is:

```
-- BEFORE (parent line 526):
hS.inter_isClubBelow hκ hκ_unc (isLimitOrdinals_isClubBelow hκ hκ_unc)

-- AFTER (parent line 526):
IsStationaryBelow.inter_isClubBelow hS hκ hκ_unc
  (isLimitOrdinals_isClubBelow hκ hκ_unc)
```

```
-- BEFORE (parent line 608):
(hS.inter_isLimitOrdinals hκ hκ_unc) (fun _ hα => hα.2)

-- AFTER (parent line 608):
(IsStationaryBelow.inter_isLimitOrdinals hS hκ hκ_unc) (fun _ hα => hα.2)
```

## Why the qualified call works

Inside `namespace FodorPressingDown`, the constant name
`IsStationaryBelow.inter_isClubBelow` is resolved by Lean's constant-
lookup machinery in this order:
1. `FodorPressingDown.IsStationaryBelow.inter_isClubBelow` ← match
2. (fallback) `IsStationaryBelow.inter_isClubBelow` in root / opened
   namespaces

Step 1 matches because the parent file declares the theorem (line 502)
inside `namespace FodorPressingDown`, regardless of which type
`IsStationaryBelow` itself resolves to. The dot in the name is
treated as part of the identifier, not as a lookup hint into the type of
the first argument.

Contrast this with the dot-notation form `hS.inter_isClubBelow`, which
Lean rewrites by first computing the type of `hS`, then looking up
`<head-of-type>.inter_isClubBelow`. With `hS : Ordinal.IsStationaryBelow
...` post-S4, that lookup targets `Ordinal.IsStationaryBelow.
inter_isClubBelow`, which does not exist.

## Why this is the minimal fix

Three alternatives were considered:

**Alternative A: Lift Part VIII to `Proofs/Club/Basic.lean`** under the
`Ordinal` namespace. This would create `Ordinal.IsStationaryBelow.inter_
isClubBelow` and `.inter_isLimitOrdinals` directly, restoring the dot-
notation calls. But Part VIII's `IsClubBelow.inter` depends on
`diagInter_isUnboundedBelow` (the 90-LOC zipper construction, parent
lines 138–229), which is cardinality-pinned (`Cardinal.{0}`) and was
intentionally left in parent per the S1 OBSERVE design lock. Lifting it
violates the design lock and requires a much larger refactor.

**Alternative B: Lift Parts III, VIII, IX wholesale to Basic.lean**.
This is a maximally clean library, but it violates the S1 OBSERVE design
lock and effectively merges the parent file into Basic.lean. Out of
scope for an "S4 cut".

**Alternative C: Convert dot notation to qualified calls** (this fix).
Two-line edit, no design changes, no LOC added to Basic.lean, no risk to
the existing PREP recipes.

Alternative C is the correct choice. The library-design question of
whether to lift Part VIII to Basic.lean (as recommended by S7 ACT's
"S6 (optional, post-S4 ACT)" note) remains open as a **post-S4** decision.

## Updated S4 ACT cut recipe (delta from S4c/d/e PREPs)

S4 ACT writer should:

1. Apply the S4c/d/e PREP recipe verbatim for deletions and re-anchoring.
2. **Add two micro-edits**, both at the bottom of the file:
   a. Parent line ~526: rewrite `hS.inter_isClubBelow ...` → qualified
      form (see §"The Fix" above).
   b. Parent line ~608: rewrite `hS.inter_isLimitOrdinals ...` →
      qualified form.
3. Build with `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown`
   plus `./proofs/scripts/docker-build.sh Proofs.Club.Basic` (or build
   the whole project) — expect ~30 min.
4. If build passes, commit + push + open PR with
   `loom:review-requested` removed (math agents bypass Judge review per
   CLAUDE.md). Apply S4 ACT meta-update (lineCount, theoremCount,
   definitionCount) per the S4c §7 recipe + S4d §9 corrections.

## Why this PREP is appropriate now

The S4 ACT cut has been blocked through 5 prior PREP iterations (S4, S4b,
S4c, S4d, S4e) plus the S5 STATE-SYNC. The slug has shipped 3 strictly-
additive ACTs (S3, S6, S7) in the interim. The parent file has grown
**269 LOC** (385 → 654) since the S4 PREP audit, including 2 sister-slug
ACTs (S2-α, S2-β-α, S2-β-β) that the older PREPs did not analyze in
detail.

This audit closes the last known **mechanical gap** in the S4 ACT recipe:
the dot-notation calls at lines 526 and 608 will fail silently if the
S4 ACT writer follows the old recipe verbatim. Catching this in a doc-
only PREP avoids a build failure during the high-stakes parent cut on a
Wiedijk #25 verified entry.

## Sanity checks for the S4 ACT writer

After deletions and the two micro-edits at lines 526 and 608, the writer
should grep for ALL dot-notation calls on receivers of type
`IsStationaryBelow` or `IsClubBelow`:

```
rg -n '\.(subset_Iio|closed|unbounded|mem_lt|mem_of_isAcc|nonempty|of_subset|inter|inter_isClubBelow|inter_isLimitOrdinals)\b' \
   proofs/Proofs/FodorPressingDown.lean
```

The expected pattern (post-S4 cut):
- `.subset_Iio` / `.closed` / `.unbounded` — these are STRUCTURE FIELDS
  of `Ordinal.IsClubBelow`, so they remain valid via dot notation on
  any `IsClubBelow` value, regardless of whether the receiver type is
  named `Ordinal.IsClubBelow` or (post-S4) the `Ordinal.IsClubBelow`
  alias. **No change needed.**
- `.mem_lt` / `.mem_of_isAcc` — these are lifted to
  `Ordinal.IsClubBelow.mem_*` in Basic.lean. **No change needed.**
- `.nonempty` / `.of_subset` — these are lifted to
  `Ordinal.IsStationaryBelow.{nonempty,of_subset}` in Basic.lean
  (via S7 ACT). **No change needed.**
- `.inter_isClubBelow` / `.inter_isLimitOrdinals` — these LIVE IN PARENT
  under `FodorPressingDown.IsStationaryBelow`; not lifted. **CONVERT TO
  QUALIFIED FORM** per §"The Fix" above (lines 526, 608).

The same exhaustive grep would also catch potential issues with
`.inter` on `IsClubBelow` receivers; current parent file does NOT call
`hC.inter` via dot notation (it uses `IsClubBelow.inter hκ hκ_unc hC
hD` at line 508 — verified by grep on origin/main).

## Iteration / Phase note

This is iteration 12, phase PREP (S4f). Strictly additive doc-only;
no Lean changes. After this PREP merges, the next ACT step (S4 ACT —
parent cut) has zero remaining mechanical unknowns.

## Files changed by this PREP

- `research/problems/fodor-pressing-down-oq-01/sessions/2026-06-05-s4f-prep-dot-notation-resolution.md` (this file, new).
- `research/problems/fodor-pressing-down-oq-01/state.md` (update phase
  / iteration counter / per-stage table / Next Action with §"The Fix"
  references).

## References

- Lean 4 dot-notation rules: <https://leanprover.github.io/theorem_proving_in_lean4/structures_and_records.html#dot-notation>
  (relevant paragraph: "field notation lookups go through the inferred
  type's head, not opened or current namespaces").
- Parent file on origin/main: 654 LOC, 20 theorems, 4 defs.
- Basic.lean on origin/main: 183 LOC, 0 axioms, 0 sorries.
