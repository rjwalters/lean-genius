# S14 ORIENT — bearer re-verification + R4 regression retraction

**Researcher**: researcher-1
**Date**: 2026-06-15
**Phase**: ORIENT (no build — dual-backend blackout)
**Lean change**: NONE (registered file is correct; blackout prevents build verification)

## Backends

- **Docker**: 5 containers (saturated) — no build window.
- **Aristotle MCP**: `mcp__aristotle__prove` on a trivial probe returns
  `{'status':'error','message':'Resource not found'}` (404). Backend down.

No sorry can be discharged-and-verified this session. Work is build-free:
independent bearer verification + correction of a same-day knowledge regression.

## Why this session matters: a contradiction between three sources

1. **The registered `.lean` file** (Step-1 docstring, lines 74–80) states the
   char-in-normal bridge is the 0-LOC instance
   `ConjAct.normal_of_characteristic_of_normal` at ConjAct.lean:260.
2. **S10 session** (researcher-7, 2026-06-14) independently found the same
   instance and corrected S8's "no bearer" verdict.
3. **The 2026-06-15 problem-JSON** (`progressSummary` + insight #7) then
   "REFUTED" this, claiming the lemma is ABSENT and R4 needs a real ~5–20 LOC
   construction.

(1) and (2) agree; (3) is a regression that would mislead the next ACT session
into building an unnecessary bridge.

## Finding: (3) is wrong; (1)/(2) are right

The "absent" check searched `Subgroup.normal_of_characteristic_of_normal`. The
instance is in the `ConjAct.` namespace. Re-confirmed this session at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
gh api repos/leanprover-community/mathlib4/contents/\
  Mathlib/GroupTheory/GroupAction/ConjAct.lean?ref=2df2f015... | jq -r .content | base64 -d
# namespace ConjAct opens line 46, closes 267
# line 260:
instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal]
    {K : Subgroup H} [h : K.Characteristic] : (K.map H.subtype).Normal
```

Signature is EXACT to the file's docstring. Being an `instance`, it fires by
typeclass resolution once `Mathlib.GroupTheory.GroupAction.ConjAct` is imported
(file line 38), no explicit invocation. **Step-4/R4 is genuinely 0-LOC.**

## Full discharge-plan bearer re-verification (all present at pin)

Step 5 (H_le_normalizer, the most discharge-ready):
`IsCycle.orderOf` (Perm/Cycle/Basic.lean:363), `Nat.card_zpowers`,
`Sylow.card_eq_multiplicity` (Sylow.lean:702), `padicValNat_factorial`
(Padics/PadicVal/Basic.lean), `Subgroup.le_normalizer_of_normal_subgroupOf`
(Algebra/Group/Subgroup/Basic.lean:378).

Step 1 (sylow_p_unique):
`derivedSeries_succ/normal/characteristic` (Solvable.lean:49/53/65),
`IsBlock.orbit_of_normal` (Blocks.lean:475),
`IsBlock.subsingleton_or_eq_univ` (Primitive.lean:115),
`Sylow.characteristic_of_normal` (Sylow.lean:728), `Sylow.ofCard` (Sylow.lean:102),
`Sylow.unique_of_normal` (Sylow.lean:710), `ConjAct.normal_of_characteristic_of_normal`
(ConjAct.lean:260).

Step 2 (already discharged): `Sylow.normal_of_subsingleton` (Sylow.lean:724).

**Path-drift caveat:** `le_normalizer_of_normal_subgroupOf` is at
`Mathlib/Algebra/Group/Subgroup/Basic.lean:378`, not the
`Mathlib/GroupTheory/Subgroup/Basic.lean` cited in older notes (line 378 is
correct; the directory moved upstream). Resolves by fully-qualified name
regardless.

## Net effect

- Knowledge base corrected: R4 char-in-normal bridge is 0-LOC (instance),
  restoring the S10 finding; the 2026-06-15 "REFUTED" note is retracted.
- Every Step-1 and Step-5 discharge-plan bearer confirmed present at the pin —
  both routes are pure-transcription-ready.
- The next Docker-up or Aristotle-up ACT session can discharge without further
  bearer hunting. Step 5 is self-contained (`import Mathlib` only) → an ideal
  single Aristotle target once the 404 clears.
- All 5 sorries intact; registered `.lean` file unchanged (it was correct).

## Files touched

- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`
  — corrected insight #7, progressSummary, currentState (S14, iter 14), blockers.
- `research/problems/.../knowledge.md` — S14 section with bearer table.
- `research/problems/.../sessions/2026-06-15-s14-orient-bearer-reverify-r4-retraction.md`
  — this note.
