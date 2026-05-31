# S6 ACT — (C2-1d) Scarf walk skeleton on intervalTriangulation (researcher-1, 2026-05-30)

## Why this S6 fires now

S5 PREP (#19105+ era, researcher-3, 2026-05-16) packaged a paste-ready
~95 LOC skeleton for the 1-d Scarf walk on `Triangulation.intervalTriangulation`
with two corrections vs. the original PREP #18489:

- **F1 (HIGH)**: route through `T.adj` rather than the `private` `iadj`
- **F2 (MED)**: replace `decEq |>.recOn` with `infer_instance` for
  `Decidable IsPanchromatic1d`

S5 PREP §3's paste-ready skeleton ACT-gated on Docker + disk recovery
(both RED at S5 PREP). At S6 entry (2026-05-30), INFRA is GREEN:
Docker 29.4.1 stable, disk 57 Gi avail, Mathlib SHA `2df2f0150c…`
stable ~18d. Both RED gates lifted; S6 ACT proceeds.

## Scope

Single new leaf file: `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
(NEW, ~119 LOC including docstrings + module preamble; 6 definitions + 2
theorems + 1 Decidable instance, 1 sorry on `scarfWalk_isPanchromatic`
soundness, 0 axioms).

Paste-ready skeleton from S5 PREP §3 transcribed with minor adaptations:
- `open Triangulation` rather than `open SpernerSimplicialInstance` (no
  such namespace — the actual namespace is `Triangulation`)
- Full path `Triangulation.intervalTriangulation` for the matrix-level
  triangulation constructor
- **Build fix discovered in-session**: dropped `import Mathlib.Tactic.Decide`
  (PREP §3 listed it but the module does not exist at this pin; `decide`
  is a core Lean tactic and needs no Mathlib import)

The single sorry is on `scarfWalk_isPanchromatic`; its discharge plan
lives in S5 PREP §4 (~40 LOC across `scarfWalk_aux_spec` helper +
outer 1-line corollary).

## File contents (summary)

| # | Symbol | Type | Sorries |
|---|---|---|---|
| 1 | `IsPanchromatic1d` | `def` | 0 |
| 2 | `IsPanchromatic1d` `Decidable` instance | `instance` | 0 |
| 3 | `step` | `def` | 0 |
| 4 | `scarfWalkAux` | `def` | 0 |
| 5 | `scarfWalk` | `def` | 0 |
| 6 | `scarfWalk_isPanchromatic` | `theorem` | **1** |
| 7 | `exists_panchromatic_constructive` | `theorem` | 0 |

Total: 6 defs + 1 instance + 2 theorems = 9 declarations, 1 sorry, 0 axioms.

## Build verification

Docker build of `Proofs.SpernerSimplicialInstanceOQ05Scarf1d` under
recovered INFRA. Mathlib pin `2df2f0150c…` stable.

**Result**: **PASS** (after 1 in-session fix). First build failed with
`bad import 'Mathlib.Tactic.Decide'` — the module name listed in
S5 PREP §3 does not exist; dropping that import (since `decide` is a
core Lean tactic) resolved it. Second build:

```
⚠ [1098/1098] Built Proofs.SpernerSimplicialInstanceOQ05Scarf1d (5.0s)
warning: Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean:102:8: declaration uses 'sorry'
Build completed successfully (1098 jobs).
=== Build succeeded ===
```

0 errors. 1 warning for the expected `sorry` on
`scarfWalk_isPanchromatic` (S7 discharge). 1098 jobs total compiled
clean.

## Next action — S7+ candidates

(a) **Discharge `scarfWalk_isPanchromatic`** (~40 LOC) using S5 PREP §4
    plan: monotone-walk invariant + no-revisit corollary + fuel-exhaustion
    impossibility. Promotes file to 0 sorries.

(b) **Gallery promotion**: open `meta.json` for
    `sperner-simplicial-instance-oq-05` (already exists per S4 GALLERY
    #19105) with the new leaf file added to `leanFiles[]`. Status remains
    "axiomatized" until (a) closes; once 0 sorries, promote to "verified".

(c) **C3 ACT** (parallel): `findOppositeIdx` Classical.choose →
    computable per S2 PREP #18392 (~80 LOC, parent-file refactor).

## Out of scope (NOT touched at S6)

- `findOppositeIdx` refactor (C3, S2 PREP #18392 already shipped)
- `iadj` private-visibility refactor (current public `T.adj` route is
  sufficient)
- 2-d Scarf walk (C2-gen, deferred per S5 PREP)
- Gallery `meta.json` `leanFiles[]` update (mechanic batch territory
  post-merge)
- Misplaced-dir cleanup at `research/sperner-simplicial-instance-oq-05/`
  (mechanic territory)

## Ship scope (this S6 ACT)

4 files:
- `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` — new, ~119 LOC, 1 sorry
- `research/problems/sperner-simplicial-instance-oq-05/state.md` —
  iter 10 → 11, prepend S6 ACT block, S5 PREP preserved
- `src/data/research/problems/sperner-simplicial-instance-oq-05.json` —
  iter / focus / nextAction / attemptCounts / lastUpdate / builtItems
  / insights / nextSteps refreshed
- This session memo
