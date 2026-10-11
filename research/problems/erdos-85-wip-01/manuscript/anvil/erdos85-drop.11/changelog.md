# Changelog: erdos85-drop.10 to erdos85-drop.11

Corrections pass (iteration 11 of `max_iterations: 8`, `operator_override: true`, same provenance as v10:
`erdos85-drop.9.operator/`, agent-transcribed). Direct edit by claude; inputs `erdos85-drop.10.review/` (37/44, advance,
ready; 3 major, 9 minor) and `erdos85-drop.10.audit/` (BLOCK: 2 critical, 2 major, 6 minor, 7 nits), plus codex room
review (53263-53279). No new claims.

## Critical (audit)
- C1 "Never call Result A a theorem" (BRIEF hard rule): abstract now "Lean thus derives the upper side from two explicit
  unsatisfiability hypotheses"; "What is new" "Lean derives the upper side from the two families of checked formulas alone";
  Result A "is derived in Lean by <capstone> from exactly two hypotheses". (Also review M3.)
- C2 unsourced "about \$215": dollar clause deleted (also R-SIMPLE's one-dollar-sentence rule; review m3).

## Major
- M1 (review M1, audit M1/m6): "What is not claimed", Table 2 (H7 t>=1 row) and the closing list state that the capstone
  cannot be recompiled from the public repository alone: 13 certificate modules include packed files (about 2.57 GB) from
  unpublished storage (refs `CAPSTONE_ABSOLUTE_PATH_AUDIT_20261011.json`, codex: exactly 13 absolute paths in the 893-source closure).
- M2: superseded-status banner on `STRATA_AND_SMALL_ORDERS_20260928.md` (a9ba1fc43ce); `\repobase` re-pinned to
  release-assembly f6daa149b807972abe1c3e669abce092a863c2bd, which contains it (all 64 link targets verified to exist).

## Minor and nits
- "refutes one case outright, splits the rest into four strata" (m1); depth 3 stated, depth is a theorem parameter (m2);
  "emitters" not "compiled emitters" (m4/audit m3); "refutations of all 377,804 formulas … one leaf through a 256-way split"
  (m5/audit m4); H7 reduction axioms 3 + 91 with `stratum.log` linked, split lemma's axiom level left unasserted (m6/audit m5);
  version-history voice removed (m7/N3); H7 logistics paragraph trimmed (m8); superseded availability item relabelled (m9/N5);
  "233 timed-out attempts" (N1); CaDiCaL cited at first H7 mention (N2); H7 shares the cake_lpr commit, separately pinned
  binary (N4); H5 prints 61 = 3 + 40 search parts + 18 cover/cardinality checks (N6, codex confirmed from the raw log).

## Build and gates
- 4 xelatex passes + aux fixpoint; 0 errors, 0 undefined, 0 overfull, 6 underfull; 14 pages, references from p. 12 (main text 11).
- Abstract 1,704 rendered characters (< 1,900). scope_lint PASS (39 numbers, 46 Lean names; --proofs = release assembly).
