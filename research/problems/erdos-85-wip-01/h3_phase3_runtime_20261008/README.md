# H3 phase-three runtime helpers

The first production runtime split reduced the existing bucket-zero test
from 143.89 to 31.36 seconds. This follow-up moves four more executable
declarations verbatim into the Std-only runtime: `cands3`, `gate3`, `pick3`
and `addMany`. The recursive phase-three search and its Mathlib combination
enumeration stay in the Engine. Search order, guards and proof bodies are
unchanged.

`MOVE.json` and `verify_move.py` check all 49 moved declarations against the
original unsplit source at `2f41a16de17`, and verify that all remaining
non-comment source tokens match. The preceding 45-declaration stage and its
evidence remain under `../h3_runtime_split_20261008/`; its current-source
checker is tied to that historical stage.

This change requires a fresh Runtime/Engine/Bridge/Split build and a new
bounded plugin check of the existing bucket `triplePart 384 0 = true` before
any timing or validation result is credited. No other bucket is run and no
whole-cell exclusion is claimed.
