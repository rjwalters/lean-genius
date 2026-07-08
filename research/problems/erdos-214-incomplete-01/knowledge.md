# Knowledge: erdos-214-incomplete-01

## Research Notes

### 2026-07-08 (researcher-1) — AXIOM ELIMINATION 2→1

The sorry originally described in `problem.md` (`unit_square_exists_in_set`,
appealing to "Juhász's stronger theorem") no longer exists — it was resolved in
#31128 as the fully-proved theorem `unit_square_from_stronger :
JuhaszStrongerTheorem → Erdos214Statement`. So the problem was **phantom-complete**
(0 real sorries across all three Erdos214 files).

Genuine progress was still available on the axiom side. `Erdos214Problem.lean`
carried **two** axioms:
- `juhasz_1979 : Erdos214Statement` (the original Problem #214 statement)
- `juhasz_stronger : JuhaszStrongerTheorem` (the deeper 4-point result)

`juhasz_1979` is **redundant**: `unit_square_from_stronger juhasz_stronger`
already produces a term of type `Erdos214Statement`. Replaced the axiom with a
derived theorem:

```lean
theorem juhasz_1979 : Erdos214Statement := unit_square_from_stronger juhasz_stronger
```

Result: **axiom count 2 → 1**. The file now rests on the single deep Juhász
4-point axiom `juhasz_stronger`; everything else (the unit-square statement, the
graph characterization, the summary) is derived. Docker build clean (2364 jobs).

## Known Facts

- Lean file: `proofs/Proofs/Erdos214Problem.lean` (237 lines, 1 axiom, 0 sorries)
- `juhasz_stronger` is the sole assumption — a deep incidence-geometry result
  (Juhász 1979) not present in Mathlib; not further reducible here.

## Approaches Tried

- Axiom-dependency analysis: identified `juhasz_1979` as derivable from
  `juhasz_stronger` via the already-proved reduction. ✓ Eliminated.
