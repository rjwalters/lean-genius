# bounded-prime-gaps-oq-03-oq-01-oq-01

## Provenance

Auto-seeded follow-up slug (registry `started` 2026-06-16T04:40Z, phase
OBSERVE) of the parent `bounded-prime-gaps-oq-03-oq-01`
(`proofs/Proofs/BoundedPrimeGapsOQ03OQ01.lean`: "Improving the 246 Bound —
k-Tuple Size and Gap Bounds"). The registry carried **no materialized
statement** for this slug. This OBSERVE pass (researcher-1, S1, 2026-06-16)
interprets it as the next un-done rung of the parent's minimal-admissible-
diameter series and states it concretely below.

## Interpreted statement — D(5) = 12

Prove, **from scratch** (no new axioms), that the minimal diameter of an
admissible 5-tuple is exactly 12:

```
minAdmissibleDiameter 5 = 12
```

where `minAdmissibleDiameter k := sInf {d | ∃ H, H.card = k ∧ IsAdmissible H ∧
fsDiameter H = d}` (parent file, line 50) and `IsAdmissible`/`fsDiameter` are
from `BoundedPrimeGaps.lean` / the parent.

This is the natural successor in the materialized series:
- `minAdmissibleDiameter_2 = 2` — PROVED (parent, line 173; witness `{0,2}`).
- `minAdmissibleDiameter_3 = 6` — PROVED (parent, line 188; witness `{0,2,6}`).
- D(4) = 8 — sibling slug `…-oq-03-oq-01-oq-04` ("Prove D(4)=8 from Scratch");
  upper-bound witness `admissible_quadruple_0_2_6_8` already in parent (line 165).
- **D(5) = 12 — this slug.**

D(5)=12 is the k=5 entry of OEIS **A008407** (minimal diameter of an admissible
k-tuple): `0, 2, 6, 8, 12, 16, 20, 26, 30, …`.

## Why it is in scope (NOT the open Maynard–Tao barrier)

The parent's headline barrier ("improving below 246 needs a narrower admissible
50-tuple — impossible by Engelsma — or a new sieve") is genuinely open/blocked.
**This sub-problem is different**: D(5)=12 is a finite combinatorial fact,
decidable by exhaustion, exactly like the already-proved D(2), D(3) and the
sibling D(4). It is build-gated, not mathematics-gated.

## Proof plan

**Upper bound `D(5) ≤ 12`** (easy): exhibit the admissible witness
`{0, 2, 6, 8, 12}` of diameter 12.
- Admissibility check (no prime covers all residues):
  - p=2: residues `{0,0,0,0,0} = {0}` — misses 1. ✓
  - p=3: `{0,2,0,2,0} = {0,2}` — misses 1. ✓
  - p=5: `{0,2,1,3,2} = {0,1,2,3}` — misses 4. ✓
  - p≥7: only 5 elements, cannot cover ≥7 classes. ✓
  - So only p ∈ {2,3,5} need checking — a `decide`/`native_decide` over the
    `IsAdmissible` predicate restricted to those primes (mirror the parent's
    `admissible_quadruple_0_2_6_8` proof shape).
- Then `minAdmissibleDiameter 5 ≤ 12` via `Nat.sInf_le` with this witness, as in
  `minAdmissibleDiameter_3`'s upper-bound half.

**Lower bound `D(5) ≥ 12`** (the real content): no admissible 5-tuple has
diameter ≤ 11. Equivalently every 5-subset of an interval of 12 consecutive
integers `{0,…,11}` (WLOG min = 0 by translation-invariance of `IsAdmissible`)
is inadmissible.
- Translation-invariance: `IsAdmissible (H + c) ↔ IsAdmissible H` (needed to fix
  min = 0; check whether the parent/`BoundedPrimeGaps.lean` already provides a
  shift lemma — if not it is ~10 LOC and reusable for D(k) generally).
- Finite check: enumerate the `C(11,4) = 330` 5-subsets of `{0,…,11}` containing
  0, and for each verify it is covered mod 2 or mod 3 (the small primes that can
  cover a 5-set in width ≤ 11). This is a `native_decide` over a
  `Finset.filter`/`Decidable` reformulation — the same engine the parent uses
  for the lower-bound halves of D(2), D(3) and (presumably) the D(4) sibling.
- Assemble `12 ≤ minAdmissibleDiameter 5` via `le_csInf` (set is nonempty by the
  witness; every member ≥ 12 by the finite check).

## Bearer audit (OBSERVE, no build)

- `IsAdmissible` (`BoundedPrimeGaps.lean:59`), `IsAdmissible` monotone/subset
  (`admissible_subset`, line 79) — present.
- `fsDiameter`, `minAdmissibleDiameter` (parent lines 44, 50) — present.
- Witness-style admissibility proofs `admissible_twin`, `admissible_triple_0_2_6`,
  `admissible_quadruple_0_2_6_8` (parent 107/127/165) — present, copy their shape.
- `Nat.sInf_le`, `le_csInf`, `Nat.sInf_eq` — Mathlib, standard.
- **Gap to confirm under build:** a translation/shift lemma for `IsAdmissible`
  (for the WLOG min = 0 step). Not located in a no-build grep; budget ~10 LOC.

## Status

OBSERVE complete. Discharge is **build-pending** — Docker (`docker run` hangs,
exit 124, git-128 Mathlib re-clone) and Aristotle MCP (`prove` → 404) are both
in blackout this session (2026-06-16), so no `.lean` proof can be verified. A
draft skeleton is parked at `D5-draft.lean` in this directory (NOT registered /
NOT in `Proofs.lean` — zero build-gate risk). Next ACT on a Docker-up worktree:
build the draft (the two `native_decide` checks are the load-bearing steps),
then transcribe into a new registered `BoundedPrimeGapsOQ03OQ01OQ01.lean` or
fold into the parent.
