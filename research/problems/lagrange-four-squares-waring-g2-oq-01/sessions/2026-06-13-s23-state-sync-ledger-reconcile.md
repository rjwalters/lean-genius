# S23 STATE-SYNC 2026-06-13 — ledger + meta reconciliation post-S22

**Date**: 2026-06-13
**Researcher**: researcher-2
**Phase**: STATE-SYNC (doc/meta-only)
**Base HEAD**: `origin/main` @ `2618a17f8f4`.

## Why this STATE-SYNC

S22 (researcher-4, earlier today, PR #23088) caught the slug header up to
the fact that S7 ACT (`g(7) ≥ 143`, PR #22968) had shipped, advancing the
header to "coverage now `k ∈ {3,4,5,6,7}`". But S22 was deliberately
minimal: it updated only the header + prepended its narrative + rewrote
the next-iteration picker. It left **two trailing ledger tables stale**:

1. *Iteration history* table — last row was **S19 ACT marked `OPEN`**
   (it merged as #21124), with no S21/S7/S22 rows at all.
2. *Future Iterations* table — **S5 / S6b / S7 rows still read `ACT TODO`**,
   directly contradicting the header.

The gallery `meta.json` `meta.additionalFiles` companion list was also two
files behind (listed G4/G5 only; G6 + G7 are registered on main).

A reader scrolling past the header hit tables claiming three shipped,
build-merged lower bounds were still unstarted. This reconciles them.

## What I verified (all via `git show origin/main:` — build-free)

| File | LOC | Real sorry | `^axiom ` | Registered in Proofs.lean | ACT PR |
|---|---:|---:|---:|:--:|---|
| `…OQ01CountingG5.lean` (g5 ≥ 37) | 150 | 0 | 0 | ✅ | #21124 (S19) |
| `…OQ01CountingG6.lean` (g6 ≥ 73) | 158 | 0 | 0 | ✅ | #22751 (S21) |
| `…OQ01CountingG7.lean` (g7 ≥ 143) | 139 | 0 | 0 | ✅ | #22968 (S7) |

- Each file's only `sorry` grep hit is the docstring phrase
  "a sorry-free, axiom-free" — confirmed by reading the matched line.
- Main theorems: `g5_lower_counting : ¬ IsSumOfFifthPowers 36 223`,
  `g6_lower_counting : ¬ IsSumOfSixthPowers 72 703`,
  `g7_lower_counting : ¬ IsSumOfSeventhPowers 142 2175`.
- ACT PR numbers cross-checked via `gh pr list --search`.

## Changes (doc/meta-only — 0 Lean edits, 0 build, 0 axiom/sorry delta)

- `src/data/proofs/lagrange-four-squares-waring-g2/meta.json`:
  appended `Proofs/LagrangeFourSquaresWaringG2OQ01CountingG6.lean` and
  `…CountingG7.lean` to `meta.additionalFiles`.
- `state.md` header: Iteration 22 → 23; prepended this S23 section.
- `state.md` *Iteration history* table: S19 ACT `OPEN` → `MERGED` #21124;
  appended S21 ACT (#22751), S7 ACT (#22968), S22 STATE-SYNC (#23088),
  and this S23 row; refreshed the "Total artifacts" summary line.
- `state.md` *Future Iterations* table: S5 / S6b / S7 `ACT TODO` →
  `ACT MERGED` with PR refs. **S4** (upper-bound axioms) and **S6**
  (correctness chain) left as genuine `ACT TODO` — they have not shipped.

## Caveat carried forward (unchanged)

G7 (PR #22968) merged during the host Docker outage and is therefore
**build-unverified**. The S22 picker's item #1 — targeted-build
`…CountingG7` once Docker recovers to confirm 7743-job parity — remains
open. This STATE-SYNC introduces no Lean changes and does not affect that.

## Next picker (unchanged from S22, abbreviated)

1. Build-verify `…CountingG7` once Docker is back (close the G7 caveat).
2. S8 ACT `g(8) ≥ 279` (counting+omega; tractability caveat — larger case-load).
3. Parametric refactor: five k-instances now justify collapsing to one template.
4. Mechanic poke for dormant `fix/mechanic-lagrange-v426` (unblocks S4 / S6).
