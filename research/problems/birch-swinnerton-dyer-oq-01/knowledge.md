# Problem: Finiteness of Sha(E/Q): formalize Kolyvagin rank-1 result

## Summary

**Status**: COMPLETED — `BirchSwinnertonDyerOQ01.lean` builds with 0 sorries, 8 axioms.

The formalization captures Kolyvagin's 1990 theorem: if the analytic rank of E/ℚ is at most 1,
then for every prime p, the p-primary Shafarevich-Tate group Ш(E/ℚ)[p^∞] is finite.

## Session 2026-04-03 (Session 1) - Initial formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. **Claimed the problem** and assessed existing infrastructure:
   - Parent file `BirchSwinnertonDyer.lean` (7423 lines, 19 axioms, 0 sorries) has
     `BSD_rank_zero_axiom` and `BSD_rank_one_axiom` encoding Kolyvagin's results as axioms
   - The `ShaFinite` definition in the parent is just `True` (placeholder)
   - No dedicated OQ01 file existed yet

2. **Identified and fixed two pre-existing bugs** in `BirchSwinnertonDyer.lean`:
   - Line 5634: Orphaned doc comment `/--...-/` with no following declaration → changed to `/-...-/`
   - Line 5706: `#check parity_conjecture` → `#check parity_conjecture_proved` (name was wrong)

3. **Created `BirchSwinnertonDyerOQ01.lean`** (297 lines, 8 theorems, 8 axioms, 0 sorries):
   - `ShaTorsionPrimary E p`: abstract structure for Ш(E/ℚ)[p^∞]
   - `pSelmerRank E p`: opaque ℕ encoding the p-Selmer rank
   - `HeegnerField E`, `HeegnerPoint E K`: Heegner hypothesis and point structures
   - 8 new axioms encoding: analytic rank/L-value connection, Heegner existence (2),
     Gross-Zagier height non-vanishing, Kolyvagin Euler system (2), Sha from Selmer (2)
   - Main theorem: `kolyvagin_sha_finiteness` — Ш[p^∞] finite when analyticRank ≤ 1
   - Combined result: `kolyvagin_complete` — BSD + Sha finiteness for rank ≤ 1
   - `bsd_rank_le_one` — BSD for rank ≤ 1 derived directly from parent axioms

4. **Build verified** via Docker: `Build completed successfully (3086 jobs)`

### Key Findings

- The main BSD file's `BSD_rank_zero_axiom` already gives `analyticRank E = 0`
  (second component of `∧`), so `analyticRank_zero_of_L_nonzero` is a provable theorem,
  not an axiom, in our file.
- Kolyvagin's rank-1 result requires 3 independent pieces: Heegner field existence,
  Gross-Zagier formula, and the Euler system Selmer bound.
- The "Selmer rank formula" (`pSelmerRank = algebraicRank + corank(Sha[p^∞])`) is
  the mathematical bridge from Selmer bounds to Sha finiteness.

### Files Modified

- `proofs/Proofs/BirchSwinnertonDyerOQ01.lean` — CREATED (main deliverable)
- `proofs/Proofs/BirchSwinnertonDyer.lean` — bug fixes only (2 changes)
- `src/data/research/problems/birch-swinnerton-dyer-oq-01.json` — knowledge updated
- `research/problems/birch-swinnerton-dyer-oq-01/knowledge.md` — CREATED

### Next Steps

- Gallery entry: create `src/data/proofs/birch-swinnerton-dyer-oq-01/` with meta.json
- The 8 axioms in OQ01 are all HARD (known mathematics) — could try Aristotle on them,
  but these require deep infrastructure (Galois cohomology, Néron-Tate heights)
- Future: when Mathlib adds Galois H¹ for elliptic curves, `ShaTorsionPrimary` could
  be made concrete rather than abstract
