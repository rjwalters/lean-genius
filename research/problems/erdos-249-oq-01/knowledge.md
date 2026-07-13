# Erdős #249 OQ-01: Tighter Bounds on Σ φ(n)/2^n

**Problem**: Prove tighter lower bounds on Σ φ(n)/2^n by computing more terms and using partial sum bounds.

**Lean File**: `proofs/Proofs/Erdos249OQ01.lean`
**Gallery**: `src/data/proofs/erdos-249-oq-01/`
**Status**: COMPLETED — 21 public theorems, 0 sorries, 0 axioms

## Final State

**Bounds proved**: 87/64 < Σ φ(n)/2^n < 351/256
- Width: 3/256 ≈ 0.012
- True value: ≈ 1.368 (inside the interval)
- Previous bounds: (5/4, 3/2) = (1.25, 1.5)

**Exclusions proved**:
- Not an integer (follows from bounds)
- Not a half-integer (3/2 is above the upper bound)
- Not a quarter-integer (interval width < 1/4, positioned away from multiples of 1/4)
- Not equal to 4/3 (since 87/64 > 4/3, as 261 > 256)

---

## Session 2026-04-24 (Session 1) — Tighter bounds + curation

**Mode**: FRESH (claimed by researcher-9)
**Outcome**: completed — extended bounds and fixed metadata

### What I Did
- Computed φ(n)/2^n for n = 7, 8, 9, 10: {3/64, 1/64, 3/256, 1/256}
- Proved partial_sum_11 (range 11, n=0..10) = 87/64 ≈ 1.359375
- Proved tight upper bound via tail splitting at n=11: comparison tail = 3/256
- Proved totientPowerSum_lt_351_256: sum < 351/256 ≈ 1.371
- Proved totientPowerSum_gt_87_64: sum > 87/64 ≈ 1.359
- Proved totientPowerSum_ne_four_thirds: sum ≠ 4/3 (since 87/64 > 4/3)
- Fixed meta.json: status "axiomatized" → "verified", badge "wip" → "original"
- Updated title, description, theorem counts, sections

### Key Findings
- Previous claim "≈1.3240" in overview was wrong; true value ≈1.368 based on partial sums
- native_decide works for Nat.totient of small composites (8, 9, 10)
- Tail comparison at n=11: 2 − (509/256) = 3/256, a very tight bound
- The lower bound 87/64 alone rules out 4/3 (no extra argument needed)

### Files Modified
- `proofs/Proofs/Erdos249OQ01.lean` — added 8 new public theorems + 1 private
- `src/data/proofs/erdos-249-oq-01/meta.json` — fixed status/badge, updated counts
- `src/data/research/problems/erdos-249-oq-01.json` — updated knowledge
- `research/problems/erdos-249-oq-01/knowledge.md` — created this file

### Next Steps
- Prove irrationality (the main Erdős #249 conjecture) — hard open problem
- Further narrowing achievable with more terms (but diminishing returns)
