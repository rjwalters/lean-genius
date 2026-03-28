# Erdős #118 OQ-01: Partition Threshold of ω^{ω²}

**Problem**: Is the partition threshold of ω^{ω²} exactly 3 or 4?
**Status**: IN-PROGRESS (4 axioms, 0 sorries)

## Current State

- **File**: `proofs/Proofs/Erdos118Problem.lean` (~144 lines)
- **Axioms**: 4 (counter_partition_3, counter_not_partition_5, partitionThreshold, threshold_exact)
- **Proved**: ordPartition (was axiom, now def), partition_monotone_down (was axiom, now theorem)
- **Key theorem**: omega_omega2_threshold bounds threshold to {3, 4}

## Session 2026-03-28 (Session 1) - Define ordPartition, prove partition_monotone_down

**Mode**: FRESH (MODERATE knowledge, score 11)
**Outcome**: progress (6A→4A, 2 axioms eliminated)

### What I Did
- Converted `ordPartition` from axiom to concrete definition:
  - Red condition: ∃ φ : Ordinal → Ordinal, StrictMono φ ∧ maps [0,α) into itself ∧ all pairs red
  - Blue condition: ∃ ψ : Fin k → Ordinal, StrictMono ψ ∧ all < α ∧ all pairs blue
- Proved `partition_monotone_down`: given blue k-clique, restrict to j-element initial segment via Fin.castLE

### Key Findings
- `ordPartition` was an opaque axiom making everything downstream unprovable. Now it's a concrete Prop.
- `partition_monotone_down` follows cleanly: compose with `embed : Fin j → Fin k` that preserves `.val`
- `StrictMono embed` holds because Fin comparison is by `.val`, and embed preserves `.val`
- `partitionThreshold` and `threshold_exact` remain axioms (would need bounded set theory for proper definition)
- Counter-partition axioms (Schipperus, Larson) remain axioms (deep results, not in Mathlib)
- Docker not available — build verification needed

### Files Modified
- `proofs/Proofs/Erdos118Problem.lean` (121→144 lines, -2 axioms, +1 def, +1 theorem)
- `src/data/proofs/erdos-118/meta.json` (axiomCount: 6→4, lineCount: 120→144)
- `src/data/research/problems/erdos-118-oq-01.json` (knowledge updated)

### Next Steps
- Verify build when Docker available
- Consider defining partitionThreshold as noncomputable def with Nat.find
- The exact threshold value (3 vs 4) requires deep ordinal combinatorics beyond current scope
