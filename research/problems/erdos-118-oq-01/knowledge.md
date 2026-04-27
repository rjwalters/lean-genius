# Erdős #118 OQ-01: Partition Threshold of ω^{ω²}

**Problem**: Is the partition threshold of ω^{ω²} exactly 3 or 4?
**Status**: IN-PROGRESS (4 axioms, 0 sorries) — bracketed in [3, 4],
exact value remains open mathematics.

## Current State

- **File**: `proofs/Proofs/Erdos118Problem.lean` (143 lines)
- **Axioms**: 4 — see classification below
- **Theorems proved**: `erdos_118_disproved`,
  `partition_monotone_down`, `omega_omega2_threshold`,
  `relation_to_592`
- **Definitions**: `ordPartition`, `IsPartitionOrd`,
  `ErdosHajnalConjecture`, `counterexampleOrd = ω^(ω²)`

## Axiom Classification

| Axiom | Source / Role | Eliminable? |
| --- | --- | --- |
| `counter_partition_3` | Schipperus (1999/2010), positive partition for K_3 | NO — deep result |
| `counter_not_partition_5` | Larson, blocker for K_5 | NO — deep result |
| `partitionThreshold : Ordinal → ℕ` | Definitional | YES — replace with classical definition |
| `threshold_exact` | Definitional (universal) | YES (conditionally) — provable when transition exists |

The two "counter" axioms encode genuinely deep mathematics not
formalizable in Mathlib without substantial ordinal Ramsey theory
infrastructure.

## Roadmap to Reduce Structural Axioms (4 → 2)

### Step 1: Add `partition_monotone_up_neg`
```lean
theorem partition_monotone_up_neg (α : Ordinal.{0}) (j k : ℕ)
    (hjk : j ≤ k) (hj : ¬ IsPartitionOrd α j) :
    ¬ IsPartitionOrd α k :=
  fun hk => hj (partition_monotone_down α k j hjk hk)
```
Trivial; safe.

### Step 2: Prove transition existence on a finite gap
```lean
theorem partition_transition_exists (α : Ordinal.{0}) (k m : ℕ)
    (hk  : IsPartitionOrd α k)
    (hm  : ¬ IsPartitionOrd α m)
    (hkm : k < m) :
    ∃ t, k ≤ t ∧ t < m ∧ IsPartitionOrd α t ∧
         ¬ IsPartitionOrd α (t + 1) := by
  -- strong induction on `m`; split on Classical.em
  -- (IsPartitionOrd α (m-1))
  ...
```
~20 lines.

### Step 3: Replace `partitionThreshold` axiom with definition
```lean
noncomputable def partitionThreshold (α : Ordinal.{0}) : ℕ :=
  if h : ∃ t, IsPartitionOrd α t ∧ ¬ IsPartitionOrd α (t + 1)
  then Classical.choose h
  else 0
```

### Step 4: Replace `threshold_exact` axiom with conditional theorem
```lean
theorem threshold_exact_of_exists (α : Ordinal.{0})
    (h : ∃ t, IsPartitionOrd α t ∧ ¬ IsPartitionOrd α (t + 1)) :
    IsPartitionOrd α (partitionThreshold α) ∧
    ¬ IsPartitionOrd α (partitionThreshold α + 1) := by
  unfold partitionThreshold; rw [dif_pos h]
  exact Classical.choose_spec h
```

### Step 5: Discharge the existence hypothesis for ω^{ω²}
Combine Steps 1–2 with `counter_partition_3` and
`counter_not_partition_5`:
```lean
theorem omega_omega2_transition_exists :
    ∃ t, IsPartitionOrd counterexampleOrd t ∧
         ¬ IsPartitionOrd counterexampleOrd (t + 1) := by
  obtain ⟨t, _, _, ht, ht'⟩ :=
    partition_transition_exists counterexampleOrd 3 5
      counter_partition_3 counter_not_partition_5 (by norm_num)
  exact ⟨t, ht, ht'⟩
```

After this refactor the file has **2 axioms** (the deep
mathematical results), down from 4.

## Why Not Done This Session

Disk was 783 MB free / 94 % capacity at session start, below the
prior-incident 1 GB threshold for safe Docker builds. The proof
strategy above is sound but I cannot verify Lean syntax without a
build, and broken proofs propagating to master would corrupt the
gallery. Recording the roadmap is the safer contribution.

## What "3 vs 4" Reduces To

The threshold is bracketed in [3, 4]. Resolving the open question
amounts to deciding:

> Does ω^{ω²} → (ω^{ω²}, 4)² hold?

If yes, threshold = 4. If no, threshold = 3. Both are consistent
with the current formalization; the answer requires new mathematics
(a positive K_4 partition argument, or a K_4 blocker), not better
Lean tooling.

## Insights

- The partition relation on ordinals is monotone *down* in the
  clique size: blue k-clique → blue j-clique for j ≤ k. Core fact
  making the threshold well-defined.
- The "exact threshold" property holds whenever a finite transition
  point exists; for `counterexampleOrd` such a point lies in {3, 4}.
- `IsPartitionOrd α k` is not obviously decidable (universal
  quantification over `Ordinal → Ordinal → Bool`), so the threshold
  must be defined classically.
- Dropping the `(threshold + 1 > 2)` guard from the original
  `threshold_exact` axiom was load-bearing for proving
  `omega_omega2_threshold` (recorded by prior session).

## Dead Ends

- Proving `omega_omega2_threshold = 4` (or = 3) inside Lean alone:
  not possible without new mathematics.
- Making `partitionThreshold` computable: blocked by the
  undecidability of `IsPartitionOrd`.

## Sessions

### Session 2026-04-27 (researcher-4) — roadmap + audit
- Audited current state; documented axiom classification.
- Wrote 5-step roadmap to reduce structural axioms 4 → 2.
- Reconciled stale problem JSON (had progressSummary text from
  Erdos1182, not this problem).
- No Lean changes (disk pressure precluded build verification).

### Session 2026-03-28 — Define ordPartition,
prove partition_monotone_down (prior session)

**Mode**: FRESH (MODERATE knowledge, score 11)
**Outcome**: progress (6A→4A, 2 axioms eliminated)

#### What was done
- Converted `ordPartition` from axiom to concrete definition.
- Proved `partition_monotone_down` from the definition by
  restricting a blue k-clique to a j-element initial segment via
  `Fin.castLE`.

#### Key Findings
- `ordPartition` was an opaque axiom blocking everything
  downstream — making it concrete unlocked further proofs.
- `partition_monotone_down` follows cleanly from the embedding
  `Fin j → Fin k`.
- `StrictMono` of the embedding holds because Fin comparison is by
  `.val`, and the embedding preserves `.val`.
- Counter-partition axioms (Schipperus, Larson) are deep; not in
  Mathlib.

#### Files Modified
- `proofs/Proofs/Erdos118Problem.lean` (121→144 lines, −2 axioms,
  +1 def, +1 theorem)
- `src/data/proofs/erdos-118/meta.json` (axiomCount: 6→4)

## Next Action

When Docker is available and disk has ≥ 5 GB free, execute
Steps 1–5 above to drop the axiom count from 4 to 2.
