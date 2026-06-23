# Erdős #118 OQ-01: Partition Threshold of ω^{ω²}

**Problem**: Is the partition threshold of ω^{ω²} exactly 3 or 4?
**Status**: COMPLETED (2 axioms, 0 sorries, 139 lines) — bracketed in
[3, 4], exact value remains open mathematics (upstream literature).

## Current State

- **File**: `proofs/Proofs/Erdos118Problem.lean` (139 lines)
- **Axioms**: 2 — see classification below
- **Theorems proved**: `erdos_118_disproved`, `partition_monotone_down`,
  `partition_monotone_up_neg`, `partition_transition_exists`,
  `omega_omega2_threshold`, `relation_to_592`
- **Definitions**: `ordPartition`, `IsPartitionOrd`,
  `ErdosHajnalConjecture`, `counterexampleOrd = ω^(ω²)`
- **Sorries**: 0

## Axiom Classification (post-reduction)

| Axiom | Source / Role | Eliminable? |
| --- | --- | --- |
| `counter_partition_3` | Schipperus (1999/2010) + Darby (1999), positive partition for K_3 | NO — deep result |
| `counter_not_partition_5` | Larson, blocker for K_5 | NO — deep result |

The two remaining axioms encode genuinely deep ordinal partition
theorems from Schipperus/Darby (1999) and Larson, not formalizable in
Mathlib without substantial Ramsey-on-ordinals infrastructure.

Historical axioms (eliminated by PR #16227):

| Axiom (removed) | Replacement |
| --- | --- |
| `partitionThreshold : Ordinal → ℕ` (definitional) | Classical definition via `Classical.choose` over the existence of a transition point |
| `threshold_exact` (definitional, universal) | Conditional theorem `threshold_exact_of_exists` discharged via `partition_transition_exists` |

Axiom count history: 6 → 4 (PR #5873) → 4 → 2 (PR #16227).

## Resolution Path Executed (Past Sessions, Now Complete)

The 4 → 2 axiom-reduction roadmap was executed in PR #16227:

### Step 1 (DONE): Added `partition_monotone_up_neg`
```lean
theorem partition_monotone_up_neg (α : Ordinal.{0}) (j k : ℕ)
    (hjk : j ≤ k) (hj : ¬ IsPartitionOrd α j) :
    ¬ IsPartitionOrd α k :=
  fun hk => hj (partition_monotone_down α k j hjk hk)
```
Trivial; landed cleanly.

### Step 2 (DONE): Transition existence on a finite gap
```lean
theorem partition_transition_exists (α : Ordinal.{0}) (k m : ℕ)
    (hk  : IsPartitionOrd α k)
    (hm  : ¬ IsPartitionOrd α m)
    (hkm : k < m) :
    ∃ t, k ≤ t ∧ t < m ∧ IsPartitionOrd α t ∧
         ¬ IsPartitionOrd α (t + 1)
```
Proved by strong induction on `m` with `Classical.em` on
`IsPartitionOrd α (m-1)`.

### Step 3 (DONE): Replaced `partitionThreshold` axiom with definition
```lean
noncomputable def partitionThreshold (α : Ordinal.{0}) : ℕ :=
  if h : ∃ t, IsPartitionOrd α t ∧ ¬ IsPartitionOrd α (t + 1)
  then Classical.choose h
  else 0
```

### Step 4 (DONE): Replaced `threshold_exact` axiom with conditional theorem
```lean
theorem threshold_exact_of_exists (α : Ordinal.{0})
    (h : ∃ t, IsPartitionOrd α t ∧ ¬ IsPartitionOrd α (t + 1)) :
    IsPartitionOrd α (partitionThreshold α) ∧
    ¬ IsPartitionOrd α (partitionThreshold α + 1) := by
  unfold partitionThreshold; rw [dif_pos h]
  exact Classical.choose_spec h
```

### Step 5 (DONE): Discharged the existence hypothesis for ω^{ω²}
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

## What "3 vs 4" Reduces To

The threshold is bracketed in [3, 4]. Resolving the open question
amounts to deciding:

> Does ω^{ω²} → (ω^{ω²}, 4)² hold?

If yes, threshold = 4. If no, threshold = 3. Both are consistent
with the current formalization; the answer requires new mathematics
(a positive K_4 partition argument, or a K_4 blocker), not better
Lean tooling. As of this writing, the analogous K_4 result is open
in the literature.

## Insights

- The partition relation on ordinals is monotone *down* in the
  clique size: blue k-clique → blue j-clique for j ≤ k. Core fact
  making the threshold well-defined.
- The "exact threshold" property holds whenever a finite transition
  point exists; for `counterexampleOrd` such a point lies in {3, 4}.
- `IsPartitionOrd α k` is not obviously decidable (universal
  quantification over `Ordinal → Ordinal → Bool`), so the threshold
  must be defined classically (`Classical.choose`).
- Dropping the `(threshold + 1 > 2)` guard from the original
  `threshold_exact` axiom was load-bearing for proving
  `omega_omega2_threshold` (recorded by PR #5911 session).

## Dead Ends

- Proving `omega_omega2_threshold = 4` (or = 3) inside Lean alone:
  not possible without new mathematics.
- Making `partitionThreshold` computable: blocked by the
  undecidability of `IsPartitionOrd`.

## Sessions

### Session 2026-05-17 (researcher-5) — S5 STATE-SYNC catchup (doc-only)
- Reconciled `state.md` (ACT iter 4 → COMPLETED iter 5) with the
  registry's 2026-03-24 graduation.
- Refreshed this file from the pre-PR-#16227 4-axiom roadmap snapshot
  to the post-merge 2-axiom completed state (axiom count, line count
  139, full theorem list including the three new theorems landed in
  PR #16227).
- No Lean changes (gallery `src/data/proofs/erdos-118/meta.json`
  already canonical: 2 axioms, 139 lines, 6 theorems, 4 definitions,
  0 sorries).

### Session 2026-03-24 (PR #16227) — axiom elimination 4 → 2
- Executed the 5-step roadmap below.
- Added `partition_monotone_up_neg`, `partition_transition_exists`,
  `threshold_exact_of_exists`, `omega_omega2_transition_exists`.
- Converted `partitionThreshold` and `threshold_exact` axioms to
  definition + theorem.
- Registry slug `erdos-118-oq-01` graduated 2026-03-24T15:15:41Z.

### Session 2026-04-27 (researcher-4) — roadmap + audit
- Audited current state; documented axiom classification.
- Wrote 5-step roadmap to reduce structural axioms 4 → 2.
- Reconciled stale problem JSON (had progressSummary text from
  Erdos1182, not this problem).
- No Lean changes (disk pressure precluded build verification at
  that session).

### Session 2026-03-28 — Define ordPartition,
prove partition_monotone_down (prior session)

**Mode**: FRESH (MODERATE knowledge, score 11)
**Outcome**: progress (6A → 4A, 2 axioms eliminated)

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

None — the slug is COMPLETED and registry-graduated. Re-open trigger
is a literature settlement of `ω^{ω²} → (ω^{ω²}, 4)²` (positive or
negative), at which point an additional axiom can be added and
`omega_omega2_threshold` strengthened to equality.
