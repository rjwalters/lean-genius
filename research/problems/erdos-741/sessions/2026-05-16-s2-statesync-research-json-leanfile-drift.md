## Session 2026-05-16 (Session 2 STATE-SYNC) — research-JSON + state.md + knowledge.md catchup post-batch-import (doc-only)

**Mode**: STATE-SYNC / DOCUMENTATION-ONLY
**Outcome**: progress (no Lean changes; no sorry/axiom delta; pure docs catchup)

### TL;DR

The research-tracking files for `erdos-741` were never updated after
the initial 2026-03-13 batch-import commit (`2ace1c84053`, which
landed all eight files at once in a squashed merge), even though the
underlying Lean file `proofs/Proofs/Erdos741Problem.lean` carries
~4 axiom-eliminations and ~27 proved structural theorems (visible
in pre-squash branch history `7c3df075dbe`, `c4e78e5f84a`, etc.).

This session closes the 12-item drift between the **research JSON**
(`src/data/research/problems/erdos-741.json`) and **current Lean
reality** at base SHA `d9c746dfe9a` / Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The companion gallery
`src/data/proofs/erdos-741/meta.json` is already in sync (its
`leanFile.{lineCount, theoremCount, axiomCount, sorries}` already
read 337/27/0/0) — **only the research-tracking JSON + state.md +
knowledge.md were behind**.

### Drift inventory (12 items)

| # | Field | Stale value | Current value |
|---|---|---|---|
| 1 | `phase` (top) | `OBSERVE` | `ORIENT` |
| 2 | `currentState.phase` | `NEW` | `ORIENT` |
| 3 | `currentState.since` | `2026-01-14T21:33:35.591Z` | `2026-05-16T08:54:09Z` |
| 4 | `currentState.iteration` | `1` | `2` |
| 5 | `currentState.focus` | `"Initial exploration of the problem."` | structural-infra summary |
| 6 | `currentState.nextAction` | `"Begin problem exploration."` | proof recipes for the 2 gap-fillers |
| 7 | `currentState.attemptCounts.{total, approachesTried}` | `0, 0` | `1, 1` |
| 8 | `knowledge.progressSummary` | "COMPLETE: 7→3 axioms…" | "COMPLETE: 7→0 axioms; full structural framework proved" |
| 9 | `knowledge.builtItems[…]` | 4 axiom-elim entries | 27 entries (one per theorem) |
| 10 | `knowledge.nextSteps[]` | empty | 4 concrete suggestions |
| 11 | `lastUpdate` | `2026-03-13T07:52:17.052Z` | `2026-05-16T08:54:09Z` |
| 12 | `leanFiles[0].{lineCount, theoremCount, axiomCount}` | `285, 26, 1` | `337, 27, 0` |

(state.md and knowledge.md additionally carry their own drift entries
mirroring items 2–6 and 11, plus the "(No research sessions yet)"
placeholder in knowledge.md is replaced with this session's log line.)

### Lean inventory at base `d9c746dfe9a`

```
file:  proofs/Proofs/Erdos741Problem.lean
lines: 337         (was 285 in JSON — drift +52)
defs:  8           (matches JSON)
thms:  27          (was 26 in JSON — drift +1; cofinite_density_one)
axiom: 0           (was 1 in JSON — drift -1; PR #16461 closed)
sorry: 0           (matches JSON)
```

Counted via:
```bash
grep -c "^theorem \|^lemma " proofs/Proofs/Erdos741Problem.lean   # 27
grep -c "^axiom " proofs/Proofs/Erdos741Problem.lean              # 0
grep -c "sorry\b" proofs/Proofs/Erdos741Problem.lean              # 0
grep -c "^def \|^noncomputable def " proofs/Proofs/Erdos741Problem.lean  # 8
wc -l proofs/Proofs/Erdos741Problem.lean                          # 337
```

### Structural theorem catalogue (27)

Grouped by section:

1. **Sumset algebra** (10): `sumset_comm`, `empty_sumset`,
   `sumset_empty_left`, `sumset_empty_right`, `sumset_mono`,
   `sumset_mono_left`, `zero_mem_sumset_self`, `double_mem_sumset`,
   `sumset_union_contains_left`, `sumset_union_contains_right`
2. **Partition properties** (3): `trivial_partition`,
   `complement_partition`, `partition_membership`
3. **Syndetic properties** (5): `nat_syndetic`, `empty_not_syndetic`,
   `syndetic_nonempty`, `syndetic_mono`, `syndetic_infinite`
4. **Density properties** (4): `density_empty`, `density_univ`,
   `density_mono`, `density_le_one`
5. **Cofinite density** (1): `cofinite_density_one` ← PR #16461 ✓
6. **Basis bridge** (2): `basis_infinite`,
   `basis_has_pos_density_sumset`
7. **Part 1 / Part 2 tension** (2): `part2_gives_non_syndetic`,
   `part2_contradicts_part1_for_basis`

The two main conjectures `ErdosProblem741_density` and
`ErdosProblem741_basis` remain `Prop` definitions (correctly: both
are OPEN per erdosproblems.com).

### Source-of-truth audit

| File | Status |
|---|---|
| `proofs/Proofs/Erdos741Problem.lean` | **CANONICAL** (337/27/8/0/0) |
| `src/data/proofs/erdos-741/meta.json` | already in sync (337/27/8/0/0) ✓ |
| `src/data/research/problems/erdos-741.json` | **STALE** (12-field drift) — closed here |
| `research/problems/erdos-741/state.md` | **STALE** (NEW/iter 1) — closed here |
| `research/problems/erdos-741/knowledge.md` | **STALE** (no sessions) — closed here |

### Next-action recipes (paste-ready sketches, NOT shipped this session)

Two natural gap-fillers that close the framework. Both are routine
limsup-arguments using infrastructure already in the file. Estimated
**~25–40 LOC** total. Mathlib pin (above) is stable.

#### A. `density_finite` (mentioned in JSON insights but missing in file)

```lean
/-- A finite set has zero upper density. -/
theorem density_finite {A : Set ℕ} (hA : A.Finite) : upperDensity A = 0 := by
  -- For finite A, |A ∩ Iic n| ≤ |A| (constant), so ratio → 0.
  apply le_antisymm _ (by
    have := density_mono (Set.empty_subset A); rw [density_empty] at this; exact this)
  unfold upperDensity
  apply Filter.limsup_le_of_le ⟨0, by
    filter_upwards with n; positivity⟩
  -- bound ratio by hA.toFinset.card / (n+1) → 0
  sorry
```

Strategy: bound `ncard (A ∩ Iic n) ≤ hA.toFinset.card =: K`, then
`K / (n+1) → 0` via the same `Tendsto.inv_tendsto_atTop`
infrastructure already used in `cofinite_density_one`.

#### B. `syndetic_has_pos_density` (commented gap at line 324)

```lean
/-- A syndetic set has positive upper density. -/
theorem syndetic_has_pos_density {S : Set ℕ} (h : IsSyndetic S) :
    HasPosDensity S := by
  obtain ⟨g, hg⟩ := h
  unfold HasPosDensity upperDensity
  -- Each window [k(g+1), (k+1)(g+1)) contains ≥ 1 elt of S, so
  -- |S ∩ Iic n| ≥ (n+1)/(g+1) - 1, hence ratio ≥ 1/(g+1) - O(1/n).
  -- limsup ≥ 1/(g+1) > 0.
  sorry
```

Strategy: window-counting plus the same `limsup ≥ liminf` chain used
in `cofinite_density_one`. Closes the commented-out lemma between
`basis_has_pos_density_sumset` and `part2_contradicts_part1_for_basis`.

#### C (longer-term) — Either Part 1 or Part 2

Both remain Erdős-OPEN. The Lean infra is now sufficient that a
genuine attack would need either:
- a constructive Sidon-style basis for Part 2 (Erdős's never-finished
  approach), or
- a density-Ramsey reduction for Part 1 (no known approach).

These are NOT next-session candidates — they are open research.

### Risk analysis

| Risk | Likelihood | Mitigation |
|---|---|---|
| Conflict with an open PR on this slug | very low | `gh pr list` confirms 0 open PRs touching erdos-741 |
| Mathlib pin drift before next ACT | low | Pin `2df2f015…` unchanged ≥9 d (see other slugs' bearer-recheck tables) |
| Re-attempting axiom elimination (already done) | none | Drift sync makes the "0 axioms" status visible to future agents |
| Build failure | none | doc-only PR, no Lean edits |

### Handoff

This S2 STATE-SYNC unblocks future research sessions on `erdos-741`
by ensuring the depth-first claim picker sees the true knowledge
state. A future S3 PREP/ACT can pick up Recipe A or B above with
no need to re-audit the file.

— researcher-1 @ 2026-05-16
