## Session 2026-05-16 (Session 3 STATE-SYNC) — research-JSON catchup post-S2 (doc-only)

**Mode**: STATE-SYNC / DOCUMENTATION-ONLY
**Outcome**: progress (no Lean changes; no sorry/axiom delta; pure docs catchup)

### TL;DR

The research-tracking JSON `src/data/research/problems/unit-distance-independence-oq-02.json`
was never updated after S2 (researcher-1, 2026-04-29) reduced
`proofs/Proofs/UnitDistanceHN7.lean` from 3 sorries to 1, even though
`state.md` and `knowledge.md` correctly reflect that work. This session
closes the resulting **10-item drift** between the research JSON and
the rest of the source-of-truth tree at base `d9c746dfe9a` /
Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

In addition, the JSON's `leanFiles` array was missing **two** files
actually under active work — `UnitDistanceHN7.lean` and
`UnitDistanceHN7Aristotle.lean` — tracking only the parent
`UnitDistanceIndependence.lean` (which is essentially passive; the
hadwiger_nelson_upper_bound axiom there is what HN7.lean aims to
eliminate).

### Drift inventory (10 items)

| # | Field | Stale value | Current value |
|---|---|---|---|
| 1 | `currentState.since` | `2026-04-05T21:40:00Z` | `2026-04-29T03:43Z` (state.md value) |
| 2 | `currentState.iteration` | `1` | `2` |
| 3 | `currentState.focus` | iter-1 "Created … 3 geometric sorries" | iter-2 "Reduced 3→1 sorries; `covering_radius` remains" |
| 4 | `currentState.nextAction` | iter-1 lemma list (mostly done) | iter-2 "Tackle `covering_radius` via cube-norm inequality" |
| 5 | `knowledge.progressSummary` | pre-iter-1 BUG FIX summary | iter-2 catch-up (3→1 sorry reduction summary) |
| 6 | `knowledge.builtItems[…]` | 3 iter-1 entries | 6 entries (+`hexCenter_dist_sq`, +inline modular step in `same_color_far`, +companion-file delegate updates) |
| 7 | `knowledge.insights[…]` | 10 entries (correct as of iter 0–1) | +2 entries (iter-2 proof-pattern insights from S2's `nlinarith` + `omega` discharges) |
| 8 | `knowledge.nextSteps[]` | 3 stale iter-1 next steps (2 done) | covering_radius cube-norm inequality sketch (from knowledge.md) |
| 9 | `lastUpdate` | `2026-04-05T21:40:00Z` | `2026-05-16T08:56:13Z` |
| 10 | `leanFiles[…]` | only parent `UnitDistanceIndependence.lean` tracked (lineCount 949, stale by -1) | +HN7.lean +HN7Aristotle.lean, parent lineCount fixed 949→948 |

### Lean inventory at base `d9c746dfe9a`

```
file:  proofs/Proofs/UnitDistanceIndependence.lean   948  65  11  2  0   (was 949 in JSON — -1 drift)
file:  proofs/Proofs/UnitDistanceHN7.lean            287   8   6  0  1   (NOT tracked in JSON)
file:  proofs/Proofs/UnitDistanceHN7Aristotle.lean    78   3   0  0  1   (NOT tracked in JSON)
                                                  lines thm def axm sor
```

Counted via:
```bash
for f in proofs/Proofs/UnitDistance*.lean; do
  echo "$f $(wc -l < $f) $(grep -c '^theorem \|^lemma ' $f) $(grep -c '^def \|^noncomputable def \|^private def ' $f) $(grep -c '^axiom ' $f) $(grep -c 'sorry\b' $f)"
done
```

(`HN7Aristotle.lean`'s `grep -c "sorry\b"` returns 2 because one is in
a comment header on line 6; only line 76 is a real proof obligation.
Hence reported `sorryCount = 1` below.)

### S2 progress (already reflected in state.md / knowledge.md)

From state.md `## Resolved This Session` and knowledge.md
`### Session 2026-04-29 progress (researcher-1)`:

1. **`hexCenter_dist_sq`** (UnitDistanceHN7.lean:123) — algebraic
   distance formula via `EuclideanSpace.dist_sq_eq` + `PiLp.toLp_apply`
   + `Real.mul_self_sqrt` + `nlinarith`.
2. **Inline modular step in `same_color_far`** (HN7.lean:180) —
   extracting `3·Δa + Δb ≡ 0 (mod 7)` via `simp only [hexColor,
   Fin.mk.injEq]` + `omega`.
3. **Companion delegate updates** (HN7Aristotle.lean):
   - `hexCenter_dist_sq_ari` delegates to the main lemma.
   - `hexColor_eq_implies_mod_ari` proved by parallel `omega`.

After S2: HN7.lean carries **1 remaining sorry** (`covering_radius`,
line 113–118). HN7Aristotle.lean carries **1 remaining sorry**
(`covering_radius_ari`, line 76 — same obligation).

### Remaining obligation: `covering_radius` (carried over from S2)

This sync re-states the knowledge.md sketch for the next session's
reference. Two natural decompositions, both lifting cleanly to a
~80–120 LOC proof:

#### Path A — cube-norm direct (preferred)

```lean
/-- The cube-coordinate Voronoi rounding produces (a, b) with
    Q(q - a, r - b) := (q - a)^2 + (q - a)(r - b) + (r - b)^2 ≤ 1/3. -/
private lemma hexCoord_cube_bound (p : Plane) :
    let (a, b) := hexCoord p
    ((axialQ p) - a) ^ 2 +
    ((axialQ p) - a) * ((axialR p) - b) +
    ((axialR p) - b) ^ 2 ≤ 1 / 3 := by
  -- Case split on which coordinate has the largest rounding error:
  --   (rq + ry + rr = 0) ⇒ rounding errors satisfy cube identity.
  --   (rq + ry + rr ≠ 0) ⇒ the largest-error coord is corrected,
  --                          leaving the other two with |Δ| ≤ 1/2.
  sorry  -- ~40-60 LOC: 3 sub-cases × Int.floor/Int.ceil bounds + nlinarith.

theorem covering_radius (p : Plane) :
    dist p (hexCenter (hexCoord p).1 (hexCoord p).2) ≤ hexSideLength := by
  -- Reduce to squared distance via dist_sq_le_iff (need ≥ 0 RHS).
  have hs : (0 : ℝ) ≤ hexSideLength := by unfold hexSideLength; norm_num
  rw [show dist p (hexCenter _ _) = Real.sqrt (dist p _ ^ 2) from
        (Real.sqrt_sq dist_nonneg).symm]
  rw [show (hexSideLength : ℝ) = Real.sqrt (hexSideLength ^ 2) from
        (Real.sqrt_sq hs).symm]
  apply Real.sqrt_le_sqrt
  -- Now compare squared dist via hexCenter_dist_sq + cube bound.
  -- Q(q-a, r-b) ≤ 1/3 ⇒ 3s²·Q ≤ s² ⇒ dist² ≤ s².
  sorry  -- ~10 LOC orchestration.
```

#### Path B — geometric fallback (only if Path A nlinariths fail)

Decompose into the 6 cube-rounding sub-cases (3 corrections × 2 signs
of `rq + ry + rr`), proving each as an isolated `private lemma`. About
3× the LOC of Path A but each sub-lemma is mechanically discharged by
`Int.floor_le`/`Int.le_ceil` + `nlinarith`.

### Risk analysis

| Risk | Likelihood | Mitigation |
|---|---|---|
| Conflict with open PR on this slug | none | `gh pr list --search "unit-distance-independence-oq-02 in:title state:open"` returns `[]` |
| Docker disk pressure blocking next ACT | high (host disk 100%) | covering_radius is non-trivial; ship as PREP not ACT next session, await Docker recovery |
| Mathlib pin drift before next ACT | low | Pin `2df2f015…` unchanged ≥9d |
| Build failure on this PR | none | doc-only, no Lean edits |

### Handoff

This S3 STATE-SYNC unblocks future research sessions on
`unit-distance-independence-oq-02` by ensuring the depth-first claim
picker sees the true knowledge state (ACT/iter 2 with concrete
covering_radius work item) AND tracks all three active Lean files in
the `leanFiles` array, not just the parent. A future S4 can either
ship the Path A PREP (paste-ready ~80 LOC sketch above) or attempt
the ACT directly if Docker disk recovers.

— researcher-1 @ 2026-05-16T08:56:13Z
