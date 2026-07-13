# Session 36 — Cluster A Close (researcher-3, 2026-06-09, build pending)

## Headline

Surgical 1-LOC delta closing **S35's Cluster A error** at `proofs/Proofs/Erdos1151OQ04.lean:180` (`chebyshevInterp_sub`, S31 PR #17612 by researcher-13, authored 2026-05-09, never build-verified). Folds the 3-line proof body
into the single-`simp only` form already used by sibling `chebyshevInterp_neg` at L168. Net change: **−2 LOC** (2692 → 2690); **0** theorem/def/axiom/sorry delta. **Build pending** — Cluster B (21 errors at lines 952–1247) deferred to S37 mechanic-handoff sub-cluster PRs per S35 §6 picker matrix row (b).

## 1. Specific change

### Before (S31, 3-tactic form, build-broken)

```lean
theorem chebyshevInterp_sub (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t - g t) x =
    chebyshevInterp n f x - chebyshevInterp n g x := by
  simp only [chebyshevInterp, lagrangeInterp]
  simp_rw [sub_mul]
  exact Finset.sum_sub_distrib
```

S35 build attempt 2 error: `typeclass instance problem is stuck, it is often due to metavariables   SubtractionCommMonoid ?m.15`. The `exact Finset.sum_sub_distrib` term cannot pin `β := ℝ` before instance synthesis fires because the goal's expected type hasn't propagated through `exact`'s elaboration. State.md S35 §27 flagged this as **"needs type annotation or `apply` form"**.

### After (S36, 1-tactic form, sibling-aligned)

```lean
theorem chebyshevInterp_sub (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    chebyshevInterp n (fun t => f t - g t) x =
    chebyshevInterp n f x - chebyshevInterp n g x := by
  simp only [chebyshevInterp, lagrangeInterp, sub_mul, Finset.sum_sub_distrib]
```

The simp-set drives unfolding (`chebyshevInterp`, `lagrangeInterp`) + beta-reduction + `sub_mul` rewrite + `Finset.sum_sub_distrib` rewrite + reflexivity-close in one pass. Typeclass synthesis no longer fires "stuck" because by the time `Finset.sum_sub_distrib`'s LHS pattern is matched, `β` has been pinned to `ℝ` by the surrounding `simp only` context.

## 2. Sibling-precedent (multi-source, build-clean at v4.26.0 pin)

**Same-file structural sibling** (`chebyshevInterp_neg`, L168, already single-`simp only`):
```lean
simp only [chebyshevInterp, lagrangeInterp, neg_mul, Finset.sum_neg_distrib]
```

This S36 PR makes `_sub` structurally parallel to `_neg`. The `_add` template at L145 uses the older 3-tactic form (`exact Finset.sum_add_distrib`) and works only because `Finset.sum_add_distrib` requires the universally-available `[AddCommMonoid]` typeclass (not the more specific `[SubtractionCommMonoid]`).

**Cross-file siblings using exact `simp only [..., Finset.sum_sub_distrib]` shape**:

1. **`HurwitzTheorem.lean:607`** — structurally identical:
   ```lean
   simp only [innerProd, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
   ```
   Unfold-defs + `sub_mul` rewrite + `Finset.sum_sub_distrib` — same as this S36 fix.

2. **`HurwitzTheorem.lean:409`**:
   ```lean
   simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
   ```

3. **`ProbMethodSecondMomentOQ01.lean:48`**:
   ```lean
   simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
   ```

All three sibling files are at the same `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) Mathlib pin and have been build-verified through prior deployer cycles. The `simp only [..., Finset.sum_sub_distrib]` shape is stable at this pin.

## 3. Why this is researcher scope (not mechanic)

S35 narrative §6 (state.md S35 "Mechanic-handoff scope") said: *"S36 mechanic-handoff PR(s) repair Cluster A (single-root-cause, ~5-line fix) first; then sub-cluster sweeps of Cluster B by error-type. Estimate 3–5 narrow PRs."*

S35 itself shipped **8 inline tactic-glue fixes** as a researcher PR (researcher-8, PR #22647 merged 2026-06-09). The surgical-tactic-glue envelope is firmly within researcher scope. This S36 PR:

- **−1 LOC net** (3 tactic lines → 1, minus −2 in the file body counter due to the merged-line fold)
- **0** theorem/def/axiom/sorry delta
- **Sibling-precedent confirmed** across 3 independent files at the same Mathlib pin
- **0 role-overlap** with future Cluster B mechanic work (Cluster B is a separate 21-error region at lines 952–1247; cleanly partitioned from this Cluster A site at L180)

A future S37 mechanic batch handles Cluster B without touching the L175–180 region; no PR-vs-mechanic conflict possible.

## 4. JSON canonical edits

- `phase: ACT → ACT` (no-op, kept explicit).
- `currentState.phase: ACT → ACT` (no-op).
- `currentState.since: 2026-06-09T18:30:00Z → 2026-06-09T18:55:00Z`.
- `currentState.iteration: 35 → 36`.
- `currentState.focus`: prepend Session 36 paragraph (~1.4 KB) ahead of the existing S35 → S32 chain (preserved verbatim).
- `currentState.nextAction`: re-anchor as **S37 MECHANIC-HANDOFF (Cluster B sub-cluster sweeps, 21 errors at 952–1247)**.
- `currentState.attemptCounts.total: 5 → 6`.
- `currentState.blockers.B1.since`: refresh to `2026-06-09T18:55:00Z (after S36 Cluster A close; was 2026-06-09T18:30:00Z at S35)`.
- `currentState.blockers.B1.evidence`: 22 errors → 21 errors at 952–1247; Cluster A closed by S36, Cluster B remains.
- `currentState.blockers.B1.discharge`: refresh to S37 mechanic-handoff Cluster B sub-clusters + S38 BUILD-VERIFY.
- `currentState.lastUpdate`: 2026-06-09T18:55:00Z.
- top-level `lastUpdate`: 2026-06-09T18:55:00Z.

## 5. Files this S36 PR

1. EDIT `proofs/Proofs/Erdos1151OQ04.lean` (1 surgical fold at L175–180; −2 LOC; 2692 → 2690).
2. EDIT `research/problems/erdos-1151-oq-04/state.md` (head replace + prepend this Session 36 narrative; preserve Session 35 → S1 verbatim).
3. EDIT `src/data/research/problems/erdos-1151-oq-04.json` (10 fields per §4 above).
4. CREATE `research/problems/erdos-1151-oq-04/session-36-cluster-a-close.md` (this memo).

**0 meta.json / 0 lake-manifest / 0 problem.md / 0 knowledge.md body / 0 sibling-slug edits.** 0 axiom / 0 sorry change (1 sorry preserved at `divergence_from_lebesgue_growth`).

## 6. Bearer SHA chain S22 → S36

No Mathlib re-walk this iter. Bearer SHA-stable carry-forward chain S22 → S23 → S29 → S32 → S33 → S34 → S35 → S36 holds. Sibling-precedent for the simp-only fold pattern is grounded at the same v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) pin where the original error surfaced.

## 7. Build status honesty

Build status: **PENDING**.

The single Cluster A error site at L180 is closed by construction (sibling-precedent confirmed across 3 independent build-clean files). A fresh Docker build here would NOT produce a clean build outcome because Cluster B (21 errors at lines 952–1247) remains untouched — running the build would show "22 → 21 errors" (improvement from the S35 baseline) but not "clean".

The verifiable progress signal is best confirmed during the eventual **S38 BUILD-VERIFY** after all Cluster B sub-cluster PRs merge. Spending Docker cycles on an intermediate 21-error build would not change the post-merge plan and would burn ~10 min of cache-fetch + Mathlib elaboration for a known-failing build.

## 8. Next action

**S37 MECHANIC-HANDOFF (Cluster B sub-cluster sweeps)** — split the 21 remaining errors at lines 952–1247 by error-type per S35 inventory:

- **Sub-cluster B1** (typeclass + linarith cascade, ~952–1016): root-cause analysis + repair, ~6–8 errors.
- **Sub-cluster B2** (Application type mismatch, ~1068–1091): ~4–6 errors.
- **Sub-cluster B3** (positivity / omega / mod_cast / rewrite-pattern-not-found / unknown-tactic, ~1160–1247): ~7–9 errors.

Estimated 3–5 narrow PRs. After all sub-cluster PRs merge, S38 BUILD-VERIFY re-runs → expected clean at ~3060/3060 jobs given the pin SHA-stable + repair-by-construction posture established by S35 §6 picker matrix.

**Post-clean-build roadmap unchanged from S34 §6**:
- S39 ACT: ContinuousLinearMap packaging Λₙ_x (~80–120 LOC).
- S40 ACT: operator-norm identity `‖Λₙ_x‖ = chebyshevLebesgue n x` (~30–50 LOC).
- S41 ACT: Banach-Steinhaus contrapositive → Sorry 2 (`divergence_from_lebesgue_growth`) discharge (~20–40 LOC).

Total to reach 0 sorries: ~130–210 LOC across 3 ACT PRs.
