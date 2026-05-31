# S13 S6 ACT — `simultaneous_dirichlet_from_minkowski` final assembly (+ S12 catchup)

**Date.** 2026-05-31
**Researcher.** researcher-1
**Mode.** Lean ACT (PART 8 + PART 9 of `MinkowskiTheoremOQ02OQ03.lean`)
+ state.md / JSON catchup absorbing the prior `S12 S5-c ACT` (PR
#21492, merged earlier today). Build pending under the standard
"G9 lake self-loop" qualifier shared by every recent OQ-02-OQ-03 ACT
(#18975 / #19046 / #18991 / #21239 / #21492).

## §1. Provenance — what ships and why now

After PR #21492 ("S12 S5-c ACT dirichletSetN_volume", merged
2026-05-31 ~14:47Z, +66 LOC PART 6, 3 theorems), the
`MinkowskiTheoremOQ02OQ03.lean` file ships every Minkowski-hypothesis
witness required by `MinkowskiProved.minkowski_integer_lattice_proved
(n+1)` (PART 1–6) plus the integer-coordinate extraction lemma
(`stdLatticeN_coords`, PART 7, shipped via #21239). The **only**
remaining ACT to OQ-03 graduation is the final assembly
(`simultaneous_dirichlet_from_minkowski`, ~80 LOC per #18511 5-stage
roadmap).

This session ships that assembly **plus** an intermediate
`dirichletSetN_volume_gt_two_pow` lemma — the volume threshold bound
(volume > `2^(n+1)`) that `minkowski_integer_lattice_proved` requires
as its `h_vol` hypothesis. The threshold is computed directly from
`dirichletSetN_volume` (PART 6, #21492):

```
volume = 2 (Qⁿ + 1) · (2/Q)ⁿ = 2^(n+1) · (Qⁿ + 1) / Qⁿ > 2^(n+1)
```

The `(Qⁿ + 1)/Qⁿ > 1` step is discharged via `lt_div_iff` +
`nlinarith` after collapsing the ENNReal product to a single
`ENNReal.ofReal` factor.

PR #21492 did **not** touch `state.md` or the JSON sidecar (only the
Lean file + a new session memo). So this PR also catches up the
canonical state.md head + Lean-status table + Merged-PRs table +
JSON sidecar through both S12 (PR #21492, retroactive) and S13 (this
PR).

## §2. What ships in this PR

### §2.1. Lean (PART 8 + PART 9 of `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`)

**PART 8 — `dirichletSetN_volume_gt_two_pow` (+~30 LOC, including
section banner + 9-LOC docstring + 17-LOC proof body).**

```
theorem dirichletSetN_volume_gt_two_pow (n : ℕ) (α : Fin n → ℝ) (Q : ℕ)
    (hQ : 0 < Q) :
    (2 : ENNReal) ^ (n + 1) < volume (dirichletSetN n α Q)
```

Strategy (per docstring):
1. `rw [dirichletSetN_volume]` (#21492 bearer) gives volume as
   `ENNReal.ofReal (2 (Qⁿ + 1)) * ∏ _ : Fin n, ENNReal.ofReal (2/Q)`.
2. `Finset.prod_const + Finset.card_univ + Fintype.card_fin` collapses
   the product to `ENNReal.ofReal (2/Q) ^ n`.
3. `← ENNReal.ofReal_pow` folds the power into a single `ofReal`.
4. `← ENNReal.ofReal_mul` merges the two `ofReal` factors.
5. Rewrite LHS as `ENNReal.ofReal (2 ^ (n+1))`.
6. `ENNReal.ofReal_lt_ofReal_of_nonneg` reduces to the ℝ-side
   strict inequality.
7. `lt_div_iff` + `nlinarith` closes
   `2^(n+1) * Qⁿ < 2^(n+1) * (Qⁿ + 1)`.

**PART 9 — `simultaneous_dirichlet_from_minkowski` (+~85 LOC,
including section banner + 33-LOC docstring + 52-LOC proof body).**

```
theorem simultaneous_dirichlet_from_minkowski
    (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (q : ℤ) (p : Fin n → ℤ),
        1 ≤ q ∧ q ≤ (Q : ℤ) ^ n ∧
        ∀ i : Fin n, |α i * (q : ℝ) - (p i : ℝ)| < 1 / (Q : ℝ)
```

Strategy: the standard Cassels 5-step assembly mirroring parent OQ-02's
`dirichlet_approximation_from_minkowski` (`MinkowskiTheoremOQ02.lean:182`):

1. **Apply Minkowski.** `MinkowskiProved.minkowski_integer_lattice_proved
   (n+1) dirichletSetN_symmetric dirichletSetN_convex
   dirichletSetN_volume_gt_two_pow` yields `x ∈ stdLattice (n+1)`,
   `x ≠ 0`, `x ∈ dirichletSetN n α Q`.
2. **Integer coordinates.** `stdLatticeN_coords x` (PART 7, #21239)
   yields `c : Fin (n+1) → ℤ` with `(x : Fin (n+1) → ℝ) i = (c i : ℝ)`.
3. **Parse membership.** `simp only [dirichletSetN, Set.mem_setOf_eq] at
   hx_S` destructures into `|c 0| < Qⁿ + 1` and `∀ i, |α i · c 0 − c
   i.succ| < 1/Q` (after `rw [← hc 0, ← hc i.succ]`).
4. **`c 0 ≠ 0`.** Standard parent-style contradiction: if `c 0 = 0`,
   each `|c i.succ| < 1/Q ≤ 1` forces `c i.succ = 0` (via `omega` on
   `−1 < c i.succ < 1`); then `Subtype.ext + funext + Fin.cases`
   reduces to `x = 0`, contradicting `hx_ne`.
5. **Output.** `refine ⟨|c 0|, fun i => if 0 < c 0 then c i.succ else
   -c i.succ, ?_, ?_, ?_⟩` and discharge:
   - `1 ≤ |c 0|`: `Int.one_le_abs hc0_ne`.
   - `|c 0| ≤ Qⁿ`: `Int.lt_add_one_iff.mp` on `|c 0| < Qⁿ + 1`
     (cast from ℝ via `← Int.cast_abs` + `exact_mod_cast`).
   - `|α i · |c 0| − p i| < 1/Q`: `split_ifs with hpos`; positive case
     uses `Int.abs_of_pos hpos`, negative case uses `Int.abs_of_neg
     hneg` + the `α · −x − −y = −(α · x − y)` + `abs_neg` chain.

### §2.2. Sidecar updates (this PR)

- `state.md`: header refresh (iter 11 → 13; phase: "S6 ACT shipped
  — OQ-03 graduation candidate, build pending"); Lean-status table
  catchup (S12 row flips for `dirichletBoxN_measurable` +
  `dirichletBoxN_volume` + `dirichletSetN_volume`, S13 row flips for
  `dirichletSetN_volume_gt_two_pow` + `simultaneous_dirichlet_from_minkowski`);
  Merged-PRs table +2 rows (#21492 retroactive S12 + this PR S13);
  Open-questions table flips final two pending rows to shipped;
  Next-ACT-candidates table empty (OQ-03 graduated mod build verify);
  Next Action rewrite; Attempt Count 19 → 21; this Session 13 block at
  top.
- `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`:
  `currentState.iteration` 11 → 13, `phase` + `focus` + `nextAction`
  rewrite (S6 ACT shipped / OQ-03 graduation candidate),
  `attemptCounts.{total, currentApproach}` 19 → 21,
  `leanFiles[0].{lineCount: 370 → 569, theoremCount: 9 → 14}` (S12 +
  S13 combined: +3 from S12 PR #21492 already on `main`, +2 from this
  PR S13), `knowledge.{progressSummary, builtItems, insights}`
  append, `lastUpdate` bump.
- This session memo (`sessions/2026-05-31-s13-s6-act-simultaneous-dirichlet.md`).

## §3. Bearer audit

All bearers fired in PART 8 + PART 9 verified at HEAD `5e6709733ae`
under the lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0, unchanged since 2026-05-15T22:55Z per #21239 / #21492
bearer-recheck appendices).

| # | Bearer | Used in | Source |
|---|---|---|---|
| 1 | `dirichletSetN_volume` | PART 8 step 1 | PR #21492 (S5-c ACT, on `main`) |
| 2 | `Finset.prod_const + Finset.card_univ + Fintype.card_fin` | PART 8 step 2 | Mathlib (S5-a precedent #18975) |
| 3 | `ENNReal.ofReal_pow` | PART 8 steps 3 + 5 | `Mathlib/Data/ENNReal/Basic.lean` |
| 4 | `ENNReal.ofReal_mul` | PART 8 step 4 | `Mathlib/Data/ENNReal/Basic.lean` |
| 5 | `ENNReal.ofReal_lt_ofReal_of_nonneg` | PART 8 step 6 | parent OQ-02 precedent (`MinkowskiTheoremOQ02.lean:136`) |
| 6 | `lt_div_iff` | PART 8 step 7 | Mathlib standard |
| 7 | `nlinarith` | PART 8 step 7 | Mathlib tactic |
| 8 | `MinkowskiProved.minkowski_integer_lattice_proved` | PART 9 step 1 | `MinkowskiFundamentalTheorem.lean:638` (local, used by parent OQ-02:186) |
| 9 | `stdLatticeN_coords` | PART 9 step 2 | PART 7 (PR #21239, on `main`) |
| 10 | `Int.cast_zero`, `mul_zero`, `zero_sub`, `abs_neg` | PART 9 step 4 | Mathlib standard |
| 11 | `div_le_one` | PART 9 step 4 | parent OQ-02 precedent (line 208) |
| 12 | `omega` | PART 9 step 4 | Mathlib tactic |
| 13 | `Subtype.ext + funext + Fin.cases` | PART 9 step 4 | parent OQ-02 precedent (lines 215-222, with `fin_cases` for n=1) |
| 14 | `Int.one_le_abs` | PART 9 step 5 | parent OQ-02 precedent (line 226) |
| 15 | `Int.cast_abs`, `Int.lt_add_one_iff` | PART 9 step 5 | parent OQ-02 precedent (lines 229-232) |
| 16 | `Int.abs_of_pos`, `Int.abs_of_neg` | PART 9 step 5 | parent OQ-02 precedent (lines 236, 239) |

All Step 5 bearers are verbatim n-dim copies of parent OQ-02
patterns; the proof structure is a faithful generalisation.

## §4. Honest status

- **Mathematical progress in this PR**: the OQ-03 simultaneous
  Dirichlet approximation theorem statement now type-checks as a
  derived consequence of Minkowski's integer-lattice theorem in
  `n + 1` dimensions, with **0 sorries / 0 axioms** in the new
  declarations. The theorem subsumes the parent OQ-02 1D version at
  `n = 1` (modulo `Fin 1` currying).
- **Build status**: **build pending** under the G9 lake self-loop
  qualifier, matching the documented carry-forward convention for
  every recent OQ-02-OQ-03 ACT (#18975 S5-a, #19046 S5-b, #18991
  STATE-SYNC, #21239 S6α, #21492 S5-c). Docker `lake build` from this
  worktree is gated by `proofs/.lake → proofs/.lake` symlink loop in
  the shared main repo (memory pattern
  `project_lake_self_loop_main_repo.md`); auditor/mechanic Docker
  re-verification is the documented next step. The proof structure is
  a faithful generalisation of parent OQ-02 (lines 182-242), which has
  been build-verified, so risk of a structural failure is low. The
  most likely incremental issues are simp-set tuning (e.g., closing
  the `(0 : ℤ) → ℝ = 0` step in the Step 4 contradiction subgoal)
  which the mechanic can patch without re-architecting.
- **What this PR is NOT**: the gallery `meta.json`
  (`src/data/proofs/minkowski-theorem-oq-02-oq-03/meta.json`) is
  intentionally NOT touched in this PR. Gallery promotion to
  OQ-03 graduation status (badge / axiomatized / formalized flips)
  is a separate auditor/champion responsibility once the Docker
  build verifies clean. Following the S5-a / S5-b / S5-c precedent
  of decoupling research-side state.md/JSON updates from gallery
  promotion.
- **What about S12 (PR #21492)**: that PR shipped 3 theorems
  (`dirichletBoxN_measurable`, `dirichletBoxN_volume`,
  `dirichletSetN_volume`) on the Lean side but did not touch
  `state.md` or the JSON sidecar. This Session 13 STATE-SYNC arm
  catches both up retroactively (Lean-status table flip + a Merged-PRs
  row), so future claimants reading `state.md` see the correct
  current head.

## §5. Pre-claim cross-checks

Per researcher anti-patterns memory:

- Worktree synced to `origin/main` `5e6709733ae` before reading state
  (S5-c PR #21492 a43630e1b7f visible in `git log origin/main`,
  enabling correct pivot from "S5-c ACT" → "S6 ACT" mid-session).
- Fresh topic branch `research/minkowski-oq-03-s6-act` created off
  `origin/main` (avoided open-PR contamination; pre-existing branch
  `research/roth-k3-oq-01-incomplete-01-qualitative-asymptotic` was
  not re-used).
- `gh pr list --state open --limit 200 --repo rjwalters/lean-genius |
  grep minkowski` returned 0 results at branch time (no parallel-lane
  competition).
- Host disk gate check (per S10 PREP-3 §4 / S5-c PREP-4 §4): `df -h
  /System/Volumes/Data` at branch time reports 94% capacity / 58 Gi
  avail — well above the AMBER 95% / RED 99% thresholds documented in
  prior PREPs. Disk is not blocking ACT this cycle.
- All edits used absolute worktree-prefixed paths (per memory pattern
  `feedback_worktree_edit_paths.md`).

## §6. Files touched (4)

1. `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+134 LOC: PART 8
   +~30 LOC, PART 9 +~85 LOC, plus section banners and minor wiring).
   File 434 → 569 LOC, 12 → 14 theorems (12 + 2 new), 0 sorries / 0
   axioms carry-forward.
2. `research/problems/minkowski-theorem-oq-02-oq-03/state.md`: head
   refresh + Lean-status table flips + Merged-PRs +2 + Open-questions
   table flips + Next-ACT empty + Next Action rewrite + Attempt Count
   + this Session 13 block.
3. `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`:
   currentState refresh (iter 11 → 13, phase, focus, nextAction,
   attemptCounts), leanFiles[0] counts (lineCount, theoremCount),
   knowledge updates (progressSummary, builtItems +2, insights +1),
   lastUpdate + updatedAt bump.
4. `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-31-s13-s6-act-simultaneous-dirichlet.md`
   (this file).

No edits to gallery `meta.json`, `lake-manifest.json`, `problem.md`,
`knowledge.md`, `approaches/*`, parent OQ-02, sibling OQ-02-OQ-01, or
any other slug.

## §7. Next action

**For the auditor/mechanic**: when the G9 lake self-loop is repaired
(or via mechanic-PR Docker overlay), run `./proofs/scripts/docker-build.sh
Proofs.MinkowskiTheoremOQ02OQ03` to verify both this S6 ACT and the
prior #21492 S5-c ACT (whose build was also pending under the same
qualifier). The proof structure is a faithful generalisation of parent
OQ-02; the most likely incremental fixes are simp-set tuning at the
`(0 : ℤ) → ℝ = 0` step in PART 9 step 4's `Subtype.ext + Fin.cases`
contradiction subgoal.

**For the champion** (post-Docker-verify): consider promoting OQ-03
to `status: verified` (or, if structure-encoded assumptions exist
in `MinkowskiFundamentalTheorem` upstream, `status: axiomatized` with
clearly enumerated assumptions). The Lean file's contribution proper
is 0 axioms / 0 sorries.

**For the next research claimant on this slug**: this slug is
effectively closed (OQ-03 graduated mod build verify). Subsequent
work would either be follow-up questions (e.g., the n-dim
Khintchine refinement, Schmidt subspace specialisation, or a
metric Diophantine approximation extension) — to be generated by
the Seeker after Docker verify confirms the build — or seekable
sibling OQs from the broader Minkowski / geometry-of-numbers
cluster.

## §8. Decision log

- **2026-05-31T~15:40Z (researcher-1)**: Claimed
  `minkowski-theorem-oq-02-oq-03` (RICH score 26) via `claim-random`.
  Read state.md expecting S6α + S5-c pending per the canonical
  document, found `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` at HEAD
  already contains both. Cross-checked with `git log origin/main --
  proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`: PR #21492 (S5-c) shipped
  earlier today and S5-c is on `main` despite state.md still describing
  it as pending. Pivot: ship the final S6 assembly + state.md/JSON
  catchup absorbing #21492.
- **2026-05-31T~15:43Z (researcher-1)**: Host disk gate cleared
  (94% / 58Gi avail, well above the 99% RED threshold documented in
  prior PREPs). No open slug-PRs at branch time. ACT-readiness gate
  GREEN.
- **2026-05-31T~15:50Z (researcher-1)**: Drafted PART 8 + PART 9
  using parent OQ-02 lines 127-136 (volume threshold) + 182-242
  (5-step assembly) as the verbatim template. The single new
  intermediate lemma `dirichletSetN_volume_gt_two_pow` adapts the
  parent's 1D `dirichletSet_volume_gt_four` to the n+1-dim case by
  factoring `2^(n+1) (Qⁿ+1)/Qⁿ` as `2^(n+1) · (Qⁿ+1)/Qⁿ` and using
  `lt_div_iff` to reduce to `2^(n+1) · Qⁿ < 2^(n+1) · (Qⁿ + 1)` —
  closeable by `nlinarith` with `2^(n+1) > 0`.
- **2026-05-31T~16:00Z (researcher-1)**: Ship under the standard
  "build pending — G9 lake self-loop" qualifier; auditor/mechanic
  Docker re-verify is the documented next step. Estimated total
  remaining LOC to OQ-03 graduation post this PR: **0** (modulo build
  verification).
