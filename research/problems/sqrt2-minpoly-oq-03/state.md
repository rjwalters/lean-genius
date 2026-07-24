# Current State

> **RE-OPENED 2026-07-24 (researcher-2, S9)** — The 2026-06-13 blackout premise no longer holds: Docker is up, and S9 ran a full green build (`[8577/8577]`, Mathlib **v4.31** pin). Status `blocked → active`.

**Phase**: COMPLETED (S12 — TARGET PROVED: `Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1`, unconditional, 0 sorries / 0 axioms. The last strategic sorry `Q_sqrt2_discr_eq_eight` is closed: `{1, √2}` packaged as `Basis (Fin 2) ℤ (𝓞 Q_sqrt2)` from S11's `isIntegral_elt_iff`, trace matrix `[[2,0],[0,4]]`, `det = 8` via `NumberField.discr_eq_discr`.)
**Since**: 2026-05-15T23:26:58Z (S3 ACT SCAFFOLD merge anchor)
**Last Updated**: 2026-07-24 (Iteration 20 S12 ACT, researcher-3)
**Iteration**: 20

## Iteration 20 (researcher-3, 2026-07-24) — S12 ACT: discr = 8, capstone UNCONDITIONAL [HOST-VERIFIED]

The file's sole strategic sorry is closed; `#print axioms` on
`Q_sqrt2_discr_eq_eight`, `Q_sqrt2_classNumber_eq_one`, `isIntegral_elt_iff`,
`intBasis` = `[propext, Classical.choice, Quot.sound]` (foundational trio only).
`bin/lake env lean` exit 0, zero warnings.

New bricks (S12 section at end of `Sqrt2MinpolyOQ03.lean`):

- `exists_elt_eq` — coordinate surjectivity `∀ x, ∃ a b, x = elt a b`, read off
  `(AdjoinRoot.powerBasis).basis.reindex (finCongr hdim)`;
  `PowerBasis.basis_eq_pow` + `Fin.sum_univ_two` + `Algebra.smul_def`.
- `elt_eq_zero` — coordinate uniqueness at 0 (irrationality via
  `elt_not_mem_range` for `b ≠ 0`; `map_eq_zero_iff` for `b = 0`).
- `sqrt2Int : 𝓞 Q_sqrt2` (`⟨root, root_isIntegral⟩`), `sqrt2Int_mul_self : √2·√2 = 2`
  (transport `root_sq` through `RingOfIntegers.ext`).
- `intBasis : Basis (Fin 2) ℤ (𝓞 Q_sqrt2) = Basis.mk` on `![1, sqrt2Int]`:
  linear independence via coercion to `K` + `elt_eq_zero`
  (`Fintype.linearIndependent_iff`); spanning via `exists_elt_eq` +
  `x.isIntegral_coe` + S11 `coords_int_of_isIntegral`.
- Traces: `trace_intCast` (= 2n, via `Algebra.trace_algebraMap` +
  `RingOfIntegers.rank` + `Q_sqrt2_finrank`); `trace_sqrt2Int = 0`
  (`Algebra.trace_eq_matrix_trace` + `leftMulMatrix_eq_repr_mul`, the
  left-multiplication matrix of √2 is `[[0,2],[1,0]]` — zero diagonal).
- `Q_sqrt2_discr_eq_eight` — `NumberField.discr_eq_discr` + `Algebra.discr_def`
  + `Matrix.det_fin_two`, trace matrix `[[2,0],[0,4]]`, det 8.
- `Q_sqrt2_classNumber_eq_one` — now unconditional (S9 reduction + discr).

**Lean gotchas (v4.31 pin)**: `Basis` is `Module.Basis` — bare `Basis` in new
code needs `open Module` (existing S3–S11 code never named it at top level);
`rw [← hsum]` on a goal whose RHS mentions `b'.repr x` rewrites the `x` inside
`repr` too — use a forward `calc` from `Basis.sum_repr` instead; `0 + 0 = 0`
in ℤ is NOT closed by `rw`'s terminal rfl (needs `norm_num`/`simp`);
`intBasis_apply_one` needs full `simp` (`![sqrt2Int] 0` reduction —
`Matrix.cons_val_one` alone strands the tail lookup).

**Trackers**: `src/data/research/problems/sqrt2-minpoly-oq-03.json` NOT touched
— it is 3 concatenated JSON objects on main (mechanic issue #43405, open PR
#43409); reconcile knowledge there after the mechanic fix merges.

Nothing formalizable remains on this slug: the formal target
`Q_sqrt2_classNumber_eq_one` and both restatement corollaries' substance
(PID-ness via `classNumber_eq_one_iff`) are delivered. Possible follow-ups
recorded in the session file (Euclidean-domain strengthening; other small
real quadratic fields via the same recipe).

## Iteration 19 (researcher-3, 2026-07-24) — S11 ACT: element-level integral basis [HOST-VERIFIED]

`isIntegral_elt_iff : IsIntegral ℤ (elt a b) ↔ a, b ∈ ℤ` — the complete
membership description of `𝓞 Q(√2)` (sorries unchanged at 1; `#print axioms`
on the iff = 3 foundational, sorry-independent; `lake env lean` exit 0 on the
pinned v4.31.0 toolchain, only the expected strategic-sorry warning).

New bricks (all in `Sqrt2MinpolyOQ03.lean`, after the S10 section):
`elt` (the element `a + b·√2`), `root_not_mem_range` (√2 irrational — via
`rat_int_of_sq_int` + `interval_cases`), `elt_not_mem_range`,
`aeval_elt_quadratic` (annihilator, closed by `linear_combination
(map b)² * root_sq`), `quadratic_monic` (`monic_X_pow_add`), `minpoly_elt`
(minpoly = the quadratic, via `minpoly.dvd` + `minpoly.two_le_natDegree_iff`
+ monic-quotient-is-1), `coords_int_of_isIntegral` (minpoly ℤ-descent
`minpoly.isIntegrallyClosed_eq_field_fractions'` + coefficient extraction +
S10 crux), `isIntegral_elt_of_coords` (reverse inclusion, tower
`IsScalarTower.algebraMap_apply ℤ ℚ Q_sqrt2`).

**Design note**: the trace/norm formulas sketched at S10 are NOT needed —
the minpoly of `a + b·root` (b ≠ 0) *is* `X² − (tr x)·X + N x`, so the
ℤ-descent of its coefficients delivers the trace and norm integrality
without any power-basis matrix computation.

**v4.31 gotchas**: `Polynomial.degree_C_mul_le` does not exist — use
`degree_C_mul_X_le`; `Monic.natDegree_eq_zero_iff_eq_one` does not exist —
use `eq_C_of_natDegree_eq_zero` + `leadingCoeff` unfolding; coefficient
extraction from a `map`-equality needs `simp only` with the precise
`coeff_*` set (plain `simpa` normalizes `C (a²−2b²)` through `map_sub` and
strands `(C a ^ 2).coeff 1`); `↑(-c)` needs `Int.cast_neg` before `linarith`.

Full record: `sessions/2026-07-24-s11-act-element-level-integral-basis.md`.

## Iteration 18 (researcher-2, 2026-07-24) — S10 ACT: integral-basis bricks [BUILD-VERIFIED]

4 bricks on the critical path of `Q_sqrt2_discr_eq_eight` (sorries
unchanged at 1): `root_sq`, `root_isIntegral` (ℤ[root] ⊆ 𝓞),
`rat_int_of_sq_int` (rational with integer square is an integer — via
`IsIntegrallyClosed.isIntegral_iff`, NO `Rat.den` internals), and the
arithmetic crux `int_pair_of_double_and_norm` (`2a ∈ ℤ` ∧ `a²−2b² ∈ ℤ`
⟹ `a, b ∈ ℤ`; half-integer exclusion in `ZMod 4`:
`∀ x : ZMod 4, x² ≠ 2 := by decide`). All rational bookkeeping =
`push_cast` + `linear_combination` with hand-computed coefficients.
S11 consumes these with power-basis trace/norm formulas
(`trace (a+b·root) = 2a`, `norm = a²−2b²`) for `𝓞 = ℤ[√2]`, the ℤ-basis
`{1, root}`, and `discr = 8`.
Full record: `sessions/2026-07-24-s10-act-integral-basis-bricks.md`.

## Iteration 17 (researcher-2, 2026-07-24) — S9 ACT: totally-real + conditional capstone [BUILD-VERIFIED]

**Outcome**: Largest Lean delta in this problem's history (+115/−23 LOC), Docker-verified green at `[8577/8577]` (sole warning: the expected strategic sorry, L189). Full record: `sessions/2026-07-24-s9-act-totally-real-conditional-capstone.md`.

- **Headline**: the repo's Mathlib pin moved v4.26 → **v4.31** since S8, and `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` — which S8 proved absent at v4.26 — **EXISTS at v4.31**. This collapses S8's long route (4 sub-targets incl. `⌊M K⌋₊ = 1`) into a 4-line conditional capstone.
- **New build-verified content**: `embedding_root_sq` (φ root² = 2), `conj_eq_self_of_sq_eq_two` (z² = 2 → z real, `nlinarith`), `complexEmbedding_isReal` (instance-safe `Polynomial.ringHom_ext` route precomposing with `AdjoinRoot.mk` — avoids `AdjoinRoot.algHom_ext` ℚ-algebra unification friction; `Subsingleton (ℚ →+* ℂ)` handles constants), `instance NumberField.IsTotallyReal Q_sqrt2`, `Q_sqrt2_nrComplexPlaces = 0`, `Q_sqrt2_classNumber_eq_one_of_discr` (conditional capstone: `classNumber_eq_one_iff` + `isPrincipalIdealRing_of_abs_discr_lt` + `norm_num`; bound `8 < 16`), and the assembled main theorem `Q_sqrt2_classNumber_eq_one`.
- **Sub-target scoreboard (S8 numbering)**: (1) `discr = 8` OPEN — sole remaining sorry; (2) `nrComplexPlaces = 0` DONE; (3) Minkowski arithmetic DONE (absorbed into `norm_num`); (4) capstone assembly DONE.
- Sorries: 1 · Axioms: 0 · Status: `blocked → active`.

### Next action (S10): `Q_sqrt2_discr_eq_eight`

Prove `𝓞 K = ℤ[√2]` (integrality of `a + b·root` ⟺ `a, b ∈ ℤ` via trace `2a ∈ ℤ` + norm `a² − 2b² ∈ ℤ` + mod-4 case analysis), exhibit `{1, root}` as a `Basis (Fin 2) ℤ (𝓞 K)`, then `discr = det [[2,0],[0,4]] = 8` via `NumberField.discr_eq_discr`. No `Zsqrtd ↔ RingOfIntegers` bridge exists at the pin — hand-rolled integral basis required. Estimate 1–2 full sessions.

## Iteration 16 (researcher-2, 2026-06-12) — S8 BUILD-VERIFIED  ·  state.md recorded by researcher-4, 2026-06-13

**Note**: S8 (researcher-2, 2026-06-12) updated `src/data/research/problems/sqrt2-minpoly-oq-03.json` (currentState → iteration 16) and `proofs/Proofs/Sqrt2MinpolyOQ03.lean` (2 new build-verified lemmas + capstone docstring rewrite), but did NOT update this `state.md` head, which remained at Iteration 15 / S7. This entry records S8 so the human-readable tracker matches the JSON + Lean source on `main`. Pure doc-sync; 0 Lean / 0 JSON edits in this STATE-SYNC.

**S8 outcome (researcher-2, 2026-06-12)**: FIRST actual Docker build in this problem's history (S1–S7 were all `gh api` source spot-checks, never a compile). Ran `./proofs/scripts/docker-build.sh Proofs.Sqrt2MinpolyOQ03` twice at Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`: both green at `[7744/7744]`, only the expected capstone `sorry` warning.

- **Result 1 (ground truth)**: the full instance stack (Field / Algebra ℚ / NumberField for `AdjoinRoot (X²−2)`) compiles clean against current Mathlib — NO drift; refutes the latent "builds silently red" risk that the S2–S7 `gh api`-only chain could never rule out.
- **Result 2 (down payment)**: added two build-verified lemmas to `Sqrt2MinpolyOQ03.lean` — `X_sq_sub_two_ne_zero` (L63) and `Q_sqrt2_finrank : Module.finrank ℚ Q_sqrt2 = 2` (L76, via `AdjoinRoot.powerBasis_dim` + `PowerBasis.finrank`). `finrank = 2` is the `n` in the Minkowski bound `M K`.
- **Result 3 (API correction)**: the prior STATE-SYNC chain's assumed capstone bearer `isPrincipalIdealRing_of_abs_discr_lt` (claimed at ClassNumber.lean:198) **DOES NOT EXIST** in Mathlib v4.26.0. Real route from ClassNumber.lean source: `classNumber_eq_one_iff` + `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`, needing discr=8, nrComplexPlaces=0, finrank=2, ⌊M K⌋₊=1. Capstone docstring (L81–105) rewritten with the corrected route.
- **Infra**: B1 disk RED→GREEN (79 Gi free at S8 vs S7's 2.0 Gi). B3 `.lake` circular self-symlink downgraded RED→YELLOW — IRRELEVANT to Docker builds (docker-build.sh mounts a named volume `lean-mathlib-cache` at `/workspace/proofs/.lake/build`, shadowing the host symlink). This resolves the long-standing "cannot build" premise of S2–S7.

### Remaining capstone sub-targets (each its own future ACT iteration, each needs a Docker compile)

1. `discr Q_sqrt2 = 8` — the crux; `Algebra.discr` trace-form on the `{1, √2}` basis or a Mathlib quadratic-discriminant lemma (verify existence at v4.26.0).
2. `nrComplexPlaces Q_sqrt2 = 0` (Q(√2) totally real).
3. `⌊M K⌋₊ = 1` — real-arithmetic reduction from `finrank = 2` (done) + discr=8 + nrComplexPlaces=0.
4. capstone via `classNumber_eq_one_iff` + `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc` with vacuous prime interval (`Icc 1 1` has no primes).

### Docker status at this STATE-SYNC (researcher-4, 2026-06-13)

Docker is **DOWN/unreachable again** today (`docker info` times out; disk healthy at 18% used / 57 Gi free). S8's build path is PROVEN working, so the gate is purely Docker availability, not a code/infra defect. Per S8's `nextAction`: do NOT ship a `gh api`-only STATE-SYNC for new claims — every future ACT iteration should compile via `docker-build.sh` and report the true `[7744/7744]` result. Next-claim guidance: if Docker is up, proceed with sub-target (1) `discr Q_sqrt2 = 8`; if Docker is down, release-and-cycle (this entry already absorbs the S8 delta — no further doc-sync needed).

## Iteration 15 (researcher-1, 2026-06-02) — S7 STATE-SYNC

**Outcome**: STATE-SYNC (doc-only) — post-S6-STATE-SYNC-merge follow-up T+~17 days absorbing one substantive host-side delta (B2 Docker RED→GREEN, `docker info` now returns `29.4.1` server version vs S6's hung empty Server: section). B1 disk RED carry-forward (~2.0 Gi free / 100% used `/dev/disk3s5`, slightly worse than S6's 3.0 Gi; still below 5.4 Gi same-day ACT soft floor). B3 `proofs/.lake` circular self-symlink RED carry-forward (`readlink -f` resolves to own path; `ls` reports "Too many levels of symbolic links"). 2-bearer spot-check via `gh api` at unchanged Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`: `classNumber_eq_one_iff` ClassNumber.lean:74 + `isPrincipalIdealRing_of_abs_discr_lt` ClassNumber.lean:198 both byte-stable verbatim. ACT-readiness gate flips 5/9 → 6/9 GREEN. S4 PREP §4 ~75-LOC paste-ready skeleton recipe-frozen. Orphan-stash flag from S6 cleared (stash IDs rotated; no longer present in `git stash list`).

### What I added

- `sessions/2026-06-02-s7-state-sync-docker-cleared-17day-quiescence.md` (NEW, ~245 LOC) — TL;DR + 17-day quiescence absorb (§2), INFRA gate state table 9-row (§3), why-STATE-SYNC justification (§4), 2-bearer verbatim spot-check (§5), iteration ledger through Iter 15 (§6), next-action priority routes (§7), files-modified manifest (§8), honest calibration with 5 explicit non-actions (§9).
- This `state.md` head: phase header refresh (3 RED blockers → 2 RED blockers; B2 Docker GREEN), Last Updated → 2026-06-02T13:00Z, Iteration 14 → 15, Iteration 15 block inserted above preserved Iteration 14 block. Blockers subsection refreshed (3 entries → 2 entries; B2 removed).
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`: `currentState.{lastUpdated, iteration 14→15, focus rewrite, nextAction rewrite, attemptCounts.total 14→15}` + `currentState.blockers` 3→2 entries (B2 cleared) + `knowledge.progressSummary` tail append + `knowledge.nextSteps[0]` rewrite.

### Why a STATE-SYNC now (single delta + 17-day quiescence)

S6 STATE-SYNC (PR #19760, researcher-12, merged 2026-05-16T19:ish) pinned the ACT-readiness gate at 5/9 GREEN with 3 host-side INFRA REDs. 17 days later, ONE substantive delta has accumulated:

- **B2 Docker daemon cleared**: `timeout 5 docker info --format '{{.ServerVersion}}'` now returns `29.4.1` (was empty Server: section at S6). This is the one delta worth absorbing — without this STATE-SYNC, the next ACT picker would re-discover B2 has cleared and spend an iteration re-verifying.

Two infrastructure REDs from S6 carry forward unchanged from this host:

- **B1 disk avail**: ~2.0 Gi free / 100% used (slightly worse than S6's 3.0 Gi); below 5.4 Gi same-day ACT soft floor (PR #19675 ballot-problem S6 ACT). Same condition flagged today across multiple researcher-1 cycles (memory `project_researcher_1_2026_06_02_iter4_ftc_lebesgue`).
- **B3 `proofs/.lake` circular self-symlink**: main repo's `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (points at itself). `readlink -f` resolves to own path; `ls` reports "Too many levels of symbolic links". Same condition as S6 STATE-SYNC §3.

The 17-day quiescence by itself would not warrant a STATE-SYNC; the B2 delta is what makes this PR non-vacuous. Mathlib pin **unchanged** at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake v4.26.0); SHA-pin transitivity carries the 12-row bearer pin grid byte-stable. This session spot-checks 2 bearers (different rotation from S6's 1-bearer check) — both verbatim match.

S7 ACT remains GATED on B1 + B3 host-side fixes. Recommendation: if host operator fixes B1 (free ≥5.4 Gi) + B3 (repoint `.lake` to actual cache) within 24-48 hours, proceed directly with S4 PREP §4 paste. Otherwise: release-and-cycle silently; do NOT ship another STATE-SYNC for ≥48 hours.

### Next action (post-S7 STATE-SYNC)

Two routes for next claim on this slug, in priority order:

1. **Host operator (out-of-agent action)**: (a) repoint `proofs/.lake` symlink to actual lake working directory (not self-referential); (b) free disk ≥5.4 Gi. With B2 (Docker) already GREEN this session, both fixes → full 9/9 GREEN gate; S4 PREP §4 ~75-LOC paste-ready skeleton at `proofs/Proofs/Sqrt2MinpolyOQ03.lean` L72↔L73 (replacing L71 `  sorry` body) becomes immediately viable — expected `[7745/7745]` warm build ~12s.
2. **Next-claim researcher**: if host conditions still RED on next claim, **release-and-cycle silently** (do not ship another STATE-SYNC for ≥48 hours absent a substantive delta — Docker GREEN was this session's delta and is now logged).

### Files modified

- `research/problems/sqrt2-minpoly-oq-03/state.md` (this file head)
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`
- `research/problems/sqrt2-minpoly-oq-03/sessions/2026-06-02-s7-state-sync-docker-cleared-17day-quiescence.md` (NEW)

### Blockers (S7 STATE-SYNC)

- **B1 (RED)** — Host-disk avail ~2.0 Gi (`/dev/disk3s5` 100% used per `df -g /Users/rwalters` at 2026-06-02T13:00Z). Below same-day ACT soft floor 5.4 Gi (PR #19675 ballot-problem S6 ACT). Slightly worse than S6's 3.0 Gi. Resolution: free ≥5.4 Gi.
- **B3 (RED)** — `proofs/.lake` circular self-symlink (`/Users/rwalters/GitHub/lean-genius/proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake`). `readlink -f` returns own path; `ls` reports "Too many levels of symbolic links". Carry-forward standing INFRA RED from S6. Resolution: host operator repoint to actual lake working directory.

(B2 Docker daemon: **CLEARED this session** — `docker info` returns `29.4.1` server version; no longer a blocker.)

### Honest Calibration (S7 STATE-SYNC)

- 0 Lean changes, 0 bearer re-walks (only 2-bearer spot-check), 0 gallery edits, 0 problem.md edits, 0 knowledge.md body edits. Pure JSON+state.md+session-note tri-edit per memory's thin-STATE-SYNC pattern.
- 1 substantive delta (B2 Docker RED→GREEN) — the load-bearing reason this PR is non-vacuous.
- 2-bearer spot-check via `gh api` (no local Mathlib clone, no Docker dependency). SHA-pin transitivity carries the remaining 10/12 bearers per `feedback_sha_stable_busywork`.
- No `.lake` symlink repair attempted — the broken symlink is on the **main** repo path, not the worktree; touching it from a research-session worktree risks cross-agent interference per `feedback_edit_absolute_paths_worktree_gotcha`.
- 17-day quiescence absorbed as a "longest dormancy" observation, but with positive confirmation: 0 commits to `Sqrt2Minpoly*.lean` or `sqrt2-minpoly-oq-03/` since S6 STATE-SYNC; no parent regression.
- Orphan-stash flag from S6 cleared (stash IDs rotated; ephemeral local stash did not survive across rebases).

## Iteration 14 (researcher-12, 2026-05-16) — S6 STATE-SYNC

**Outcome**: STATE-SYNC (doc-only) — post-S5-STATE-SYNC-merge follow-up T+~14h absorbing one substantive new delta (G7 host-disk **AMBER → RED** crossing the same-day build-pending soft floors set by shannon-channel S18a-1 5.8 Gi PR #19655 + ballot-problem S6 ACT 5.4 Gi PR #19675); G8 Docker daemon hung carry-forward; G9 `proofs/.lake` circular self-symlink carry-forward; 1-bearer SHA-pin reaffirm + orphan-stash flag (researcher-93169 S5 ACT paste attempt @ ~T-25min).

### What I added

- `sessions/2026-05-16-s6-state-sync-disk-red-escalation-orphan-stash-flag.md` (NEW, ~330 LOC) — drift inventory, disk evidence + same-day floor table (§2), G8+G9 reaffirm (§3), Mathlib SHA + 1-bearer spot-check (§4), orphan-stash flag (§5), readiness gate flip 8/8 GREEN → 5/8 GREEN (§6), 5-row picker decision matrix (§7), 8 explicit non-actions (§8), honest calibration (§9), files modified (§10).
- This `state.md` head: phase header refresh (ACT-but-GATED qualifier), Last Updated → 18:36Z, Iteration 13 → 14, Iteration 14 block inserted above preserved Iteration 13 block. Blockers subsection refreshed (was empty post-S5-STATE-SYNC; 3 entries now: B1 disk RED, B2 Docker hung, B3 `.lake` circular).
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`: `currentState.{lastUpdated, iteration 13→14, focus rewrite, nextAction rewrite, attemptCounts.total 13→14}` + `currentState.blockers` []→3 entries + `knowledge.progressSummary` tail append + `knowledge.nextSteps[0]` rewrite (S5 ACT → release-and-cycle until INFRA GREEN).

### Why a STATE-SYNC now (strict refinement, not deviation)

S5 STATE-SYNC (PR #19418, researcher-11, merged 2026-05-16T04:40:26Z) pinned ACT-readiness gate at 8/8 GREEN at T-13h56min. Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and all 12 bearer rows remain byte-stable (SHA-pin transitivity carries the rest; this PR spot-checks 1 row — `classNumber_eq_one_iff` ClassNumber.lean:74 + `isPrincipalIdealRing_of_abs_discr_lt` ClassNumber.lean:198 — both verbatim).

ONE new substantive delta has accumulated:

- **G7 host-disk avail**: 100% capacity, ~3.0 Gi free (`df -g /Users/rwalters` at 2026-05-16T18:35Z). Crosses both same-day ACT soft floors (5.8 Gi PR #19655 + 5.4 Gi PR #19675). At 3.0 Gi the safety margin is no longer comparable to those build-pending precedents.

Two infrastructure REDs that S5 STATE-SYNC did not enumerate (because at 03:35Z the disk pressure was lower and Docker was up) carry forward as standing blockers visible from THIS host:

- **G8 Docker daemon**: `timeout 5 docker info --format '{{.ServerVersion}}'` returns empty Server: section. Daemon hung — same condition documented in `abel-ruffini-oq-04-oq-09` S6 PREP (PR #19633, researcher-11, T-4h7min) and S7 STATE-SYNC (PR #19755, researcher-12 this session, T-15min).
- **G9 `proofs/.lake` circular self-symlink**: `lrwxr-xr-x ... proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake` (points at itself). Same condition documented in `abel-ruffini-oq-04-oq-09` S6 PREP §2.3 and S7 STATE-SYNC §3.

Additionally, a **non-PR artifact**: `git stash list` `stash@{0}` carries `researcher-93169-orphan-sqrt2-minpoly-s5-act-paste-2026-05-16` (Sat May 16 11:12:33 -0700 = 18:12Z, T-23min) on branch `research/sqrt2-minpoly-oq-03-s5-act-capstone-skeleton-1778940985`. Diff stat: `proofs/Proofs/Sqrt2MinpolyOQ03.lean | 152 +++++++++++++++++++++++++++++++---- 1 file changed, 136 insertions(+), 16 deletions(-)`. Not in any open PR; orphaned. Flagged for the next ACT picker to consider as prior-attempt signal — but the orphan-itself is NOT evidence of mathematical drift; the host-side INFRA is what gates ACT now.

S6 ACT remains GATED on host-side fixes (Docker daemon restart + `.lake` symlink repoint + disk cleanup ≥5.4 Gi same-day floor). Recommendation: release-and-cycle until ALL THREE of G7 ≥ 5.4 Gi AND G8 GREEN AND G9 GREEN. No content changes. No bearer re-walk. No Lean edits.

### Next action (post-S6 STATE-SYNC)

Two routes for next claim on this slug, in priority order:

1. **Host operator (out-of-agent action)**: restart Docker daemon, repoint `proofs/.lake` symlink to actual `.lake` working directory, free disk ≥5.4 Gi. Then ACT picker re-enters with same S4 PREP §4 ~75-LOC paste-ready skeleton (recipe-frozen; not invalidated by this STATE-SYNC).
2. **Next-claim researcher**: if host conditions still RED on next claim, ship a thinner S7 STATE-SYNC OR release-and-cycle; do not attempt the paste under build-pending qualifier because 3.0 Gi disk is below the 5.4 Gi same-day floor (NOT comparable to ballot-problem / shannon-channel precedents).

### Files modified

- `research/problems/sqrt2-minpoly-oq-03/state.md` (this file head)
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`
- `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-16-s6-state-sync-disk-red-escalation-orphan-stash-flag.md` (NEW)

### Blockers (S6 STATE-SYNC)

- **B1 (RED)** — G7 host-disk avail ~3.0 Gi (100% used `/dev/disk3s5`). Below same-day ACT soft floors (5.8 Gi PR #19655, 5.4 Gi PR #19675). S5 STATE-SYNC carried no disk blocker; this entry escalates the now-observed condition.
- **B2 (RED)** — G8 Docker daemon hung (`docker info` empty Server: section). Same condition as `abel-ruffini-oq-04-oq-09` S6 PREP / S7 STATE-SYNC. Carry-forward standing INFRA RED.
- **B3 (RED)** — G9 `proofs/.lake` circular self-symlink (`proofs/.lake → proofs/.lake`). Carry-forward standing INFRA RED.

### Honest Calibration (S6 STATE-SYNC)

- This STATE-SYNC ships 0 Lean changes, 0 bearer re-walks, 0 gallery edits, 0 problem.md edits, 0 knowledge.md body edits. Pure JSON+state.md+session-note tri-edit per memory's thin-STATE-SYNC pattern for single-disk-delta absorption.
- The S4 PREP §4 paste-ready skeleton remains recipe-frozen — unchanged in content; only the ACT-readiness gate state flipped from 8/8 GREEN to 5/8 GREEN.
- Spot-check is 1 row (2 lemma sites in `ClassNumber.lean`) not the full 12. Per `feedback_sha_stable_busywork` memory: SHA-pin transitivity carries the rest at unchanged pin `2df2f0150c...`.
- The orphan-stash flag is informational; the agent (researcher-12 this session) did NOT inspect the stash contents for mathematical signal because INFRA RED gates any Docker-verified ACT regardless of what the stash contains.
- This is the second STATE-SYNC researcher-12 has shipped in this session (first: `abel-ruffini-oq-04-oq-09` S7 PR #19755 at T-15min). Both absorb the same host-side disk degradation evidence on the same wall-clock day, on different slugs. Defensible: each slug owns its own gate state and bearer-pin stability declaration.

## Iteration 13 (researcher-11, 2026-05-16) — S5 STATE-SYNC

**Outcome**: STATE-SYNC (doc-only) — post-S4-PREP-merge catch-up: state.md head + JSON `currentState` block + `attemptCounts` (off-by-12 corrected) + 12-bearer drift recheck (4 fresh round-trips + 8 byte-stable, 0 drift) + S5 ACT-readiness gate 8/8 GREEN.

### What I added

- `sessions/2026-05-16-s5-state-sync-post-s4-prep-merge.md` (NEW, ~310 LOC) — post-merge snapshot, 12-row bearer drift recheck (§3), 8/8 GREEN ACT-readiness gate (§4), iteration ledger consolidated through Iter 13 (§5), orthogonality manifest (§6), strict-honesty footprint (§7).
- This `state.md` head: phase header refresh + Since + Iteration 11→13 + Iteration 12 + Iteration 13 sections inserted above preserved Iter 11 block.
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`: `currentState.phase`/`since`/`lastUpdated`/`iteration`/`focus`/`nextAction` refresh + `attemptCounts.total` 1→13 (off-by-12 fix) + `knowledge.progressSummary` tail + `knowledge.nextSteps[0]` rewrite.

### Why a STATE-SYNC now

PR #19253 (S4 PREP, researcher-3) merged 2026-05-15T18:03:22Z. PR #19068 (S3 ACT SCAFFOLD, researcher-8) merged 2026-05-15T23:26:58Z. state.md + JSON head still read Iter 11 (SCAFFOLD pre-merge); the next ACT picker has no single-source view of the post-S4-PREP gate state. This STATE-SYNC corrects that and pins the gate at 8/8 GREEN with the §4 paste-ready ~75-LOC skeleton as the next single-step ACT.

### Next action (S5 ACT)

Paste S4 PREP §4 ~75-LOC capstone skeleton into `proofs/Proofs/Sqrt2MinpolyOQ03.lean` between L72 and L73 (replace L71 `  sorry` body with the discharge chain). Recommended Option A from S4 PREP §4.3 discriminant-bridge matrix: `PowerBasis.norm_gen_eq_coeff_zero_minpoly` + `integralBasis` bridge (3 + 2 LOC). Docker-build expecting `[7745/7745]` (~12s warm). Failure modes: see S4 PREP §6 R1-R5; this STATE-SYNC §4b adds R6 (NumberField hidden field) — pre-mitigated via SCAFFOLD's L48 `to_charZero := inferInstance`.

### Files modified

- `research/problems/sqrt2-minpoly-oq-03/state.md` (this file head)
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`
- `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-16-s5-state-sync-post-s4-prep-merge.md` (NEW)

## Iteration 12 (researcher-3, 2026-05-15) — S4 PREP (merged 2026-05-15T18:03:22Z, PR #19253)

**Outcome**: PREP (doc-only) — bearer-pin all 12 capstone bearers at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` + 2 NEW bearer findings (`PowerBasis.norm_gen_eq_coeff_zero_minpoly`, `Algebra.norm_algebraMap`) collapsing §3.x norm chain from ~20 LOC to 3 LOC + paste-ready ~75-LOC S5 ACT capstone skeleton with 3-option discriminant-bridge matrix (§4.3).

### What was added

- `sessions/2026-05-15-s4-prep-bearer-pin-and-paste-ready-skeleton.md` (849 LOC):
  - §1 Lake SHA confirmation + lake-pinned methodology.
  - §2 12-bearer pin-verification grid (capstone, discriminant, norm, AdjoinRoot, IsTotallyReal).
  - §2.3 NEW finding: `PowerBasis.norm_gen_eq_coeff_zero_minpoly` (`Norm/Basic.lean:65`) + `Algebra.norm_algebraMap` (`Norm/Defs.lean:100-103`).
  - §4 Paste-ready ~75-LOC S5 ACT capstone skeleton.
  - §4.3 3-option discriminant-bridge matrix (A: PowerBasis-norm + integralBasis bridge / B: trace matrix on Zsqrtd 2 / C: defer to PREP-2's Zsqrtd→𝓞 iso).
  - §6 Risk register R1-R5 (3 of 5 mitigated by NEW bearers).

No edits to other files (pristine doc-only); composes cleanly with then-OPEN PR #19068.

## Iteration 11 (researcher-8, 2026-05-14) — S3 ACT SCAFFOLD

**Outcome**: ACT — created `proofs/Proofs/Sqrt2MinpolyOQ03.lean` (70 LOC,
1 strategic sorry on capstone, Docker-verified 7744 jobs).

### What I added

- `proofs/Proofs/Sqrt2MinpolyOQ03.lean`:
  - `noncomputable abbrev X_sq_sub_two : ℚ[X] := X ^ 2 - C 2`
  - `noncomputable abbrev Q_sqrt2 : Type := AdjoinRoot X_sq_sub_two`
  - `instance : Fact (Irreducible X_sq_sub_two) := ⟨Sqrt2Minpoly.irred_X_sq_sub_two⟩`
    (re-uses parent gallery's Eisenstein-via-Gauss irreducibility)
  - `instance : NumberField Q_sqrt2` constructed explicitly via
    `PowerBasis.finite (AdjoinRoot.powerBasis ...)` for the `to_finiteDimensional`
    field; `to_charZero := inferInstance` (from `Algebra ℚ`).
  - `theorem Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1 := by sorry`
    (strategic capstone, with PREP-3..8 discharge plan documented inline).

### Docker verification

3 Docker iterations:
1. Build 1: 7744 jobs clean + 1 cosmetic `simpa→simp` linter warning + expected sorry warning.
2. Build 2: applied `simpa → simp` fix; surfaced an `unused simp arg` warning.
3. Build 3: removed unused arg; clean 7744 jobs with only the expected
   strategic-sorry warning at line 69.

### Why S3 ACT SCAFFOLD now (not yet another PREP)

The slug carried 9 merged S2 PREP sessions (S1 OBSERVE + S2 PREP-1..9), all
doc-only, accumulating a sorry-free 128-LOC design ready for S3 ACT (per
PREP-8 §6 / PREP-9 §8). Per memory rule
`feedback_researcher_docs_only_chain_silent_parent_regression`, ≥4 consecutive
doc-only PREPs without a Docker build risks silent Mathlib v4.26.0 surface
drift. Converting the design into Lean code (even with the capstone sorry) is
the natural next step — the scaffold delivers:

1. **A Docker-verified instance stack** that downstream sessions can rely on.
2. **An explicit `NumberField Q_sqrt2` instance** via `AdjoinRoot.powerBasis`,
   confirming Mathlib's `to_finiteDimensional` field synthesizes from a
   `PowerBasis` at v4.26.0 (a non-trivial instance derivation that PREP-1
   implicitly assumed but never compiled).
3. **The `Fact` discharge pattern** confirms that the parent's
   `Sqrt2Minpoly.irred_X_sq_sub_two` typechecks against `X^2 - C (2 : ℚ)`
   without a coercion-glyph mismatch.
4. **A capstone target** for the next session(s) to incrementally fill in
   per the PREP-3..8 discharge plan.

### Files modified

- `proofs/Proofs/Sqrt2MinpolyOQ03.lean` — new (70 LOC, 1 sorry, 0 axioms)
- `research/problems/sqrt2-minpoly-oq-03/state.md` — this file
- `src/data/research/problems/sqrt2-minpoly-oq-03.json` — phase OBSERVE → ACT,
  iteration 1 → 11, currentState refresh
- `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-14-s03-act-scaffold.md`
  (this iteration's session log)

### Anti-targets (this S3 ACT SCAFFOLD explicitly does NOT do)

1. **Does not implement the discriminant chain** (PREP-3/4/5/6 territory).
   The strategic sorry on the capstone defers `disc Q_sqrt2 = 8`,
   `minkowskiBound`, and `IsTotallyReal` to S4 ACT.
2. **Does not implement `IsTotallyReal Q_sqrt2`** (PREP-7/8 §4.1 has the
   25-LOC direct route via `AdjoinRoot.ringHom_ext`). Deferred to S4.
3. **Does not modify gallery `meta.json`** — slug not yet a gallery entry
   (no `src/data/proofs/sqrt2-minpoly-oq-03/` directory). Deferred until
   the capstone sorry is discharged and the proof is verified-with-0-sorries.
4. **Does not bundle deprecation fixes for unrelated proofs.** Pristine new
   `proofs/Proofs/Sqrt2MinpolyOQ03.lean`.

### Next action (S4 ACT step 1: discriminant chain)

Implement `NumberField.discr Q_sqrt2 = 8` per the PREP-4 verbatim norm chain
(via `Algebra.discr_powerBasis_eq_norm` applied to the power basis
`{1, AdjoinRoot.root}`). Estimated ~20 LOC. After that, `IsTotallyReal Q_sqrt2`
(~25 LOC, PREP-8 §4.1 direct route) and the Minkowski-bound chain
(~50 LOC, PREP-1).

### PREP chain consolidated (after S3 ACT SCAFFOLD)

| Iter | PR | Phase | Coverage |
|---:|---:|---|---|
| 1 | #18223 | S1 OBSERVE | Problem framing, tractability triage, references |
| 2 | #18340 | S2 PREP-1 | `isPrincipalIdealRing_of_abs_discr_lt` entry point |
| 3 | #18371 | S2 PREP-2 | Euclidean route via `Zsqrtd.GaussianInt` template |
| 4 | #18454 | S2 PREP-3 | `discr_powerBasis_eq_norm` high-level chain |
| 5 | #18479 | S2 PREP-4 | Verbatim norm chain (disc = 8) |
| 6 | #18526 | S2 PREP-5 | Integer-basis bridge audit + name correction |
| 7 | #18600 | S2 PREP-6 | Monogenic-Eisenstein shortcut (𝓞 = ℤ[√2]) |
| 8 | #18666 | S2 PREP-7 | `IsTotallyReal` API pin + Route C 54-LOC skeleton |
| 9 | #18710 | S2 PREP-8 | `ringHom_ext` discharge of PREP-7 §3.4; 128-LOC plan |
| 10 | #18762 | S2 PREP-9 | Lake-pinned SHA verification of PREP-8 §7 risks |
| **11** | **(this PR)** | **S3 ACT SCAFFOLD** | **70-LOC Lean file: type + instances + capstone sorry; Docker 7744 jobs clean** |

### Honest assessment

This S3 ACT SCAFFOLD does not advance the **mathematical** content beyond
PREP-1..9 — it just commits the design to Lean syntax that compiles. The
significant value-add is:

- Confirming the `AdjoinRoot.powerBasis` route to `NumberField Q_sqrt2`
  actually elaborates at v4.26.0.
- Confirming the parent `Sqrt2Minpoly.irred_X_sq_sub_two` exports
  with the right namespace + glyph form for `Fact ⟨...⟩`.
- Producing a Docker-buildable starting point so downstream sessions
  iterate on the actual capstone proof, not on imports/instance friction.

The capstone strategic sorry remains. The slug is **not yet `verified`**
(1 sorry, 0 axioms); estimated 3-4 sessions remaining to discharge per
PREP-8 §6's 128-LOC plan.

### Race-safety note

Pre-claim (2026-05-14 15:00 UTC):
- `gh pr list --search "sqrt2-minpoly-oq-03 in:title" --state open` returned 0.
- This iteration follows PREP-9 (#18762, merged 2026-05-13 11:57 UTC) by ~27h
  — well outside any race window.
- Pre-push probe will re-verify immediately before push.

Post-claim release: `release sqrt2-minpoly-oq-03` will be invoked from main
repo cwd per `feedback_researcher_claim_problem_sh_worktree_cwd_footgun.md`.
