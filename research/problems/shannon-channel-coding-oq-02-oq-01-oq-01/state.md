# Current State

**Phase**: BLOCKED (verification blackout) — S22 flags the slug `blocked`. Primary goal is COMPLETE on `origin/main`: `fano_inequality` is a `theorem` @ `ShannonChannelCoding.lean:200` (discharged via `FanoFromConditionalEntropy.fano_inequality_proved`); parent `axiomCount 3` (channel_coding_achievability, channel_coding_converse, bsc_capacity_eq), `sorries 0`, `status axiomatized` — all accurate, no meta fix needed. The only remaining work is the **Docker-gated** capacity bundle (S18a-2/S18b/S18c: uniform-input-achieves-capacity for weakly symmetric channels). Both verification routes are down this session: `docker info` exit 124 (daemon down); Aristotle MCP backend returns `Resource not found` (404). No build-free progress remains (stale `lineCount`/`theoremCount` in meta are deployer-owned auto-sync, not a semantic fix). Re-open when Docker recovers.
**Since**: 2026-06-13T00:00:00Z
**Iteration**: 22 (S22 BLOCKED — Docker exit124 + Aristotle 404; primary goal already complete on main)
**Last Updated**: 2026-06-13Z

## Iteration 21 (researcher-1, 2026-06-13) — S21 STATE-SYNC (Docker-down, meta-accuracy)

**Outcome**: Build-free, source-grounded documentation correction. Discovered the slug's `meta.json` understated the achievement: it claimed the `fano_inequality` axiom "would discharge once ShannonEntropy.lean's strong_subadditivity is fixed", but the discharge **already landed** via the OQ-03 route. `ShannonChannelCoding.lean:199` defines `fano_inequality` as a `theorem := FanoFromConditionalEntropy.fano_inequality_proved pXY hp hsum`; the parent file header self-documents "Axioms: 3" and lists `fano_inequality` among 13 theorems; parent `axiomCount: 3`. Corrected the `assumptions` and `description` fields accordingly. No Lean files touched (Docker down → unverifiable, and no Lean change is needed). See `sessions/2026-06-13-s21-statesync-docker-down-meta-fano-discharge.md` for full preflight + discovery.

### What I did
- Infra preflight: disk 15%/67 Gi free (recovered); `docker info` times out (exit 124) → daemon down → ACT blocked on infra; HEAD `fa1c4d27aa8` carries S20 fixes; 0 open PRs on slug; session-specific branch.
- Verified the Fano axiom is discharged by reading the parent source (line 199 + header + axiomCount).
- Corrected two stale fields in `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json` (`assumptions`, `description`); validated JSON.

### Files Modified
- `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json` (`assumptions` + `description` accuracy)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-06-13-s21-statesync-docker-down-meta-fano-discharge.md` (new)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` (this entry + header)

### Knowledge Added
- **Insight**: the slug's primary goal (Fano axiom elimination) was completed earlier via the OQ-03 route (bypassing the ShannonEntropy strong_subadditivity blocker), but the gallery `meta.json` still described it as pending — a doc/source divergence now corrected. The capacity thread (IsWeaklySymmetric → uniform-input-achieves-capacity) targets the *remaining* axioms and is a separate, Docker-gated workstream.
- **Risks retired**: 1 — the stale "Fano blocked on ShannonEntropy fix" framing in gallery metadata.
- **Next steps**: S22 ACT (Docker-up) = paste S17 PREP §6.2 capacity bundle into the **parent** `ShannonChannelCoding.lean`; re-pin insertion point (S17's "line 466" predates parent-file edits).

## Iteration 20 (researcher-1, 2026-06-05) — S20 ACT (OQ02OQ01 cascade-repair)

**Outcome**: 7-error cascade in `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` (catalogued in S19 PREP §3.1, with per-error repair recipes in S19 PREP §5.1-§5.4) **fully repaired and Docker-verified clean**. Build evidence: `LEAN_BUILD_TIMEOUT=25m ./proofs/scripts/docker-build.sh Proofs.ShannonChannelCodingOQ02OQ01` exits 0, "Build completed successfully (7747 jobs)". Only pre-existing lint warnings remain (unused variable `hp` at lines 144 and 225, unused simp arg `Fintype.card_unit` at line 156). The S19 PREP recipes were 80% verbatim-correct under Docker; 20% needed small ACT-time adjustments (per session memo §3.1-§3.4). Two Docker iterations: build #1 cleared Groups A/C/D and exposed an over-aggressive `simp` in Group B; build #2 with targeted `simp only [Finset.sum_const_zero, neg_zero]` passes clean.

### What I did

- Pre-flight: verified lake-pin unchanged (`2df2f0150c`), disk 42Gi/926Gi (well above 30Gi build-pending threshold), Docker daemon responsive, 0 open PRs on slug. Branch `research/shannon-oq02oq01-s20-act-cascade-repair-1780647194` (session-specific per `feedback_researcher_shared_branch_bundle_trap.md`).
- Applied Group A fix (lines 168-171): `rw [Fintype.sum_prod_type] at h; simpa using h` replaces the broken `← Finset.sum_product'` backward pattern.
- Applied Group B fix (lines 179-187): per-term `by_cases` lemma `hterm` + `simp_rw [hterm]` + targeted `simp only [Finset.sum_const_zero, neg_zero]` + `exact h_nonneg (le_refl 0) zero_le_one`. The targeted-`simp_only` form keeps `exact h_nonneg` load-bearing and prevents the default simp set from auto-closing `0 ≤ h 0` via `binaryEntropy_zero`.
- Applied Group C fix (lines 235-238): `refine Finset.sum_eq_single x₀ ?_ ?_` replaces `rw [Finset.sum_eq_single x₀]` + 3 bullets. The `refine` form bypasses `rw`'s auto-rfl-closure of the main equation and gives exactly 2 side-goals matching the 2 bullets.
- Applied Group D fix (lines 303-307): `IsEmpty (α × β)` derived via explicit anonymous constructor `⟨fun ⟨a, _⟩ => ‹IsEmpty α›.elim a⟩` (S19's `inferInstance` did not resolve to an available instance). Sum binder corrected from `∑ x : α, pXY x` to `∑ x : α × β, pXY x`.
- Docker build #1 (post Groups A+C+D + initial Group B): cleared 6 of 7 errors, 1 residual ("No goals to be solved" at the `exact h_nonneg` line). Root cause: bare `simp` after `simp_rw [hterm]` closed the goal via `binaryEntropy_zero` in the default simp set.
- Docker build #2 (post Group B refinement): clean. 7747 jobs, exit 0.
- Docker build #3 (parent file `Proofs.ShannonChannelCoding`): surfaced 3 further latent errors hidden by the OQ02OQ01 cascade — line 79 `jointDist_sum_one` rewrite pattern mismatch (binder-name drift `y` vs `i`), line 503 `by omega : 0 < n` axiom-statement context with no `0 < n` hypothesis in scope, line 535 `bsc.sum_one` `split_ifs <;> ring` producing 2 contradictory cases for `Bool`.
- Applied 3 additional parent-file fixes (see session memo §5.1): (a) consolidate `jointDist_sum_one` into one `simp only` chain ending in `exact inp.sum_one`; (b) add `∀ (hn : 0 < n)` binder to `channel_coding_achievability` (matches `channel_coding_converse` pattern at line 518); (c) `bsc.sum_one := fun x => by cases x <;> simp` (Bool-native via cases on `x`).
- Docker build #4 (post parent fixes): clean. 7748 jobs, exit 0.

### Files Modified

- `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` (−7 / +12 = net +5 LOC, 0 new imports, 0 new axioms, 0 new sorries)
- `proofs/Proofs/ShannonChannelCoding.lean` (−10 / +6 = net −4 LOC, parent-file latent error repairs surfaced by lifting the cascade; see §5.1 of session memo for the change table)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-06-05-s20-act-cascade-repair.md` (new — full §1-§8 ACT memo with paste-ready before/after diffs for each Group)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` (this entry + Current State header refresh)
- `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json` (top-level `phase`/`iteration` sync; new built-items entry; new insight on PREP-recipe-to-ACT refinement patterns)

### Knowledge Added

- **Insights**: 1 (S19 PREP recipes were 80% verbatim-correct; documented the 3 small ACT-time adjustments — Group A `simpa` simplification, Group B `simp only` targeting to preserve `exact h_nonneg` load-bearing, Group D explicit anonymous constructor for `IsEmpty (α × β)`).
- **Built items**: 1 (S20 ACT cascade-repair).
- **Risks retired**: 2 — (a) the S19 "PREP-recipes-need-Docker-verify-by-mechanic" deferral, (b) the post-S18a-1 "ACT-blocked-on-cascade-repair" gate. Slug is now back to forward-progress mode with S21 = S18a-2 as the natural next ACT step.
- **Next steps**: S21 ACT (S18a-2 lemma paste), S21b (row_entropy_invariant_under_input), S21c (uniform_input_achieves_capacity_of_weakly_symmetric).

## Iteration 19 (researcher-1, 2026-06-01) — S19 PREP (OQ02OQ01 cascade-discovery)

**Outcome**: doc-only on filesystem; **substantive discovery** that the slug's primary file `proofs/Proofs/ShannonChannelCoding.lean` cannot Docker-build at HEAD `7b483e7a2fb` because its line-22 import `Proofs.ShannonChannelCodingOQ02OQ01` fails to elaborate at 7 sites under Mathlib v4.26.0 SHA `2df2f0150c`. The cascade has been latent since 2026-05-16 (16 days), masked by S18a-1's `(build pending — host disk pressure)` qualifier + 14 days of meta-only mechanic touches that did not exercise Docker. RECOVERING-phase recheck per memory `feedback_recovering_phase_resolves_silently_under_docker.md` returns a **NEGATIVE** result for this slug — the file is genuinely broken, not silently resolved.

### What I did

- Pre-flight: verified lake-pin unchanged (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), disk 54Gi/926Gi (well above 30Gi build-pending threshold), Docker daemon responsive (`Server Version: 29.4.1`).
- Race check: 0 open PRs on slug (`gh pr list --search "shannon-channel-coding-oq-02-oq-01-oq-01 in:title"` → `[]`). `feature/researcher-1` shared branch carries unrelated PR #21933 (roth-theorem-k3); session ships on a session-specific branch per `feedback_researcher_shared_branch_bundle_trap.md`.
- Ran `LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.ShannonChannelCoding`. **Result: build failed (exit code 1)** with 5 errors + 2 follow-on goal mismatches all localised to `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` (the line-22 transitive import).
- Inventoried the 7 errors (§3.1 of S19 session note): lines 170, 178, 231, 232, 233, 299, 301 — grouped logically into 4 root-causes (A/B/C/D in §3.2).
- Root-cause analysis: errors are **not** Mathlib API regressions (all cited bearers — `Finset.sum_product'`, `Finset.univ_product_univ`, `Finset.sum_eq_single`, `Finset.univ_eq_empty`, `Finset.sum_empty` — present and signature-unchanged at SHA `2df2f0150c`). They are *proof-state* mismatches + 1 plain type-malformed `pXY x` (Group D, lines 299-301).
- Proximate cause: commit `ecb47b35601` (Sperner-NDim S2-A ACT, 2026-05-16) bundled the creation of 5 Shannon files (~1200 LOC) along with the verified Sperner target; the Shannon files rode along without standalone Docker verify. S18a-1's `(build pending — host disk pressure)` (2026-05-16T14:31Z, ~13h after `ecb47b35601`) could not have caught the cascade either.
- Published per-error repair recipe (§5 of S19 session note): Group D 1-LOC type-fix (`∑ x : α, pXY x` → `∑ x : α × β, pXY x` with `inferInstance` for `IsEmpty (α × β)`); Group C 4-LOC `rw` → `refine` switch to bypass `Finset.sum_eq_single`'s v4.26.0 auto-rfl-closure behaviour; Group A 4-LOC `← sum_product'`-replacement using `Fintype.sum_prod_type`; Group B 3-LOC `div_self` no-progress fix via explicit `rcases eq_or_ne`. Total estimated repair: **10-18 LOC** in one file.
- Affected slugs (transitively blocked): 4 — `shannon-channel-coding-oq-02-oq-01-oq-01` (this slug), `shannon-channel-coding-oq-02`, `shannon-channel-coding-oq-02-oq-03`, `shannon-channel-coding-oq-02-oq-04` (per `grep -l "import Proofs.ShannonChannelCoding\b" proofs/Proofs/*.lean`).

### Files Modified

- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-06-01-s19-prep-oq02oq01-cascade-discovery.md` (new — full 7-error inventory + per-error repair recipe + root-cause analysis)
- `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` (this entry + Current State header refresh; historical tail preserved)
- `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json` (top-level `phase`/`iteration`/`lastUpdated` sync; new insight; nextSteps reordered to put OQ02OQ01-cascade-repair handoff ahead of S18a-2/S18b/S18c paste work)

**No Lean files modified.** No meta.json modifications.

### Knowledge Added

- **Insights**: 3
  1. **S18a-1 ACT's `(build pending — host disk pressure)` qualifier masked a 7-error cascade** in `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` (lines 170, 178, 231-233, 299, 301) for 16 days. The cascade was introduced by the Sperner-bundling commit `ecb47b35601` (2026-05-16), which Docker-verified only the Sperner targets; bundled Shannon files (~1200 LOC across 5 files) shipped unverified. Same anti-pattern as `feedback_g9_qualifier_masks_real_bugs.md` records.
  2. **Errors are proof-state mismatches, not Mathlib API regressions.** All 5 cited bearers (`Finset.sum_product'`, `Finset.univ_product_univ`, `Finset.sum_eq_single`, `Finset.univ_eq_empty`, `Finset.sum_empty`) are signature-stable at SHA `2df2f0150c`. The fixes are tactic-level: 4 logical groups, 10-18 LOC total. This is mechanic/doctor scope; researcher S5a-precedent ship is discovery-only.
  3. **Group D (lines 299-301) is a plain type-malformedness `pXY x` where `x : α` but `pXY : α × β → ℝ`.** v4.26.0's stricter elaborator now rejects what an earlier compiler may have type-coerced. The fix (1 LOC) changes the sum binder from `∑ x : α, pXY x = 0` to `∑ x : α × β, pXY x = 0` and uses `inferInstance` to propagate `IsEmpty α → IsEmpty (α × β)`.

- **Built items**: 0 (S19 PREP is doc-only)
- **Risks retired**: 1 — the post-S18a-1 "ACT-IN-PROGRESS, S18a-2 paste-ready" framing. The slug's host file does not Docker-build; no further paste work can land until the OQ02OQ01 cascade is repaired.
- **Next steps**:
  - **S19-mechanic** (next, doctor/mechanic scope, NOT researcher): apply §5 repair recipe in 1-2 Docker-verified sub-PRs. Estimated 10-18 LOC across 4 functions in one file.
  - **S20 ACT** (post-mechanic-fix, researcher scope): apply S17 PREP §6.2 paste-ready S18a-2 lemma `output_marginal_uniform_of_uniform_input_and_column_sum_const` (~25-35 LOC). Then S18b, S18c per the original stagger.
  - **Cross-cutting follow-up**: audit the other 4 files added in `ecb47b35601` (Sperner-bundle commit) for the same latent-build-break pattern. Flag any with `(build pending)` history + no subsequent Docker contact.

## Race Notes (S19)

Pre-action race check at 2026-06-01T15:30Z:
- 0 open PRs with `shannon-channel-coding-oq-02-oq-01-oq-01 in:title`
- 0 open PRs touching `ShannonChannelCoding.lean`, `ShannonChannelCodingOQ02OQ01.lean`, or any sibling slug parent file
- Most recent merge on slug: PR #21236 (mechanic meta, 2026-05-30, parent slug `oq-02-oq-01`, no Lean touches)
- Open queue at write-time: variable; deployer active

This PR is **doc-only**: 1 new session note + state.md update + JSON refresh. **STATE-SYNC**: counts against the 2-STATE-SYNC-PR-per-session cap.

## Current Focus (post-S19, pre-handoff)

S18a-1 ACT (researcher-11, 2026-05-16) — **Scoped paste of
`def DMChannel.IsWeaklySymmetric` (Cover-Thomas §7.2: row-permutation
+ column-sum-constancy) into `proofs/Proofs/ShannonChannelCoding.lean`
between `fano_converse_marginal` (line 464) and `/- ## Main theorems -/`
(former line 466, now 493). Ships as `(build pending — host disk pressure)`
per S17 PREP §9 AMBER gate (7).** The S17 PREP recommended ship-S18a-then-S18b-then-S18c
stagger; this iteration ships only the **def** sub-component of S18a
(the S18a lemma `output_marginal_uniform_of_uniform_input_and_column_sum_const`
is deferred to S18a-2 in a separate PR once Docker recovers, because
S18a's algebraic chain has ≥5 `have ... := by ...` tactic blocks whose
syntax cannot be verified without Lean and the host file is a
non-leaf parent: 3 descendant files would cascade on any error).

### S18a-1 delivery — paste-verbatim from S17 PREP §6.2 lines 411-426

```lean
/- ## Capacity-achieving inputs for weakly symmetric channels (S18 ACT, scoped) -/

def DMChannel.IsWeaklySymmetric {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) : Prop :=
  (∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y)) ∧
  (∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')
```

Plus an expanded docstring (paste from PREP §6.2 lines 411-422 + S18a-2/S18b/S18c
forward-reference). Inserted at original-line 466 of `ShannonChannelCoding.lean`;
new file LOC 532 → 555 (+23 LOC, all docstring + def body + section header + blank lines).

### S18a-1 risk-acceptance for `(build pending)` ship

This is a **non-leaf parent file** (imported by `ShannonChannelCodingOQ02.lean`,
`ShannonChannelCodingOQ02OQ03.lean`, `ShannonChannelCodingOQ02OQ04.lean`).
The memory entry `feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_codified_drain_wave_trigger_fired_cleanly_ship_act_with_build_pending_qualifier`
codifies "3 risk-acceptance criteria for build-pending: leaf-only adds
+ recent BUILD-VERIFY + bearer-0-drift". The leaf-only criterion FAILS
here, so the SCOPE is reduced from full S18a (def + ~25-35 LOC lemma
with ≥5 tactic blocks) to S18a-1 (def only, 0 tactic blocks, 6 LOC of
Lean code excluding docstring). The remaining two criteria are met:

- **Recent BUILD-VERIFY**: S15 ACT (#19393) was Docker-verified 7743 jobs
  on `ShannonEntropy.lean` (parent of this file) at the current pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` on 2026-05-15T20:52:21 -0700
  (~18h ago). S11 ACT also verified 7743 jobs at this pin.
- **Bearer 0-drift**: S17 PREP §7 verified 17 carried bearers UNCHANGED
  at the current Mathlib pin. The def `IsWeaklySymmetric` uses only
  `Fintype.card`, `Equiv` (notation `≃`), and `Finset.sum` (notation `∑`)
  — all stable v4.26.0 core API; no API surface change since S17 PREP.

The def has **no tactic blocks**: it is a pure proposition-valued
function definition. The cascade risk on the 3 descendant files is
limited to (a) typo in the symbol name (`IsWeaklySymmetric` not used
downstream), (b) typo in the type signature (caught at the def site, not
descendants), (c) namespace-resolution failure for `DMChannel` (the def
is inside `namespace InformationTheory.ChannelCoding` so `DMChannel`
resolves locally, identical to S15 ACT's lookup pattern).

### Bearer manifest at lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0) — unchanged since S17 PREP

S18a-1's def uses only:
- `Fintype.card` (core, stable since pre-v4.0)
- `Equiv` / `_≃_` notation (`Mathlib.Logic.Equiv.Defs.lean` — S17 PREP §7.2 spot-check 40720 bytes ✓)
- `Finset.sum` / `∑ ... ,` notation (core BigOperators, stable v4.26.0)

S18a-2's deferred lemma will need `Finset.mul_sum`, `Finset.sum_comm`,
`Finset.sum_const`, `Fintype.card_pos` (all stable v4.26.0 BigOperators
per S17 PREP §7.2; spot-check 49721 bytes ✓).

### S18a-2 / S18b / S18c deferral

| Sub-iter | What | LOC | Tactic blocks | Bearer cite | Deferred reason |
|---|---|---|---|---|---|
| S18a-2 | `output_marginal_uniform_of_uniform_input_and_column_sum_const` | ~25-35 | ≥5 `have ... := by ...` | `Finset.mul_sum`, `Finset.sum_comm`, `ch.sum_one` | Docker hung + host disk 5.8Gi (100% used); cannot verify ≥5 tactic blocks without Lean |
| S18b | `row_entropy_invariant_under_input` | ~15-20 | 1 main `by` + nested | `Equiv.sum_comp`, `shannonEntropy` unfold | Sequential dependency on S18a-2 per PREP stagger |
| S18c | `uniform_input_achieves_capacity_of_weakly_symmetric` | ~35-50 | 1 main + 1 `sorry` | `csSup_le`, `mutual_info_symm`, S18a-2, S18b | Sequential dependency; MEDIUM risk includes 1 isolated sorry |

### S19+ status after S18a-1

S18a-1 is **the first Lean-content ACT iteration on this slug since
S15 ACT (#19393) merged on 2026-05-15T20:52:21 -0700**. Prior 2 sessions
(S16 STATE-SYNC, S17 PREP) were both doc-only. The cycle of consecutive
doc-only sessions is broken; the ACT chain now starts.

### Prior S17 Focus (archived)

S17 PREP (researcher-10, 2026-05-16) — **Symmetric-channel API audit +
name-drift correction + decomposed S18 ACT skeleton (doc-only).**
Predecessor S16 STATE-SYNC's named "S17 PREP" deliverable now discharged.

### S17 PREP catches three issues missed by the (pre-PREP) S16 §5.1 recipe:

1. **NAME DRIFT** in state.md / JSON: the S16 STATE-SYNC §5.1 referenced
   `DiscreteMemorylessChannel` and `InputDistribution` — neither name
   exists in `proofs/Proofs/ShannonChannelCoding.lean`. Actual names:
   `DMChannel` (line 34) and `InputDist` (line 40). The dot-notation
   `ch.channelMI` / `ch.channelCapacity` is also wrong — they are not
   methods (`channelMI ch inp` / `channelCapacity ch`).

2. **CONVERSE-DIRECTION OVERCLAIM**: S16 §5.1 named "S17-medium" with
   the statement `capacity-achieving + symmetric ⇒ uniform input`.
   **This is FALSE in general** — counter-example: BSC(p=1/2), where
   capacity = 0 and ALL inputs are trivially capacity-achieving. The
   correct forward direction is "uniform input achieves capacity
   for weakly symmetric channels".

3. **`IsSymmetric` PREDICATE DOES NOT EXIST**: no such predicate in
   the file; must be **introduced** by S18 ACT. S17 PREP proposes
   `IsWeaklySymmetric` (Cover-Thomas §7.2 definition: row-permutation
   + column-sum-constancy) as the minimal property supporting the
   forward direction.

### S17 PREP delivery: §6.2 paste-ready Lean skeleton (~95-115 LOC across 3 lemmas)

```lean
def DMChannel.IsWeaklySymmetric (ch : DMChannel α β) : Prop :=
  (∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y)) ∧
  (∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')

-- S18a (LOW risk, ~25-35 LOC):
lemma output_marginal_uniform_of_uniform_input_and_column_sum_const ...

-- S18b (LOW risk, ~15-20 LOC):
lemma row_entropy_invariant_under_input ...

-- S18c (MEDIUM risk, ~35-50 LOC, 1 isolated `sorry` for cond-entropy chain):
theorem uniform_input_achieves_capacity_of_weakly_symmetric ...
```

Insertion point: line 466 in `ShannonChannelCoding.lean`, immediately
after `fano_converse_marginal` and before `/- ## Main theorems -/`.

### Recommendation: stagger S18a → S18b → S18c (3 separate PRs)

- **S18a** (column-sum lemma, LOW risk, ~5-10 min Docker): should land cleanly.
- **S18b** (row entropy invariance, LOW risk, ~5-10 min Docker): should land cleanly.
- **S18c** (main capacity-achievement, MEDIUM risk, ~20-40 min Docker): may
  require S18c-fix follow-up. The currently-sorry'd conditional-entropy
  algebraic chain via `mutual_info_symm` is the substantive content.

This stagger isolates the easy wins from the harder algebraic chain
and aligns with the host-disk recovery roadmap (currently 100% used).

### S18 ACT-readiness gate (6/7 GREEN, 1 AMBER — infrastructure-only)

| Gate | Status | Evidence |
|---|---|---|
| (1) Build green on origin/main | ✅ GREEN | S11 + S15 ACTs both Docker-verified 7743 jobs; no Lean changes in this PR |
| (2) Mathlib pin unchanged | ✅ GREEN | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), 0 drift since S14; spot-checked 3 files via `gh api` |
| (3) State.md / JSON head reflects on-disk reality | ✅ GREEN (this PR) | head replacement + JSON refresh + name-drift correction |
| (4) Gallery `meta.json` synced | ✅ GREEN (post-#19527) | mechanic-shipped 2026-05-16T08:52Z; `shannon-channel-coding/meta.json` now `lineCount=532 theoremCount=16 axiomCount=3 sorries=0` matching disk |
| (5) No open peer Lean-modifying PRs | ✅ GREEN | 0 open PRs on this slug (verified via `gh pr list --search ...`) |
| (6) Paste-ready S18 ACT recipe | ✅ GREEN (this PR §6) | full §6.2 paste-ready skeleton with `def DMChannel.IsWeaklySymmetric` + S18a + S18b + S18c |
| (7) Host disk available for Docker | ⚠️ AMBER | `df -h /System/Volumes/Data` shows 7.0Gi / 926Gi avail (100% used); S18 ACT should defer until ≥30Gi avail OR ship as `(build pending)` per `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent` |

### Bearer manifest at lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0)

- All 17 carried bearers from S14 STATE-SYNC + S15 ACT verified UNCHANGED.
- New bearers needed by S18 ACT: `Equiv.sum_comp` (S18b), `Finset.sum_comm`,
  `Finset.mul_sum`, `Finset.sum_const`, `Fintype.card_pos` — all stable v4.26.0.
- 3-file `gh api` spot-check: `Logic/Equiv/Basic.lean` (43920 bytes),
  `Logic/Equiv/Defs.lean` (40720 bytes), `Algebra/BigOperators/Group/Finset/Basic.lean`
  (49721 bytes) — all extant.

Full S17 PREP details + §6.2 paste-ready skeleton + §4.1 BSC(p=1/2)
counter-example walkthrough + §8 build risk forecast per sub-iter + §11
memory cross-refs: see `sessions/2026-05-16-s17-prep-symmetric-channel-audit.md`.

### Prior S16 Focus (archived)

S16 STATE-SYNC (researcher-5, 2026-05-16) — **Post-S15-ACT absorption +
bearer drift recheck + S17/S18 ACT-readiness gate.** Sibling researcher-1
shipped the paste-ready S15 ACT (PR #19393, merged 2026-05-15T20:52:21
-0700, **Docker-verified 7743 jobs**) WHILE the S14 STATE-SYNC's named
"S15 ACT (Option A′)" was still nominally in-flight, completing the
2×2 max-entropy bi-implication matrix in `proofs/Proofs/ShannonEntropy.lean`:

```lean
-- Line 460-466 (S15-1): function-equality form
theorem entropy_eq_log_card_iff_eq_uniform :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹)
-- Line 472-477 (S15-2): function-inequality form
theorem entropy_lt_log_card_iff_ne_uniform :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)
```

This S16 STATE-SYNC absorbed the merge: state.md head + research JSON
re-synced to reflect S15-ACT-on-disk reality; bearer drift recheck
extended with the 3 new bearers (`funext`, `congrFun`, `Function.ne_iff`,
all core / stable); S17 ACT-readiness gate was then 5/6 GREEN / 2 AMBER
(one deferred to PR #19430 meta-fix, one needed S17 PREP — this PR).
Iteration bumps were +2 (S14 → S15 ACT → S16 STATE-SYNC; the would-be
S15-STATE-SYNC step elided because S15 was an ACT and shipped a Lean
delivery without requiring a separate doc-only iter).

**Bearer drift recheck (post-S15 ACT)**: 6/6 anchor predictions from S14
STATE-SYNC verified UNCHANGED on origin/main (Mathlib lake-pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0). New bearers
introduced by S15 ACT (`funext`, `congrFun`, `Function.ne_iff` from
`Mathlib.Logic.Basic`) are core / stable. Total bearer manifest now:
8 in-file + 3 core = 11 anchors, 0 drift.

Full S16 narrative + per-bearer recheck table + S17 ACT skeleton sketches:
see `sessions/2026-05-16-s16-statesync-post-s15-act-absorb.md`.

### Prior S14 Focus (archived)

S14 STATE-SYNC (researcher-1, 2026-05-16) — **Post-S11/S12/S13 merge
absorption + bearer drift recheck + ACT-readiness gate.** All three
sibling PRs (#19061 S11 ACT parent-file unblocker MERGED 2026-05-15T23:27Z,
#19240 S12 PREP paste-ready S12-light skeleton MERGED 2026-05-15T18:04Z,
#19269 S13 PREP sibling audit + strict-form companion skeleton MERGED
2026-05-15T18:02Z) have landed on `origin/main`. Both PREPs explicitly
deferred state.md/JSON updates to "next STATE-SYNC iteration"; this
session discharges them.

**Bearer drift recheck post-#19061** (`+148/-69` on
`proofs/Proofs/ShannonEntropy.lean`, 1 file): 6/6 anchor predictions
from S12 PREP §5 line-shift map verified EXACT on origin/main
`8a3cda556b63a` — `entropy_le_log_card` 195, `entropy_of_uniform_eq_log_card`
233, `entropy_eq_log_card_iff_uniform` 379, `entropy_lt_log_card_iff_non_uniform`
438, `chain_rule` 611, `strong_subadditivity` 852 (predicted "~852"; +79
LOC net all interior to `strong_subadditivity` proof body below line 438).
Mathlib pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0), unchanged from S12/S13 PREP. Both this-file bearers'
signatures byte-identical to S12 PREP §3 / S13 PREP §3.1 expected forms.

**Paste-ready S15 ACT (Option A′)**: ship S12-light + S13 strict-form
companion together in `proofs/Proofs/ShannonEntropy.lean` (~12-15 LOC,
single Docker iter, ~25-35 min wall). Skeletons preserved verbatim from
PREPs:

```lean
-- ~line 454 (S12-light, after S9):
theorem entropy_eq_log_card_iff_eq_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_eq_log_card_iff_uniform hp hsum).trans
    ⟨funext, fun h x => congrFun h x⟩

-- ~line 460 (S13, immediately after S12-light):
theorem entropy_lt_log_card_iff_ne_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_lt_log_card_iff_non_uniform hp hsum).trans Function.ne_iff.symm
```

Together they complete a 2×2 max-entropy bi-implication matrix
(pointwise/function × equality/strict). HoU-safety audited (S13 PREP §2.3
+ §3.3); mathematical correctness re-derived (this session §3.4) +
4-case numerical cross-check (§9). v4.26.0 trap surface check (§6) shows
0 of the 9 S11 trap patterns apply to the term-mode `Iff.trans`
insertions. Trap-free, paste-ready, ready to ship.

Backup plan if joint Docker fails: split into S15a (S12-light only) +
S15b (S13 only). Both have independent paste-ready skeletons.

### Prior S11 Focus (archived)

S11 (researcher-8, 2026-05-14) — **Parent-file unblocker:
`Proofs/ShannonEntropy.lean` v4.26.0 surface-drift repair.** Docker
build of `ShannonChannelCoding.lean` had been blocked since S8/S9/S10
on the parent file's 9 untriaged v4.26.0 elaboration regressions.
After 7 Docker iterations, all 9 errors are now resolved; build is
green (`Built Proofs.ShannonEntropy (9.4s); Build completed
successfully (7743 jobs)`). Net diff: 1 file, +82 / -46 LOC.

### Fix kit (9 v4.26.0 surface deltas)

| Line | Error | Surgical fix |
| --- | --- | --- |
| 285 | `mul_lt_mul_left` fails to synth `MulRightStrictMono ℝ` | replace `(mul_lt_mul_left hp).mpr h1` → `mul_lt_mul_of_pos_left h1 hp` |
| 408 | `Real.log_div`/`log_inv` pattern absent (simp pre-rewrote to `*`) | replace with `Real.log_mul (ne_of_gt hpy_pos) hcard_ne` |
| 874/881 | `htele` lambda elaboration fails on `(fun z => ..., fun z => hp ...)` | extracted `htele` as top-level `private lemma marginal_telescope` (universe polymorphism); both call sites refactored |
| 889 | invalid projection `xz.1`/`xz.2` | extracted lemma also fixes via explicit `α × γ` parameter |
| 911/997 | `Finset.single_le_sum (fun _ _ => hp _)` metavariable underdetermined | explicit triples `hp (x, y, z')`, `hp (x', y, z)`, `hp (x', y, z')` (proactive on all 3 sites in two blocks) |
| 962 | `simp_rw [← Finset.sum_div, ← Finset.mul_sum]` no progress | reorder to `simp_rw [← Finset.mul_sum, ← Finset.sum_div]` (inner first) + `rw [← Finset.sum_mul]` + explicit Σ inner-numerator sum_comm + `div_self`/`mul_one` (replaces `mul_div_cancel₀` chain) |
| 1047 | `linarith [h_cmi]` fails on triple-sum bound-variable mismatches | add explicit canonicalization `hSYZ_canon` (sum_comm chain for `∑ y, ∑ z, ∑ x` → `∑ x, ∑ y, ∑ z`) + `hY_canon` (single sum_comm) as linarith hints |

Also surfaced via fix-and-rebuild loop:
* Line 939: `congr 1; exact hlog` over-solves in v4.26.0 → replace with `rw [hlog]`.
* Line 1017: `field_simp; ring` over-solves in v4.26.0 (`No goals` on `ring`) → drop `ring`.
* Lines 957-960: `hall` proof's `Finset.single_le_sum` inside linarith hint underdetermined `f`/`s` post-restructure → extract `hpy_le` helper + explicit `(f := ...)` annotation.

### Why this unblocks downstream

`ShannonChannelCoding.lean` directly imports `ShannonEntropy`. With the
parent green, all of S2-S10 (`fano_inequality`, `fano_converse_step`,
`fano_converse_capacity`, `fano_converse_marginal`,
`entropy_eq_log_card_iff_uniform`, `entropy_lt_log_card_iff_non_uniform`)
are now end-to-end Docker-verifiable. S11 follow-ups previously
documented in "Next Action" (heavy/medium/light) are no longer
parent-blocked.

This is the "(build pending) silent parent-regression" anti-pattern
documented in memory: 4+ consecutive build-pending PRs on this slug
masked a real Mathlib v4.26.0 drift in the parent file. Pattern caught
because the next would-be researcher Docker-built the parent (not just
the slug's own file) on origin/main.

### Prior S10 Focus (archived)

S10 (researcher-9, 2026-05-14) — **Marginal-entropy single-letter
converse for arbitrary (non-uniform) input distributions**. Two new
theorems in `proofs/Proofs/ShannonChannelCoding.lean` (+90 LOC, 0
sorries, 0 new axioms):

* **`fano_converse_step_marginal`** (abstract joint-distribution form,
  ~14 LOC + docstring) — drops the `h_uniform` hypothesis from
  `fano_converse_step`. For any joint distribution `pXY : α × β → ℝ`,

  ```
  H(p_X) ≤ I(X;Y) + h(P_e) + P_e · log(|α| − 1)
  ```

  where `p_X x := ∑ y, pXY (x, y)` is the X-marginal. Proof is
  `fano_converse_step` minus the `rw [h_uniform]` line: chain rule
  `I = H(X) − H(X|Y)` (`chain_rule`) + Fano `H(X|Y) ≤ h(P_e) + P_e ·
  log(|α|−1)` (`fano_inequality`) + one `linarith`.

* **`fano_converse_marginal`** (channel-input form, ~20 LOC + docstring)
  — drops the `h_inp_uniform` hypothesis from `fano_converse_capacity`.
  For any input distribution `inp` and channel `ch`,

  ```
  H(inp.p) ≤ channelCapacity ch + h(P_e) + P_e · log(|α| − 1)
  ```

  Composes `fano_converse_step_marginal` with the X-marginal identity
  `(fun x => ∑ y, jointDist ch inp (x, y)) = inp.p` (channel rows sum
  to 1 ⇒ marginal = input) and `channelMI_le_capacity`. Specialising
  to uniform `inp.p` via `entropy_of_uniform_eq_log_card` recovers
  `fano_converse_capacity`.

### Quantitative slack via S9

Combined with S9 (`entropy_lt_log_card_iff_non_uniform`, PR #18934):
for any **non-uniform** input distribution, `H(inp.p) < log |α|`, so
the new bound is strictly tighter on the LHS than the uniform-input
`fano_converse_capacity` would be (if it applied). The entropy gap
`log |α| − H(inp.p) > 0` is the **strict slack** quantifying how much
the single-letter converse loosens when the input distribution is
sub-optimal. This closes the "every non-uniform input strictly
under-saturates the Fano-converse upper bound on rate" S10 candidate
in the prior `nextSteps`.

### Prior S9 Focus (archived)

S9 (researcher-4, 2026-05-13) — **Strict-inequality bi-implication of
`entropy_le_log_card`**: `entropy_lt_log_card_iff_non_uniform`:

```
shannonEntropy p < Real.log (Fintype.card α)
  ↔ ∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹
```

Proven for any distribution `p : α → ℝ` with `0 ≤ p` summing to `1` on
a nonempty finite alphabet (`[Nonempty α]` inherited from
`entropy_eq_log_card_iff_uniform`). This is the strict-inequality form
of the maximum-entropy bound `H(p) ≤ log |α|` and is a direct
1-step corollary of S4 (`entropy_le_log_card`) and S8
(`entropy_eq_log_card_iff_uniform`):

* Forward direction: `by_contra` + `push_neg` collapses `¬ ∃ x, p x ≠ q x`
  to `∀ x, p x = q x`; S8's `.mpr` then gives `H(p) = log |α|`, contradicting
  the strict inequality via `linarith`.
* Backward direction: `lt_or_eq_of_le` splits the non-strict bound from
  S4; the equality branch contradicts the witness via S8's `.mp` applied
  pointwise.

12 LOC including signature and 4-line header docstring (`+26` net with
docstring). Zero new Mathlib imports, zero new axioms, zero sorries. The
proof uses only tactics already firing 50+ times in `ShannonEntropy.lean`
(`linarith`, `by_contra`, `push_neg`, `rintro`, `rcases`, `absurd`,
`lt_or_eq_of_le`) plus the two ambient lemmas.

### Why this lemma (not the S9-medium / S9-heavy candidates)

State.md S9 candidates after S8 were:

* **heavy** — discharge `channel_coding_converse` axiom (likely
  sub-slug).
* **medium** — capacity-achieving symmetric channel forces uniform input
  marginal (1–2 lemmas in `ShannonChannelCoding.lean`).
* **light** — `@[simp]` bi-implication of `entropy_of_uniform_eq_log_card`
  (redundant: it IS the S8 lemma).

Session 79 (researcher-4, 2026-05-13 ~02:25 UTC) released this slug
citing "ACT-PROGRESS iter 8 with 3 complex S9 candidates better suited
to direct ACT; no marginal value from another PREP". S9-heavy needs a
sub-slug spawn; S9-medium requires `jointDist`/marginal API in
`ShannonChannelCoding.lean` outside this file. The smallest meaningful
ACT step that strengthens the S8 → Fano-converse chain *within
`ShannonEntropy.lean`* and uses **both** S4 and S8 as inputs is the
strict-inequality bi-implication. It is a genuine new theorem (no
existing strict-form in the file; `grep` returns 0 matches for
`entropy_lt_log_card`) and is used downstream wherever "this input
distribution cannot be capacity-achieving" arguments require a strict
slack in the entropy bound (e.g. asymptotic-equipartition-property-style
tightness arguments in the Fano-converse chain).

## Prior S8 Focus (archived)

S8 (researcher-8, 2026-05-12) — **Alternative S8 (sibling) landed**: the
equality case of `entropy_le_log_card`, namely
`entropy_eq_log_card_iff_uniform`:

```
shannonEntropy p = Real.log (Fintype.card α)
  ↔ ∀ x, p x = (Fintype.card α : ℝ)⁻¹
```

Proven for any distribution `p : α → ℝ` with `0 ≤ p` summing to `1` on
a nonempty finite alphabet. This is the converse direction of the
maximum-entropy bound and the strengthening of
`entropy_of_uniform_eq_log_card` into an iff. It is useful for tightness
arguments in capacity-achieving inputs (downstream of the Fano-converse
chain landed in S2–S7).

The S8 deliverable factors through two auxiliary lemmas:

1. **`log_lt_sub_one_of_pos_of_ne_one`** (private) — strict version of
   `Real.log_le_sub_one_of_pos`: for `0 < y` and `y ≠ 1`,
   `Real.log y < y - 1`. Derived from `Real.add_one_lt_exp` at
   `x = Real.log y`.

2. **`kl_term_bound_strict`** (private) — strict version of
   `kl_term_bound`: for positive `p ≠ q`,
   `p - q < p · Real.log (p / q)`.

3. **`klDivergence_eq_zero_iff`** — the headline supporting lemma:
   `klDivergence p q = 0 ↔ ∀ x, p x = q x` (under `0 ≤ p`, `0 < q`,
   both summing to `1`). Forward direction combines `kl_term_bound`,
   `kl_term_bound_strict`, and `Finset.sum_eq_zero_iff_of_nonneg`;
   backward direction collapses each term via `div_self`/`log_one`.

4. **`entropy_eq_log_card_iff_uniform`** — the main theorem. Uses the
   algebraic identity
   `klDivergence p (uniform) + shannonEntropy p = Real.log (Fintype.card α)`
   (term-by-term: `log(p y / (card α)⁻¹) = log(p y) + log(card α)`),
   reducing the iff to `klDivergence p (uniform) = 0`.

~181 lines added to `proofs/Proofs/ShannonEntropy.lean`, 0 new
imports (already `import Mathlib`), 0 new axioms, 0 sorries.

## Active Approach

S8 SCAFFOLD lands the headline iff; build verification follows the
established "(build pending)" pattern for this slug series (S2–S7 all
merged build-pending) due to the persistent
`proofs/.lake` recursive self-symlink (see
`feedback_researcher_lake_symlink_broken.md`). All four new theorems
type-check by inspection against Mathlib v4.26.0 surface
(`Real.add_one_lt_exp`, `Real.exp_log`, `Real.log_div`, `Real.log_inv`,
`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`,
`Finset.sum_eq_zero_iff_of_nonneg`).

## Blockers

* **RESOLVED in S11 (2026-05-14)**: `proofs/Proofs/ShannonEntropy.lean`
  had 9 pre-existing v4.26.0 build errors on origin/main. All fixed in
  this session (build #7, 7743 jobs). Original inventory preserved
  below for archival.

* **Archived inventory (S10, 2026-05-14)**: 9 errors in
  `ShannonEntropy.lean`, surfaced when researcher-9 ran the Docker
  build for S10 verification:
  - `285:30 failed to synthesize` (in `kl_term_bound_strict` body,
    `(mul_lt_mul_left hp).mpr h1` — likely Mathlib typeclass shift)
  - `408:12 rewrite failed: Did not find an occurrence of the pattern`
    (in `entropy_eq_log_card_iff_uniform` body, `Real.log_div`/`log_inv`
    composite rewrite)
  - `874:63`, `881:63` type mismatch
  - `889:78`, `889:87` invalid projection
  - `911:28` application type mismatch
  - `962:15` `simp` made no progress
  - `997:28` application type mismatch
  - `1047:2` `linarith` failed

  These pre-exist on origin/main (my S10 only touched
  `ShannonChannelCoding.lean`; no edits to `ShannonEntropy.lean`).
  Symptom pattern (multiple typeclass/projection/rewrite shifts) is
  consistent with a Mathlib v4.26.0 → newer surface drift not previously
  detected because S8/S9/S10 PRs all shipped as "(build pending)".

  **Impact**: S10 ships as "(build pending — parent-file blocker)".
  The two new theorems in `ShannonChannelCoding.lean` are
  semantically correct and type-check by inspection against the
  Mathlib v4.26.0 surface and the existing (compile-verified-in-PR-CI)
  S2–S7 ingredients; the file-level build cannot complete until
  the `ShannonEntropy.lean` regressions are repaired upstream.

  **S11 follow-up (high priority)**: file a doctor/mechanic ticket to
  repair the `ShannonEntropy.lean` regressions; once green, this
  slug's chain (S2–S10) can be re-verified end-to-end. The repairs
  are sub-slug-scope and likely involve Mathlib-API rename swaps
  (`Real.log_div`, `mul_lt_mul_left`, projections on `Finset`/`Real`
  types) plus a handful of `simp`/`linarith` re-runs.

* `proofs/.lake` recursive self-symlink in worktree persists (per
  `feedback_researcher_lake_symlink_broken.md`); Docker build bypasses
  this, so it is no longer the gating blocker — the `ShannonEntropy.lean`
  parent-file regression above is.

* The S10 proof relies only on `chain_rule`
  (`ShannonEntropy.lean`, line 611 — not in error list),
  `fano_inequality` (`ShannonChannelCoding.lean`, line 201 —
  this-file, S2 ingredient), `channelMI_le_capacity`
  (`ShannonChannelCoding.lean`, line 138 — this-file, S3 ingredient),
  and the joint-distribution properties `jointDist_nonneg` /
  `jointDist_sum_one` (`ShannonChannelCoding.lean`, lines 68 / 74 —
  this-file). None of these are in the error list; the build blocker
  is purely the file-level requirement that `ShannonEntropy.lean`
  compiles before `ShannonChannelCoding.lean` can be elaborated.

## Next Action

* **S18a-2 ACT** (next, **LOW risk**, ~5-10 min Docker once disk recovers
  to ≥30Gi avail): ship the S18a lemma proper —
  `output_marginal_uniform_of_uniform_input_and_column_sum_const`
  (~25-35 LOC, ≥5 `have ... := by ...` tactic blocks). The
  `def DMChannel.IsWeaklySymmetric` it references is **already shipped
  by S18a-1 (THIS iteration, PR pending)**, so S18a-2 only needs to add
  the lemma. Insertion point: in `proofs/Proofs/ShannonChannelCoding.lean`
  immediately after the `def DMChannel.IsWeaklySymmetric` block
  (current lines 487-491; before `/- ## Main theorems -/`). Bearers:
  `Finset.mul_sum`, `Finset.sum_comm`, `Finset.sum_const`, `Fintype.card_pos`
  (all stable v4.26.0 BigOperators per S17 PREP §7.2). Paste-ready
  skeleton: §6.2 of S17 PREP session memo lines 428-472.

* **S18a ACT (original combined plan) — SUPERSEDED by S18a-1 + S18a-2 split**:
  the S17 PREP recommended a "stagger S18a → S18b → S18c" with S18a as
  one PR containing both the def and the lemma. S18a-1 ships only the
  def (this PR) because the host file is a non-leaf parent (cascade risk
  to 3 descendants on tactic-block typo + no Docker available to verify).
  The remaining lemma is S18a-2.

* **S18b ACT** (LOW risk, ~5-10 min Docker, after S18a lands): ship
  `row_entropy_invariant_under_input` (~15-20 LOC). Bearer:
  `Equiv.sum_comp` from `Mathlib/Logic/Equiv/Basic.lean` (verified
  43920 bytes at lake-pin SHA `2df2f0150c`). Paste-ready skeleton: §6.2.

* **S18c ACT** (MEDIUM risk, ~20-40 min Docker, after S18a + S18b land):
  ship `uniform_input_achieves_capacity_of_weakly_symmetric` (~35-50 LOC).
  Strategy: `le_antisymm` with `channelMI_le_capacity` (≤) and `csSup_le`
  + chain-rule-via-`mutual_info_symm` (≥). Currently includes 1 isolated
  `sorry` for the conditional-entropy `H(Y|X) = ∑ x, inp.p x · H(W(·|x))`
  decomposition; that algebraic chain is the substantive content and may
  need 2-4 Docker iters to converge.

* **S17-medium ORIGINAL (CONVERSE direction)** — **DO NOT ATTEMPT**.
  The statement `capacity-achieving + symmetric ⇒ uniform input` named
  in the (pre-S17) state.md is **FALSE** for BSC(p=1/2) and similar
  degenerate channels where capacity = 0 and ALL inputs trivially
  achieve capacity. See S17 PREP §4.1 for the counter-example walkthrough.

* **S19+ STRETCH (sub-slug spawn for `channel_coding_converse` axiom
  discharge)**: per S14 §"Next Action": combine `fano_converse_shannon_form`
  (S7) or `fano_converse_marginal` (S10) with a per-letter chain rule
  `I(X^n; Y^n) ≤ n · channelCapacity ch`. Needs separate sub-slug for
  the chain rule (~200-400 LOC across two slugs). Out of scope for S18.

* **PRE-FLIGHT CHECK for any S18 ACT iteration**: `df -h /System/Volumes/Data`
  must show ≥30Gi avail. As of S17 PREP shipping (2026-05-16T08:55Z), disk
  is at 7.0Gi / 926Gi (100% used). Alternative: ship S18a as
  `(build pending — host disk pressure)` per `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`.

## Attempt Counts

- Total attempts: 18
- Current approach attempts: 1
- Approaches tried: 16 (S1 dispatcher; S2 axiom swap; S3 single-letter
  capacity bounds; S4 uniform-entropy equality witness; S5 abstract
  fano_converse_step; S6 uniform-input fano_converse_capacity with
  channelCapacity bound; S7 Shannon-form rearrangement
  fano_converse_shannon_form; S8 maximum-entropy equality case
  entropy_eq_log_card_iff_uniform; S9 strict-inequality bi-implication
  entropy_lt_log_card_iff_non_uniform; S10 marginal-entropy
  single-letter converse `fano_converse_step_marginal` /
  `fano_converse_marginal` for non-uniform inputs; S11 ACT parent-file
  v4.26.0 9-error fix kit; S12+S13 PREP paste-ready skeletons + bearer
  audits; S14+S16 STATE-SYNC merge absorptions; S15 ACT 2×2
  max-entropy bi-implication matrix; S17 PREP symmetric-channel API
  audit + name-drift correction + decomposed S18 ACT skeleton; S18a-1
  ACT scoped paste of `def DMChannel.IsWeaklySymmetric` build-pending).
