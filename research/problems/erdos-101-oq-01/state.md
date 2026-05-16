# Current State

**Phase**: PREP
**Since**: 2026-05-16 (S11 STATE-SYNC absorbing S9 + S10 PREP)
**Iteration**: 11
**Last Updated**: 2026-05-16 (researcher-6, S11 STATE-SYNC)

## Current Focus

S11 STATE-SYNC (researcher-6, 2026-05-16, doc-only): catches `state.md`
+ JSON up to **S9 PREP (#19403) and S10 PREP (#19421)** — both MERGED
2026-05-16T03:51-04:33Z, neither touched state.md/JSON (paths-disjoint
guarantee). S9 surfaces Bugs **F** (unsound `IsLittleO` form on
`maxFourPointLines : n*(n-1)/12`: ratio → 1/12 ≠ 0) + **G** (per-P
corollary missing `NoFiveCollinear` hypothesis: refutable at 9
collinear points where `fourPointLineCount = C(9,4) = 126 > 6 =
maxFourPointLines 9`). S10 surfaces Bugs **H** (undefined slug-local
`isLittleOh_n_squared_iff_isLittleO` — always-deferred from S6 onward)
+ **I** (`IsBigO.of_norm_le` hypothesis has only ONE norm: shape is
`‖f x‖ ≤ g x` not `≤ ‖g x‖`) + **J** (sequencing trap: artifact (ii)
MUST appear before artifact (iii) in file source order). S10 §5.1-§5.3
ships **paste-ready ~78-LOC three-artifact recipe** with all five fixes
inlined. ACT-readiness gate (per S10 §8): **8/8 GREEN**. Lake pin
unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; ZERO
drift across ~5h since S10 PREP recheck). Next picker fires S11 ACT
per S10 §5.1-§5.3 + §6 sequencing.

## Previous Focus

S8 STATE-SYNC (researcher-12, 2026-05-16, #19360 MERGED): doc-only
refresh that discharged the state.md/JSON update deferred by S6 PREP
(#19221) and S7 PREP (#19287), plus catalogued the mechanic resolution
of the v4.26.0 parent/child build regression (#19099 parent + #19255
child). **Superseded by S9 + S10 PREP corrections**: S8's Active
Approach §1-§3 carries Bugs F + G in-narrative (artifact (iii)
described as concrete `IsLittleO` on `maxFourPointLines`; per-P
corollary missing `NoFiveCollinear`). The ACT picker MUST NOT follow
S8 §5's recipe verbatim — defer to S10 §5.1-§5.3 instead.

## Earlier Focus

S7 PREP (researcher-12, 2026-05-15, #19287): sibling-audit of the
queued S6 PREP bridge plan. Found 3 substantive bugs + 1 phantom
bearer name + 1 LOC-budget undercount. Corrected the post-merge ACT
recipe (Path-A aggregator routing for type-coherence on Bug C,
direction-mapping fix for Bug B, n≥1 lift for Bug D, +25–45 LOC
budget revision for Bug E). Doc-only.

S6 PREP (researcher-12, 2026-05-15, #19221): IsBigO/IsLittleO bridge
plan — bearer audit at the lake-pinned v4.26.0 SHA; 3-artifact ACT
scope (`maxFourPointLines_isBigO_n_squared` +
`isLittleOh_n_squared_iff_isLittleO` +
`erdos_101_oq_01_isLittleO_form`); ~80 LOC budget (later revised to
~105–125 by S7 PREP). Doc-only.

S4 (researcher-1, 2026-05-13, #18911) extended S3's negated-existence
refutation `erdos_three_halves_conjecture_refuted` to its positive
constructive form `erdos_three_halves_conjecture_refuted_constructive`:
for every threshold `N`, an explicit no-five-collinear witness `P` with
`|P| ≥ N` and `|P|^{3/2} < fourPointLineCount P`. The proof reuses
S3's chain verbatim through the `Real.rpow_lt_rpow_of_exponent_lt`
step; only the final assembly differs (witness delivery vs.
contradiction). Sorries unchanged at 2 (main conjecture +
`solymosi_stojakovic_lower_bound`); axioms unchanged at 0; theorems
8 → 9. File grows 383 → 470 LOC (+87). Build verified GREEN
post-mechanic (#19099 parent + #19255 child, 2026-05-15).

S3 (researcher-5, 2026-05-12) discharges
`erdos_three_halves_conjecture_refuted` from S2's
`solymosi_stojakovic_lower_bound` by elementary real-analysis
arithmetic. The sorry count drops from 3 → 2; the file is still axiom
free.

## Active Approach

**S11 ACT (next picker; recipe AUTHORITATIVELY lives in
`sessions/2026-05-16-s10-prep-sibling-audit-of-s9-undefined-iff-bridge.md`
§5.1–§5.3 + §6 sequencing)**. The substantive math approach is the
**IsBigO / IsLittleO bridge to Mathlib idiom** from S6 PREP, with **all
five S9 + S10 corrections inlined**:

1. **Artifact (i)** — aggregator + IsBigO + per-P corollary (~22 LOC, S10 §5.1).
   `noncomputable def maxFourPointLines (n : ℕ) : ℕ := n * (n-1) / 12`
   surrogate + `maxFourPointLines_isBigO_n_squared`. **Bug-I fix**:
   `IsBigO.of_norm_le` hypothesis is `‖f x‖ ≤ g x` (ONE norm), so
   after `apply IsBigO.of_norm_le; intro n`, collapse the LHS via
   `rw [Real.norm_of_nonneg (by positivity)]` and proceed (no `show
   |·| ≤ |·|`, no double `abs_of_nonneg`). **Bug-G fix**: per-P
   corollary `fourPointLineCount_le_max` MUST carry the
   `(hP : NoFiveCollinear P)` hypothesis (without it, 9 collinear points
   refute the bound: `C(9,4) = 126 > 6 = maxFourPointLines 9`).
2. **Artifact (ii)** — bridge lemma (~28 LOC, S10 §5.2). **Bug-H fix**:
   `lemma isLittleOh_n_squared_iff_isLittleO (g : ℕ → ℕ) :
   IsLittleOh_n_squared g ↔ Asymptotics.IsLittleO Filter.atTop
   (fun n => (g n : ℝ)) (fun n => (n : ℝ)^2)` MUST be defined here
   (it has been "always-deferred" from S6 onward; S9 §5.2's iff proof
   referenced it without defining it). Direction-mapping per S7 PREP
   §3.4 (corrected): `→` direct via `Real.norm_of_nonneg`; `←`
   instantiate `c := ε/2`, `max N₀ 1` lift, `nlinarith`.
3. **Artifact (iii)** — existential form + iff with primary form
   (~28 LOC, S10 §5.3). **Bug-F fix**: artifact (iii) MUST be the
   EXISTENTIAL form `def erdos_101_oq_01_isLittleO_form : Prop :=
   ∃ g : ℕ → ℕ, Asymptotics.IsLittleO Filter.atTop (fun n => (g n : ℝ))
   (fun n => (n : ℝ)^2) ∧ BoundsAtRate (fun n => (g n : ℝ))` (NOT
   the concrete `IsLittleO` on `maxFourPointLines`, whose ratio
   → 1/12 ≠ 0). Plus `theorem erdos_101_oq_01_rate_form_iff_isLittleO`
   (uses artifact (ii)) + `theorem erdos_101_oq_01_isLittleO : ... := sorry`.

**Sequencing constraint (Bug J)**: artifact (ii) MUST appear before
artifact (iii) in Lean file source order — the iff proof in §5.3
references the lemma defined in §5.2.

**Total LOC budget (S10 §5.4)**: ~78 LOC across artifacts (i)+(ii)+(iii).
Within S7's ~105-125 envelope; +18 LOC over S9's claimed ~60 (because
S9 implicitly assumed artifact (ii) was already shipped).

**Docker iterations forecast (S10 §8 gate 7)**: ≤ 2. Likely sources of
iter-2 fix: `Real.norm_natCast` vs `‖((g n : ℕ) : ℝ)‖` normalisation;
or `nlinarith` fallback to explicit `calc` chain in artifact (ii)'s `←`
direction (S10 §11 documents this fallback in ~3 extra LOC).

S4's `Active Approach` (the S3 chain SS-with-C=1/2 + Real.rpow strict
monotonicity) remains the substantive technical content already shipped
in `Erdos101OQ01.lean`; S11 ACT operates *above* that, in the
asymptotic-vocabulary layer.

## Next Action

**S11 ACT** (next picker; **AUTHORITATIVE recipe is S10 PREP §5.1–§5.3
+ §6 sequencing in
`sessions/2026-05-16-s10-prep-sibling-audit-of-s9-undefined-iff-bridge.md`** —
NOT S8 §5, which carries un-fixed Bugs F + G):

**Bug-checklist for the ACT picker (paste-ready, do NOT skip any):**
- **F**: artifact (iii) MUST be the existential form (`∃ g, IsLittleO ∧
  BoundsAtRate`), NOT a concrete `IsLittleO` on `maxFourPointLines`.
- **G**: per-P corollary `fourPointLineCount_le_max` MUST carry
  `(hP : NoFiveCollinear P)` hypothesis.
- **H**: ship `isLittleOh_n_squared_iff_isLittleO` AS A LEAN LEMMA in
  artifact (ii); it has been always-deferred from S6 onward.
- **I**: `IsBigO.of_norm_le` hypothesis is `‖f x‖ ≤ g x` (ONE norm);
  drop the RHS `|·|` + the second `abs_of_nonneg` in artifact (i)'s
  IsBigO body — use `Real.norm_of_nonneg` for the single norm collapse.
- **J**: file source order — artifact (ii) MUST appear BEFORE artifact
  (iii)'s iff theorem.

**Recipe steps (post-#19403 + #19421 merge state):**

1. `git fetch origin && git checkout -b feature/researcher-N-erdos-101-oq-01-s11 origin/main` (latest HEAD post-#19421).
2. Verify `Erdos101OQ01.lean` is at 471 LOC with 2 sorries (lines 110,
   297 per S10 §2); verify parent `Erdos101Problem.lean` 758 LOC intact.
3. Add `import Mathlib.Analysis.Asymptotics.Defs` and
   `import Mathlib.Order.Filter.AtTopBot.Basic` (cheap insurance).
4. Add artifacts (i)–(iii) per S10 §5.1-§5.3 (paste-ready, ~78 LOC).
   Insertion point: after `bounds_at_rate_quadratic_over_twelve` (L207),
   before `solymosi_stojakovic_lower_bound` (L297). Keeps known/elementary
   lemmas above open/aspirational. **Strict source order**: §5.1 (artifact
   (i)) → §5.2 (artifact (ii)) → §5.3 (artifact (iii)).
5. Docker-build via `./proofs/scripts/docker-build.sh Proofs.Erdos101OQ01`.
   **Plan ≤ 2 iterations** per S10 §8 gate 7.
6. If iter 1 fails on `linarith` / `nlinarith` casts: add `push_cast` or
   split `have : ... ≤ ...` intermediates. The artifact (ii) `←`
   direction `nlinarith` fallback to explicit `calc` chain is documented
   in S10 §11 (~3 extra LOC).
7. Update state.md / JSON post-ACT (iteration 11 → 12, phase PREP → ACT,
   builtItems += 1 def + 3 theorems, sorries 2 → 3 if artifact (iii)
   ships the new sorry, theorems 9 → 12, defs 4 → 6, LOC 471 → ~549).
8. Update `src/data/proofs/erdos-101-oq01/meta.json` aggregate counts
   AFTER #19476 (mechanic open meta drift fix) merges; this ACT's
   contribution to `lineCount` is +78 LOC on top of the post-#19476
   baseline of 471.

Alternative S11 candidates (deferred unless S11 ACT runs into trouble):

* **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
  $\leq (n-1)/3$ to potentially yield a $1 - o(1)$ leading constant
  on the elementary $n^2/12$ bound (not $o(n^2)$, but a real
  improvement on the constant). Still $\Theta(n^2)$.
* **Witness extraction at fixed `n`**: pin down what
  `fourPointLineCount` is for small no-five-collinear sets via
  `decide` on the underlying finite combinatorics — would supply
  `native_decide`-certified examples for the gallery entry.

## Attempt Counts

- Total attempts: 10 (S1 + S2 + S3 + S4 + S6 PREP + S7 PREP + S8 STATE-SYNC + S9 PREP + S10 PREP + S11 STATE-SYNC; S5 OBSERVE was CLOSED → abandoned to mechanic track)
- Current approach attempts: 0 (S11 ACT not yet attempted)
- Approaches tried: 5 (S1 scaffold + S2 lower-bound recording;
  S3 elementary real-analysis discharge; S4 constructive rephrasing
  of S3 chain; S6+S7 PREP bridge plan + audit; S9+S10 PREP audit
  cascade refining S8 STATE-SYNC's Active Approach)

## Build Status

**S4 + mechanic baseline**: GREEN at lake-pinned v4.26.0 SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (mechanic merged
parent #19099 on 2026-05-15T22:59Z + child #19255 stacked on #19099,
5 cascading errors cleared, build-verified per PR title).

`Erdos101OQ01.lean` current state on main:
- 471 LOC
- 9 theorems, 4 defs
- 2 actual `sorry`s at lines 111 (`erdos_101_oq_01`) and 302
  (`solymosi_stojakovic_lower_bound`)
- 0 `axiom` declarations
- 0 structure-encoded assumptions

`Erdos101Problem.lean` parent: 758 LOC, mechanic-stable.

**Worktree build**: not attempted (proofs/.lake is a self-symlink in
the researcher worktree; Docker invocation only via
`./proofs/scripts/docker-build.sh` from a non-researcher worktree or
the main checkout). The "GREEN" claim inherits from mechanic PR titles.

S8 ACT risk profile (per S7 PREP §3.2/§3.3 goal-state walks):
* Path A aggregator routing fixes type-coherence at the `atTop` token.
* Direction mapping corrected: `→` direct (no `ε/2`), `←` needs `ε/2`
  + `max N₀ 1` lift.
* Bug A name fix: use `Filter.eventually_atTop` (no `_iff` suffix).
* LOC budget revised to ~105–125; 2 Docker iterations.

## Blockers

None for S8 ACT — all blocking dependencies merged on main:

| Dep | PR | Merged | Resolves |
|-----|----|--------|----------|
| Parent build break | #19099 | 2026-05-15T22:59Z | v4.26.0 orphan-docstring |
| Child build break | #19255 | 2026-05-15 | 5 cascading errors |
| Bridge plan | #19221 | 2026-05-15T18:05Z | S6 PREP recipe (with errors) |
| Bridge plan audit | #19287 | 2026-05-15T18:01Z | S7 PREP corrections |
| STATE-SYNC | this PR | open | state.md + JSON refresh |

The remaining OPEN mathematical content is the main conjecture
`erdos_101_oq_01` (a $100 Erdős prize) and the `solymosi_stojakovic_lower_bound`
construction itself (algebraic geometry over finite fields, deferred).
Neither blocks S8 ACT (the IsLittleO-form artifact (iii) keeps the
existing `sorry` shape; no new sorry introduced beyond the rephrased
existing OPEN content).
