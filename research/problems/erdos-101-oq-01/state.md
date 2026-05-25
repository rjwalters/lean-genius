# Current State

**Phase**: ACT
**Since**: 2026-05-24 (S12 ACT lands IsBigO/IsLittleO bridge)
**Iteration**: 12
**Last Updated**: 2026-05-24 (researcher-1, S12 ACT)

## Current Focus

S12 ACT (researcher-1, 2026-05-24): IsBigO/IsLittleO bridge to Mathlib
idiom **landed** per S10 PREP §5.1–§5.3 recipe with all five S9 + S10
audit-corrections (Bugs F/G/H/I/J) inlined.

**Three artifacts shipped in `Erdos101OQ01.lean`**:

1. **Artifact (i)** — `noncomputable def maxFourPointLines (n : ℕ) : ℕ
   := n*(n-1)/12` aggregator + `theorem maxFourPointLines_isBigO_n_squared :
   Asymptotics.IsBigO Filter.atTop ↑maxFourPointLines (·^2)` + `theorem
   fourPointLineCount_le_max (P : PlanarPointSet) (hP : NoFiveCollinear P) :
   ...` (the `NoFiveCollinear` hypothesis is load-bearing per Bug-G).
2. **Artifact (ii)** — `lemma isLittleOh_n_squared_iff_isLittleO (g : ℕ → ℕ)
   : IsLittleOh_n_squared g ↔ Asymptotics.IsLittleO Filter.atTop ↑g (·^2)`
   (first materialisation per Bug-H; direction-mapping per S10 §3.4).
3. **Artifact (iii)** — `def erdos_101_oq_01_isLittleO_form : Prop := ∃ g,
   IsLittleO atTop ↑g (·^2) ∧ BoundsAtRate ↑g` (existential per Bug-F, NOT
   concrete IsLittleO on `maxFourPointLines`) + `theorem
   erdos_101_oq_01_rate_form_iff_isLittleO` + `theorem
   erdos_101_oq_01_isLittleO : erdos_101_oq_01_isLittleO_form` (OPEN, sorry).

**Bug fixes inlined**:
- Bug F: artifact (iii) IS existential (`∃ g, …`), NOT concrete `IsLittleO` on `maxFourPointLines`.
- Bug G: `fourPointLineCount_le_max` carries `(hP : NoFiveCollinear P)`.
- Bug H: `isLittleOh_n_squared_iff_isLittleO` materialised as a Lean lemma (no longer a phantom name).
- Bug I: `IsBigO.of_norm_le` body uses single-norm `rw [Real.norm_of_nonneg (by positivity)]` (no `show`, no double `abs_of_nonneg`).
- Bug J: file source order — artifact (ii) at L248-L286 precedes artifact (iii) iff at L312-L325.

**New imports**: `Mathlib.Analysis.Asymptotics.Defs` + `Mathlib.Order.Filter.AtTopBot.Basic`.

**Counters (verified by `wc -l` + `grep`)**:
- Sorries 2 → 3 (added `erdos_101_oq_01_isLittleO` at L336)
- Axioms 0 → 0 (unchanged)
- Theorems 9 → 13 (+4: IsBigO certificate, per-P corollary, iff bridge, isLittleO-form main)
- Lemmas 0 → 1 (+1: bridge lemma)
- Defs 4 → 6 (+2: `maxFourPointLines`, `erdos_101_oq_01_isLittleO_form`)
- LOC 471 → 603 (+132; +78 pure body + ~54 docstrings/intro block)

**Build status**: NOT verified locally (worktree's `.lake` is a self-symlink).
Docker build requires invocation from main repo or via mechanic. Forecast
≤ 2 iterations per S10 §8 gate 7; iter-2 fallbacks documented in
session-file §4 (Real.norm_of_nonneg normalisation; explicit calc chain
in artifact (ii) ← direction).

## Previous Focus

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
inlined. S12 ACT (this iteration) lands the recipe verbatim.

## Earlier Focus

S8 STATE-SYNC (researcher-12, 2026-05-16, #19360 MERGED): doc-only
refresh that discharged the state.md/JSON update deferred by S6 PREP
(#19221) and S7 PREP (#19287), plus catalogued the mechanic resolution
of the v4.26.0 parent/child build regression (#19099 parent + #19255
child). **Superseded by S9 + S10 PREP corrections**: S8's Active
Approach §1-§3 carries Bugs F + G in-narrative.

S7 PREP (researcher-12, 2026-05-15, #19287): sibling-audit of the
queued S6 PREP bridge plan. Found 3 substantive bugs + 1 phantom
bearer name + 1 LOC-budget undercount. Corrected the post-merge ACT
recipe.

S6 PREP (researcher-12, 2026-05-15, #19221): IsBigO/IsLittleO bridge
plan — bearer audit at the lake-pinned v4.26.0 SHA; 3-artifact ACT
scope. Doc-only.

S4 (researcher-1, 2026-05-13, #18911) extended S3's negated-existence
refutation to its positive constructive form
`erdos_three_halves_conjecture_refuted_constructive`. Sorries
unchanged at 2; theorems 8 → 9. File grew 383 → 470 LOC.

S3 (researcher-5, 2026-05-12) discharged
`erdos_three_halves_conjecture_refuted` from S2's
`solymosi_stojakovic_lower_bound` by elementary real-analysis
arithmetic. Sorries 3 → 2.

## Active Approach

S12 ACT (this PR) is the **first** session in the S6-S10 PREP chain that
actually edits `Erdos101OQ01.lean`. The substantive math approach is the
**IsBigO / IsLittleO bridge to Mathlib idiom** from S6 PREP, with all
five S9 + S10 audit-corrections inlined.

The slug now exposes the OQ-01 open question in **two equivalent
Mathlib-flavored forms**: the original ε–N `erdos_101_oq_01` and the
existential `erdos_101_oq_01_isLittleO`. The iff
`erdos_101_oq_01_rate_form_iff_isLittleO` certifies their equivalence;
the slug-form's primary statement (`erdos_101_oq_01_conjecture`) is
related to the rate form via the standard ε-N ↔ rate-witness bridge
(definitional, not requiring a new theorem).

Downstream consumers can now cite OQ-01 in Mathlib idiom directly
without local slug-vocabulary indirection.

## Next Action

**S13 PREP or mechanic-iter** (next picker):

1. **If the S12 PR's Docker build passes iter 1**: S13 PREP candidates
   (in tentative priority):
   - **True-sup `maxFourPointLines`**: replace the surrogate `n*(n-1)/12`
     with `Finset.sup'` over no-five-collinear point sets of fixed size.
     ~15 LOC additional; tightens artifact (i) to the actual supremum.
   - **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound`
     $\leq (n-1)/3$ to yield a $1 - o(1)$ leading constant on the
     elementary $n^2/12$ bound. Still $\Theta(n^2)$, but a concrete
     improvement.
   - **Witness extraction at small `n`** via `decide` / `native_decide`
     on small finite combinatorics; supplies `native_decide`-certified
     examples for the gallery entry.
   - **Downstream integration**: search the proofs directory for places
     where the `Asymptotics.IsLittleO`-style form of OQ-01 would help
     consume the result without local slug-vocabulary indirection.

2. **If the S12 PR's Docker build fails iter 1**: mechanic applies the
   fallback per session-file §4:
   - `Real.norm_of_nonneg` vs `Real.norm_natCast` normalisation: fall
     back to `simp only [Real.norm_eq_abs, abs_of_nonneg (by
     positivity)]`.
   - `nlinarith` in artifact (ii) `←` direction: fall back to explicit
     `calc` chain (S10 §11 ~3 extra LOC).

The main open conjecture `erdos_101_oq_01` ($100 Erdős prize) and the
`solymosi_stojakovic_lower_bound` construction remain OPEN.

## Attempt Counts

- Total attempts: 11 (S1 + S2 + S3 + S4 + S6 PREP + S7 PREP + S8 STATE-SYNC + S9 PREP + S10 PREP + S11 STATE-SYNC + S12 ACT; S5 OBSERVE was CLOSED → abandoned)
- Current approach attempts: 1 (S12 ACT first ACT in the S6-S10 PREP chain)
- Approaches tried: 6 (S1 scaffold + S2 lower-bound recording;
  S3 elementary real-analysis discharge; S4 constructive rephrasing
  of S3 chain; S6+S7 PREP bridge plan + audit; S9+S10 PREP audit
  cascade refining S8's Active Approach; **S12 ACT** lands the recipe)

## Build Status

**S12 ACT baseline**: NOT verified locally. The researcher worktree's
`proofs/.lake` is a self-symlink (per
`feedback_researcher_lake_symlink_broken.md`); Docker build requires
invocation from main repo or via mechanic.

**Forecast**: ≤ 2 Docker iterations per S10 §8 gate 7.

`Erdos101OQ01.lean` current state on branch
`research/erdos-101-oq-01-r1`:
- 603 LOC (+132 vs `origin/main` baseline)
- 13 theorems + 1 lemma + 6 defs (+4 thms, +1 lemma, +2 defs)
- 3 `sorry`s (added `erdos_101_oq_01_isLittleO` at L336;
  `erdos_101_oq_01` still at L113; `solymosi_stojakovic_lower_bound`
  shifted from L302 → L434)
- 0 `axiom` declarations
- 0 structure-encoded assumptions

`Erdos101Problem.lean` parent: 758 LOC, unchanged.

## Blockers

None blocking from S12's perspective:

| Item | Status |
|------|--------|
| Build verification | DEFERRED to mechanic/CI (worktree symlink trap) |
| Main conjecture `erdos_101_oq_01` | OPEN ($100 Erdős prize) — not aimed at by S12 |
| `solymosi_stojakovic_lower_bound` | OPEN (algebraic geometry over finite fields, deferred) |
| Open meta PR #19476 (mechanic meta drift fix) | path-disjoint from S12 (this PR doesn't touch meta.json) |

The remaining OPEN mathematical content is the main conjecture
`erdos_101_oq_01` (in either form — primary or Mathlib-idiom) and the
`solymosi_stojakovic_lower_bound` construction. Neither blocks any S13
candidate.
