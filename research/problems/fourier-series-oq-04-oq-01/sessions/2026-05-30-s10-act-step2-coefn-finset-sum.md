# S10 ACT — `Lp.coeFn_finset_sum` helper (step 2 of S7 audit §4 recipe)

**Researcher**: researcher-1
**Date**: 2026-05-30
**Mode**: ACT (sorry-free / axiom-free Lean delta; not STATE-SYNC)
**Phase delta**: Iteration 8 → 9; phase header unchanged (still ACT)
**Worktree HEAD**: branch `research/fourier-series-oq-04-oq-01-1780179312` off main `f19276d72c8`
**Mathlib pin**: unchanged (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0)

---

## §1 — Trigger

S9 ACT (2026-05-29, researcher-1, PR #21131 MERGED) landed step 3 of the
S7 audit §4 recipe (cofinality bearer). Remaining S2e ACT scope per the
post-S9 update in `state.md` (lines 116–129):

| Step | Pre-S10 status | Post-S10 status | Notes |
|---|---|---|---|
| 1 — Setup (haarT2/volume) | pending (3-5 LOC + 3-5 LOC contingency) | unchanged | this iteration deferred |
| 2 — `coeFn_finset_sum` helper | pending (8-10 LOC) | **DONE ✅** | this iteration |
| 3 — Cofinality | DONE (S9) | unchanged | |
| 4 — Bridge `sphPartialSum` → Lp | pending (15-25 LOC) | unchanged | |
| 5 — Cite engine | pending (5-10 LOC) | unchanged | |
| 6 — Close `eLpNorm`-form | pending (5-10 LOC) | unchanged | |
| **Total** | **38-65 LOC** | **30-55 LOC** | scope reduction ~20% |

Step 2 is independent of step 1 (no `haarT2 = volume` dependency — the
helper is stated and proved entirely over `haarT2`) and independent of
steps 4–6 (no `sphPartialSum`, `mFourierBasis`, or `eLpNorm` dependency).
Landing it standalone shrinks the future ACT scope without taking on the
risky measure-theoretic bridge work.

---

## §2 — Deliverable

One new sorry-free, axiom-free **private** theorem in
`proofs/Proofs/FourierSeriesOQ04OQ01.lean` (in a new `S2e-step2` section
after the cofinality block):

### §2.1 `coeFn_finset_sum_haarT2`

```lean
private theorem coeFn_finset_sum_haarT2
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 haarT2) :
    ⇑(∑ k ∈ s, f k) =ᵐ[haarT2] fun x => ∑ k ∈ s, (f k : T2 → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 haarT2] with x hx
    simp [hx]
  | @insert k s hkS ih =>
    rw [Finset.sum_insert hkS]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with x hx
    simp [Finset.sum_insert hkS, hx, Pi.add_apply]
```

**Proof outline**:
- **Empty case**: `Finset.sum_empty` reduces both sides to `(0 : Lp ℂ 2 haarT2)`
  on the left and `fun _ => (0 : ℂ)` on the right. The Mathlib lemma
  `Lp.coeFn_zero ℂ 2 haarT2` (at `LpSpace/Basic.lean:187` at pin — the
  `variable (E p μ)` block makes `ℂ`, `2`, `haarT2` explicit) supplies the
  AE-equality `⇑(0 : Lp ℂ 2 haarT2) =ᵐ[haarT2] (0 : T2 → ℂ)`. A
  `filter_upwards` + `simp` closes the final pointwise step (`0 = 0`).
- **Insert case**: `Finset.sum_insert hkS` rewrites the LHS as
  `f k + ∑ j ∈ s, f j` in Lp. `Lp.coeFn_add` (at `LpSpace/Basic.lean:195`
  at pin) gives the AE-equality with the Pi-add of coercions. The
  inductive hypothesis (`⇑(∑ j ∈ s, f j) =ᵐ[haarT2] fun x => ∑ j ∈ s, (f j) x`)
  is combined via `filter_upwards`; the final pointwise goal is
  `⇑(f k) x + ⇑(∑ j ∈ s, f j) x = ∑ j ∈ insert k s, (f j) x`, which
  `simp [Finset.sum_insert hkS, hx, Pi.add_apply]` closes.

LOC: 12 (proof body after fix) + 14 (signature + docstring) + 14 (section docstring) ≈ 40 LOC (375 → 413 = +38; -2 net for cleaner proof vs first attempt).

---

## §3 — Why this is safe to ship standalone

| Property | Status | Notes |
|---|---|---|
| Sorry-free | ✅ | No `sorry` in the new theorem |
| Axiom-free | ✅ | No new `axiom` declarations |
| Measure-disambiguation-free | ✅ | Stated and proved entirely over `haarT2`; no `volume`/`haarT2` rfl-or-not question |
| Mathlib-stable | ✅ | Uses only `Lp.coeFn_zero`, `Lp.coeFn_add`, `Finset.induction_on`, `Finset.sum_empty`, `Finset.sum_insert`, `Filter.filter_upwards`, `Pi.add_apply` — all in v4.26.0 |
| Standalone | ✅ | Independent of S2e ACT steps 1 (setup), 4 (bridge), 5 (engine), 6 (close) |
| Composable | ✅ | The AE-equality form composes via `filter_upwards` with future bridge steps; the signature matches the obvious generic-Mathlib-bound generalisation (with `{E p μ}` parameters) |
| Privacy | private | Marked `private` per the S7 audit recipe — the helper is bespoke (specialised to `ℂ`, `2`, `haarT2`) and not intended for re-export. The generic Mathlib-bound version is a separate (deferred) upstream contribution. |

---

## §4 — Build verification

Docker build via `./proofs/scripts/docker-build.sh Proofs.FourierSeriesOQ04OQ01`
(per CLAUDE.md's mandatory wrapper for `lake build` — direct invocation is
unsafe).

**Build result (first attempt — failed)**: The initial proof used
`filter_upwards [Lp.coeFn_zero ℂ 2 haarT2] with x hx; simp [hx]` for the
empty case and `filter_upwards [ih] with x hx; simp [Finset.sum_insert
hkS, hx, Pi.add_apply]` for the insert case. Build failed with two
`unsolved goals` errors:

1. **Empty case (line 403)**: post-`filter_upwards` the hypothesis was
   `hx : ↑↑0 x = 0 x` (double up-arrow from `⇑` unfolded to `↑↑`) but the
   goal was `↑0 x = 0` (single up-arrow on `Lp → AEEqFun`). `simp [hx]`
   didn't bridge the syntactic gap; the simp linter further reported
   `hx` as unused.
2. **Insert case (line 407)**: `simp [Finset.sum_insert hkS, hx,
   Pi.add_apply]` triggered an unintended `Lp.coe_finset_sum`-style
   distribution on the inductive LHS, leaving the goal as
   `↑(∑ i ∈ s, ↑(f i)) x = ∑ k ∈ s, ↑↑(f k) x` — i.e. simp pushed the
   outer ⇑ through the Finset.sum, producing a sum of single-coerced
   `Lp → AEEqFun` elements applied at `x`. The inductive hypothesis was
   never matched.

**Fix**: drop `filter_upwards` + `simp` entirely. Use `Lp.coeFn_zero ℂ 2
haarT2` directly via `exact` (Lean's `exact` handles the `(0 : T2 → ℂ)`
vs `fun x => 0` eta-bridge), and combine the EventuallyEqs via
`Filter.EventuallyEq.add` (which avoids the misbehaving `Lp.coe_finset_sum`
lemma in the simp set entirely).

**Final proof** (line 398-409, 12 LOC body + 14 LOC docstring + section
header):
```lean
private theorem coeFn_finset_sum_haarT2
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 haarT2) :
    ⇑(∑ k ∈ s, f k) =ᵐ[haarT2] fun x => ∑ k ∈ s, (f k : T2 → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 haarT2
  | @insert k s hkS ih =>
    simp only [Finset.sum_insert hkS]
    refine (Lp.coeFn_add (f k) _).trans ?_
    exact (Filter.EventuallyEq.refl _ (⇑(f k))).add ih
```

**Build result (second attempt — success)**: Docker build via
`./proofs/scripts/docker-build.sh Proofs.FourierSeriesOQ04OQ01` completed
with **7743 jobs replayed cleanly**, single expected warning
`Proofs/FourierSeriesOQ04OQ01.lean:148:8: declaration uses 'sorry'` (the
pre-existing `sphPartialSum_L2_norm_converge` sorry, unchanged). No new
warnings from the helper addition. Build wall-clock: ~7 min (cold cache
fetch from Azure, then ~2 min elaboration); subsequent builds will be
faster.

---

## §5 — Gallery sync

`src/data/proofs/fourier-series-oq-04-oq-01/meta.json`:
- `lineCount`: 375 → 413 (synced in both top-level `leanFile` and inner `meta` blocks)
- `theoremCount`: 10 → 11 (the new `private theorem` is counted)
- `sorries`: 1 (unchanged)
- `axiomCount`: 1 (unchanged)
- `originalContributions`: extended with 1 entry for the new helper
- `sections`: new `lp-coefn-finset-sum` entry with `startLine: 373`,
  `endLine: 409`

`src/data/research/problems/fourier-series-oq-04-oq-01.json`:
- `currentState.focus` / `nextAction`: updated to reflect step-2 done
- `currentState.iteration`: 8 → 9
- `lastUpdate`: refreshed to 2026-05-30
- `knowledge.progressSummary`: appended S10 ACT mini-task summary
- `knowledge.builtItems`: extended with the new helper line
- `leanFiles[0].lineCount`: 279 (out-of-date) → 415 (current)
- `leanFiles[0].theoremCount`: 8 (out-of-date) → 11 (current)

(Note: the research JSON was out-of-date from S9 — the cofinality landed
in proofs meta.json but not in research JSON. This iteration corrects
that drift too.)

---

## §6 — S2e ACT scope reduction

| Step | Pre-S10 budget | Post-S10 budget | Status |
|---|---|---|---|
| 1 — Setup (haarT2/volume) | 3-5 LOC + 3-5 LOC contingency | unchanged | pending |
| 2 — `coeFn_finset_sum` helper | 8-10 LOC | **0 LOC (DONE this iter)** | ✅ |
| 3 — Cofinality | 0 LOC (S9 DONE) | unchanged | ✅ |
| 4 — Bridge `sphPartialSum` → Lp | 15-25 LOC | unchanged | pending |
| 5 — Cite engine | 5-10 LOC | unchanged | pending |
| 6 — Close `eLpNorm`-form | 5-10 LOC | unchanged | pending |
| **Total** | **38-65 LOC** | **30-55 LOC** | scope reduction ~20% |

The remaining S2e ACT close is now a 30-55 LOC single-iteration target
(plus 2-3 Docker iterations) — the close is genuinely tractable in a
single future session.

---

## §7 — Honest-status block

- **Mathematical progress this iteration**: 1 new private helper theorem
  (`coeFn_finset_sum_haarT2`) closing a documented Mathlib gap (no named
  `Lp.coeFn_finset_sum` at pin). Sorry-free, axiom-free, build-verified
  ✅ (7743 Docker jobs clean, single pre-existing L² sorry warning at
  line 148 unchanged). Step 2 of the S7 audit §4 ACT recipe done.
- **Build-verification status**: ✅ Docker-built clean at worktree HEAD
  `f19276d72c8` (7743 jobs, single expected pre-existing sorry at
  line 148). First attempt failed on `simp` heuristics; fix iteration
  replaced `simp` with `Filter.EventuallyEq.add` (see §4 for forensics).
- **Race disclosure**: 0 open PRs touching
  `proofs/Proofs/FourierSeriesOQ04OQ01.lean` at iteration pickup (verified
  via `gh pr list`).
- **Open conjecture status**: unchanged (Carleson L²-pointwise
  convergence for 2D spherical-Fourier sums remains open;
  `carleson_2d_sph` axiom unchanged at line 132).
- **Generic-Mathlib-bound upgrade path**: The helper as written is
  specialised to `ℂ`, `2`, `haarT2`. The obvious upstream-bound
  generalisation (with `{E p μ}` parameters) requires careful typeclass
  bookkeeping but uses the same proof body verbatim. Deferred to a
  separate `mathlib4#XXXX` PR; not part of this slug's deliverable.

---

## §4.1 — Build confirmation (folded back post-Docker)

✅ **Build succeeded** (Docker, 7743 jobs replayed cleanly):
```
⚠ [7743/7743] Built Proofs.FourierSeriesOQ04OQ01 (21s)
warning: Proofs/FourierSeriesOQ04OQ01.lean:148:8: declaration uses 'sorry'
Build completed successfully (7743 jobs).
```
Single expected warning at line 148 (the pre-existing
`sphPartialSum_L2_norm_converge` sorry, unchanged). No new warnings from
the helper addition.
