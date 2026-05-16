# S27 — S24 ACT PR-A: `volume_eq_setLIntegral_indicator_tsum_lattice`

**Date**: 2026-05-16
**Researcher**: researcher-1
**Predecessor merge**: S26 STATE-SYNC #19370 (researcher-12) merged 2026-05-16T03:53:25Z
**Knowledge tier at claim**: RICH (score 57)
**Outcome**: ✅ PR-A shipped — build-verified

## 1. Setup

S26 STATE-SYNC absorbed the 4-PR drain wave (S23 PREP #18989, Iter 23 BUILD-VERIFY #19113, S24 PREP #19176, S25 PREP #19314, all merged 2026-05-15T22:55–23:44Z) and refreshed the ACT-readiness gate to 5/6 GREEN (condition 3 self-satisfying on its own merge). Per the S26 head: **PR-A is the entry point with paste-ready bearer manifest and ≤30 LOC budget**, ready to ship as soon as STATE-SYNC merges. STATE-SYNC merged at T+0:00; researcher-1 claimed at T+~8min and executed PR-A.

**Open-PR snapshot at claim**: 1 PR (#17599, Iter 21 `minkowski_three_points`, DIRTY 7-day-stale, safe to ignore per S26 §"Open-PR snapshot"). No competing in-flight S24 ACT.

**Lake-manifest pin (this commit)**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S25 PREP).

## 2. Spec & insertion site

Per **S23 PREP §4 row 6**:

> | `volume_eq_setLIntegral_indicator_tsum` (`:187`) | A `_lattice` version of the same identity, or the existing one specialised to `b`. | The existing … uses `stdLattice` and `stdFundDomain` only as conveniences; the underlying Mathlib API (`IsAddFundamentalDomain.lintegral_eq_tsum''`) is already generic in the basis. **Recommended**: generalise this helper first (small PR), then use it inside `blichfeldt_general_lattice`. |

And **S23 PREP §4 implementation order**:

> 1. **PR-A**: Generalise `volume_eq_setLIntegral_indicator_tsum` to `volume_eq_setLIntegral_indicator_tsum_lattice` (or just add a `_lattice` version alongside). ≤ ~30 LOC.

PR-A here takes the "add alongside" route — leaves the `stdLattice`-specialised version in place (referenced by `blichfeldt_general`) and adds the basis-parametric `_lattice` variant immediately after at line 264.

## 3. Bearer manifest recheck (B1 only — B2/B3/B4 not needed for PR-A)

PR-A's proof body uses only **B1** = `ZSpan.isAddFundamentalDomain'` (S25 PREP §2 B1).

Re-fetched via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Module/ZLattice/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Symbol | Path | S25 line | This recheck | Drift | Section-header typeclasses |
|---|---|---|---|---|---|---|
| B1 | `ZSpan.isAddFundamentalDomain'` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | 359 | **359** | ✅ none | `section Real` → `variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)`; theorem-level `[Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]` |

Per memory-trap `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`, the explicit section-header recheck above guards against the PREP-author trap of citing a body-level signature without registering the section-level `variable` block. For PR-A, all four section-header predicates are auto-derived at `E = Fin n → ℝ`, `ι = Fin n` (NeZero n is carried on the wrapping theorem, but the bearer doesn't depend on it).

## 4. Implementation — the diff

Inserted at `proofs/Proofs/MinkowskiTheoremOQ04.lean:244` (immediately after `volume_eq_setLIntegral_indicator_tsum`, before `blichfeldt_general`):

```lean
/-- **Lattice-parametric covering-count integral identity** (basis-parametric variant
of `volume_eq_setLIntegral_indicator_tsum`; S24 PR-A entry point per S23 PREP §4 +
S25 PREP §2 bearer manifest).
…
-/
theorem volume_eq_setLIntegral_indicator_tsum_lattice {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} (h_meas : MeasurableSet s) :
    ∫⁻ x in ZSpan.fundamentalDomain b,
        (∑' g : (Submodule.span ℤ (Set.range b)).toAddSubgroup,
            s.indicator (fun _ => (1 : ENNReal))
              ((g : Fin n → ℝ) + x)) ∂volume
      = volume s := by
  …
```

Proof shape — identical to the `stdLattice`-specialised template, with three substitutions:

| Original (`stdLattice` version) | This PR (`_lattice` version) |
| --- | --- |
| `(stdLattice n).toAddSubgroup` | `(Submodule.span ℤ (Set.range b)).toAddSubgroup` |
| `stdFundDomain n` | `ZSpan.fundamentalDomain b` |
| `stdLattice_isAddFundamentalDomain n` (which itself unfolds to `ZSpan.isAddFundamentalDomain' (stdBasis n) volume`) | `ZSpan.isAddFundamentalDomain' b volume` |

Calc chain unchanged: `lintegral_congr` → `tsum_congr` → `congr 1` (vadd_def unfold) → `lintegral_tsum` → `IsAddFundamentalDomain.lintegral_eq_tsum''.symm` → `lintegral_indicator_const + one_mul`.

## 5. Build verification

**Command**: `LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`

**Result**: `Build completed successfully (3075 jobs).` — first try, warm cache, ~2 min wall.

Per S26 baseline, the pre-PR baseline was also 3075 jobs (Iter 23 BUILD-VERIFY measurement); the +1 theorem evidently merged into the same elaboration unit count. All 11 `#check` block entries at lines 977–987 still elaborate.

## 6. Tracker syncs (this PR)

| File | Change |
| --- | --- |
| `proofs/Proofs/MinkowskiTheoremOQ04.lean` | +65 LOC (922 → 987); 1 new theorem |
| `src/data/proofs/minkowski-theorem-oq-04/meta.json` | `lineCount: 921 → 987` (×2 occurrences); `theoremCount: 15 → 16` (×2 occurrences) |
| `research/problems/minkowski-theorem-oq-04/state.md` | New §"S27 — S24 ACT PR-A" head block; iteration 26 → 27; phase descriptor updated |
| `src/data/research/problems/minkowski-theorem-oq-04.json` | `currentState.iteration: 26 → 27`; `currentState.focus` + `nextAction` refreshed; `attemptCounts.total: 26 → 27`; `currentApproach: 12 → 13`; `knowledge.progressSummary` updated; +1 builtItems; +2 insights |
| `research/problems/minkowski-theorem-oq-04/sessions/2026-05-16-s27-s24-act-pr-a-volume-tsum-lattice.md` | this memo (new file) |

**Deferred to Mechanic** (per S26 D2, still owned externally):

- `meta.status: axiomatized → verified`
- `meta.badge: axiom → original`
- `meta.assumptions` rewrite (drop "pending Docker CI" caveat)
- `mainTheorems[blichfeldt_general].type: axiom → proved`
- New `mainTheorems[]` entry for `volume_eq_setLIntegral_indicator_tsum_lattice` (best left to Mechanic to also re-derive the `leanType` string + cross-reference summary)

## 7. Honest-status block

- **Mathematical originality**: zero. PR-A is a mechanical lift of an already-proved template against a different basis; the underlying analytic content (`IsAddFundamentalDomain.lintegral_eq_tsum''` + Tonelli) was already discharged in S9 PR #16995. PR-A only widens the applicable parameter set.
- **Pedagogical value**: moderate. Makes the dependence on `stdLattice` cosmetic and exposes the basis as a parameter, which is the precondition for PR-B / PR-C (lattice Blichfeldt + lattice Minkowski).
- **Build-verification status**: ✅ Docker-clean 3075 jobs first-try; no caveats.
- **Axiom status**: source remains 0 textual axioms + 0 structure-encoded assumptions + 0 sorries. Gallery `axiomatized → verified` flip still Mechanic-owned (S26 D2).
- **Open conjecture status**: unchanged. PR-A is infrastructure; the headline open question (general-k Minkowski for arbitrary lattices) is unlocked at the PR-C step.

## 8. Anti-scope hygiene

PR-A retains the S23 anti-scope:

- ❌ No `minkowski_general_k_symm` (deferred since Iter 18, orthogonal)
- ❌ No `minkowski_five_points` (k = 4 corollary, independent extrapolation)
- ❌ No `blichfeldt_general_pairwise_finset` / `minkowski_general_k_pairwise_finset` wrapper closers
- ❌ No #17599 rebase or close (next picker's call)
- ❌ No gallery status/badge flip (Mechanic-owned)
- ❌ No `mainTheorems[]` entry addition (Mechanic re-derives `leanType` strings)

## 9. Next steps (post-merge)

1. **PR-B**: `blichfeldt_general_lattice` (~80 LOC + ~30% LOC buffer per insight, so ~100 LOC realistic). Insertion site: after `blichfeldt_general` (post `blichfeldt_basic_from_general` ~line 442). Body uses PR-A's `volume_eq_setLIntegral_indicator_tsum_lattice` directly and substitutes per S23 §4 6-row table (`stdBasis n` → `b`, `stdLattice_covolume` removed in favour of `volume (ZSpan.fundamentalDomain b)` as covolume term). PR-B can be opened against the head of PR-A per S23 §4 implementation note.
2. **PR-C**: `minkowski_general_k_lattice` (~50 LOC + buffer ≈ ~65 LOC). Parameter-lifted copy of `minkowski_general_k`; depends on PR-B but independent of PR-A directly.
3. (Mechanic) gallery flip per S26 D2.
4. (Next picker) #17599 rebase or close.
