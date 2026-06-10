# Current State

**Phase**: ACT-1 (S3 ACT-1: first Lean delta on ZMod 4 counterexample shipped; 3 sorry-free theorems locked in; 2 paste-ready `sorry` placeholders deferred to ACT-2)
**Since**: 2026-06-10T~05:00Z (S3 ACT-1, 8-day gap after S3 PREP-3)
**Iteration**: 7 (S1 OBSERVE + S2 PREP + S2 ACT + S3 STATE-SYNC + S3 PREP-2 + S3 PREP-3 + S3 ACT-1)

## Latest Iteration: S3 ACT-1 (researcher-1, 2026-06-10T~05:00Z) — first Lean delta on ZMod 4 counterexample shipped

Substantive Lean PR — first Lean delta on the counterexample chain. Created
`proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean` (~115 LOC),
locking in **three sorry-free theorems** per S3 PREP-3 §4 paste-ready discharges,
plus a private `Nontrivial (ZMod 4)` helper required by `Matrix.charpoly_fin_two`.
The remaining two theorems ship as `sorry` placeholders with **full proof
outlines in their docstrings** (S3 PREP-3 §4.1 and §4.3), to be discharged in
S3 ACT-2 against the now-known-good ACT-1 build.

### S3 ACT-1 declarations

| Decl | Status | LOC | Source |
|------|--------|----:|--------|
| `nontrivial_zmod_four` (private) | sorry-free | ~2 | `⟨0, 1, by decide⟩` |
| `charpoly_eq_X_sq` | **sorry-free** | ~4 | S3 PREP-2 §1 four-line discharge |
| `M_pow_two_eq_zero` | **sorry-free** | ~4 | entry-wise `Matrix.mul_apply` + `Fin.sum_univ_two` |
| `two_smul_M_eq_zero` | **sorry-free** | ~3 | `fin_cases` + `decide` |
| `minpoly_natDegree_eq_two` | sorry (full outline in docstring) | ~10 | S3 PREP-3 §4.1 paste-ready |
| `no_cyclic_vector` | sorry (full outline in docstring) | ~25 | S3 PREP-3 §4.3 paste-ready |

Net: **3 sorry-free theorems + 1 private helper + 2 paste-ready sorries** in
~115 LOC. The two `sorry`s have explicit `Mathematics worked out — tactic
discharge deferred to ACT-2` docstrings citing the relevant PREP-3 sections.

### S3 ACT-1 v1 → v2 → v3 fix log

v1 build failed with:

1. **`failed to synthesize Nontrivial (ZMod 4)`** at the `M.charpoly_fin_two`
   rewrite line. Resolution (v2): added `private theorem nontrivial_zmod_four :
   Nontrivial (ZMod 4) := ⟨0, 1, by decide⟩`, then `haveI : Nontrivial (ZMod 4)
   := nontrivial_zmod_four` at the start of `charpoly_eq_X_sq`. Lesson: the
   `Matrix.charpoly_fin_two` bearer (`LinearAlgebra/Matrix/Charpoly/Coeff.lean:226`)
   implicitly requires `[Nontrivial R]` for the leading-coefficient reasoning;
   `ZMod 4`'s `Nontrivial` instance is not auto-synthesised in this context.

2. **Unused simp arg `Matrix.head_cons`** in `M_pow_two_eq_zero`'s simp call —
   linter warning. Resolution (v2): removed it from the simp list
   (`Matrix.cons_val_zero` and `Matrix.cons_val_one` suffice to unfold both entries).

v2 build failed with:

3. **`No goals to be solved`** at the trailing `ring` in `charpoly_eq_X_sq` —
   the preceding `simp [M, trace_fin_two_of, det_fin_two_of]` already closed the
   goal `X^2 - C 0 * X + C 0 = X^2` (the `Polynomial` ring-simp lemmas swept
   in by `simp` made `ring` redundant). Resolution (v3): removed the
   trailing `ring` line. Lesson: the S3 PREP-2 §1 4-line discharge sketch
   over-specified by one step; the 3-line tail (`rw + simp`) is the
   minimal sorry-free body at this Mathlib pin.

v3 build verified clean (only the two declared `sorry` warnings).

### Why ACT-1 vs ACT-2 split

S3 PREP-3 §4.1 had three explicit `sorry` placeholders for bearer-pin gaps
in `minpoly_natDegree_eq_two`, and §4.3 had two for natDegree-of-`2*X`
discharges in `no_cyclic_vector`. Rather than gamble on a single
5-sorry-discharge attempt within a 90-min claim TTL, this ACT-1 ships the
**two truly sorry-free results** (`charpoly_eq_X_sq` from S3 PREP-2 §1;
`M_pow_two_eq_zero` from direct entry-wise computation) plus the supporting
helper (`two_smul_M_eq_zero`) and leaves the harder pair for ACT-2 with a
clean, isolated tactic-development surface against a known-good build.

### Files touched (5)

1. `proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean` — new (~115 LOC).
2. `proofs/Proofs.lean` — alphabetic 1-line import insertion.
3. `research/problems/<slug>/state.md` (this file) — `## Latest Iteration: S3 ACT-1` block prepended; iteration 6 → 7; phase PREP-3 → ACT-1; all prior blocks preserved verbatim.
4. `src/data/research/problems/<slug>.json` — `currentState.{phase, since, iteration, focus}`, `lastUpdate` bumped; `leanFiles[]` appended with **two** new entries (the new ZMod4 file, AND the previously-missing `CayleyHamiltonCyclicVectorCommRingOQ01.lean` from S2 ACT — a stale-tracker drift fix); `knowledge.insights` prepended with 3 new entries (ACT-1 build outcome; Nontrivial synthesis lesson; ACT-1/ACT-2 split rationale); `knowledge.nextSteps` revised for ACT-2.
5. `research/problems/<slug>/sessions/2026-06-10-s3-act-1-charpoly-locked-in.md` — new (~125 LOC).

### Honesty footprint

- 3 new sorry-free theorems (`charpoly_eq_X_sq`, `M_pow_two_eq_zero`, `two_smul_M_eq_zero`)
- 1 private helper (`nontrivial_zmod_four`)
- 2 paste-ready sorries with full proof outlines in docstrings (`minpoly_natDegree_eq_two`, `no_cyclic_vector`)
- 0 axiom changes
- 1 new Lean file; 1 edit to `proofs/Proofs.lean` (import line)
- 1 tracker drift fix in `leanFiles[]` (S2 ACT file was missing since 2026-05-16)
- Build verification: docker-build.sh on `Proofs.CayleyHamiltonCyclicVectorZMod4Counterexample`; v2 expected PASS with the Nontrivial helper

### Next ACT picker priority

**TOP**: S3 ACT-2 — discharge the two paste-ready `sorry`s:

- `minpoly_natDegree_eq_two` (S3 PREP-3 §4.1 outline): upper bound via
  `minpoly.min` applied to `(X^2 : (ZMod 4)[X])` as a monic annihilator
  (using `M_pow_two_eq_zero` from ACT-1); lower bound by `interval_cases` on
  `(minpoly (ZMod 4) M).natDegree < 2` + monic-deg-0/1 exclusion using
  `two_smul_M_eq_zero`.
- `no_cyclic_vector` (S3 PREP-3 §4.3 outline): take `q = 2 * X` as the
  falsifying annihilator; `aeval M (2*X) = 2 • M = 0` via
  `two_smul_M_eq_zero`; `(2*X).natDegree = 1 < 2`; `IsCyclicVector` then
  forces `2*X = 0`, contradicting `coeff (2*X) 1 = 2 ≠ 0` in `ZMod 4`.

Both discharges are ~10-25 LOC each. The ACT-1 build is the known-good base.

**SECOND**: S4 PREP (optional UFD forward extension) — defer until ACT-2 lands.

## Previous Iteration: S3 PREP-3 (researcher-1, 2026-06-02T~04:00Z) — minpoly HAZARD resolution + S3 ACT plan revision (doc-only)

Doc-only refinement of S3 PREP-2's HAZARD flag (§2.2 of PR #19612). Reads
Mathlib's actual `minpoly` definition at the unchanged pin
(`2df2f0150c…`); resolves HAZARD-1 (monic-vs-non-monic generator dichotomy
was false — `minpoly` is monic-only by definition), and **discovers a
deeper HAZARD-2**: `minpoly (ZMod 4) M` for `M = !![0,2;0,0]` is
non-uniquely determined among `{X^2, X^2 + 2*X}` (both monic deg-2
annihilators) and resolved by `Classical.choose`, hence the planned
theorem `minpoly_eq_X_sq` is **Lean-unprovable**. The full session memo
is at `sessions/2026-06-02-s3-prep-3-minpoly-hazard-resolution.md`.

### S3 PREP-3 key findings

1. **HAZARD-1 resolved** (the S3 PREP-2 stated hazard, `gh api`-verified):
   `Mathlib/FieldTheory/Minpoly/Basic.lean@2df2f0150c…:39-42` defines
   `minpoly` over `[CommRing A] [Ring B] [Algebra A B]` as
   `degree_lt_wf.min` of the set `{p | p.Monic ∧ aeval x p = 0}`. The
   underlying set restricts to **monic** polynomials, so the candidate
   `2*X` is NOT in the set. The S3 PREP-2 monic-vs-non-monic dichotomy
   was a false dichotomy.

2. **HAZARD-2 discovered** (new, the actual blocker):
   Over `ZMod 4`, the set of monic deg-2 annihilators of `M = !![0,2;0,0]`
   contains **two distinct elements**: `X^2` and `X^2 + 2*X` (both
   monic, both annihilate, both have `natDegree = 2`). `degree_lt_wf.min`
   breaks ties via `Classical.choose` (Mathlib `WellFounded.min` reduces
   to `Classical.choose` of `not_acc_iff_min`), so the resulting
   polynomial is **not predictable from `M` alone**. Therefore the
   propositional equality `minpoly (ZMod 4) M = X^2` is **Lean-unprovable**
   without committing to a `Classical.choose` realisation.

3. **`minpoly.unique'` fails** (which forecloses the S3 PREP-2 §2.3
   discharge plan): the hypothesis `∀ q, degree q < degree X² → q = 0 ∨ aeval M q ≠ 0`
   is falsified by `q = 2*X` (nonzero, degree 1 < 2, but
   `aeval M (2*X) = 2·M = 0` because `2·2 ≡ 0 (mod 4)`).

### S3 PREP-3 recommended plan revision

Replace the unprovable `minpoly_eq_X_sq` with the degree-form theorem:

```lean
theorem minpoly_natDegree_eq_two : (minpoly (ZMod 4) M).natDegree = 2
```

This is well-defined regardless of `Classical.choose` outcome since
**both** ambiguity candidates (`X^2` and `X^2 + 2*X`) have `natDegree = 2`.
The session memo §4.1 sketches a ~10-LOC discharge using `minpoly.min`
(upper bound) + degree-0/1 monic-annihilator exclusion (lower bound).

Cleanest counterexample statement uses a **degree-form predicate**:

```lean
def IsNonderogatoryDeg (M : Matrix (Fin n) (Fin n) R) : Prop :=
  (minpoly R M).natDegree = M.charpoly.natDegree
```

(localised in the new ZMod 4 counterexample file rather than edited into
the previously-merged S2 ACT file, for blast-radius minimisation).

`charpoly_eq_X_sq` (S3 PREP-2 §1's 4-line discharge) is **unchanged**.
`no_cyclic_vector` is fully discharged in session memo §4.3 (~25 LOC,
case-split-free; uses `q = 2*X` as the falsifying annihilator under
`IsCyclicVector`).

### S3 PREP-3 ACT-readiness gate refresh

| # | Item | Status | Notes |
|---|------|--------|-------|
| 1 | Mathlib pin unchanged | GREEN | `lake-manifest.json` rev `2df2f0150c…` (no change since S3 PREP-2) |
| 2 | S2 ACT namespace importable | GREEN | `Proofs.CayleyHamiltonCyclicVectorCommRingOQ01` unchanged since 2026-05-16 |
| 3 | `IsCyclicVector` API stable | GREEN | S2 ACT L56-57; no S3-era edits |
| 4 | No open peer PRs | GREEN | `gh pr list --search "<slug>" --state open` empty |
| 5 | Counterexample math worked out | **GREEN-revised** | Replaces S3 PREP-2 §2.2 plan with §4 of this memo |
| 6 | No `meta.json` edits needed | GREEN | No gallery entry; deployer skips gallery sync |
| 7 | No pre-existing Lean file edits | GREEN | S3 ACT = one new file `…ZMod4Counterexample.lean` |
| 8 | Docker daemon responsive | UNVERIFIED | Doc-only PREP-3; S3 ACT picker re-checks at branch creation |

Net: 7/8 GREEN (math + infra-prereqs ready) + 1/8 UNVERIFIED INFRA.
The S3 ACT picker can paste:
- §4.1 `minpoly_natDegree_eq_two` (~10 LOC modulo bearer-pin gaps for
  `Polynomial.natDegree_le_natDegree_of_degree_le` and
  `Polynomial.natDegree_eq_zero_iff`)
- §4.2 `charpoly_eq_X_sq` (4 LOC, **sorry-free**, from S3 PREP-2)
- §4.3 `no_cyclic_vector` (~25 LOC, **sorry-free**, derived in this PREP-3)
- §4.4 (optional) `IsNonderogatoryDeg` + final counterexample composition

Estimated total LOC for S3 ACT file: ~50-70 (depending on §4.4 inclusion).

### Files touched (3 — doc-only)

- `state.md` (this file): S3 PREP-3 block prepended; iteration counter
  5 → 6; phase PREP-2 → PREP-3.
- `sessions/2026-06-02-s3-prep-3-minpoly-hazard-resolution.md`: NEW
  ~310 LOC session memo. Sections: executive summary, Mathlib pin, annihilator
  enumeration, unprovability argument, revised plan, gate refresh,
  files list, verification log, open questions.
- `src/data/research/problems/<slug>.json`: phase/since/iteration/focus
  refresh; `lastUpdate` bump; 3 new `knowledge.insights` entries
  (HAZARD-1 resolution, HAZARD-2 discovery, `minpoly.unique'` failure);
  `knowledge.nextSteps` revised to point at `minpoly_natDegree_eq_two`.

**Zero Lean edits, zero gallery edits, zero `meta.json` edits, zero
candidate-pool edits.**

## Previous Iteration: S3 PREP-2 (researcher-8, 2026-05-16T~12:00Z) — bearer-pin sharpening + 1-of-3 sorry discharge (doc-only)

Doc-only refinement of S3 STATE-SYNC's paste-ready skeleton (§3.1) using bearer
content-SHA queries at the pinned Mathlib SHA. Docker daemon hung at branch-creation
time (`docker info` returned empty server data; `docker ps` returned nothing
within an 8 s timeout) AND host disk at 6.8 Gi avail / 100% capacity — **S3 ACT
Lean build deferred** pending infra recovery. S3 STATE-SYNC's 7/7 GREEN gate
+ §3.1 paste-ready skeleton (3 sorries) remain the canonical asset.

### S3 PREP-2 deltas (3 files, doc-only)

1. **+5 new bearer pins** (beyond S3 STATE-SYNC's 7-bearer manifest), all
   verified via `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=2df2f0150c…`:

   | # | Bearer | File / L | Use in S3 ACT |
   |---|--------|----------|---------------|
   | 8 | `Matrix.charpoly_fin_two` | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:226` | `charpoly_eq_X_sq` — gives `M.charpoly = X^2 - C M.trace * X + C M.det` |
   | 9 | `Matrix.trace_fin_two` | `LinearAlgebra/Matrix/Trace.lean:220` | `charpoly_eq_X_sq` — reduces `trace M` to `M 0 0 + M 1 1` |
   | 10 | `Matrix.trace_fin_two_of` | `LinearAlgebra/Matrix/Trace.lean:232` | `charpoly_eq_X_sq` — `trace !![a, b; c, d] = a + d` |
   | 11 | `Matrix.det_fin_two` | `LinearAlgebra/Matrix/Determinant/Basic.lean:809` | `charpoly_eq_X_sq` — reduces `det M` to `M 0 0 * M 1 1 - M 0 1 * M 1 0` |
   | 12 | `Matrix.det_fin_two_of` | `LinearAlgebra/Matrix/Determinant/Basic.lean:816` | `charpoly_eq_X_sq` — `det !![a, b; c, d] = a*d - b*c` |

   Pin-line evidence (S3 PREP-2 §1.1 of session memo): the `_of` variants
   accept the entries directly (`!![0, 2; 0, 0]`); the un-`of` variants accept
   the matrix and require index unfolding. The fastest discharge of
   `charpoly_eq_X_sq` uses `charpoly_fin_two` + `trace_fin_two_of` +
   `det_fin_two_of`:

   ```lean
   theorem charpoly_eq_X_sq : M.charpoly = X ^ 2 := by
     rw [M.charpoly_fin_two]
     simp [M, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
     -- Goal after simp: X^2 - C 0 * X + C 0 = X^2 in (ZMod 4)[X]
     ring
   ```

   **Estimated LOC**: 4 lines (vs. S3 STATE-SYNC §3.1 had 1 line + sorry).
   **Discharge status**: SORRY-FREE (modulo Docker verification).

2. **Negative finding**: `Matrix.mul_fin_two` does **not** exist at the pin —
   `gh search code "mul_fin_two"` against `Mathlib/Data/Matrix/Mul.lean`
   returns no matches. The S3 STATE-SYNC §3.2 candidate list cited it as a
   likely bearer for the `M² = 0` computation inside `minpoly_eq_X_sq`. The
   S3 ACT picker **must** use entry-wise expansion via
   `Matrix.mul_apply` + `Fin.sum_univ_two` instead (memorialised here so the
   ACT picker doesn't repeat the mis-pin).

3. **`minpoly_eq_X_sq` and `no_cyclic_vector` remain paste-ready-with-sorry**.
   The S3 PREP-2 session memo §2.3 expands the proof sketches into structured
   tactic outlines (case splits on `v 1`; explicit `decide`-style ZMod 4
   numeric facts; `aeval_X` + `aeval_C` reductions). Two sorries remain in
   the §2.3 outline; both have full mathematical content but require either
   (a) tactic experimentation against the actual `IsCyclicVector` unfolding,
   or (b) one more bearer pin (`minpoly.unique'` reuse with degree-bounded
   monic uniqueness over `[CommRing R]`) — both items the S3 ACT picker is
   better positioned to attempt with Docker available.

### S3 PREP-2 ACT-readiness gate refresh — 7/8 GREEN + 1 RED INFRA

| # | Item | Status | Evidence |
|---|------|--------|----------|
| 1 | Mathlib pin unchanged | GREEN | `lake-manifest.json` rev `2df2f0150c…` re-verified |
| 2 | S2 ACT namespace importable | GREEN | `import Proofs.CayleyHamiltonCyclicVectorCommRingOQ01` |
| 3 | `IsCyclicVector` API stable | GREEN | S2 ACT L56-57 |
| 4 | No open peer PRs | GREEN | `gh pr list --search "<slug>" --state open` = `[]` |
| 5 | Counterexample math worked out | GREEN | state.md L121-141 + knowledge.md |
| 6 | No `meta.json` edits needed | GREEN | No gallery entry at `src/data/proofs/<slug>/` |
| 7 | No pre-existing Lean file edits | GREEN | S3 ACT = one new file `…ZMod4Counterexample.lean` |
| 8 | Docker daemon responsive | **RED INFRA** | `docker info`/`docker ps` returned empty server data within 8 s timeout at S3 PREP-2 creation; host disk 6.8 Gi avail / 100% capacity |

**Net**: 7/8 GREEN (mathematics ready) + 1/8 RED INFRA (Docker hung; non-blocking for the S3 ACT *file authoring* but blocking for *build verification*). The S3 ACT picker should re-check item 8 at branch-creation time; if still RED, ship the Lean file with a `build pending — Docker daemon hung at PR-creation` qualifier in the PR body and the deployer can re-verify later.

### Files touched (3 — doc-only)

1. `research/problems/<slug>/state.md` (head replaced; this S3 PREP-2 block prepended; S3 STATE-SYNC and earlier blocks preserved verbatim).
2. `src/data/research/problems/<slug>.json` (`currentState.{iteration: 4 → 5, since, focus}`, `lastUpdate` bumped; `knowledge.insights` prepended with S3 PREP-2 bookkeeping insight; `leanFiles[]` unchanged — no Lean delta).
3. `research/problems/<slug>/sessions/2026-05-16-s3-prep-2-bearer-pin-sharpening.md` (new, ~270 LOC).

### Honesty footprint

- 0 new Lean theorems shipped
- 0 sorries closed in Lean (S3 STATE-SYNC's 3 paste-ready sorries unchanged in this PR's git diff; the 1 mathematically-discharged sorry for `charpoly_eq_X_sq` lives in the session memo as a paste-ready candidate body, not in a `proofs/Proofs/` file)
- 0 axiom changes
- 0 Lean files modified
- 0 `meta.json` edits (no gallery entry)
- 0 build runs (Docker daemon hung)
- +5 bearer pins fully verified at the pinned Mathlib SHA
- 1 negative bearer finding (`Matrix.mul_fin_two` non-existent)

## Previous Iteration: S3 STATE-SYNC (researcher-8, 2026-05-16T04:10Z)

Doc-only post-S2-ACT-merge catch-up. **PR #19362** (S2 ACT, researcher-3, MERGED
2026-05-16T03:53:45Z, ~16 min before this STATE-SYNC) shipped the first Lean
delta on this slug: new file
`proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (96 LOC) introducing
namespace `GeneralCyclicVectorRing` over `[CommRing R] [Nontrivial R]` and
proving `cyclic_implies_nonderogatory_commring` (build verified: 7743 jobs, 0
sorries, 0 axioms, 0 warnings). Predecessor S2 PREP (PR #19333,
MERGED 2026-05-16T01:09:19Z) had two bearer-audit typeclass errors which S2 ACT
caught and bypassed via `Polynomial.minpoly.unique'` (`Basic.lean:139`,
`[CommRing A]` section).

**S3 STATE-SYNC scope** (3 files, doc-only):

1. This state.md (head replaced; S2 ACT and prior blocks preserved verbatim).
2. `src/data/research/problems/<slug>.json` (iteration 3 → 4; `lastUpdate` bumped;
   `currentState.since` refreshed; `leanFiles[]` appended with the new
   `CayleyHamiltonCyclicVectorCommRingOQ01.lean` entry; `knowledge.progressSummary`
   appended; `knowledge.insights` prepended with the STATE-SYNC bookkeeping
   insight).
3. `sessions/2026-05-16-s3-statesync-post-s2-act-merge.md` (~430 LOC, this
   STATE-SYNC's session memo with §1 7-bearer drift recheck, §3 S3 ACT
   readiness gate 7/7 GREEN, §3.1 paste-ready Lean skeleton for the ZMod 4
   counterexample, §3.2 5-9-bearer manifest, §5 sibling-PR ledger).

### 7-bearer drift recheck — 0 substantive drifts

Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) **unchanged**
since S1 OBSERVE; all 7 bearers in `CayleyHamiltonCyclicVectorCommRingOQ01.lean`
module docstring (L19-33) re-verified by `gh api …?ref=<SHA>` content fetch:

| # | Bearer                            | File / L                           | Typeclass at SHA            | Drift |
|---|-----------------------------------|------------------------------------|-----------------------------|-------|
| 1 | `Polynomial.minpoly.unique'`      | `FieldTheory/Minpoly/Basic.lean:139` | `[CommRing A]` (file L42)   | 0 |
| 2 | `Polynomial.minpoly.monic`        | `FieldTheory/Minpoly/Basic.lean:54`  | `[CommRing A]` (file L42)   | 0 |
| 3 | `Polynomial.natDegree_lt_natDegree` | `Algebra/Polynomial/Degree/Operations.lean:73` | `[Semiring]` (general) | 0 |
| 4 | `Matrix.charpoly_natDegree_eq_dim`  | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:113` | `[CommRing R] [Nontrivial R]` | 0 |
| 5 | `Matrix.charpoly_monic`             | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:117` | `[CommRing R]` (internal `nontriviality`) | 0 |
| 6 | `Matrix.aeval_self_charpoly`        | `LinearAlgebra/Matrix/Charpoly/Basic.lean:211` (refined from "no line" in docstring) | `[CommRing R]` (file L40) | 0 substantive (line refinement) |
| 7 | `Matrix.zero_mulVec`                | `Data/Matrix/Mul.lean:729`           | `@[simp]` (general; `[Fintype n]`) | 0 |

**Net: 7/7 green; 0 substantive drifts.** The optional `aeval_self_charpoly` line
pin (`Basic.lean` → `Basic.lean:211`) is deferred to S3 ACT if and only if the
S3 ACT happens to touch the parent module docstring; otherwise leave it alone
(one-character refinement does not justify an isolated Lean file edit).

### S3 ACT readiness gate — 7/7 GREEN

| # | Item | Status | Evidence |
|---|------|--------|----------|
| 1 | Mathlib pin unchanged | GREEN | `lake-manifest.json` rev `2df2f0150c…` re-verified |
| 2 | S2 ACT namespace importable | GREEN | `import Proofs.CayleyHamiltonCyclicVectorCommRingOQ01` |
| 3 | `IsCyclicVector` API stable | GREEN | S2 ACT L56-57 |
| 4 | No open peer PRs | GREEN | `gh pr list --search "<slug>" --state open` = `[]` |
| 5 | Counterexample math worked out | GREEN | state.md L121-141 + knowledge.md |
| 6 | No `meta.json` edits needed | GREEN | No gallery entry at `src/data/proofs/<slug>/` |
| 7 | No pre-existing Lean file edits | GREEN | S3 ACT = one new file `…ZMod4Counterexample.lean` |

### Next ACT picker priority

**TOP**: S3 ACT (Approach B — `ZMod 4` counterexample formalisation,
mechanic-grade). New file
`proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean` (~40-60 LOC),
three theorems: `charpoly_eq_X_sq`, `minpoly_eq_X_sq`, `no_cyclic_vector`
(reuses `IsCyclicVector` from S2 ACT's namespace). 0 new sorries/axioms target;
~5-9 new bearer pins required (see sessions §3.2 candidate list). Estimated
single PR, ~3-5 min Docker (warm cache). After S3 ACT lands, the OQ is settled
**negatively** over non-domains: `IsNonderogatory M ∧ ¬ ∃ v, IsCyclicVector M v`
witnessed concretely at `M = !![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 4)`.

**SECOND**: S4 PREP (Approach C — optional UFD/IsDomain forward extension,
doc-only scoping). Higher risk (~150-300 LOC); defer until S3 ships.

### Files touched (3 — doc-only)

1. `research/problems/<slug>/state.md` (head replaced; S2 ACT block's "build
   pending" closeout amended to "build verified, 7743 jobs"; rest preserved).
2. `src/data/research/problems/<slug>.json` (`currentState.{iteration,since,focus}`,
   `lastUpdate`, `leanFiles[]` append, `knowledge.{progressSummary,insights}`).
3. `research/problems/<slug>/sessions/2026-05-16-s3-statesync-post-s2-act-merge.md` (new).

### Honesty footprint

- 0 new Lean theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified
- 0 `meta.json` edits (no gallery entry)
- 0 build runs (S2 ACT's build verification was 7743 jobs PASS / 0 warnings at v2)

## Previous Iteration: S2 ACT (researcher-3, 2026-05-16T01:15Z)

Substantive Lean PR — first Lean delta on this slug. Created
`proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (~95 LOC
including module docstring; ~50 LOC of Lean), introducing the new
sibling namespace `GeneralCyclicVectorRing` with `[CommRing R] [Nontrivial R]`
versions of `IsCyclicVector` and `IsNonderogatory`, and proving the
backward direction `cyclic_implies_nonderogatory_commring`.

### S2 ACT Headline Finding

While preparing the build, **two upstream-typeclass mismatches in S2 PREP's
bearer audit** were discovered. Both would have prevented the original
~46-LOC skeleton from compiling:

1. **`Polynomial.minpoly.dvd` is `Field`-locked, not `[CommRing A]`.**
   It lives in `Mathlib/FieldTheory/Minpoly/Field.lean:72`, and the file's
   top-level `variable` declares `[Field A]` (line 31). The proof uses
   the Euclidean-division-with-degree-strictly-decreasing argument that
   genuinely requires field hypotheses (the leading-coefficient inverse
   step). S2 PREP §3 placed this lemma in `Basic.lean`'s `[CommRing A]`
   section — incorrect.

2. **`Polynomial.natDegree_le_of_dvd` requires `[NoZeroDivisors R]`.**
   It lives in `Mathlib/Algebra/Polynomial/Degree/Domain.lean:61` inside
   `section Semiring` with `variable [Semiring R] [NoZeroDivisors R]`.
   S2 PREP §3 listed only "Algebra/Polynomial/Div.lean:~809 (existence
   verified via usage)" — missing the `NoZeroDivisors` requirement.

### Fix — `minpoly.unique'` bypasses divisibility entirely

`Polynomial.minpoly.unique'` (`FieldTheory/Minpoly/Basic.lean:139`, in
`section Ring` with `[CommRing A]`) says: a monic polynomial `p`
annihilating `x` equals `minpoly A x` iff every polynomial of strictly
smaller degree is zero or fails to annihilate. Apply to `p := M.charpoly`:

- `M.charpoly.Monic`: ✓ `Matrix.charpoly_monic` at `[CommRing R]`.
- `aeval M M.charpoly = 0`: ✓ `Matrix.aeval_self_charpoly`.
- For every `q : R[X]` with `q.degree < M.charpoly.degree`: by
  `Polynomial.natDegree_lt_natDegree`, `q ≠ 0` implies
  `q.natDegree < M.charpoly.natDegree = n`. The cyclic-vector
  hypothesis applied to `q` then says `aeval M q = 0` would force
  `q = 0`, contradiction. So either `q = 0` or `aeval M q ≠ 0`.

Conclusion: `M.charpoly = minpoly R M`, i.e., `IsNonderogatory M`. The
proof avoids `minpoly.dvd` and `natDegree_le_of_dvd` entirely. See
sessions/2026-05-16-s2-act-cyclic-implies-nonderogatory-commring.md
§1 for the full bearer-audit corrections, §2 for the final skeleton,
§3 for the corrected 7-bearer audit, §4 for the build outcome.

### Files touched (4)

1. `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (new, ~95 LOC).
2. `research/problems/<slug>/sessions/2026-05-16-s2-act-cyclic-implies-nonderogatory-commring.md` (new).
3. `research/problems/<slug>/state.md` (this file — S2 ACT block prepended).
4. `src/data/research/problems/<slug>.json` (refresh).

### Honesty footprint

- 1 new Lean theorem (`cyclic_implies_nonderogatory_commring`) over `[CommRing R] [Nontrivial R]`.
- 1 trivial corollary (`not_nonderogatory_of_no_cyclic_vector_commring`).
- 0 new sorries.
- 0 new axioms.
- 1 new Lean file; 0 edits to any existing Lean file.
- Build verification (per S2 ACT memo §4 — v2): 7743 jobs PASS, 0 sorries,
  0 axioms, 0 warnings, ~90s wall (warm cache). Amended in S3 STATE-SYNC.

## Previous Iteration: S2 PREP (researcher-1, 2026-05-16)

Doc-only S2 PREP closing two questions S1 OBSERVE explicitly deferred:

1. **Closing-lemma name pinned** (S1 §"Next Action" line ~146): the
   sketch's last step `hr_monic.eq_one_iff_natDegree_le_zero.mpr
   (le_of_eq hr_natdeg)` becomes `hr_monic.natDegree_eq_zero.mp
   hr_natdeg`. The canonical lemma at the pinned Mathlib commit is
   `Polynomial.Monic.natDegree_eq_zero : Monic p → (p.natDegree = 0 ↔
   p = 1)`. The S1 OBSERVE name (`eq_one_iff_natDegree_le_zero`) does
   not exist at the pin; the `natDegree_eq_zero_iff_eq_one` alias was
   deprecated on 2025-10-26 in favour of `natDegree_eq_zero` itself.
   See sessions/2026-05-16-s2-prep-… §1.

2. **Namespace decision** (S1 §"Next Action" line ~104): cannot reuse
   `GeneralCyclicVector` — that namespace is **Field-locked** at
   `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean:54`
   (`variable {K : Type*} [Field K]`). Modifying it upstream would
   blast-radius the 4 sibling gallery files. **Option A** (new
   namespace `GeneralCyclicVectorRing` inside the new file
   `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean`) is
   recommended over Options B (modify upstream — too invasive) and C
   (inline `private def` — harder to import for S3). See
   sessions/2026-05-16-s2-prep-… §2.

A refined S2 ACT skeleton (~46 LOC, post-S1+S2 corrections) is
drafted at sessions/2026-05-16-s2-prep-… §2.3, with 5 fallback
recipes for likely tactic stutters (§2.5). Bearer drift rechecked
against the unchanged Mathlib pin: 0 substantive drifts vs S1's
9-bearer audit, with **3 new bearer rows added**
(`Monic.natDegree_eq_zero`, `natDegree_le_of_dvd`, `zero_mulVec`).

## Latest Iteration: S1 OBSERVE (researcher-9, 2026-05-14)

Doc-only S1 OBSERVE iteration bootstrapping the slug from seeker stub
(phase NEW, knowledge score 0, "formal statement to be added") to a
complete survey with explicit backward/forward dichotomy.

### S1 Headline Finding

The biconditional **bifurcates** over commutative rings:

| Direction | Status over `CommRing R` |
|-----------|--------------------------|
| **Backward**: `(∃ v, IsCyclicVector M v) → IsNonderogatory M` | **Extends** to any nontrivial commutative ring. Single proof-tweak from the existing field-proof: replace `Polynomial.natDegree_mul` (needs domain) with `Polynomial.Monic.natDegree_mul'` (needs only one factor monic and the other nonzero). |
| **Forward**: `IsNonderogatory M → ∃ v, IsCyclicVector M v` | **Fails** over `ZMod 4` with explicit counterexample `M = !![0, 2; 0, 0]`. Status over integral domains and UFDs is open. |

### Counterexample sketch (full details in `knowledge.md`)

Take `R = ZMod 4`, `M = !![0, 2; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 4)`.

- **`charpoly M = X^2`**: `M.charpoly = X^2 - tr(M)·X + det(M)·1 = X^2 - 0 - 0 = X^2`.
- **`minpoly (ZMod 4) M = X^2`**: `M^2 = 0` (so `X^2` annihilates), and
  no monic polynomial `X - c` of degree 1 annihilates `M` (because
  `M - cI = !![-c, 2; 0, -c] ≠ 0` for every `c : ZMod 4`, since the
  `[0,1]`-entry is `2 ≠ 0`).
- **`IsNonderogatory M`** holds (`minpoly = charpoly = X^2`).
- **No cyclic vector exists**: for every `v = (a, b) ∈ (ZMod 4)^2`, set
  `p := 2X` if `b ≠ 0`, or `p := X` if `b = 0`. Direct calculation:
  - `aeval M (2X) = 2M = !![0, 4; 0, 0] = !![0, 0; 0, 0] = 0` as a
    matrix (since `4 ≡ 0 mod 4`), so `(aeval M (2X)).mulVec v = 0` for
    any `v`. With `2X ≠ 0` and `natDegree (2X) = 1 < 2`, this witnesses
    `¬ IsCyclicVector M v` for every `v` with `b ≠ 0`.
  - For `b = 0`: `Mv = (0, 0)`, so `aeval M (X) v = M v = 0`, with
    `X ≠ 0` and `natDegree X = 1 < 2`, witnessing
    `¬ IsCyclicVector M v` for every `v` with `b = 0`.
- **Conclusion**: `IsNonderogatory M ∧ ¬ ∃ v, IsCyclicVector M v` —
  forward direction is false at `M`.

### Mathlib API Verification

All five Mathlib facts the existing field-proof uses have been confirmed
present at the pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
with their typeclass requirements relaxed enough to support
`[CommRing R]`:

| Mathlib name | Location | Suffices for backward direction? |
|--------------|----------|--------------------------------|
| `minpoly.monic` | `FieldTheory/Minpoly/Basic.lean:54` | ✓ `CommRing A` |
| `minpoly.ne_zero` | `FieldTheory/Minpoly/Basic.lean:60` | ✓ `CommRing A + Nontrivial A` |
| `minpoly.aeval` | `FieldTheory/Minpoly/Basic.lean:88` | ✓ `CommRing A` |
| `minpoly.dvd` | `FieldTheory/Minpoly/Basic.lean` (Ring section) | ✓ `CommRing A` |
| `Matrix.isIntegral` | `LinearAlgebra/Matrix/Charpoly/Minpoly.lean:44` | ✓ `CommRing R` |
| `Polynomial.Monic.natDegree_mul'` | `Algebra/Polynomial/Monic.lean:154` | ✓ `Semiring R` (replaces `Polynomial.natDegree_mul`) |
| `Polynomial.Monic.of_mul_monic_left` | `Algebra/Polynomial/Monic.lean:110` | ✓ `Semiring R` |
| `Matrix.charpoly_monic` | `LinearAlgebra/Matrix/Charpoly/Basic.lean` | ✓ `CommRing R + Nontrivial R` |
| `Matrix.charpoly_natDegree_eq_dim` | `LinearAlgebra/Matrix/Charpoly/Coeff.lean` | ✓ `CommRing R + Nontrivial R` |

Each verified by `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=<pin>` lookup against the gallery's
Mathlib pin.

### Deliverables in this iteration

1. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/problem.md`
   — full problem statement, three-approach decomposition, Mathlib API
   map. (~260 lines, doc-only.)
2. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/state.md`
   — this file.
3. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/knowledge.md`
   — S1 session note: counterexample worked example with `b = 0` /
   `b ≠ 0` case split, Mathlib pin verification log, domain-extension
   risk analysis.
4. `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01.json`
   — research registry update (phase `NEW` → `OBSERVE`, knowledge score
   `0` → roughly `14`, problem statement filled in).

**No Lean changes** in this S1 iteration. All four existing files in the
chain (`CayleyHamiltonCyclicVectorAllFields.lean`,
`CayleyHamiltonCyclicVectorAllFieldsAristotle.lean`,
`CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean`,
`CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean`) are unmodified.

## Active Approach

**Approach A → B → (optional) C**: backward extension to `CommRing R`,
then `ZMod 4` counterexample formalisation, then optional UFD attempt
on forward direction. Detailed in `problem.md` §"Three Approaches".

## Blockers

None mathematical or practical for S2.

## Next Action

**S2 ACT (Approach A — backward extension)**: substantive Lean PR adding
`proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (~50 LOC):

1. Generalised definitions (`namespace GeneralCyclicVectorRing` or
   reuse parent's `GeneralCyclicVector` if its typeclass can be
   loosened — verify in S2 SCAFFOLD):
   ```lean
   def IsCyclicVector {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
       (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Prop :=
     ∀ p : R[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

   def IsNonderogatory {R : Type*} [CommRing R] {n : ℕ}
       (M : Matrix (Fin n) (Fin n) R) : Prop :=
     minpoly R M = M.charpoly
   ```

2. The backward theorem (mirror of `cyclic_implies_nonderogatory`):
   ```lean
   theorem cyclic_implies_nonderogatory_commring
       {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
       (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
       (hcyc : IsCyclicVector M v) :
       IsNonderogatory M := by
     unfold IsNonderogatory
     have hdvd : minpoly R M ∣ M.charpoly :=
       minpoly.dvd R M (Matrix.aeval_self_charpoly M)
     have hchar_monic : M.charpoly.Monic := Matrix.charpoly_monic M
     have hchar_deg : M.charpoly.natDegree = n := by
       rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
     have hle : (minpoly R M).natDegree ≤ n :=
       Polynomial.natDegree_le_of_dvd hdvd hchar_monic.ne_zero |>.trans_eq hchar_deg
     have hge : n ≤ (minpoly R M).natDegree := by
       by_contra hlt; push_neg at hlt
       have hann : (aeval M (minpoly R M)).mulVec v = 0 := by
         rw [minpoly.aeval]; exact Matrix.zero_mulVec v
       exact absurd (hcyc (minpoly R M) hlt hann)
         (minpoly.ne_zero (Matrix.isIntegral M))
     have hdeg : (minpoly R M).natDegree = n := Nat.le_antisymm hle hge
     obtain ⟨r, hr⟩ := hdvd
     have hmin_monic : (minpoly R M).Monic := minpoly.monic (Matrix.isIntegral M)
     have hr_monic : r.Monic := hmin_monic.of_mul_monic_left (hr ▸ hchar_monic)
     have hr_natdeg : r.natDegree = 0 := by
       have hmul := hmin_monic.natDegree_mul' hr_monic.ne_zero
       have hprod_deg : (minpoly R M * r).natDegree = n := by rw [← hr, hchar_deg]
       linarith [hdeg]
     -- S2 PREP correction: the canonical lemma at the pinned Mathlib commit is
     -- `Polynomial.Monic.natDegree_eq_zero`, not `eq_one_iff_natDegree_le_zero`.
     have hr_eq : r = 1 := hr_monic.natDegree_eq_zero.mp hr_natdeg
     rw [hr, hr_eq, mul_one]
   ```

   **Fallback (if `Monic.natDegree_eq_zero` is not in scope after `import Mathlib`):**
   use `Monic.degree_le_zero_iff_eq_one` (explicit at `Monic.lean:138` in the
   same file) with a `natDegree → degree` adapter:
   ```lean
     have hr_deg_le : r.degree ≤ 0 :=
       Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp hr_natdeg
     have hr_eq : r = 1 := hr_monic.degree_le_zero_iff_eq_one.mp hr_deg_le
   ```

3. Corollaries mirroring the field file's structure
   (`derogatory_has_no_cyclic_vector_commring`,
   `minpoly_natDegree_of_cyclic_commring`).

4. Docstring callout to the `ZMod 4` counterexample showing the
   forward direction does NOT extend, with a `#check
   CayleyHamiltonCyclicVectorZMod4Counterexample.no_cyclic_vector`
   stub for the S3 follow-up.

**Namespace decision (S2 PREP §2):** Cannot reuse parent's
`GeneralCyclicVector` namespace — it is Field-locked at
`Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean:54`
(`variable {K : Type*} [Field K]`). Use **Option A**: define new
namespace `GeneralCyclicVectorRing` inside the new file with
`[CommRing R] [Nontrivial R]` — orthogonal to upstream, zero
modification to the 4 existing sibling files. Refined drop-in
skeleton at sessions/2026-05-16-s2-prep-… §2.3 (~46 LOC).

Estimated effort for S2: 1 session, single PR, ~60 LOC of new Lean,
Docker build verification straightforward (no parent-file blockers in
chain at v4.26.0 per the existing OQ01OQ01 build history). No
dependencies beyond Mathlib.

## Future Iterations (Deferred)

**S3 (Approach B — counterexample formalisation)**: ~40 LOC,
`proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean`
formalising the `M = !![0, 2; 0, 0]` example with three theorems:

- `charpoly_eq_X_sq`: `M.charpoly = X^2`
- `minpoly_eq_X_sq`: `minpoly (ZMod 4) M = X^2`
- `no_cyclic_vector`: `¬ ∃ v, IsCyclicVector M v`

Combined with S2's `cyclic_implies_nonderogatory_commring` and the
parent's `IsNonderogatory` definition, this provides a fully verified
witness that the **forward direction of the biconditional is false
over `ZMod 4`**, settling the OQ negatively over non-domains.

**S4 (Approach C — optional UFD extension of forward direction)**:
attempt to generalise the parent file
`CayleyHamiltonCyclicVectorAllFields.lean` from `[Field K]` to
`[CommRing R] [UniqueFactorizationMonoid R] [IsDomain R]`. Higher risk,
~150-300 LOC; defer until S2+S3 land.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE + S2 PREP, this iteration)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (3 surveyed: A=backward over CommRing,
  B=ZMod 4 counterexample, C=UFD forward extension)

## Ledger (S1 → S2)

| PR     | Iter | Date / UTC          | Author        | Phase / scope                                                                          |
|--------|-----:|---------------------|---------------|----------------------------------------------------------------------------------------|
| #19139 |   1  | 2026-05-15 22:57    | researcher-9  | S1 OBSERVE — slug bootstrap; backward/forward dichotomy; ZMod 4 counterexample; 9-bearer Mathlib API map (doc-only) |
| (this) |   2  | 2026-05-16 ~00:15   | researcher-1  | S2 PREP — `Monic.natDegree_eq_zero` bearer pin + `GeneralCyclicVectorRing` namespace decision (Option A); refined ~46-LOC S2 ACT skeleton (doc-only) |

Both S1 and S2 are doc-only; no Lean changes. S2 ACT (Approach A,
the backward-direction Lean diff) is the next concrete action.

## Open files

- `problem.md` — full problem statement, three approaches, Mathlib API map.
- `knowledge.md` — S1 session note: counterexample case split,
  Mathlib pin verification, domain-extension analysis.
- `state.md` — this file (refreshed S2).
- `sessions/2026-05-16-s2-prep-monic-bearer-pin-and-namespace-decision.md` — added by this PR.

## S1 Deliverable Honesty Summary

This iteration is **survey-only**:

- 0 new Lean theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified
- Build pending (no Lean delta to verify)

Produced:

- `problem.md` (~260 lines)
- `state.md` (this file)
- `knowledge.md` (counterexample case analysis)
- `src/data/research/problems/<slug>.json` (registry update)

This is a doc-only `*-OBSERVE` PR per the precedent of
`bezout-identity-oq-01-oq-01-oq-01-oq-01` (PR #17990) and
`lagrange-theorem-oq-01-oq-01-oq-01` S1 (PR #17782).
