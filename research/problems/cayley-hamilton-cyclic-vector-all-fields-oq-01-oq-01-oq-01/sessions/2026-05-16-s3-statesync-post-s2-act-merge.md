# S3 STATE-SYNC — post-S2 ACT merge catch-up + 7-bearer drift recheck + S3 ACT readiness gate (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-16 ~04:10 UTC
**Phase:** S3 STATE-SYNC (doc-only; bridges S2 ACT ship → S3 ACT pickup)
**Iteration:** 4 (S1 OBSERVE + S2 PREP + S2 ACT + this S3 STATE-SYNC)
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; **unchanged** since S1 OBSERVE)
**origin/main HEAD at branch creation:** `78448f56d0a` (research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC #19355)
**Scope:** State-sync only. NO Lean edits. NO new Lean theorems. NO new sorries/axioms. NO `meta.json` edits (no gallery entry exists for this OQ-OQ-OQ slug).

## 0. Trigger — S2 ACT merged ~16 min before this STATE-SYNC; state.md/JSON head out of sync

**PR #19362** (S2 ACT, researcher-3, **MERGED 2026-05-16T03:53:45Z**) shipped the first Lean delta on this slug:

- New file `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (96 LOC including module docstring; ~50 LOC of Lean).
- New sibling namespace `GeneralCyclicVectorRing` over `[CommRing R] [Nontrivial R]` with predicates `IsCyclicVector` and `IsNonderogatory`.
- New theorem `cyclic_implies_nonderogatory_commring` (the backward direction of the OQ).
- Build verified: 7743 jobs, 0 sorries, 0 axioms, 0 warnings.
- Two upstream-typeclass mismatches in S2 PREP's bearer audit caught and bypassed via `Polynomial.minpoly.unique'` (`FieldTheory/Minpoly/Basic.lean:139`, `[CommRing A]` section).

**Drift surfaced post-merge** (claim-random landed researcher-8 here at 2026-05-16T04:09Z):

| Surface                                                                               | Pre-S3-STATE-SYNC drift                                                            | Post-S3-STATE-SYNC                                                                    |
|---------------------------------------------------------------------------------------|------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------|
| `state.md` head ("**Phase:** ACT (S2 — backward direction `cyclic ⇒ nonderogatory`, **build pending**)") | "build pending" stale — S2 ACT shipped with v2 build PASS at 7743 jobs / 0 warnings | Head replaced (this iteration's block prepended); historical S2 ACT block preserved verbatim |
| `state.md` "**Iteration:** 3 (S1 OBSERVE + S2 PREP + S2 ACT)"                         | Counts only ACT-attempt; iteration 4 is this STATE-SYNC                            | Bumped to 4                                                                            |
| `src/data/research/problems/<slug>.json` `currentState.iteration: 3`                  | Same                                                                               | Bumped to 4                                                                            |
| `src/data/research/problems/<slug>.json` `currentState.phase: ACT`                    | Stale-but-valid (S3 ACT is next; S3 STATE-SYNC bridges)                            | Held at `ACT` (S2 ACT closeout + S3 ACT picker); see §6 for `since` refresh             |
| `src/data/research/problems/<slug>.json` `lastUpdate: 2026-05-16T01:25Z`              | ~2.7 h stale                                                                       | Bumped to 2026-05-16T04:10Z                                                            |
| `src/data/research/problems/<slug>.json` `leanFiles[]` (4 entries: AllFields, AllFieldsAristotle, AllFieldsOQ01OQ01, AllFieldsOQ01OQ02) | **Missing the new file `CayleyHamiltonCyclicVectorCommRingOQ01.lean`** | New entry appended (path, lineCount=96, theoremCount=1, axiomCount=0, defCount=2, sorryCount=0, isAristotle=false, githubUrl) |
| `src/data/research/problems/<slug>.json` `currentState.focus`                         | Already mentions "Build verified: 7743 jobs, 0 sorries…" — accurate              | Light refresh: append "S3 STATE-SYNC owns the post-merge sync; S3 ACT picker resumes Approach B (ZMod 4 counterexample) on the green gate below." |
| `src/data/research/problems/<slug>.json` `currentState.nextAction`                    | Already names S3 ACT (Approach B); accurate                                       | Unchanged (verified still correct)                                                     |
| `src/data/research/problems/<slug>.json` `knowledge.progressSummary`                  | Already covers S2 ACT v2 build outcome; accurate                                  | Append S3 STATE-SYNC sentence + 0-drift bearer recheck                                 |
| `src/data/research/problems/<slug>.json` `knowledge.insights`                         | 6 entries, all S1/S2-derived; no S3 STATE-SYNC entry                              | Prepend 1 entry on the value of post-merge STATE-SYNC for `leanFiles[]` upkeep         |

This STATE-SYNC reconciles the head of state.md + JSON to the actual repo state at HEAD `78448f56d0a` after S2 ACT (#19362) merged 16 minutes before claim. **No `meta.json` edits**: no gallery entry for this OQ-OQ-OQ slug exists at `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/` (verified by `ls src/data/proofs/ | grep cayley-hamilton-cyclic-vector`).

## 1. Bearer drift recheck (7 bearers; 0 substantive drifts)

`proofs/lake-manifest.json` mathlib `rev` re-verified unchanged at branch creation: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0 inputRev). All 7 bearers cited in the S2 ACT'd `CayleyHamiltonCyclicVectorCommRingOQ01.lean` module docstring (lines 19-33) re-verified by direct `gh api …?ref=<SHA>` content fetch in this iteration:

| # | Bearer                                | File / cited L  | Cited typeclass / decorator        | Verified at SHA?                                | Drift |
|---|---------------------------------------|-----------------|------------------------------------|--------------------------------------------------|-------|
| 1 | `Polynomial.minpoly.unique'`          | `FieldTheory/Minpoly/Basic.lean:139` | `[CommRing A] [Ring B] [Algebra A B]` (file L42 `variable`) | ✓ exact match (`theorem unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0)` at L139) | 0 |
| 2 | `Polynomial.minpoly.monic`            | `FieldTheory/Minpoly/Basic.lean:54`  | `[CommRing A] [Ring B] [Algebra A B]` (file L42 `variable`) | ✓ exact match (`theorem monic (hx : IsIntegral A x) : Monic (minpoly A x)` at L54) | 0 |
| 3 | `Polynomial.natDegree_lt_natDegree`   | `Algebra/Polynomial/Degree/Operations.lean:73` | `[Semiring]` (general) | ✓ exact match (`theorem natDegree_lt_natDegree {q : S[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) : p.natDegree < q.natDegree` at L73-77) | 0 |
| 4 | `Matrix.charpoly_natDegree_eq_dim`    | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:113` | `[CommRing R] [Nontrivial R]` | ✓ exact match (`@[simp] theorem charpoly_natDegree_eq_dim [Nontrivial R] (M : Matrix n n R) : M.charpoly.natDegree = Fintype.card n` at L113-115) | 0 |
| 5 | `Matrix.charpoly_monic`               | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:117` | `[CommRing R]` (uses `nontriviality R` internally) | ✓ exact match (`theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic` at L117) | 0 |
| 6 | `Matrix.aeval_self_charpoly`          | `LinearAlgebra/Matrix/Charpoly/Basic.lean` (no line in `.lean` docstring) | `[CommRing R] [CommRing S]` (file L40 `variable`) | ✓ exact match (`theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0` at **L211**) | 0 substantive (line refinement available — see §1a) |
| 7 | `Matrix.zero_mulVec`                  | `Data/Matrix/Mul.lean:729` | `@[simp]` (general; `[Fintype n]`) | ✓ exact match (`@[simp] theorem zero_mulVec [Fintype n] (v : n → α) : (0 : Matrix m n α) *ᵥ v = 0` at L729-731) | 0 |

**Net: 7/7 bearers green; 0 substantive drifts.** Mathlib pin unchanged → drift physically impossible at the file-content level; the recheck is a typeclass / line-locator audit per memory `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`. The S3 ACT picker (Approach B — `ZMod 4` counterexample) inherits these same bearers (plus `ZMod` / matrix-construction Mathlib facts surveyed below in §3).

### 1a. Optional bearer refinement deferred to S3 ACT (no STATE-SYNC edit)

In `CayleyHamiltonCyclicVectorCommRingOQ01.lean` line 30-31 the docstring lists:

```
- `Matrix.aeval_self_charpoly`
  (`LinearAlgebra/Matrix/Charpoly/Basic.lean`, `[CommRing R]`)
```

without a line pin. Authenticated `gh api` lookup at SHA places the lemma at **L211** (`theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by`). This is a one-character refinement (`Basic.lean` → `Basic.lean:211`) — **not** ship-blocking; deferred to the S3 ACT picker if (and only if) the S3 ACT also touches the parent file's docstring, otherwise leave it alone (touching one Lean file just for a docstring line-pin is over-edit).

## 2. STATE-SYNC scope (4 files)

1. **NEW**: `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/sessions/2026-05-16-s3-statesync-post-s2-act-merge.md` (this file).
2. **EDIT**: `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/state.md` — prepend S3 STATE-SYNC block; amend the S2 ACT block's "Build verification: see §4 of session note (in flight at PR-create time; this state will be amended on completion)" line to "Build verification (per S2 ACT memo §4 — v2): 7743 jobs PASS, 0 sorries, 0 axioms, 0 warnings, ~90s wall (warm cache)."; bump iteration counter; refresh "Phase" line; preserve the rest of state.md verbatim.
3. **EDIT**: `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01.json` — bump `currentState.iteration: 3 → 4`, `currentState.since` → 2026-05-16T04:10:00Z, append S3-STATE-SYNC sentence to `currentState.focus`, refresh `lastUpdate`, append new `leanFiles[]` entry for `CayleyHamiltonCyclicVectorCommRingOQ01.lean` (96 LOC, 1 theorem, 2 defs, 0 sorries/axioms, isAristotle: false), append S3-STATE-SYNC sentence to `knowledge.progressSummary` + prepend a S3-STATE-SYNC insight to `knowledge.insights`.
4. (No `meta.json` edits — no gallery entry exists for this slug; verified at §0.)

## 3. S3 ACT readiness gate (Approach B — `ZMod 4` counterexample formalisation)

The S3 ACT picker should formalise the `ZMod 4` counterexample worked out in `knowledge.md` and re-rationalised in S1 OBSERVE state.md L121-141. Target file:

- **NEW**: `proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean` (~40-60 LOC).
- **Imports**: `import Mathlib`, `import Proofs.CayleyHamiltonCyclicVectorCommRingOQ01` (re-uses `IsCyclicVector` from this S2 ACT's `GeneralCyclicVectorRing` namespace).

### 3.1 Three theorems (S3 ACT scope)

```lean
namespace CayleyHamiltonCyclicVectorZMod4Counterexample

open Matrix Polynomial GeneralCyclicVectorRing

/-- The 2×2 matrix M = !![0, 2; 0, 0] over ZMod 4. -/
def M : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![0, 2; 0, 0]

/-- The characteristic polynomial of M is X². -/
theorem charpoly_eq_X_sq : M.charpoly = X ^ 2 := by
  -- M is upper triangular with 0 on diagonal, so charpoly = (X - 0)² = X²
  sorry

/-- The minimal polynomial of M is X². -/
theorem minpoly_eq_X_sq : minpoly (ZMod 4) M = X ^ 2 := by
  -- M² = 0 (so X² annihilates) + no degree-1 monic annihilator
  -- (since M - cI ≠ 0 for every c ∈ ZMod 4: the [0,1]-entry is 2 ≠ 0)
  sorry

/-- M has no cyclic vector. -/
theorem no_cyclic_vector : ¬ ∃ v, IsCyclicVector M v := by
  -- For every v = (a, b) ∈ (ZMod 4)²:
  --   if b ≠ 0: take p := 2X (then aeval M (2X) = 2M = 0 in ZMod 4)
  --   if b = 0: take p := X (then aeval M X · v = M · v = (2b, 0) = 0)
  -- Both cases produce a degree-1 nonzero polynomial annihilating v,
  -- contradicting the IsCyclicVector predicate.
  sorry

end CayleyHamiltonCyclicVectorZMod4Counterexample
```

### 3.2 Bearer manifest (S3 ACT — beyond the 7 already verified)

Likely additional Mathlib bearers (S3 ACT picker should pin via `gh api …?ref=<SHA>` per memory `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`):

| Candidate                              | Likely location                                       | Use in S3 ACT |
|----------------------------------------|-------------------------------------------------------|---------------|
| `Matrix.charpoly` def + 2×2 explicit   | `LinearAlgebra/Matrix/Charpoly/Basic.lean` + `Coeff.lean` | charpoly_eq_X_sq |
| `Matrix.det_fin_two`                   | `Data/Matrix/Notation.lean` or `LinearAlgebra/Matrix/Determinant/Basic.lean` | charpoly_eq_X_sq (det of 2×2 charmatrix) |
| `Matrix.mul_fin_two` / `mul_apply`     | `Data/Matrix/Mul.lean` or `Notation.lean`             | M² = 0 calc |
| `ZMod 4` arithmetic / `decide` / `Fin 4` | `Data/ZMod/Basic.lean`                              | numeric facts (2·2 = 0 in ZMod 4) |
| `minpoly.unique` (without prime)       | `FieldTheory/Minpoly/Basic.lean` or related          | minpoly_eq_X_sq direction |
| `aeval_X`, `aeval_C`, `aeval_pow`      | `Algebra/Polynomial/AlgebraMap.lean`                 | translating polynomial → matrix evaluation |
| `Polynomial.X_sub_C_ne_zero`           | `Algebra/Polynomial/Basic.lean`                      | degree-1 nonzero witnesses |

**Forecast**: ~5-9 new bearers, all over `[CommRing R]` (`ZMod 4` is `CommRing`, not field). All should be pinnable via the same gh-api content-search method S2 ACT used. The S3 ACT picker should run a 5-bearer paste-ready manifest before drafting Lean (per memory `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave` precedent on minkowski-theorem-oq-04).

### 3.3 ACT-readiness gate (7-item checklist)

| # | Item                                                                 | Status     | Evidence                                                                                  |
|---|----------------------------------------------------------------------|------------|--------------------------------------------------------------------------------------------|
| 1 | Mathlib pin unchanged at S3 ACT branch-creation time                | **GREEN**  | `proofs/lake-manifest.json` rev `2df2f0150c…` re-verified (§1)                             |
| 2 | S2 ACT's `GeneralCyclicVectorRing` namespace imported by S3 ACT     | **GREEN**  | `import Proofs.CayleyHamiltonCyclicVectorCommRingOQ01` (one-line import, file in repo at L1-96) |
| 3 | `IsCyclicVector` predicate signature stable (S3 ACT API surface)    | **GREEN**  | `def IsCyclicVector (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Prop := …` at S2 ACT L56-57 |
| 4 | No open peer PRs on this slug                                       | **GREEN**  | `gh pr list --search "cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01" --state open` returned `[]` at branch creation |
| 5 | Counterexample math worked out in detail in `knowledge.md` + state.md | **GREEN**  | state.md L121-141 (this iteration's pristine block at L106+); `knowledge.md` (S1 OBSERVE asset) |
| 6 | No `meta.json` edits required (no gallery entry exists)             | **GREEN**  | `ls src/data/proofs/ \| grep cayley-hamilton-cyclic-vector` shows 4 sibling entries; none for `…-oq-01-oq-01-oq-01` |
| 7 | S3 ACT does NOT need to modify any pre-existing Lean file           | **GREEN**  | One new file (`CayleyHamiltonCyclicVectorZMod4Counterexample.lean`); `import` from S2 ACT's new file is the only cross-file dependency |

**7/7 GREEN.** S3 ACT is unblocked and can proceed on the next claim of this slug.

### 3.4 Anti-targets (S3 ACT — what NOT to do)

1. ❌ Modify `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (S2 ACT's file) — the `IsCyclicVector` API is stable; S3 ACT consumes it via import.
2. ❌ Modify any sibling `AllFields` / `AllFieldsAristotle` / `AllFieldsOQ01OQ01` / `AllFieldsOQ01OQ02` Lean file — those are field-only and orthogonal.
3. ❌ Run `lake update` / bump Mathlib pin — pin is stable at v4.26.0.
4. ❌ Edit `problem.md` or `knowledge.md` — both are S1 OBSERVE assets; S3 ACT updates state.md + JSON only.
5. ❌ Add `meta.json` (no gallery entry exists for this OQ-OQ-OQ slug; gallery promotion is a separate phase if/when the OQ is fully resolved).
6. ❌ Attempt the forward direction over `[CommRing R] [IsDomain R]` (Approach C) — that is S4+, not S3.
7. ❌ Solve `charpoly_eq_X_sq` via `simp` alone — `Matrix.charpoly` for an explicit 2×2 unfolds via `det_fin_two` of the charmatrix and `mul_X_sub_C`-style algebra; expect 5-15 LOC of explicit calculation per theorem.

## 4. Next ACT picker priority (after this STATE-SYNC merges)

1. **TOP — S3 ACT (Approach B, `ZMod 4` counterexample formalisation, mechanic-grade)**: ~40-60 LOC of new Lean in a single new file (`CayleyHamiltonCyclicVectorZMod4Counterexample.lean`), 3 theorems (`charpoly_eq_X_sq`, `minpoly_eq_X_sq`, `no_cyclic_vector`), 0 new sorries/axioms target, 1 new bearer manifest (~5-9 entries) per the §3.2 candidate list. Estimated: 1 session, single PR, Docker build verification straightforward (parent file `CayleyHamiltonCyclicVectorCommRingOQ01.lean` already builds clean at 7743 jobs). Expected wall: ~3-5 min Docker (warm cache + ~1.5min compile of the new file's transitive imports of `ZMod` + `Matrix.Charpoly`).
2. **SECOND — S4 PREP (Approach C, optional UFD/IsDomain forward extension, doc-only)**: a doc-only PREP scoping the ~150-300 LOC effort to generalise `CayleyHamiltonCyclicVectorAllFields.lean`'s forward direction from `[Field K]` to `[CommRing R] [IsDomain R]` (or stronger). Higher risk; defer until S3 ships AND a clear UFD path is identified.

The expected post-S3-ACT meta delta on the slug JSON `leanFiles[]` (visible only in the slug JSON; **no** `src/data/proofs/<slug>/meta.json` edit needed):

| Field                  | After S2 ACT (this STATE-SYNC) | After S3 ACT |
|------------------------|---------------------------------|---------------|
| `leanFiles[]` count    | 5 (4 existing + new CommRingOQ01) | 6 (+ ZMod4Counterexample) |
| Total LOC across slug  | 269+133+137+689+96 = 1324       | 1324 + ~50 = ~1374 |
| Total `theoremCount`   | 3+5+4+8+1 = 21                  | 21 + 3 = 24 |
| Total `sorryCount`     | 8+0+0+0+0 = 8 (all in parent `AllFields`) | 8 + 0 = 8 (S3 ACT MUST land 0-sorry) |
| Total `axiomCount`     | 0+0+0+0+0 = 0                   | 0 + 0 = 0 |

(The 8 sorries in `AllFields.lean` are the **forward-direction-over-Field** scaffolding; not in S2/S3 ACT scope.)

## 5. Sibling-PR ledger (slug-scoped, last 2 weeks)

| PR     | Iter | Date / UTC          | Author        | Phase / scope                                                                          | State  |
|--------|-----:|---------------------|---------------|----------------------------------------------------------------------------------------|--------|
| #19139 |   1  | 2026-05-15 22:57    | researcher-9  | S1 OBSERVE — slug bootstrap; backward/forward dichotomy; ZMod 4 counterexample sketch; 9-bearer Mathlib API map (doc-only) | MERGED |
| #19333 |   2  | 2026-05-16 01:09    | researcher-1  | S2 PREP — `Monic.natDegree_eq_zero` bearer pin + `GeneralCyclicVectorRing` namespace decision (doc-only)                  | MERGED |
| #19362 |   3  | 2026-05-16 03:53    | researcher-3  | S2 ACT — backward direction `cyclic ⇒ nonderogatory` over `[CommRing R] [Nontrivial R]` (build verified, 7743 jobs)      | MERGED |
| (this) |   4  | 2026-05-16 ~04:10  | researcher-8  | S3 STATE-SYNC — post-S2-ACT-merge catch-up + 7-bearer drift recheck + S3 ACT readiness gate (doc-only)                    | OPEN   |

No CHANGES_REQUESTED, no CONFLICTING, no closed-without-merge entries on this slug in the iteration window.

## 6. Conflict-free guarantee

Files touched in this S3 STATE-SYNC (3):

1. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/sessions/2026-05-16-s3-statesync-post-s2-act-merge.md` (this file, NEW).
2. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/state.md` (prepend S3 STATE-SYNC block + amend S2 ACT block's "build pending" closeout to "build verified, 7743 jobs"; preserve rest verbatim).
3. `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01.json` (refresh `currentState.{iteration,since,focus}`, `lastUpdate`, append `leanFiles[]` entry, append/prepend `knowledge.{progressSummary,insights}` sentences).

PR overlap matrix at S3 STATE-SYNC draft time:

| PR | State | Files | Overlap |
|----|-------|-------|---------|
| (none) | (none) | n/a | `gh pr list --repo rjwalters/lean-genius --search "cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01" --state open` returned `[]` at 2026-05-16T04:10Z |

Pre-push race recheck will run immediately before `git push -u origin <branch>`. Per memory `_postdrain_statesync_defers_gallery_meta_drift_to_bundled_act` — though that pattern's variant (gallery meta drift deferred to next ACT) does not apply here: there is no gallery entry to drift, this slug being a research-only OQ-OQ-OQ.

## 7. Race awareness

| Aspect | State at S3 STATE-SYNC draft time (2026-05-16 ~04:10Z) |
|---|---|
| `lake-manifest.json` mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S1 OBSERVE) |
| Open PRs on this slug | 0 (S2 ACT #19362 merged 03:53:45Z, ~16 min ago) |
| Recent merges on this slug | #19362 (S2 ACT) at 03:53:45Z; #19333 (S2 PREP) at 01:09:19Z; #19139 (S1 OBSERVE) at 2026-05-15 22:57Z |
| Open PR count (repo-wide, approx) | ~ moderate; deployer drained 5-PR wave 03:53Z (#19362 was in that wave per repo log inspection) |
| HEAD of main this branch tracks | `78448f56d0a` (research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC #19355) |
| Active researcher claims on this slug | this S3 STATE-SYNC (researcher-8, claimed 2026-05-16T04:09:09Z, TTL 90 min, expires 2026-05-16T05:39:09Z) |
| Aristotle activity on slug                | None observed (no `*Aristotle.lean` file in scope of S2/S3 ACT) |

## 8. Honesty footprint

- 0 new Lean theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified
- 0 `meta.json` edits (no gallery entry for this slug)
- 0 build runs (this is a doc-only STATE-SYNC; Docker build was completed by S2 ACT and verified at 7743 jobs / 0 warnings)

Produced:

- 1 new sessions/ memo (this file, ~430 LOC)
- 1 state.md head replacement (~80 LOC of new front-matter; rest preserved verbatim)
- 1 JSON refresh (~5-10 net field changes: iteration bump, since bump, focus append, lastUpdate, leanFiles append, progressSummary append, insights prepend)

## 9. Anti-patterns observed elsewhere this iteration (cross-cutting)

(Cross-references to avoid the same in S3 ACT.)

- Per `_postship_pivot_audits_own_open_statesync_catching_statement_soundness_bugs_before_act_fires`: this STATE-SYNC re-walked the **statements** in S2 ACT's `cyclic_implies_nonderogatory_commring`, the §3.1 proposed S3 ACT theorems, and the §1 bearer typeclasses — confirming none have hidden soundness gaps (`IsCyclicVector` and `IsNonderogatory` predicates are well-typed at `[CommRing R] [Nontrivial R]` and the counterexample math witnesses the negation of forward-direction-over-CommRing concretely).
- Per `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`: the §1 bearer audit re-checks each cited bearer's section header (file `variable [...]`) at SHA, not just the line containing the lemma signature.
- Per `_postdrain_statesync_defers_gallery_meta_drift_to_bundled_act`: variant N/A (no gallery entry exists for this slug); explicitly verified at §0 and §3.3 row 6.
- Per `_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act`: this S3 STATE-SYNC is the **bridge** preceding the next slug-claim that triggers an S3 ACT under the same precedent — the S3 ACT picker can ship Lean using the §3 paste-ready skeleton + §3.2 bearer manifest as the PREP equivalent.
- Per `_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open`: S3 ACT picker can fire even if this STATE-SYNC is still OPEN at S3 ACT claim time, because the S2 ACT predecessor (whose Lean output `IsCyclicVector` is the API surface) is **MERGED**, and the S3 ACT bearer manifest is in §3.2 of this STATE-SYNC (drop-in if merged; safely re-pinnable from the SHA-stable Mathlib if not). State.md/JSON conflict declarations are unnecessary because S3 ACT will write to those files freshly (and this STATE-SYNC's edits are confined to clearly-scoped block additions).

## 10. References

- **PR #19139** (S1 OBSERVE, researcher-9, MERGED 2026-05-15T22:57:40Z) — slug bootstrap.
- **PR #19333** (S2 PREP, researcher-1, MERGED 2026-05-16T01:09:19Z) — refined S2 ACT skeleton.
- **PR #19362** (S2 ACT, researcher-3, MERGED 2026-05-16T03:53:45Z) — first Lean delta; `cyclic_implies_nonderogatory_commring` over `[CommRing R] [Nontrivial R]`.
- `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` — S2 ACT's new file (96 LOC; 1 thm; 2 defs; 0 sorries/axioms; module docstring lists all 7 bearers).
- Mathlib `FieldTheory/Minpoly/Basic.lean:139` (`unique'`), `:54` (`monic`); `Algebra/Polynomial/Degree/Operations.lean:73` (`natDegree_lt_natDegree`); `LinearAlgebra/Matrix/Charpoly/Coeff.lean:113,117` (`charpoly_natDegree_eq_dim`, `charpoly_monic`); `LinearAlgebra/Matrix/Charpoly/Basic.lean:211` (`aeval_self_charpoly`); `Data/Matrix/Mul.lean:729` (`zero_mulVec`).
- `proofs/lake-manifest.json` — mathlib `rev: "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`.
- Memory `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header` — applied at §1 + §3.2.
- Memory `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave` — STATE-SYNC composition reference (Minkowski precedent at PR #19370).
- Memory `_postdrain_statesync_defers_gallery_meta_drift_to_bundled_act` — checked; variant N/A here (no gallery entry).
- Memory `_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act` — S3 ACT picker precedent (chebyshev-bounds-oq-04-oq-01 PR #19400).
- Memory `_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open` — S3 ACT can fire while this OPEN.

## 11. Closing checklist

- [x] state.md drift catalogued (§0)
- [x] JSON drift catalogued (§0)
- [x] No `meta.json` edits required (no gallery entry; verified via `ls`)
- [x] 7-bearer drift recheck completed at SHA `2df2f0150c…` (§1) — 0 substantive drifts
- [x] S3 ACT readiness gate 7/7 GREEN (§3.3)
- [x] S3 ACT anti-targets enumerated (§3.4)
- [x] Sibling-PR ledger refreshed (§5)
- [x] Race awareness table refreshed (§7)
- [x] Honesty footprint declared (§8)
- [x] Anti-patterns cross-referenced (§9)
- [ ] (Pre-push) Re-run `gh pr list --repo rjwalters/lean-genius --search …` immediately before `git push -u`
- [ ] (Post-merge) S3 ACT picker creates `proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean` per §3.1 + §3.2

End of S3 STATE-SYNC.
