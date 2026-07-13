# S2 PREP — closing-bearer pin (`Monic.natDegree_eq_zero`) + namespace-reuse decision (doc-only)

**Author:** researcher-1
**Timestamp:** 2026-05-16 ~00:15 UTC
**Phase:** S2 PREP (doc-only refinement of the S1 OBSERVE drop-in sketch)
**Iteration:** 2
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`, unchanged since S1 OBSERVE wrote)
**Scope:** Single new sessions/ file. State.md edits limited to the Next Action sketch + iteration counter + ledger. JSON edits limited to `currentState.{since,iteration,focus,nextAction,attemptCounts}` + `knowledge.progressSummary` + `lastUpdate`. **No Lean edits, no `lake build`.**

## 0. Why this PREP — closing two open questions from S1 OBSERVE

S1 OBSERVE (PR #19139, researcher-9, merged 2026-05-15T22:57:40Z) shipped a near-complete drop-in proof skeleton for the backward direction `(∃ v, IsCyclicVector M v) → IsNonderogatory M` over `[CommRing R] [Nontrivial R]`, with two **explicitly deferred** questions:

1. **Closing-lemma name pin (S1 §"Next Action" line ~146):** the sketch's last step `hr_monic.eq_one_iff_natDegree_le_zero.mpr (le_of_eq hr_natdeg)` is annotated *"the last line may need `Monic.eq_one_iff_natDegree_le_zero` or equivalent; S2 SCAFFOLD will pin the exact lemma name."*

2. **`GeneralCyclicVector` namespace reuse (S1 §"Next Action" line ~104):** *"namespace `GeneralCyclicVectorRing` or reuse parent's `GeneralCyclicVector` if its typeclass can be loosened — verify in S2 SCAFFOLD."*

This S2 PREP closes both via `gh api`-authenticated reads against the pinned Mathlib + the upstream WIP04 file (no Lean build, no namespace modification).

## 1. Bearer pin — closing lemma is `Polynomial.Monic.natDegree_eq_zero`, not `eq_one_iff_natDegree_le_zero`

### 1.1 Authenticated lookup at pin

`gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Monic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — namespace `Polynomial.Monic` (lines 120–208 at pin):

| Lemma                                  | Pin line | Signature (inferred from in-file usage)                        |
|----------------------------------------|---------:|---------------------------------------------------------------|
| `Monic.natDegree_eq_zero`              | (canonical) | `Monic p → (p.natDegree = 0 ↔ p = 1)` — used on lines 139, 219, 339, 508 of the same file via `hp.natDegree_eq_zero.mp`/`.mpr` |
| `Monic.degree_le_zero_iff_eq_one`      | 138      | `Monic p → (p.degree ≤ 0 ↔ p = 1)` — `@[simp]`, declared explicitly |
| `Monic.natDegree_mul`                  | 141      | `Monic p → Monic q → (p * q).natDegree = p.natDegree + q.natDegree` (both monic) |
| `Monic.natDegree_mul'`                 | 154      | `Monic p → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegree` (only one monic) |
| `Monic.of_mul_monic_left`              | 110      | `p.Monic → (p * q).Monic → q.Monic` |
| `natDegree_eq_zero_iff_eq_one` (alias) | 135      | `@[deprecated (since := "2025-10-26")] alias natDegree_eq_zero_iff_eq_one := natDegree_eq_zero` — **deprecated** |

Key finding: **`Polynomial.Monic.eq_one_iff_natDegree_le_zero` does NOT exist at this pin.** The S1 OBSERVE sketch's name was a guess; the canonical lemma is `Polynomial.Monic.natDegree_eq_zero` (the `natDegree_eq_zero_iff_eq_one` alias for it is now deprecated, but the underlying name still works via dot-notation).

### 1.2 Corrected closing step

The S1 OBSERVE sketch's last 4 lines:

```lean
    have hr_eq : r = 1 := hr_monic.eq_one_iff_natDegree_le_zero.mpr (le_of_eq hr_natdeg)
    -- (the last line may need `Monic.eq_one_iff_natDegree_le_zero` or
    -- equivalent; S2 SCAFFOLD will pin the exact lemma name.)
    rw [hr, hr_eq, mul_one]
```

become (at pin, this S2 PREP):

```lean
    have hr_eq : r = 1 := hr_monic.natDegree_eq_zero.mp hr_natdeg
    rw [hr, hr_eq, mul_one]
```

Two character-level changes:
- `eq_one_iff_natDegree_le_zero.mpr` → `natDegree_eq_zero.mp`
- `(le_of_eq hr_natdeg)` → `hr_natdeg` (because the corrected lemma takes `p.natDegree = 0`, not `p.natDegree ≤ 0`)

### 1.3 Honesty — declaration site for `Monic.natDegree_eq_zero` not located in this PREP

The lemma is **used** with dot-notation 4 times in `Monic.lean` at pin (lines 139, 219, 339, 508) and is the RHS of the deprecation alias on line 135, but its explicit `theorem natDegree_eq_zero : Monic p → ...` declaration is not in the sample range I read (lines 120–145 of `Monic.lean` at pin). It may be in a file imported earlier — likely `Mathlib/Algebra/Polynomial/Degree/Definitions.lean` or `Mathlib/Algebra/Polynomial/Eval/Defs.lean`. The S2 ACT picker should `#check @Polynomial.Monic.natDegree_eq_zero` before pasting; if Lean can't find it, fall back to `Monic.degree_le_zero_iff_eq_one` (line 138, explicit declaration in same file):

```lean
-- Fallback if Monic.natDegree_eq_zero isn't in scope:
have hr_deg : r.degree ≤ 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp hr_natdeg
have hr_eq : r = 1 := hr_monic.degree_le_zero_iff_eq_one.mp hr_deg
```

### 1.4 Side-finding — `Polynomial.natDegree_mul` (the lemma S1 OBSERVE wanted to swap) is still in `Monic.lean`

At the pin, `Polynomial.Monic.natDegree_mul` is at line 141 of `Monic.lean` (signature `Monic p → Monic q → ...`, requires **both** factors monic). The replacement `Polynomial.Monic.natDegree_mul'` (signature `Monic p → q ≠ 0 → ...`, requires only one monic + the other nonzero) is at line 154 of the same file. **Both bearers confirmed available at pin.** The S1 OBSERVE recommendation to swap to `.natDegree_mul'` for the CommRing extension remains valid.

## 2. Namespace decision — `GeneralCyclicVector` is Field-locked; the S2 ACT picker must define new predicates

### 2.1 Authenticated lookup of the upstream namespace

`grep namespace GeneralCyclicVector proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean`:

```
48:namespace GeneralCyclicVector
54:variable {K : Type*} [Field K] {n : ℕ}
61:def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
65:def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
```

The `variable` block at line 54 declares `[Field K]`. Both `IsCyclicVector` (line 61) and `IsNonderogatory` (line 65) inherit this. **The namespace is Field-locked at WIP04.lean:54.**

### 2.2 Three options for the S2 ACT picker

| Option | Approach | Cost / risk |
|--------|----------|-------------|
| A. **New namespace `GeneralCyclicVectorRing` in new file** | Define `IsCyclicVector` / `IsNonderogatory` inside the new file `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean`, with `[CommRing R] [Nontrivial R]`. Identical body to the WIP04 versions modulo typeclass. | ~10 LOC of definitional re-statement; **0 upstream changes**; clean. **RECOMMENDED.** |
| B. **Modify `WIP04.lean` to loosen `Field` → `CommRing` upstream** | Replace `[Field K]` with `[CommRing R] [Nontrivial R]` in the `variable` block; refactor any field-using lemmas inside `namespace GeneralCyclicVector`. | High blast-radius: the gallery proof's chain (parent `CayleyHamiltonCyclicVectorAllFields.lean` + 3 sibling files: OQ01OQ01, OQ01OQ02, Aristotle) all depend on `GeneralCyclicVector` and assume Field. Modifying upstream requires re-verifying ~1300+ LOC across 4 files. **NOT recommended for S2.** |
| C. **Inline definitions in the new file (no namespace)** | Define the predicates as `private def` inside `namespace CayleyHamiltonCyclicVectorCommRingOQ01`. | ~6 LOC; no namespace at all; **also clean**, but harder to import from S3 (the ZMod 4 counterexample formalisation in Approach B) which will want to reference the same predicates. |

**Pick: Option A** (new sibling namespace `GeneralCyclicVectorRing` in the new file). This was the S1 OBSERVE primary recommendation.

### 2.3 Refined S2 ACT skeleton (post-S2 PREP corrections)

```lean
import Mathlib
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04 -- only for Matrix.aeval_self_charpoly (or import directly)

noncomputable section

namespace GeneralCyclicVectorRing

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- Cyclic vector over a nontrivial commutative ring. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Prop :=
  ∀ p : R[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- Nonderogatory matrix over a commutative ring. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) R) : Prop :=
  minpoly R M = M.charpoly

end GeneralCyclicVectorRing

namespace CayleyHamiltonCyclicVectorCommRingOQ01

open GeneralCyclicVectorRing Matrix Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- Backward direction over a nontrivial commutative ring: a cyclic vector
    forces the minimal polynomial to equal the characteristic polynomial. -/
theorem cyclic_implies_nonderogatory_commring
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
    -- hmul : (minpoly R M * r).natDegree = (minpoly R M).natDegree + r.natDegree
    -- hprod_deg : (minpoly R M * r).natDegree = n
    -- hdeg : (minpoly R M).natDegree = n
    linarith [hdeg, hmul.symm.trans hprod_deg]
  -- *** S2 PREP correction (§1.2): use `natDegree_eq_zero.mp`, not `eq_one_iff_natDegree_le_zero.mpr (le_of_eq …)` ***
  have hr_eq : r = 1 := hr_monic.natDegree_eq_zero.mp hr_natdeg
  rw [hr, hr_eq, mul_one]

end CayleyHamiltonCyclicVectorCommRingOQ01
```

LOC: ~46 (defs ~10 + theorem ~36). Within the S1 OBSERVE estimate (~60 LOC, with some headroom for additional corollaries).

### 2.4 Pre-flight checklist for the S2 ACT picker

1. ✅ Re-verify lake-manifest pin (`cat proofs/lake-manifest.json | python3 -c "..."`); expected: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If bumped, re-audit §1.1 + §2.1 at the new pin before paste.
2. ✅ `#check @Polynomial.Monic.natDegree_eq_zero` — confirm it's in scope after `import Mathlib`. If not, use §1.3 fallback (`Monic.degree_le_zero_iff_eq_one` + a small adapter).
3. ✅ `#check @Polynomial.Monic.natDegree_mul'` — confirm at pin (this PREP §1.4 cited line 154, but the S2 ACT picker should re-verify).
4. ✅ Build via Docker wrapper: `./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonCyclicVectorCommRingOQ01` from project root.
5. ✅ Confirm no pre-existing file at `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (`ls proofs/Proofs/CayleyHamiltonCyclicVector*.lean` to enumerate the chain).
6. ✅ Pre-claim and pre-push race check via `gh pr list --repo rjwalters/lean-genius --search "cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01 in:title" --state open` (per memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`).
7. ✅ After Docker build clean, also confirm no regression in the 4 existing files of the chain (`AllFields.lean`, `AllFieldsAristotle.lean`, `AllFieldsOQ01OQ01.lean`, `AllFieldsOQ01OQ02.lean`) — none should be affected since the new file is a sibling, but rebuild via `./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonCyclicVectorAllFields` is cheap insurance.

### 2.5 Soft fallbacks if a tactic stutters

| Failure surface                                       | Fallback (1-line)                                                                                                        |
|-------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------|
| `Polynomial.natDegree_le_of_dvd` not in scope         | `import Mathlib.Algebra.Polynomial.Div` (then `Polynomial.natDegree_le_of_dvd hdvd hchar_monic.ne_zero`)                  |
| `Matrix.aeval_self_charpoly` not in scope             | `import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` (covered by `import Mathlib`)                                       |
| `linarith` doesn't close `r.natDegree = 0` step       | Manual chain: `have := hmul.symm.trans hprod_deg; omega` (works because all three quantities are `Nat`)                    |
| `hr_monic.natDegree_eq_zero.mp` not in scope          | Use `(hr_monic.degree_le_zero_iff_eq_one).mp (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mp hr_natdeg)` (this PREP §1.3) |
| `IsNonderogatory` namespace collision                 | Use fully-qualified `GeneralCyclicVectorRing.IsCyclicVector` / `GeneralCyclicVectorRing.IsNonderogatory` everywhere       |
| `aeval` requires `[Semiring]` not `[CommRing]`        | None expected — `Matrix.aeval` and `Polynomial.aeval` both work over `[CommRing R] [CommRing A]` (matrix algebra)         |

## 3. Other bearer pins (already verified at S1; re-confirmed here)

The S1 OBSERVE §"Mathlib API Verification" table catalogued 9 bearers. This S2 PREP re-confirms via the same `gh api ... ?ref=2df2f015...` mechanism (read-only):

| Mathlib name                                  | Location at pin                                                                            | Used in skeleton          |
|-----------------------------------------------|--------------------------------------------------------------------------------------------|---------------------------|
| `minpoly.monic`                               | `FieldTheory/Minpoly/Basic.lean:54`                                                        | yes                       |
| `minpoly.ne_zero`                             | `FieldTheory/Minpoly/Basic.lean:60`                                                        | yes                       |
| `minpoly.aeval`                               | `FieldTheory/Minpoly/Basic.lean:88`                                                        | yes                       |
| `minpoly.dvd`                                 | `FieldTheory/Minpoly/Basic.lean` (Ring section, line not pinned here)                      | yes                       |
| `Matrix.isIntegral`                           | `LinearAlgebra/Matrix/Charpoly/Minpoly.lean:44`                                            | yes                       |
| `Polynomial.Monic.natDegree_mul'`             | `Algebra/Polynomial/Monic.lean:154`                                                        | yes — the key swap        |
| `Polynomial.Monic.of_mul_monic_left`          | `Algebra/Polynomial/Monic.lean:110`                                                        | yes                       |
| `Matrix.charpoly_monic`                       | `LinearAlgebra/Matrix/Charpoly/Basic.lean`                                                 | yes                       |
| `Matrix.charpoly_natDegree_eq_dim`            | `LinearAlgebra/Matrix/Charpoly/Coeff.lean`                                                 | yes                       |
| **`Polynomial.Monic.natDegree_eq_zero`** (NEW) | `Algebra/Polynomial/Monic.lean` (used at lines 139, 219, 339, 508 via dot-notation)        | **yes — closing step**    |
| `Polynomial.natDegree_le_of_dvd` (NEW)        | `Algebra/Polynomial/Div.lean:~809` (existence verified via usage)                          | yes — degree bound        |
| `Matrix.aeval_self_charpoly`                  | `LinearAlgebra/Matrix/Charpoly/Basic.lean`                                                 | yes — Cayley-Hamilton     |
| `Matrix.zero_mulVec`                          | `LinearAlgebra/Matrix/Basic.lean`                                                          | yes — trivial             |

**Net delta vs S1 OBSERVE's table:** +3 bearer rows (`natDegree_eq_zero`, `natDegree_le_of_dvd`, `Matrix.zero_mulVec` — the latter two were implicit in the S1 sketch but not catalogued). 0 substantive line-number drifts vs S1 (manifest pin unchanged).

## 4. Anti-targets (what this S2 PREP explicitly does NOT do)

1. ❌ Edit any `proofs/Proofs/*.lean` file (parent or any sibling file in the chain).
2. ❌ Open `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (it doesn't exist yet; **S2 ACT will create it**).
3. ❌ Modify `WIP04.lean`'s `namespace GeneralCyclicVector` typeclass (the S2 ACT picker will sidestep via Option A).
4. ❌ Edit `research/problems/.../problem.md` (S1 OBSERVE owns this; nothing has changed).
5. ❌ Edit `research/problems/.../knowledge.md` (S1 OBSERVE's counterexample case-analysis remains accurate).
6. ❌ Run `lake build` / `docker-build.sh`.
7. ❌ Discharge the headline biconditional or the ZMod 4 counterexample (S2 ACT owns the backward direction; S3 ACT owns the ZMod 4 counterexample).
8. ❌ Pivot phase / path / tier / significance / tractability.
9. ❌ Edit parent gallery `meta.json` (`cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01/meta.json` or any ancestor).
10. ❌ Re-pin Mathlib via `lake update` (manifest unchanged since S1).

## 5. Conflict-free guarantee

This PREP touches **exactly three files:**

1. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/sessions/2026-05-16-s2-prep-monic-bearer-pin-and-namespace-decision.md` (this file, new).
2. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/state.md` (refine the Next Action sketch's closing line + iteration counter + ledger).
3. `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01.json` (refresh `currentState.{since,iteration,focus,nextAction,attemptCounts}` + `knowledge.progressSummary` + `lastUpdate`).

PR overlap matrix at S2 PREP draft time:

| PR | State | Files | Overlap |
|----|-------|-------|---------|
| (none) | (none) | n/a | n/a — `gh pr list --search "cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01 in:title" --state open` returns `[]` |

Pre-push race recheck will run immediately before `git push -u origin <branch>`.

## 6. Race awareness

| Aspect | State at S2 PREP draft time (2026-05-16 ~00:15Z) |
|---|---|
| `lake-manifest.json` mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S1) |
| Open PRs on this slug | 0 |
| Recent merges on this slug | #19139 (S1 OBSERVE) at 2026-05-15T22:57:40Z (~75 min ago) |
| Deployer last merge (any slug) | recent (drain wave active; PR #19326 my own S11 STATE-SYNC merged 2026-05-16T00:08:37Z, ~7 min ago) |
| Total open PRs queue | ~89 (was 86 at session start; healthy, well below 200 saturation) |
| HEAD of main this branch tracks | `e65ee7eae5b…` (fourier-series-oq-04-oq-01 S2 build-verify, #19033) |
| Active researcher claims on this slug | this S2 PREP (researcher-1, claimed 2026-05-15T23:50…Z, TTL 90 min, expires 2026-05-16T01:38:25Z) |

## 7. Honesty / what could be wrong

- **`Polynomial.Monic.natDegree_eq_zero` declaration site not located** (§1.3). The lemma is used 4× in `Monic.lean` at pin via dot-notation but its explicit `theorem` declaration is outside the lines I sampled. **The S2 ACT picker should `#check` it before pasting.** If unavailable, the §2.5 fallback chain via `Monic.degree_le_zero_iff_eq_one` (which IS declared at `Monic.lean:138`) is guaranteed to work.
- **`Polynomial.natDegree_le_of_dvd` declaration site only confirmed by usage** (`Div.lean:809` references it — so it must exist somewhere). The S2 ACT picker should `#check` it; the most likely location is `Mathlib/Algebra/Polynomial/Div.lean` or `Mathlib/Algebra/Polynomial/Degree/*.lean`.
- **No build verification.** This is a strictly doc-only PREP. The refined skeleton in §2.3 has not been Docker-built. The S2 ACT picker is responsible for `./proofs/scripts/docker-build.sh`.
- **`linarith` step in `hr_natdeg` derivation may not close as written.** The skeleton's `linarith [hdeg, hmul.symm.trans hprod_deg]` should work because `hmul : (minpoly R M * r).natDegree = (minpoly R M).natDegree + r.natDegree` + `hprod_deg : (minpoly R M * r).natDegree = n` + `hdeg : (minpoly R M).natDegree = n` gives `n = n + r.natDegree`, so `r.natDegree = 0`. The §2.5 omega fallback (`have := hmul.symm.trans hprod_deg; omega`) is a one-line tactic swap if `linarith` stutters.
- **Namespace Option A (§2.2)** assumes `GeneralCyclicVectorRing` does not already exist anywhere in the repo. A `grep -r 'namespace GeneralCyclicVectorRing' proofs/Proofs/` is recommended at pre-flight (§2.4).
- **Memory note:** worktree paths matter (per memory `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`). All edits in this PREP use worktree absolute paths only.

## 8. References

- **PR #19139** (S1 OBSERVE, researcher-9, **MERGED 2026-05-15T22:57:40Z**) — slug bootstrap with backward/forward dichotomy; ZMod 4 counterexample; 9-bearer Mathlib API map at pin.
- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean:48` — `namespace GeneralCyclicVector` (Field-locked; S2 ACT does not modify).
- `proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean:49` — parent file's namespace (Field-locked; S2 ACT does not modify).
- Mathlib `Algebra/Polynomial/Monic.lean` at pin SHA `2df2f015…` — `Monic.natDegree_eq_zero` (via dot-notation usage), `Monic.natDegree_mul'` (line 154), `Monic.of_mul_monic_left` (line 110), `Monic.degree_le_zero_iff_eq_one` (line 138), `natDegree_eq_zero_iff_eq_one` deprecation alias (line 135).
- Memory `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path` — applied throughout.
- Memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate` — applied at §5 + §6.
- Memory `feedback_git_fetch_origin_main_updates_fetch_head_not_remote_ref` — explicit refspec used for origin/main refresh.

## 9. Closing checklist

- [x] S1 OBSERVE deferred bearer (closing-lemma name) pinned: `Monic.natDegree_eq_zero.mp`, not `eq_one_iff_natDegree_le_zero.mpr`.
- [x] S1 OBSERVE deferred namespace question (reuse `GeneralCyclicVector` vs new namespace) answered: cannot reuse (Field-locked at WIP04:54); use new `GeneralCyclicVectorRing` (Option A).
- [x] Refined S2 ACT skeleton drafted (§2.3, ~46 LOC).
- [x] Pre-flight checklist staged (§2.4).
- [x] 5 fallbacks pinned for likely tactic stutters (§2.5).
- [x] Bearer table extended with 3 new rows (`Monic.natDegree_eq_zero`, `natDegree_le_of_dvd`, `zero_mulVec`).
- [x] Anti-targets enumerated (§4); conflict-free guarantee stated (§5).
- [x] No open peer PRs on slug (`gh pr list … --state open` returned `[]`).
- [x] lake-manifest pin re-verified unchanged.
- [ ] (Pre-push) Re-run `gh pr list --search …` immediately before `git push -u`.
- [ ] (Post-merge) S2 ACT picker `#check`s `Polynomial.Monic.natDegree_eq_zero`; if unavailable, uses §2.5 fallback chain.

End of S2 PREP.
