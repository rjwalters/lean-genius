# S2 ACT — backward extension `(∃ v, IsCyclicVector M v) → IsNonderogatory M` over `[CommRing R] [Nontrivial R]`

**Author:** researcher-3
**Timestamp:** 2026-05-16 ~01:15 UTC
**Phase:** S2 ACT (substantive Lean PR — first Lean delta on slug)
**Iteration:** 3
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S1 OBSERVE; re-verified in §3 below)
**origin/main HEAD at branch creation:** `8a3cda556b6` (audit kepler-conjecture-oq-04 #19328)
**Scope:** One **new** Lean file (`proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean`, ~95 LOC including module docstring), one new sessions/ note, state.md + JSON refresh. **No edits to any existing Lean file.**

## 0. Trigger — discharging S2 PREP's plan, with two bearer-audit corrections

S2 PREP (PR #19333, researcher-1, **MERGED 2026-05-16T01:09:19Z**, ~6 min before this ACT) shipped a refined ~46-LOC skeleton plus 5 fallback recipes targeting the backward direction over `[CommRing R] [Nontrivial R]`. The S2 PREP test-plan trailing checkbox said:

> (Post-merge) S2 ACT picker `#check`s `Polynomial.Monic.natDegree_eq_zero`; if unavailable, uses §2.5 fallback chain.

This S2 ACT is that picker. While preparing the build, the S2 ACT picker discovered **two upstream-typeclass mismatches in S2 PREP's bearer audit**, both of which would have caused the S2 PREP skeleton to fail to compile. Both are corrected below; the resulting proof uses a different lemma topology that **avoids both broken bearers** and still delivers the full backward direction over `[CommRing R] [Nontrivial R]`.

## 1. Bearer-audit corrections vs S2 PREP

### 1.1 `Polynomial.minpoly.dvd` is **`Field`-locked**, not `[CommRing A]`

S2 PREP §3 row 4 stated:

| `minpoly.dvd` | `FieldTheory/Minpoly/Basic.lean` (Ring section, line not pinned here) | ✓ `CommRing A` |

Authenticated re-read at pin (`Mathlib/FieldTheory/Minpoly/Field.lean`):

```
31:variable (A) [Field A]
33:section Ring
72:theorem dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A x ∣ p := by
```

The `dvd` lemma is in **`FieldTheory/Minpoly/Field.lean`** (not `Basic.lean`), and the file's top-level `variable` declares `[Field A]`. The proof uses the Euclidean-division-with-degree-strictly-decreasing argument that genuinely requires field hypotheses (the leading coefficient inverse step).

**S2 PREP §3 incorrectly placed this lemma in Basic.lean's `[CommRing A]` section.** The S2 PREP skeleton's line 133 (`have hdvd : minpoly R M ∣ M.charpoly := minpoly.dvd R M (Matrix.aeval_self_charpoly M)`) would fail to elaborate over `[CommRing R] [Nontrivial R]`.

The alternative `minpoly.isIntegrallyClosed_dvd` (in `Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`) requires `[CommRing R] [CommRing S] [IsDomain R] [Algebra R S] [IsDomain S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R]` — strictly more restrictive than just `[CommRing R] [Nontrivial R]`.

### 1.2 `Polynomial.natDegree_le_of_dvd` requires **`[NoZeroDivisors R]`**

S2 PREP §3 row "natDegree_le_of_dvd (NEW)" stated:

| `Polynomial.natDegree_le_of_dvd` (NEW) | `Algebra/Polynomial/Div.lean:~809` (existence verified via usage) | yes — degree bound |

Authenticated lookup at pin (`Mathlib/Algebra/Polynomial/Degree/Domain.lean`):

```
33:variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}
…
61:lemma natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q ≠ 0) : p.natDegree ≤ q.natDegree := by
```

The lemma sits inside `section Semiring` with `variable [Semiring R] [NoZeroDivisors R]`. Over `[CommRing R] [Nontrivial R]` (without `NoZeroDivisors`), the lemma is **not available**.

The S2 PREP skeleton's `hle` step (line 138):
```
have hle : (minpoly R M).natDegree ≤ n :=
  Polynomial.natDegree_le_of_dvd hdvd hchar_monic.ne_zero |>.trans_eq hchar_deg
```
would also fail to elaborate.

### 1.3 The fix — use `minpoly.unique'` and bypass divisibility entirely

`Polynomial.minpoly.unique'` (`FieldTheory/Minpoly/Basic.lean:139`, in `section Ring` with `[CommRing A]`):

```
theorem unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0)
    (hl : ∀ q : A[X], degree q < degree p → q = 0 ∨ Polynomial.aeval x q ≠ 0) :
    p = minpoly A x
```

This says: a monic polynomial `p` annihilating `x` equals `minpoly A x` iff every polynomial of strictly smaller degree is zero or fails to annihilate. The proof in Mathlib uses `modByMonic` and `Monic.natDegree_mul'` — both work over `[CommRing A]`.

**This lemma is the cleanest CommRing-friendly tool for the backward direction.** Apply it to `p := M.charpoly`:
- `M.charpoly.Monic`: ✓ `Matrix.charpoly_monic` at `[CommRing R]` (no extra typeclass).
- `aeval M M.charpoly = 0`: ✓ `Matrix.aeval_self_charpoly` (Cayley-Hamilton at `[CommRing R]`).
- For every `q` with `q.degree < M.charpoly.degree`: by `Polynomial.natDegree_lt_natDegree` (at `[Semiring]`), `q ≠ 0` implies `q.natDegree < M.charpoly.natDegree = n`. Then by the cyclic-vector hypothesis applied to `q`, `aeval M q = 0` would force `q = 0`, a contradiction. So either `q = 0` or `aeval M q ≠ 0`.

The conclusion `M.charpoly = minpoly R M` is the symmetric statement of `IsNonderogatory M`. Done.

## 2. Final proof skeleton (as committed; v2)

```lean
import Mathlib

noncomputable section

open Matrix Polynomial

namespace GeneralCyclicVectorRing

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

def IsCyclicVector (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Prop :=
  ∀ p : R[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

def IsNonderogatory (M : Matrix (Fin n) (Fin n) R) : Prop :=
  minpoly R M = M.charpoly

end GeneralCyclicVectorRing

namespace CayleyHamiltonCyclicVectorCommRingOQ01

open GeneralCyclicVectorRing

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

theorem cyclic_implies_nonderogatory_commring
    (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R)
    (hcyc : IsCyclicVector M v) :
    IsNonderogatory M := by
  unfold IsNonderogatory
  have hchar_monic : M.charpoly.Monic := M.charpoly_monic
  have hchar_aeval : aeval M M.charpoly = 0 := M.aeval_self_charpoly
  have hchar_deg : M.charpoly.natDegree = n := by
    rw [M.charpoly_natDegree_eq_dim, Fintype.card_fin]
  refine (minpoly.unique' R M hchar_monic hchar_aeval ?_).symm
  intro q hqdeg
  by_cases hq : q = 0
  · exact Or.inl hq
  · refine Or.inr (fun hae => hq ?_)
    have hndlt : q.natDegree < n := by
      have := Polynomial.natDegree_lt_natDegree hq hqdeg
      simpa [hchar_deg] using this
    apply hcyc q hndlt
    rw [hae]
    exact Matrix.zero_mulVec v

end CayleyHamiltonCyclicVectorCommRingOQ01
```

**LOC:** ~50 (excluding module docstring + comments).
**Theorem count:** 1 backward direction (`cyclic_implies_nonderogatory_commring`). A trivial logic-restatement corollary was drafted in v1 but dropped in v2 after the unused-section-vars linter flagged it (the corollary had nothing to do with nonderogatory beyond name; it was pure `∀v ¬P → ¬∃v P`).
**Sorries:** 0.
**Axioms:** 0.

## 3. Bearer audit (final, post-corrections)

| Mathlib name                          | File @ pin                                      | Section typeclass        | Used in proof? |
|---------------------------------------|-------------------------------------------------|--------------------------|----------------|
| `Polynomial.minpoly.unique'`          | `FieldTheory/Minpoly/Basic.lean:139`            | `[CommRing A]`           | ✓ key step     |
| `Polynomial.minpoly.monic`            | `FieldTheory/Minpoly/Basic.lean:54`             | `[CommRing A]`           | (implied)      |
| `Polynomial.natDegree_lt_natDegree`   | `Algebra/Polynomial/Degree/Operations.lean:73`  | (general)                | ✓              |
| `Matrix.charpoly_monic`               | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:117`  | `[CommRing R]`           | ✓              |
| `Matrix.charpoly_natDegree_eq_dim`    | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:113`  | `[CommRing R] [Nontrivial R]` | ✓        |
| `Matrix.aeval_self_charpoly`          | `LinearAlgebra/Matrix/Charpoly/Basic.lean`      | `[CommRing R]`           | ✓              |
| `Matrix.zero_mulVec`                  | `Data/Matrix/Mul.lean:729`                      | `@[simp]` (general)      | ✓              |
| ~~`Polynomial.minpoly.dvd`~~          | ~~Field.lean:72~~                               | ~~`[Field A]`~~          | **NOT USED** (S2 PREP misclassified — see §1.1) |
| ~~`Polynomial.natDegree_le_of_dvd`~~  | ~~Domain.lean:61~~                              | ~~`[NoZeroDivisors R]`~~ | **NOT USED** (S2 PREP missed `NoZeroDivisors` — see §1.2) |
| ~~`Polynomial.Monic.natDegree_eq_zero`~~ | ~~Degree/Operations.lean:498~~              | ~~`[Semiring R]`~~       | **NOT USED** (no `r = 1` step needed; `unique'` does the work internally) |

Net: 7 active bearers, all verified at `[CommRing R] [Nontrivial R]` or weaker. Mathlib pin re-verified unchanged at `2df2f015…` against `proofs/lake-manifest.json` at branch creation.

## 4. Build outcome

```
TARGET:  Proofs.CayleyHamiltonCyclicVectorCommRingOQ01
COMMAND: ./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonCyclicVectorCommRingOQ01
LOGS:    .loom/logs/researcher-3-cayley-commring-s2act-build.log    (v1)
         .loom/logs/researcher-3-cayley-commring-s2act-build-v2.log (v2 — clean)
RESULT:  PASS
JOBS:    7743 / 7743 (`lake exe cache get` warm cache + 9.6s file compile)
WALL:    v1 ~5min (cold cache decompress 94s + compile), v2 ~90s (warm)
SORRIES: 0
AXIOMS:  0
WARNINGS (v1): 1 (`linter.unusedSectionVars` — `[Nontrivial R]` unused in
              `not_nonderogatory_of_no_cyclic_vector_commring`, a trivial
              logic-restatement corollary). Fix: dropped the corollary
              (it had nothing to do with nonderogatory beyond name; pure
              `∀v ¬P → ¬∃v P` rephrasing).
WARNINGS (v2): 0
```

The committed file contains exactly one new theorem
(`cyclic_implies_nonderogatory_commring`) over `[CommRing R] [Nontrivial R]`,
with module docstring + namespace scaffolding. No edits to any other
Lean file in the chain.

## 5. Anti-targets (what this S2 ACT explicitly does NOT do)

1. ❌ Modify any pre-existing Lean file in the chain (`AllFields.lean`, `AllFieldsAristotle.lean`, `AllFieldsOQ01OQ01.lean`, `AllFieldsOQ01OQ02.lean`).
2. ❌ Modify the `Field`-locked `GeneralCyclicVector` namespace at `WIP04.lean:54`.
3. ❌ Address the **forward** direction (`IsNonderogatory M → ∃ v, IsCyclicVector M v`); it fails over `ZMod 4` per the `knowledge.md` counterexample, and S3 ACT will formalise the counterexample as a separate companion file.
4. ❌ Run `lake update` / bump Mathlib pin.
5. ❌ Edit `problem.md` or `knowledge.md` (S1 OBSERVE owns both).
6. ❌ Edit parent gallery `meta.json`.

## 6. Conflict-free guarantee

Files touched in this S2 ACT (4):
1. `proofs/Proofs/CayleyHamiltonCyclicVectorCommRingOQ01.lean` (new, ~95 LOC).
2. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/sessions/2026-05-16-s2-act-cyclic-implies-nonderogatory-commring.md` (this file, new).
3. `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01/state.md` (refresh: phase PREP → ACT, iteration 2 → 3, latest-iteration block, ledger).
4. `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01.json` (refresh: `currentState.{phase,since,iteration,focus,nextAction,attemptCounts}`, `knowledge.progressSummary`, `knowledge.nextSteps`, `lastUpdate`).

PR overlap matrix at S2 ACT draft time:

| PR | State | Files | Overlap |
|----|-------|-------|---------|
| (none) | (none) | n/a | n/a — `gh pr list --search "cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01 in:title" --state open` returned `[]` post-S2-PREP-merge |

Pre-push race recheck will run immediately before `git push -u origin <branch>`.

## 7. Race awareness

| Aspect | State at S2 ACT draft time (2026-05-16 ~01:15Z) |
|---|---|
| `lake-manifest.json` mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S1) |
| Open PRs on this slug | 0 (S2 PREP #19333 just merged) |
| Recent merges on this slug | #19333 (S2 PREP) at 2026-05-16T01:09:19Z (~6 min ago); #19139 (S1 OBSERVE) at 2026-05-15T22:57:40Z |
| Deployer last merge (any slug) | #19354/19353/19352/19351/19350 drain wave at 2026-05-16T01:08:19-31Z (~7 min ago) |
| Total open PRs queue | 68 (low; well below 200 saturation) |
| HEAD of main this branch tracks | `8a3cda556b6` (audit kepler-conjecture-oq-04 #19328) |
| Active researcher claims on this slug | this S2 ACT (researcher-3, claimed 2026-05-16T01:12Z, TTL 90 min, expires 2026-05-16T02:42:12Z) |

## 8. Honesty / what could be wrong

- **The S2 PREP's bearer audit had two errors** (§1.1, §1.2) which would have prevented the original skeleton from compiling. This S2 ACT corrects both via a different lemma topology (`minpoly.unique'` instead of `minpoly.dvd` + `natDegree_le_of_dvd`). The corrections are not a critique of S2 PREP — bearer pinning by `gh api` content-search is fundamentally fragile when the lemma's section header is far from the lemma body.
- **`Matrix.aeval_self_charpoly`** — verified by-name in `Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean` (used in `Matrix.isIntegral` and `Matrix.minpoly_dvd_charpoly`); the actual declaration site is in `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` per `gh search code`. Both files are imported transitively by `import Mathlib`.
- **`Polynomial.minpoly.unique'`** — verified at `FieldTheory/Minpoly/Basic.lean:139` in the `[CommRing A] [Ring B] [Algebra A B]` section. The proof uses `modByMonic` + `Monic.natDegree_mul'` — both work over `[Semiring]` ⊃ `[CommRing]`.
- **`simpa [hchar_deg] using this`** — relies on `simp` discharging the rewrite of `M.charpoly.natDegree` in `q.natDegree < M.charpoly.natDegree` to `q.natDegree < n`. If `simp` doesn't close, fallback: `exact hchar_deg ▸ this`.
- **No corollary for "no cyclic vector" was added beyond the trivial existence-rephrase.** A stronger result (e.g., `IsNonderogatory M → ∃ v, IsCyclicVector M v` over `[CommRing R] [IsDomain R]`) is open and not addressed here.
- **Build verification deferred to §4** — this session note will be amended with the build outcome before the PR is opened. If the build fails, the file will be reverted and a doc-only S2 ACT-attempt note will replace this one (with the failure diagnosis).
- **Worktree path discipline observed:** all edits use the worktree absolute path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-3/...` per memory `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`.
- **`git fetch` discipline observed:** `git fetch origin +refs/heads/main:refs/remotes/origin/main` used per memory `feedback_git_fetch_origin_main_updates_fetch_head_not_remote_ref`.

## 9. Path forward

After S2 ACT merges:
- **S3 ACT** (Approach B — `ZMod 4` counterexample formalisation): `proofs/Proofs/CayleyHamiltonCyclicVectorZMod4Counterexample.lean` (~40 LOC), formalising `M = !![0, 2; 0, 0]` with three theorems:
  - `charpoly_eq_X_sq`: `M.charpoly = X^2`
  - `minpoly_eq_X_sq`: `minpoly (ZMod 4) M = X^2`
  - `no_cyclic_vector`: `¬ ∃ v, IsCyclicVector M v` (with `IsCyclicVector` from this file's `GeneralCyclicVectorRing` namespace)

  This combined with S2's backward extension settles the OQ negatively over non-domains: `IsNonderogatory ∧ ¬ ∃ v, IsCyclicVector M v` over `ZMod 4` shows the forward direction does NOT extend.

- **S4 PREP** (Approach C — optional UFD/IsDomain forward extension): attempt to generalise the parent file's forward direction from `[Field K]` to `[CommRing R] [IsDomain R]` (or stronger). Higher risk (~150-300 LOC); defer.

## 10. References

- **PR #19139** (S1 OBSERVE, researcher-9, MERGED 2026-05-15T22:57:40Z) — slug bootstrap, 9-bearer Mathlib API map.
- **PR #19333** (S2 PREP, researcher-1, MERGED 2026-05-16T01:09:19Z) — refined ~46-LOC skeleton + 5 fallback recipes; bearer audit had two typeclass errors corrected here.
- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04.lean:48` — `namespace GeneralCyclicVector` (Field-locked; this S2 ACT does NOT modify).
- `proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean` — parent file's namespace (Field-locked; this S2 ACT does NOT modify).
- Mathlib `FieldTheory/Minpoly/Basic.lean:139` — `minpoly.unique'` (key bearer; CommRing-friendly).
- Mathlib `FieldTheory/Minpoly/Field.lean:72` — `minpoly.dvd` (Field-only; NOT used).
- Mathlib `Algebra/Polynomial/Degree/Domain.lean:61` — `natDegree_le_of_dvd` (NoZeroDivisors-only; NOT used).
- Memory `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path` — applied throughout.
- Memory `feedback_git_fetch_origin_main_updates_fetch_head_not_remote_ref` — explicit refspec used.
- Memory `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md` — applied at §6.

## 11. Closing checklist

- [x] S2 PREP's two bearer-audit errors caught and worked around (§1.1, §1.2).
- [x] Final proof skeleton uses only CommRing-friendly bearers (§3 table).
- [x] New file `CayleyHamiltonCyclicVectorCommRingOQ01.lean` written (worktree absolute path).
- [x] No edits to any existing Lean file (verified via `git diff --name-only`).
- [x] No open peer PRs on slug at PR-create time.
- [x] lake-manifest pin re-verified unchanged at branch creation.
- [x] Docker build clean: v1 PASS with 1 linter warning (unused `[Nontrivial R]` in trivial corollary); v2 PASS, 0 warnings, 7743 jobs, ~90s wall.
- [ ] (Pre-push) Re-run `gh pr list --search …` immediately before `git push -u`.
- [ ] (Post-merge) S3 ACT picker creates `CayleyHamiltonCyclicVectorZMod4Counterexample.lean`.

End of S2 ACT.
