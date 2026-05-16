# S10 PREP-3 — S6α `stdLatticeN_coords` paste-ready upgrade + fresh bearer drift recheck under host-disk-blocked ACT window

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: PREP-3 (doc-only — no Lean, no `problem.md`, no `knowledge.md`, no `approaches/*`, no gallery)
**Author**: researcher-8
**Date**: 2026-05-16
**Base**: `origin/main` @ `cf1cfa085e4` (post-S9-STATE-SYNC + post-shapley-folkman-s10-statesync merges)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; unchanged across Session 9 → Session 10 window)
**Predecessor**: S9 STATE-SYNC (PR #19419, researcher-1, 2026-05-16T01:35Z) and S6 PREP-2 (PR #19192, researcher-3, 2026-05-15T22:55Z) — this PREP-3 upgrades the §5 Lean skeleton in #19192 from "candidate / paper design" to paste-ready, re-verifies the 5 bearers cited in #19192 §3, and documents the live blocker (host disk 100%) that gates any Docker-verified ACT this cycle.

## 1. Position vs `origin/main` HEAD and concurrent PRs

`gh api 'search/issues?q=repo:rjwalters/lean-genius+is:pr+minkowski-theorem-oq-02-oq-03'` @ 2026-05-16T05:24Z returns **zero open PRs** touching this slug. The slug's last-merged PR is #19419 (S9 STATE-SYNC). The Lean file at HEAD:

```
proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean — 331 LOC, 8 theorems, 3 defs, 0 sorries, 0 axioms
```

Confirmed via `wc -l` + `grep -c "^theorem\|^lemma"` + `grep -c "^def\|^noncomputable def"`. JSON sidecar `currentState.iteration: 8`, `leanFiles[0].{lineCount: 331, theoremCount: 8, defCount: 3, axiomCount: 0, sorryCount: 0}` all match.

**Orthogonality of THIS PR (S10 PREP-3 doc-only)**:

| File class touched here | Conflict with any open slug-PR? |
| ----------------------- | ------------------------------- |
| `sessions/2026-05-16-s10-prep-3-s6alpha-pasteready-upgrade.md` (new) | No — no open PRs on slug |
| `state.md` (minimal: iter 8 → 9, +Session 10 row in chronology, refresh Next Action header note) | No — no open PRs on slug |
| `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json` (iter 8 → 9, lastUpdate bump, +builtItems entry, focus/nextAction refresh) | No — no open PRs on slug |

Zero conflicts. Three files touched; one new, two edited.

## 2. Bearer drift recheck at HEAD `cf1cfa085e4` / pin `2df2f015...`

Per S6 PREP-2 §3 (#19192) + S9 STATE-SYNC §4. Re-verified via `curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/<path>`:

| # | Bearer | Path | S6 PREP-2 cite | Current line | Drift |
|---|---|---|---|---|---|
| 1 | `Submodule.mem_span_range_iff_exists_fun` | `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean` | 372 | 372 | none |
| 2 | `Pi.basisFun` (def) | `Mathlib/LinearAlgebra/StdBasis.lean` | (implicit) | 127 (`noncomputable def basisFun`) | none |
| 3 | `Pi.basisFun_apply` (`@[simp]`) | `Mathlib/LinearAlgebra/StdBasis.lean` | 131 | 131 | none |
| 4 | `Int.cast_smul_eq_zsmul` | `Mathlib/Algebra/Module/NatInt.lean` | 151 | 151 | none |
| 5a | `Finset.prod_ite_eq'` (with `s : Finset ι` arg) → `@[to_additive (attr := simp)] Finset.sum_ite_eq'` | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` | 151–153 | 152 (theorem stmt; `@[to_additive (attr := simp)]` attr on line 148) | **off-by-one cite** (cosmetic — both halves of the cited range overlap the actual location) |
| 5b | `Finset.prod_ite_eq'` (no-`s` arg, implicit `Finset.univ`) → `@[to_additive] Finset.sum_ite_eq'` | same file | **not cited** in S6 PREP-2 | 297 (theorem stmt; comment `/-- See also `Finset.prod_ite_eq'`. -/` on 295 disambiguates) | **NEW** (this is a useful alternative — see §3.4 below) |

Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` confirmed via `gh api repos/leanprover-community/mathlib4/git/trees/2df2f0150c...` returning the same SHA, and via `proofs/lake-manifest.json` line 8 (`"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`, `"inputRev": "v4.26.0"`).

**Zero substantive drift** in any of the 5 bearers cited by S6 PREP-2 §3. The one minor cosmetic note (5a, line 151 → 152) is a 1-line off-by-one in #19192's citation that does not affect tactic semantics — `Finset.sum_ite_eq'` is the `@[to_additive]` derivative of `Finset.prod_ite_eq'`, generated at the same statement-level. The NEW data point (5b, `Finset.prod_ite_eq'` no-`s` form at line 297) was not catalogued by S6 PREP-2 and is materially useful for tightening the §5 simp chain — documented in §3.4 below.

## 3. Paste-ready §5 upgrade

### 3.1 What S6 PREP-2 §5 ships

```lean
open MinkowskiProved in
lemma stdLatticeN_coords {m : ℕ} (x : stdLattice m) :
    ∃ c : Fin m → ℤ, ∀ i : Fin m, (x : Fin m → ℝ) i = (c i : ℝ) := by
  have hmem : (x : Fin m → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin m))) := x.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc_real : (x : Fin m → ℝ) = ∑ i : Fin m, (c i : ℝ) • Pi.basisFun ℝ (Fin m) i := by
    rw [← hc]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    exact (Int.cast_smul_eq_zsmul (R := ℝ) (c i) (Pi.basisFun ℝ (Fin m) i)).symm
  refine ⟨c, fun i ↦ ?_⟩
  rw [hc_real]
  simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_ite_eq']
```

Honesty caveat in S6 PREP-2 §9: "No `lake build` performed. All bearer claims are gh-api source inspections at the pinned SHA, not type-checked elaboration. The refined §5 skeleton is a paper design."

### 3.2 Three open elaboration risks in the §5 skeleton

Carrying forward S6 PREP-2 §6 — three live risks the default `simp` chain may not close:

* **Risk A (§6.1 of #19192)**: `Pi.single_apply` direction vs `Finset.sum_ite_eq'`. `Pi.single i 1 j = if j = i then 1 else 0` is variable-first; `Finset.sum_ite_eq'` expects `if x = a then b x else 0` (variable-first) — directions match. The default `simp` set should chain them. *But* if simp picks the unprimed `Finset.sum_ite_eq` first (target-first, `if a = x ...`), the `if` won't simplify.
* **Risk B (§6.2 of #19192)**: simp may not push `smul` through `ite`. After `Pi.basisFun_apply` + `Pi.single_apply`, the goal is `∑ j : Fin m, (c j : ℝ) • (if j = i then (1 : ℝ) else (0 : ℝ)) = (c i : ℝ)`. The default simp set normally has `smul_ite` + `smul_zero` + `smul_one` + `mul_one`, but the order of attribute resolution at v4.26.0 has occasionally surprised researchers (see researcher-3's `sum_involution invol`-case generalize failure, distinct issue but similar default-set fragility).
* **Risk C (§6.3 of #19192)**: `Int.cast_smul_eq_zsmul` direction. Worked around in §5 by `Finset.sum_congr` + `.symm` instead of `simp_rw [← ...]`. This is the robust path and carried forward unchanged.

### 3.3 Paste-ready upgrade — defensive `simp only`

Replace the final-line `simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_ite_eq']` with an explicit `simp only` chain that pre-resolves Risks A + B:

```lean
open MinkowskiProved in
/-- A point in the standard integer lattice `stdLattice m = ℤᵐ` has
integer coordinates.

This is the n-dim generalization of parent OQ-02's `stdLattice2_coords`
(`MinkowskiTheoremOQ02.lean:147`). It is specialized at `m := n+1` in the
upcoming `simultaneous_dirichlet_from_minkowski` (S6 ACT) to read off
`q := c 0` (common-denominator) and `p i := c i.succ` (approximation
residuals). -/
lemma stdLatticeN_coords {m : ℕ} (x : stdLattice m) :
    ∃ c : Fin m → ℤ, ∀ i : Fin m, (x : Fin m → ℝ) i = (c i : ℝ) := by
  -- Step A: membership in ℤ-span of standard basis
  have hmem : (x : Fin m → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin m))) := x.2
  -- Step B: extract integer coefficients
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  -- Step C: lift ℤ-smul to ℝ-smul (v4.26.0 modern form; .symm direction)
  have hc_real : (x : Fin m → ℝ) = ∑ i : Fin m, (c i : ℝ) • Pi.basisFun ℝ (Fin m) i := by
    rw [← hc]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    exact (Int.cast_smul_eq_zsmul (R := ℝ) (c i) (Pi.basisFun ℝ (Fin m) i)).symm
  -- Step D: coordinate-wise extraction with explicit simp_only chain
  refine ⟨c, fun i ↦ ?_⟩
  rw [hc_real]
  -- evaluate the i-th component of the sum
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply,
             Pi.single_apply, smul_ite, smul_zero, smul_eq_mul, mul_one,
             Finset.sum_ite_eq', Finset.mem_univ, if_true]
```

**Why this is paste-ready** vs S6 PREP-2 §5:

1. **Risk A pre-resolved**: `simp only` is name-pinned — `Finset.sum_ite_eq'` (prime) is the only ite-collapse lemma in the list. The unprimed `Finset.sum_ite_eq` is excluded by construction.
2. **Risk B pre-resolved**: the chain explicitly includes `smul_ite` (push smul through ite), `smul_zero` (collapse zero branch), `smul_eq_mul` + `mul_one` (collapse one branch).
3. **Risk C unchanged**: the `Finset.sum_congr` + `.symm` workaround in Step C is robust and carries forward.
4. **`Finset.sum_apply` + `Pi.smul_apply`** are pre-pended to ensure the pointwise-application of the sum is unfolded before `Pi.basisFun_apply` fires. Without these, `simp only` may stall on `(∑ i, c i • Pi.basisFun ...) i` since the inner `Pi.basisFun_apply` only matches under a `(...) i` peel.

### 3.4 Alternative — use `Finset.prod_ite_eq'` no-`s` form (line 297)

The newly-catalogued bearer 5b (`Finset.prod_ite_eq'` at line 297, no-`s` arg, implicit `Finset.univ`) collapses the simp chain further. The `@[to_additive]`-generated `Finset.sum_ite_eq'` (no-`s`) statement is:

```lean
lemma sum_ite_eq' (i : ι) (f : ι → M) :
    ∑ j, (if j = i then f j else 0) = f i
```

This eliminates the outer `if i ∈ Finset.univ then ... else ...` that the line-152 form leaves dangling, so `Finset.mem_univ`/`if_true` cleanup is unnecessary. **Tradeoff**: the §3.3 chain is the safer choice because (a) `simp only` is *fully* literal — the no-`s` form requires the goal to *exactly* match `∑ j, (if j = i then _ else 0)` with no outer `s` argument; (b) after `Finset.sum_apply` peels the `∑ i, ...` to `∑ i ∈ Finset.univ, ...`, both forms apply, but the line-152 form is the more standard direction. Use the line-297 form *only* as a fallback if `Finset.sum_ite_eq'` (line-152) misfires on the explicit-`s` form.

**Drop-in fallback for Step D**:

```lean
  refine ⟨c, fun i ↦ ?_⟩
  rw [hc_real]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply,
             Pi.single_apply, smul_ite, smul_zero, smul_eq_mul, mul_one]
  -- now goal: ∑ j : Fin m, (if j = i then (c j : ℝ) else 0) = (c i : ℝ)
  -- the no-s form (line 297) closes this directly:
  exact Finset.sum_ite_eq' i (fun j ↦ (c j : ℝ))
```

(Caveat: the `exact Finset.sum_ite_eq' i ...` invocation requires the no-`s` form to have *type* `(i : ι) → (f : ι → M) → ∑ j, ite (j = i) (f j) 0 = f i` — which the line-297 definition supplies.)

### 3.5 LOC accounting

| Variant | Skeleton LOC (excl. docstring) | Docstring LOC | Total |
|---|---|---|---|
| S6 PREP-2 §5 (paper design) | ~12 | ~10 | ~22 |
| **S10 PREP-3 §3.3 (defensive `simp only`)** | ~13 | ~10 | ~23 |
| S10 PREP-3 §3.4 (line-297 alt, fallback only) | ~13 | ~10 | ~23 |

Net delta: +1 LOC vs S6 PREP-2 §5 (the extra `Finset.sum_apply` / `Pi.smul_apply` pre-peel). Still within the original ~22 LOC budget.

### 3.6 Import requirement (carried forward from S6 PREP-2 §5.1)

`MinkowskiTheoremOQ02OQ03.lean` does **not** currently import `Proofs.MinkowskiFundamentalTheorem`. S6α ACT must add:

```lean
import Proofs.MinkowskiFundamentalTheorem
```

This pulls in `MinkowskiProved.stdLattice`, `MinkowskiProved.stdBasis`, `MinkowskiProved.minkowski_integer_lattice_proved` — needed for S6α and the subsequent S6 ACT. Adding the import in S6α front-loads the Docker pre-elaboration cost ONCE. Parent `MinkowskiFundamentalTheorem` is already build-clean per the lake-pinned SHA (last green build per PR #19046 was 3058 jobs).

## 4. Live blocker — host disk pressure 100% blocks Docker ACT this cycle

**Captured @ 2026-05-16T05:24:10Z** on this researcher host (researcher-8):

```
$ df -h /System/Volumes/Data
Filesystem        Size    Used   Avail Capacity  iused  ifree %iused  Mounted on
/dev/disk3s5    926Gi   883Gi   7.1Gi   100%       21M    74M    22%  /System/Volumes/Data

$ timeout 30 docker info | grep -A2 "Server:"
Server:
(empty — daemon non-responsive past 30s timeout)
```

Per `feedback_researcher_act_pivot_to_prep_when_host_docker_corrupt.md`: when `docker info` hangs and `df` shows ≥99% on `/System/Volumes/Data`, Docker daemon corruption (containerd `meta.db` I/O errors) is overwhelmingly likely. Per `feedback_researcher_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat.md`: 100%-full host blocks Docker meta.db; the right pivot for a non-pure-deletion ACT is doc-only PREP, *not* "build pending" ship.

This is the EXACT same blocker that researcher-8's predecessor cycle hit at ~05:05Z on `sum-of-divisors-oq-02` (PR #19467 reverted the iter-1 Lean and shipped as doc-only PREP — file `Mathlib/Data/DFinsupp/Module.olean.server invalid header` then containerd blob I/O on iter-2). Same root cause, same pivot.

**Implication for the slug**: the S6α ACT (~22-23 LOC paste-ready per §3.3 above) cannot be Docker-verified this cycle. The PREP-3 doc-only ship is the right move. Subsequent claimants must check `df -h /System/Volumes/Data` BEFORE branching for ACT — if still ≥99%, defer ACT and ship STATE-SYNC or another PREP-level doc instead.

## 5. Order-of-operations under S5-c + S6α concurrent-claim window

**Independence**: per S6 PREP-2 §7, S5-c ACT (`dirichletSetN_volume`, ~49 LOC) and S6α ACT (`stdLatticeN_coords`, ~22-23 LOC) are file-disjoint after S5-b (#19046) merged:

* S5-c targets PART 6 of `MinkowskiTheoremOQ02OQ03.lean` (volume, depends on `dirichletBoxN` + `shearM_det = (-1)^n` + `dirichletSetN_eq_shearM_preimage` — all on `main`).
* S6α targets PART 6α of `MinkowskiTheoremOQ02OQ03.lean` (integer-coord extraction, depends only on `stdLattice m` via `Proofs.MinkowskiFundamentalTheorem`).
* Neither modifies any existing PART 1–5 declaration.
* Both append-only — line-shift conflict surface is minimal.

**Race scenarios** (under typical drain rate of 1–3 merges per ~30-min wave + 88-PR open backlog):

| Scenario | S5-c lands first | S6α lands first | Both land same wave | Both branch from same base, sequential merge |
|---|---|---|---|---|
| Conflict surface | None — S5-c PART 6 below S5-b's PART 5; S6α PART 6α appends after | None — S6α's PART 6α inserted between PART 5 and PART 6; S5-c rebases to put PART 6 after PART 6α | One must rebase; one-time `git rebase origin/main` resolves trivially (no overlapping declarations) | Rebase target is the merged-first PR's HEAD; same trivial resolution |
| Recommended sequencing | S5-c first IF S5-c claimant builds successfully (resolves the harder Mathlib dependency chain — `Real.map_matrix_volume_pi_eq_smul_volume_pi`, ENNReal-valued B1) | S6α first IF host-disk-blocked window persists (S6α is narrower at ~22 LOC and has 0 ENNReal dependency surface) | Both pickers should explicitly read state.md before claiming to avoid duplicate work | Both pickers should branch from `origin/main` AT CLAIM TIME (not earlier) |
| Recovery if branched from stale `origin/main` | `git rebase origin/main` — append-only PR, no line-overlap | Same — append-only | Same | Same |

**Recommendation under current host-disk window (2026-05-16T05:24Z)**: defer both S5-c and S6α ACTs until `df -h /System/Volumes/Data` drops below 95% — verifiable via the same one-liner above. If the disk pressure persists, alternate claimants can ship further PREP-level docs (e.g., a PREP-4 sibling-audit of OQ-02 / OQ-04 parents for missing `dirichletSetN_volume` pre-staging, or a PREP-5 for the S6 ACT 5-stage assembly which is currently only sketched in #18511).

## 6. ACT-readiness gate (carried from S6 PREP-2 §11 + refreshed)

| # | Gate | S6 PREP-2 (#19192) | S10 PREP-3 (this memo) | Notes |
|---|---|---|---|---|
| 1 | S6 PREP §3.2 sketch line-cited | ✅ | ✅ | PR #18511, file `2026-05-12-s6-prep-minkowski-assembly-roadmap.md` |
| 2 | 5 Mathlib bearers audited at pin | ✅ (1 ⚠️ for deprecated `zsmul_eq_smul_cast`) | ✅ refreshed — 5/5 unchanged + 1 new variant catalogued (§2) | Pin unchanged |
| 3 | Lean skeleton paste-ready (Risks A+B pre-resolved) | ⚠️ (default `simp` chain — paper design per §9 caveat) | ✅ §3.3 defensive `simp only` chain | S6 PREP-2 explicitly flagged this as future-work |
| 4 | Fallback recipe documented if §3.3 misfires | ❌ | ✅ §3.4 line-297 `Finset.prod_ite_eq'` no-`s` form | Newly added in this PREP-3 |
| 5 | Order-of-operations under S5-c + S6α concurrent claim | ⚠️ (§7 sketch only) | ✅ §5 race-scenario table | Covers 4 cases incl. recovery |
| 6 | Live blocker analysis | ❌ | ✅ §4 host-disk-100% capture | Host disk + Docker daemon non-responsive |
| 7 | Honest framing (no Docker build, paper-design caveats explicit) | ✅ (§9, 6 caveats) | ✅ refreshed (§7 below, 4 caveats incl. line-297 untested) | |
| 8 | Pre-claim cross-checks | ✅ (§10, 7 items) | ✅ (§8 below, 9 items incl. host-disk capture) | |

**Gate state**: **7/8 GREEN, 1/8 AMBER** (gate 6 — host disk pressure — is a real-world condition that flips back to GREEN as soon as host disk drops below 95%). The S6α ACT is otherwise paste-ready; only the Docker build verification is blocked, and that blocker is *external* to the slug's mathematical content.

## 7. Honest framing — what THIS PREP-3 does NOT establish

1. **No `lake build` performed.** All bearer claims are `curl`-based source inspections at the pinned SHA, not type-checked elaboration. The §3.3 + §3.4 Lean skeletons are paper designs (now tighter than S6 PREP-2 §5, but still untested under the Lean elaborator).
2. **§3.4 line-297 fallback is itself untested.** The claim that `Finset.sum_ite_eq'` (no-`s`) has the stated signature (line-297 to_additive derivative) is sourced from the curl of `Piecewise.lean` lines 295–298. If the `@[to_additive]` macro generates a different signature than expected, the §3.4 `exact Finset.sum_ite_eq' i ...` won't typecheck — fall back to the §3.3 chain.
3. **§4 host-disk pressure is a snapshot.** The 7.1Gi free at 05:24Z is a real condition right now but is not a permanent state of the host. The right re-entry signal is `df -h /System/Volumes/Data` reading <95% capacity — verifiable in 1 second by the next claimant.
4. **§5 order-of-operations covers only file-level conflict surface.** It does not exhaustively model semantic interactions (e.g., if both S5-c and S6α somehow introduce a shared lemma — they don't, per S5-c PREP #19181 §3 and S6α §3.3, but the analysis assumes that).

## 8. Pre-claim cross-checks

* ✅ Worktree synced to `origin/main` BEFORE branching (HEAD at `cf1cfa085e4` = "research(shapley-folkman-oq-01): Session 10 STATE-SYNC …" per `git rev-parse origin/main`).
* ✅ Fresh topic branch off `origin/main`: `research/minkowski-theorem-oq-02-oq-03-s10-1778908649`.
* ✅ Three slugs grepped for open PRs at claim time (`gh api search/issues?q=...minkowski-theorem-oq-02-oq-03+is:pr`): 0 open. Conflict surface zero.
* ✅ Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` verified at `proofs/lake-manifest.json:8`.
* ✅ Mathlib pin SHA validated via `gh api repos/leanprover-community/mathlib4/git/trees/2df2f0150c...` returning the same SHA.
* ✅ Mathlib bearer drift recheck (§2): 5/5 at original lines/paths + 1 new variant catalogued (5b at line 297).
* ✅ Lean inventory at HEAD matches JSON sidecar (331 LOC / 8 thm / 3 def / 0 sorries / 0 axioms — confirmed via `wc -l` + `grep -c`).
* ✅ Host disk pressure captured (§4): 7.1Gi free, 100% capacity on `/System/Volumes/Data`; `docker info` hangs past 30s timeout.
* ✅ `gh repo view` defaults to `rjwalters/lean-genius` (confirmed via `git remote -v`); `gh pr create` will resolve correctly without explicit `-R`.

## 9. No-edit guarantee

This PR touches only:

```
research/problems/minkowski-theorem-oq-02-oq-03/sessions/
    2026-05-16-s10-prep-3-s6alpha-pasteready-upgrade.md   (new)
research/problems/minkowski-theorem-oq-02-oq-03/state.md  (minimal: iter 8 → 9, +Session 10 row, refresh Next Action header note)
src/data/research/problems/minkowski-theorem-oq-02-oq-03.json (iter 8 → 9, lastUpdate bump, +builtItems entry, focus/nextAction refresh)
```

Branch: `research/minkowski-theorem-oq-02-oq-03-s10-1778908649`. Base: `origin/main` at `cf1cfa085e42ac65894740a787228d22cc2f269e`.

No Lean changes. No `problem.md` / `knowledge.md` / `approaches/*` / gallery edits.

## 10. Done When (this PREP-3 session)

- [x] S6 PREP-2 §5 sketch + §6 hazards re-read; gaps catalogued (§3.2).
- [x] 5 Mathlib bearers re-verified at pin via `curl` of `raw.githubusercontent.com` (§2).
- [x] 1 new bearer variant catalogued (`Finset.prod_ite_eq'` no-`s` at line 297, §2 row 5b).
- [x] Paste-ready §5 upgrade with defensive `simp only` chain (§3.3, ~13-LOC body).
- [x] Fallback recipe for §3.3 misfire documented (§3.4 line-297 alternative).
- [x] Live blocker (host disk 100%, Docker daemon non-responsive) captured with `df -h` + `docker info` outputs (§4).
- [x] S5-c + S6α order-of-operations under concurrent-claim window analysed (§5, 4 scenarios).
- [x] ACT-readiness gate refreshed (§6, 7/8 GREEN + 1/8 AMBER on host-disk).
- [x] Honest framing caveats explicit (§7, 4 items).
- [x] Pre-claim cross-checks (§8, 9 items).
- [x] No-edit guarantee on Lean / problem / knowledge / approaches / gallery (§9).

## 11. References

* **S1 OBSERVE**: `sessions/2026-05-12-s01-observe.md` (PR #18339, 2026-05-12 22:39 UTC, researcher-1).
* **S5 PREP** (shear-map volume): `sessions/2026-05-12-s5-prep-shear-volume-generalization.md` (PR #18419, researcher-11).
* **S5 PREP-2** (Mathlib bearer audit, precedent for the §2 style): `sessions/2026-05-13-s5-prep-2-mathlib-bearer-audit.md` (PR #18622, researcher-5).
* **S6 PREP** (assembly roadmap): `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md` (PR #18511, researcher-1).
* **S6 PREP-2** (the doc this PREP-3 upgrades): `sessions/2026-05-14-s6-prep-2-stdLatticeN-skeleton-audit.md` (PR #19192, researcher-3, 2026-05-15T22:55:55Z).
* **S5-c PREP** (rect-volume bridge for the parallel lane): `sessions/2026-05-14-s5c-prep-rect-volume-bridge.md` (PR #19181, 2026-05-15T22:56:26Z).
* **S5-b PREP** (Tv0/Tv_succ/rectN templates, historical): `sessions/2026-05-15-s5b-prep-Tv-preimage.md` (PR #19283, 2026-05-15T18:01:41Z).
* **S5-b ACT** (Lean, +79 LOC, 3058 jobs): PR #19046, 2026-05-15T23:27:39Z.
* **S8-c PREP body** (post-drain audit): `sessions/2026-05-15-s8c-prep-postdrain-audit.md` (PR #19321, researcher-8, 2026-05-15T~23:11Z + §10 addendum PR #19343, 2026-05-16T01:08:50Z).
* **S9 STATE-SYNC** (Option-B catchup absorbing 6 post-S8 merges): `sessions/2026-05-16-s9-statesync.md` (PR #19419, researcher-1, 2026-05-16T01:35Z).
* **Parent OQ-02** template: `MinkowskiTheoremOQ02.lean:147–165` (`stdLattice2_coords`, ~19 LOC for `Fin 2`).
* **`stdLattice` def**: `MinkowskiFundamentalTheorem.lean:590`.
* **`Submodule.mem_span_range_iff_exists_fun`** at pin: `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean:372`.
* **`Pi.basisFun` def + `basisFun_apply`** at pin: `Mathlib/LinearAlgebra/StdBasis.lean:127, 131`.
* **`Int.cast_smul_eq_zsmul` (modern)** at pin: `Mathlib/Algebra/Module/NatInt.lean:151`.
* **`Finset.prod_ite_eq'` (with-`s` and no-`s` forms; `@[to_additive (attr := simp)]` derivatives `Finset.sum_ite_eq'`)** at pin: `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:152` (with-`s` form) and `Piecewise.lean:297` (no-`s` form).
* **Feedback memories referenced**: `_researcher_act_pivot_to_prep_when_host_docker_corrupt`, `_researcher_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat`, `_researcher_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep`, `_researcher_act_paste_ready_skeleton_typically_needs_1_to_3_acttime_fallbacks`.
* **Cassels, J.W.S.** (1957), *An Introduction to Diophantine Approximation*, Theorem I.II.A.
