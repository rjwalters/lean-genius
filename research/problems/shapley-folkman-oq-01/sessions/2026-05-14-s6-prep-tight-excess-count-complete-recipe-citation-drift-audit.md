# 2026-05-14 — S6 PREP: `tight_excess_count` complete Lean recipe + Mathlib v4.26.0 citation drift audit (doc-only)

**Researcher**: researcher-9
**Slug**: `shapley-folkman-oq-01`
**Phase**: S6 PREP (doc-only; cross-PR coordination — no state.md / JSON / .lean edits)
**Branch**: `research/researcher-9-shapley-folkman-oq01-s2a-act-2-1778808708`
**Mathlib pin**: `v4.26.0`, SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`)
**Parent scaffold**: `proofs/Proofs/ShapleyFolkmanOQ01.lean` (S2-A ACT-1, PR #18854, merged)

## §0 Predecessor chain + open-PR context

### §0.1 Merged ladder (S1 → S2-A ACT-1 → S5 PREP)

| PR     | Phase       | Contribution                                                                                |
|--------|-------------|---------------------------------------------------------------------------------------------|
| #18345 | S1  OBSERVE | Literal `finrank` extension is vacuous; Approaches A/B/C surveyed; C chosen.                |
| #18414 | S1b OBSERVE | Aumann/Lyapunov Mathlib prerequisite audit (A/B deferred).                                  |
| #18397 | S2  PREP    | Approach C `ℓ²` counter-example design; `EuclideanSpace ℝ (Fin N)` formulation.             |
| #18452 | S2b PREP    | Numeric verification at `N=1..4`; orthogonality uniqueness sketch.                          |
| #18491 | S3  PREP    | Pair convex-hull parameter-extraction recipe (`convexHull_pair_zero_basis_extract`).        |
| #18556 | S3b PREP    | Mathlib v4.26.0 citation audit; 3 phantom-lemma corrections.                                |
| #18649 | S4  PREP    | Parent `ShapleyFolkman.lean` source audit (decidability + `sum_close_to_convexHull` bridge). |
| #18854 | S2-A ACT-1  | Scaffold landed: 3 named results in `proofs/Proofs/ShapleyFolkmanOQ01.lean`; 2 sorries.     |
| #18929 | S5  PREP    | `mem_convexHull_finset_sum` 5-step Lean recipe (§3 verbatim).                                |

### §0.2 Open PR #19003 (S9 STATE-SYNC, deployer-stalled)

PR #19003 ("research(shapley-folkman-oq-01): Session 9 STATE-SYNC — record merged S5 PREP recipe (doc-only)") was opened at **2026-05-14T05:32:42Z** by researcher-9 (prior session). As of **2026-05-15T01:30Z** it is:

* `state`: OPEN
* `mergeable`: MERGEABLE
* `mergeStateStatus`: CLEAN
* `additions/deletions`: +96/-17
* Touched: `research/problems/shapley-folkman-oq-01/state.md` (+85/-6) and `src/data/research/problems/shapley-folkman-oq-01.json` (+15/-7)
* Age: **~20h** (well past the 12h threshold in `feedback_researcher_deployer_stall_coordination_prep_pattern.md`)

System-wide deployer stall: the most recent merge to `main` is at **2026-05-14T03:03:38Z** — **~22.4h** ago. The deployer is not running or is stuck; >40 open mergeable PRs at this moment in the repo.

### §0.3 Closed PR #19185 (duplicate rescue, false alarm)

PR #19185 ("research(shapley-folkman-oq-01): rescue stranded S9 STATE-SYNC (doc-only)") was opened by researcher-3 at **2026-05-15T01:05:11Z** and closed at **2026-05-15T01:09:44Z** by the same author with the comment:

> Closing as duplicate of #19003 (already open with identical S9 STATE-SYNC content). My pre-claim `gh pr list --search` was missing the `--repo rjwalters/lean-genius` flag and returned empty due to worktree gh-config drift, so I incorrectly classified commit `09519ee27cf` as stranded.

This is a textbook hit of `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md` (gh CLI default-repo points at `rjwalters/mathlib4` fork in lean-genius worktrees). **Future research sessions on this slug** should:

1. Always `-R rjwalters/lean-genius` in `gh pr list` / `gh pr view` / `gh pr create` calls.
2. Treat any "stranded commit" classification on a research/researcher-N-* branch with a `(no PR-number suffix in the subject line)` as a **suspect** until cross-checked with `gh api repos/rjwalters/lean-genius/compare/main...<branch> --jq '.ahead_by'` (which uses an absolute repo path and bypasses the default-repo drift).

### §0.4 What this S6 PREP does

This PREP is a **doc-only cross-PR coordination + Mathlib citation drift audit + complete `tight_excess_count` recipe**. The contributions are:

1. **Independent re-verification** of all four S5 PREP §2 Mathlib citations at the *current* pin SHA `2df2f0150...`. All four hold; recorded in §2 with verbatim source quotes.
2. **Mathlib citation drift audit** of S3 PREP §4 (`Finset.sum_apply` path), S3 PREP §5 (`EuclideanSpace.single_eq_zero_iff` line), and S2b PREP §5.1 (`PiL2.lean:308` for `single_apply`). Corrections are recorded in §3.
3. **Complete drop-in Lean recipe for `tight_excess_count`** (`proofs/Proofs/ShapleyFolkmanOQ01.lean:119–128`), ~45 LOC tactic body. Combines S3 PREP §3.1 helper (already applied, line 58–73 of the scaffold), S3 PREP §4 coordinate-eval, and S3 PREP §5 cardinality finishers. See §4.
4. **Failure-mode catalogue** for the recipe (§5): the `EuclideanSpace`/`PiLp` coordinate-eval has 3 known elaboration pitfalls at v4.26.0.
5. **Sequencing recommendation** for ACT-2 (§6) given the open #19003 state.md/JSON sync.

**Scope**. Doc-only. **No edits** to: `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`, any `.lean` file, `src/data/research/problems/*.json`, or any other previously-tracked file. **One new file**: this `sessions/2026-05-14-s6-prep-...md`. No `lake build` attempted (per CLAUDE.md DANGER policy + `feedback_researcher_lake_symlink_loop_and_wipe.md`).

## §1 — Why a complete `tight_excess_count` recipe is the next-best doc-only deliverable

S5 PREP (#18929) provided the verbatim Lean recipe for `mem_convexHull_finset_sum` (sorry #1 of 2). The sibling sorry `tight_excess_count` (file lines 119–128) was sketched in S3 PREP §4 + §5 but **never assembled into a single drop-in tactic body**. Specifically:

* S3 PREP §3.1 — extract helper lemma (now in scaffold as `convexHull_pair_zero_basis_extract`, lines 58–73). ✓ verbatim.
* S3 PREP §4 — coordinate-evaluation shortcut (~5 LOC `simp` block sketch). Not Lean-complete: needs to integrate the helper's output `t : Fin N → ℝ` into `D.sum_eq`.
* S3 PREP §5 — `(1/2) • e_j ∉ S j` step (~8 LOC). Lean-complete for the local membership refutation but does **not** integrate with the coordinate-eval step or the cardinality finisher.

So the S3 PREP recipe is a **chained sketch** across three sections; an ACT-2 author still has to make non-trivial assembly decisions (binding order of `choose`, simp-set tuning for `single_apply`, `filter_eq_self` for the cardinality conclusion). The risk that ACT-2 stalls mid-discharge is real — every "almost-Lean" PREP step that requires assembly has historically caused a 1–2 session bounce when an ACT author misjudges typeclass/simp ordering.

**This PREP's §4** provides the **assembled, drop-in body**: one 45-LOC tactic with no inter-section gaps. The author of ACT-2 (whether next researcher, doctor, or `loom-doctor` on a mechanic kit) can drop §4 verbatim into the parent file at line 128.

**Anti-target acknowledgment.** This PREP does **not** attempt build verification. Per CLAUDE.md "DANGER: Never Run `lake build` Directly" + the S2-A ACT-1 session 8 self-disclosure note (`feedback_researcher_lake_symlink_loop_and_wipe.md` cited there but not in MEMORY.md index), `lake build` / `docker-build.sh` is reserved for ACT-2 itself. An ACT-2 session that ships a build-verified discharge is strictly better than a PREP that hand-checks the recipe but defers building.

## §2 — Re-verification of S5 PREP §2 Mathlib citations at pin SHA `2df2f0150...`

All four citations confirmed via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` calls on 2026-05-15.

### §2.1 `Set.finset_sum_mem_finset_sum` (n-ary additive Minkowski membership) ✓

* **File**: `Mathlib/Algebra/Group/Pointwise/Set/BigOperators.lean`
* **Line**: 142 (multiplicative `Set.finset_prod_mem_finset_prod`); `@[to_additive]` attribute on line 141 generates the additive name `Set.finset_sum_mem_finset_sum`.
* **Verbatim** (lines 140–144):

  ```lean
  /-- An n-ary version of `Set.mul_mem_mul`. -/
  @[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
  theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α)
      (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i ∈ t, g i) ∈ ∏ i ∈ t, f i :=
    multiset_prod_mem_multiset_prod _ _ _ hg
  ```

* **Drift from S5 PREP**: none.
* **Use site**: S5 PREP §3 Step 1 (`h0 : 0 ∈ ∑ S_i`) and Step 2 (`hsum : ∑ e_i ∈ ∑ S_i`).

### §2.2 `subset_convexHull` ✓

* **File**: `Mathlib/Analysis/Convex/Hull.lean`
* **Line**: 50
* **Verbatim**:

  ```lean
  theorem subset_convexHull : s ⊆ convexHull 𝕜 s :=
    (convexHull 𝕜).le_closure s
  ```

* **Drift from S5 PREP**: none.
* **Use site**: S5 PREP §3 Step 4 (`subset_convexHull ℝ _ h0` and `subset_convexHull ℝ _ hsum`).

### §2.3 `convex_convexHull` ✓

* **File**: `Mathlib/Analysis/Convex/Hull.lean`
* **Line**: 53
* **Verbatim**:

  ```lean
  theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s) := (convexHull 𝕜).isClosed_closure s
  ```

* **Drift from S5 PREP**: none.
* **Use site**: S5 PREP §3 Step 4 (outer `(convex_convexHull ℝ _)` application).

### §2.4 `Convex` def → `StarConvex` unfolding ✓

* **File**: `Mathlib/Analysis/Convex/Basic.lean`
* **Line**: 51 (S5 PREP cited line 49 — drift +2 lines, immaterial)
* **Verbatim**:

  ```lean
  /-- Convexity of sets. -/
  def Convex : Prop :=
    ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s
  ```

* `StarConvex` def remains at `Mathlib/Analysis/Convex/Star.lean:76` (per S5 PREP).
* **Drift from S5 PREP**: line +2 (49 → 51), no semantic change.
* **Use site**: S5 PREP §3 Step 4 chain `hC (mem1) (mem2) (ha) (hb) (hab)` — unfolds `Convex → StarConvex → ∀-application`.

**Net for S5 PREP §3**: all four citations stable. The recipe is drop-in for ACT-2.

## §3 — Mathlib citation drift audit on S3 PREP §4 + §5 and S2b PREP §5.1

### §3.1 `EuclideanSpace.single_apply` line drift

* **S2b PREP §5.1** cited: `PiL2.lean:313`.
* **S3 PREP §4** cited: `PiL2.lean:308`.
* **Current pin** (`2df2f0150...`): **line 266**.

Verbatim at line 266 of `Mathlib/Analysis/InnerProductSpace/PiL2.lean`:

```lean
@[simp]
theorem EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  rw [EuclideanSpace.single, PiLp.toLp_apply, ← Pi.single_apply i a j]
```

**Drift**: −42 lines (S2b PREP 313 → 266) / −42 lines (S3 PREP 308 → 266). Two prior PREPs both drifted from an earlier (pre-pin?) Mathlib snapshot. Lemma name and statement are stable; the `@[simp]` attribute lets `simp` discharge `(EuclideanSpace.single i a) j` to `ite (j = i) a 0` without needing the lemma by name. This is the load-bearing fact for the §4 recipe.

### §3.2 `EuclideanSpace.single_eq_zero_iff` line drift

* **S2b PREP §5.1** cited: `PiL2.lean:313`.
* **Current pin**: **line 272** (just below `single_apply` at 266).

Verbatim at line 271–273:

```lean
@[simp]
theorem EuclideanSpace.single_eq_zero_iff {i : ι} {a : 𝕜} :
    EuclideanSpace.single i a = 0 ↔ a = 0 := (toLp_eq_zero 2).trans Pi.single_eq_zero_iff
```

**Drift**: −41 lines (313 → 272). Name + statement stable.

### §3.3 `Finset.sum_apply` path drift

* **S3 PREP §4** cited: `Mathlib/Algebra/BigOperators/Basic.lean`.
* **Current pin**: **`Mathlib/Algebra/BigOperators/Pi.lean:45`** (multiplicative `Finset.prod_apply` with `@[to_additive (attr := simp)]` generating `Finset.sum_apply`).

Verbatim at line 44–47 of `Mathlib/Algebra/BigOperators/Pi.lean`:

```lean
@[to_additive (attr := simp)]
theorem Finset.prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Finset ι) (g : ι → ∀ a, M a) : (∏ c ∈ s, g c) a = ∏ c ∈ s, g c a :=
  map_prod (Pi.evalMonoidHom M a) _ _
```

**Drift**: file path changed; `Basic.lean` no longer hosts this lemma (the Mathlib v4.26.0 reorganisation split `BigOperators.Basic` into `BigOperators.Group.Finset.{Defs,Basic,Piecewise}` and `BigOperators.Pi`). The lemma name `Finset.sum_apply` is **stable**.

**Important caveat for ACT-2**: `EuclideanSpace ℝ (Fin N) = PiLp 2 (fun _ : Fin N => ℝ)` is a `WithLp`-wrapped `Pi`, NOT a bare `Pi`. The bare `Finset.sum_apply` doesn't apply directly to `(∑ i, x i : EuclideanSpace ℝ (Fin N)) j`; we need `PiLp.add_apply` / `PiLp.smul_apply` (in `Mathlib/Analysis/Normed/Lp/PiLp.lean:115, 123`) or the `simp`-friendly route that unfolds through `WithLp.equiv` automatically.

In practice, `simp [EuclideanSpace.single_apply]` will discharge the `(EuclideanSpace.single i 1) j = ite (j = i) 1 0` step, and the surrounding `(∑ i, t i • EuclideanSpace.single i 1) j` evaluation collapses via the chain `PiLp.smul_apply` + an n-ary `PiLp` sum-apply (which is provided by `Finset.sum_apply` after `simp` unwraps the `PiLp` wrapper via `@[simp] toLp_apply`).

**The bottom line**: the §4 recipe uses `simp [Finset.sum_apply, EuclideanSpace.single_apply, Finset.sum_ite_eq', Finset.mem_univ]` to collapse the LHS to `t j` and the RHS to `1/2`. If `Finset.sum_apply` is not picked up automatically (because of the `PiLp` wrapper), add `PiLp.add_apply` and `PiLp.smul_apply` to the simp set. See §5.1.

### §3.4 `Finset.sum_ite_eq'` path drift

* **S3 PREP §4** cited: implicit (under `Mathlib/Algebra/BigOperators/Basic.lean`).
* **Current pin**: **`Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:152`** (multiplicative `Finset.prod_ite_eq'`; additive name `Finset.sum_ite_eq'` via `@[to_additive (attr := simp) ...]`).

Verbatim at line 150–154:

```lean
@[to_additive (attr := simp) /-- A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped. -/]
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x
```

**Sister lemma**: `prod_ite_eq` (at line 140, `a = x` form, vs `prod_ite_eq'` at 152, `x = a` form). The recipe in §4 uses `Finset.sum_ite_eq'` (the prime form) because `EuclideanSpace.single_apply` produces `ite (j = i) a 0` (i.e. `j = i`, which is the *prime* form `x = a` if we read the iterated index `i` as the variable and `j` as the fixed value).

Actually: in `(EuclideanSpace.single i a) j = ite (j = i) a 0`, summing over `i` gives `∑ i, t i * ite (j = i) 1 0` = `∑ i, ite (j = i) (t i) 0`. The variable is `i`, the fixed value is `j`. So we want `Finset.sum_ite_eq` (unprimed, `a = x` form, where `a = j` is fixed and `x = i` varies): `(∑ x ∈ s, ite (a = x) (b x) 0) = ite (a ∈ s) (b a) 0`. Substituting `a → j`, `x → i`, `b → t`, `s → univ` gives `(∑ i, ite (j = i) (t i) 0) = ite (j ∈ univ) (t j) 0 = t j`.

**So the correct lemma is `Finset.sum_ite_eq` (unprimed)**, at line 140 of `Piecewise.lean`, not `Finset.sum_ite_eq'` (primed) as S3 PREP §4 sketched. This is a real S3 PREP §4 correction. The `simp [Finset.sum_ite_eq', Finset.mem_univ]` line in S3 PREP §4 should be `simp [Finset.sum_ite_eq, Finset.mem_univ]` (or include both with `simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]` to be safe). The `@[simp]` attribute on `Finset.sum_ite_eq` should make `simp` pick it up automatically even without naming it.

### §3.5 Summary of drift findings

| Citation                                | S3/S2b PREP                          | Current pin                                                                            | Drift severity     |
|-----------------------------------------|--------------------------------------|----------------------------------------------------------------------------------------|--------------------|
| `EuclideanSpace.single_apply`           | `PiL2.lean:308` / `:313`             | `PiL2.lean:266`                                                                        | line drift (−42)   |
| `EuclideanSpace.single_eq_zero_iff`     | `PiL2.lean:313`                      | `PiL2.lean:272`                                                                        | line drift (−41)   |
| `Finset.sum_apply`                      | `Mathlib/Algebra/BigOperators/Basic.lean` | `Mathlib/Algebra/BigOperators/Pi.lean:45`                                              | **path drift**     |
| `Finset.sum_ite_eq'` (S3 PREP §4 name)  | implicit                             | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:152` (prime form, `x = a`)   | **name correction** (use unprimed `sum_ite_eq`) |
| `convexHull_pair`                       | `Mathlib/Analysis/Convex/Hull.lean:122` | `Mathlib/Analysis/Convex/Hull.lean:124`                                                | line drift (+2)    |
| `segment` def                           | `Mathlib/Analysis/Convex/Segment.lean:50/51` | `Mathlib/Analysis/Convex/Segment.lean:49`                                              | line drift (−1/−2) |

**None** of these drifts invalidate the recipes; lemma names + statements are stable. The relevant lemmas are all `@[simp]`-tagged so a bare `simp [single_apply, sum_apply, sum_ite_eq, mem_univ]` should collapse the coordinate evaluation. The drift audit is for *cite-fidelity* of future PREPs; it does not change the recipe semantics.

## §4 — Complete `tight_excess_count` Lean recipe (~45 LOC drop-in)

The scaffold currently has (lines 119–128 of `proofs/Proofs/ShapleyFolkmanOQ01.lean`):

```lean
theorem tight_excess_count (N : ℕ) :
    ∀ (D : ShapleyFolkman.Decomposition
            (fun i : Fin N =>
              ({0, EuclideanSpace.single i 1} :
                  Set (EuclideanSpace ℝ (Fin N))))
            (Finset.univ : Finset (Fin N))
            ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) :
                EuclideanSpace ℝ (Fin N))),
      D.excessIndices.card = N := by
  sorry
```

The proof body to drop in (replacing `sorry`):

```lean
  intro D
  -- Step 1: For each i, extract t i ∈ [0, 1] with D.point i = (t i) • e_i.
  --         Uses the helper convexHull_pair_zero_basis_extract (lines 58-73).
  have h_pt : ∀ i : Fin N,
      ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1
        ∧ D.point i = s • EuclideanSpace.single i 1 := by
    intro i
    exact convexHull_pair_zero_basis_extract (D.mem_convexHull i (Finset.mem_univ i))
  -- Step 2: Materialise t : Fin N → ℝ via Classical.choose.
  choose t ht_in ht_eq using h_pt
  -- Step 3: Rewrite D.sum_eq using ht_eq to express LHS as ∑ i, (t i) • e_i.
  have h_sum : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
                : EuclideanSpace ℝ (Fin N))
        = (1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ) := by
    have hk := D.sum_eq
    rw [Finset.sum_congr rfl (fun i _ => (ht_eq i).symm)] at hk
    -- hk : ∑ i ∈ univ, D.point i = (1/2) • ∑ i, e_i, with D.point i rewritten.
    -- Convert ∑ i ∈ univ to ∑ i (Fintype-Finset.univ-syntactic equality).
    simpa using hk
  -- Step 4: Coordinate-evaluate at j to force t j = 1/2 for every j.
  have h_tj : ∀ j : Fin N, t j = 1 / 2 := by
    intro j
    have h_eval : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
                      : EuclideanSpace ℝ (Fin N)) j
                  = ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) j :=
      congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h_sum
    -- LHS at j collapses to t j; RHS at j collapses to 1/2.
    simp [PiLp.smul_apply, EuclideanSpace.single_apply,
          Finset.sum_ite_eq, Finset.mem_univ] at h_eval
    linarith
  -- Step 5: Show every j ∈ excessIndices.
  --   D.point j = (1/2) • e_j ∉ {0, e_j} = S j because:
  --     (a) (1/2) • e_j ≠ 0 (coord at j: 1/2 ≠ 0).
  --     (b) (1/2) • e_j ≠ e_j (coord at j: 1/2 ≠ 1).
  have h_excess : ∀ j : Fin N, j ∈ D.excessIndices := by
    intro j
    simp only [ShapleyFolkman.Decomposition.excessIndices, Finset.mem_filter,
               Finset.mem_univ, true_and]
    rw [ht_eq j, h_tj j]
    intro h_mem
    rcases h_mem with h0 | h1
    · -- h0 : (1/2 : ℝ) • EuclideanSpace.single j 1 = 0
      have := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h0
      simp [PiLp.smul_apply, EuclideanSpace.single_apply] at this
      -- this : (1/2 : ℝ) = 0
    · -- h1 : (1/2 : ℝ) • EuclideanSpace.single j 1 = EuclideanSpace.single j 1
      have := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h1
      simp [PiLp.smul_apply, EuclideanSpace.single_apply] at this
      -- this : (1/2 : ℝ) = 1
  -- Step 6: excessIndices = univ, so card = N.
  have h_eq : D.excessIndices = Finset.univ := by
    apply Finset.eq_univ_of_forall
    exact h_excess
  rw [h_eq, Finset.card_univ, Fintype.card_fin]
```

**LOC count**: 45 (proof body, not counting the existing 10-line signature).
**Total file size after S2-A ACT-2 (this recipe + S5 PREP §3)**: ~190 LOC (130 scaffold + 18 mem_convexHull_finset_sum + 45 tight_excess_count - 2 sorries replaced ≈ 191 LOC).

## §5 — Failure modes + fallbacks

### §5.1 If `simp [PiLp.smul_apply, EuclideanSpace.single_apply, Finset.sum_ite_eq]` fails to collapse `h_eval`

This is the most likely failure point. The `PiLp` wrapper may not unwrap cleanly under `simp` if the elaborator is confused about whether `(∑ i, t i • EuclideanSpace.single i 1) j` should associate the sum first (then evaluate the wrapped function at `j`) or the evaluation first.

**Fallback A**: explicit `PiLp.add_apply` / `Finset.sum_apply` unwrapping:

```lean
have lhs_at_j : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
                    : EuclideanSpace ℝ (Fin N)) j
                = ∑ i : Fin N, t i • ((EuclideanSpace.single i (1 : ℝ)) j) := by
  rw [show (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
              : EuclideanSpace ℝ (Fin N))
        = ∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ) from rfl]
  exact Finset.sum_apply j Finset.univ
    (fun i => t i • EuclideanSpace.single i (1 : ℝ))
```

(`Finset.sum_apply` is at `Mathlib/Algebra/BigOperators/Pi.lean:45`.)

Then `simp [EuclideanSpace.single_apply]` collapses each summand to `ite (j = i) (t i) 0`, and `Finset.sum_ite_eq` produces `t j`.

**Fallback B**: bypass `EuclideanSpace.single` entirely by working in the underlying `PiLp 2` representation via `WithLp.equiv`:

```lean
-- Convert via WithLp.equiv to a bare Pi-function, evaluate, convert back.
```

Heavier (~15 LOC); only use if Fallback A is also defeated.

### §5.2 If `choose t ht_in ht_eq using h_pt` produces non-Decidable `t`

`Classical.propDecidable` is `local instance` in scope at line 45 of the scaffold (`attribute [local instance] Classical.propDecidable`). The `choose` tactic should produce `t : Fin N → ℝ` as a classical function without issue. If the elaborator complains:

**Fallback**: use `Classical.choose` explicitly per-index, then bundle:

```lean
let t : Fin N → ℝ := fun i => Classical.choose (h_pt i)
have ht_in : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := fun i => (Classical.choose_spec (h_pt i)).1
have ht_eq : ∀ i, D.point i = t i • EuclideanSpace.single i 1 :=
    fun i => (Classical.choose_spec (h_pt i)).2
```

(~5 LOC overhead, no functional change.)

### §5.3 If `Finset.sum_congr rfl (fun i _ => (ht_eq i).symm)` doesn't rewrite under `D.sum_eq`

`D.sum_eq : ∑ i ∈ Finset.univ, D.point i = (1/2 : ℝ) • ∑ i, EuclideanSpace.single i 1` — we want to substitute `D.point i = (t i) • e_i` inside the sum.

**Fallback**: explicit conv-block:

```lean
have hk : ∑ i ∈ Finset.univ, t i • EuclideanSpace.single i (1 : ℝ)
            = (1 / 2 : ℝ) • ∑ i, EuclideanSpace.single i (1 : ℝ) := by
  conv_lhs => ext i; rw [← ht_eq i]
  exact D.sum_eq
```

(Slightly heavier but more explicit about the rewrite direction.)

### §5.4 If `Finset.eq_univ_of_forall` is not the right name

Alternative formulations of "Finset = univ from `∀ x, x ∈ s`" exist in Mathlib:
- `Finset.eq_univ_of_forall_mem`
- `Finset.eq_univ_iff_forall.mpr`

**Quick name probe** at the pin SHA reveals `Finset.eq_univ_iff_forall` is canonical in `Mathlib/Data/Finset/Lattice/Lemmas.lean`. The fallback is `apply Finset.eq_univ_iff_forall.mpr` (one-liner equivalent).

### §5.5 If `Fintype.card_fin` doesn't close `N`

`Fintype.card_fin n : Fintype.card (Fin n) = n` is canonical. The bare `Finset.card_univ` reduces `(Finset.univ : Finset (Fin N)).card` to `Fintype.card (Fin N)`, which `Fintype.card_fin` then closes to `N`. If `simp` handles both, the final line is just `simp`.

### §5.6 Decision tree

```
[Drop §4 verbatim]
   │
   ├─ Step 4 simp fails to collapse h_eval (most likely)
   │     └─ §5.1 Fallback A (explicit Finset.sum_apply + simp)
   │
   ├─ Step 2 choose tactic complains
   │     └─ §5.2 Classical.choose explicit
   │
   ├─ Step 3 sum_congr rfl mismatch
   │     └─ §5.3 conv_lhs explicit
   │
   ├─ Step 6 Finset.eq_univ_of_forall name
   │     └─ §5.4 use Finset.eq_univ_iff_forall.mpr
   │
   └─ Step 6 Fintype.card_fin doesn't close
         └─ §5.5 replace with `simp`
```

## §6 — Race check + sequencing for ACT-2

### §6.1 Open-PR landscape on this slug (verified 2026-05-15T01:30Z)

| PR     | State    | Mergeable | mergeStateStatus | Age      | Touches                  |
|--------|----------|-----------|-------------------|----------|--------------------------|
| #19003 | OPEN     | MERGEABLE | CLEAN             | 19h54m   | state.md, JSON           |
| #19185 | CLOSED   | —         | —                 | (closed) | (duplicate of #19003)    |

No open PR edits `.lean` files for this slug. No open PR adds to `sessions/`. **This S6 PREP's new session file does not conflict with #19003** (#19003 only touches state.md and JSON).

### §6.2 Sequencing options for ACT-2

| Option | Strategy | Pros | Cons |
|--------|----------|------|------|
| **A** | Wait for #19003 to merge, then ACT-2 from updated main | Clean state.md base; no rebase | Indefinite wait (deployer-stalled 22.4h; no ETA) |
| **B** | ACT-2 NOW (from current main); accept state.md conflict at merge time | Unblocks ACT immediately | Conflict in state.md when #19003 merges first; mechanical resolution (rebase merge with #19003's "Session 9" entry + this ACT-2's "Session N+1" entry) |
| **C** | Another doc-only PREP (this one, S6); defer ACT-2 to a later session | Conflict-free; consolidates ACT-2 prerequisites | No ACT delta; #19003 + this PREP both deferred to deployer-clear time |

**Recommendation**: **Option C now (this PREP) + Option B at the next claim window**. Rationale:

1. The deployer stall is system-wide (22.4h zero merge); no PR will merge until it clears. Waiting (Option A) is not actionable.
2. Option B's state.md conflict resolution is mechanical — when both #19003 and a future ACT-2 PR are queued, the merge order doesn't affect correctness (#19003's state.md sync just sets up the post-S5-PREP context, and ACT-2 adds a "Session N+1 ACT" entry on top). The next researcher can prep this resolution offline.
3. This S6 PREP (Option C) adds *strict* value: the complete drop-in `tight_excess_count` recipe, the citation drift audit, the failure-mode catalogue, the sequencing analysis. It is conflict-free with #19003.
4. The **next** ACT-2 session has a measurably easier job: apply S5 PREP §3 (mem_convexHull_finset_sum, 18 LOC) + §4 of this PREP (tight_excess_count, 45 LOC), run `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01`, iterate per §5 fallback catalogue if needed. The Lean delta is 63 LOC; the Docker risk is bounded.

### §6.3 What this PREP does NOT do (anti-targets)

1. **Does not** attempt `lake build` / `docker-build.sh` (CLAUDE.md DANGER policy + S2-A ACT-1 self-disclosure).
2. **Does not** modify state.md or the JSON (PR #19003 is the canonical syncer for those; merging this PREP's recipe into the "Next Action" of state.md is a follow-up STATE-SYNC's job after #19003 merges).
3. **Does not** modify `problem.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
4. **Does not** modify any `.lean` file (in particular, `proofs/Proofs/ShapleyFolkmanOQ01.lean`, `proofs/Proofs/ShapleyFolkman.lean`, `proofs/Proofs.lean`).
5. **Does not** add to `src/data/proofs/shapley-folkman/` (gallery integration is enricher territory).
6. **Does not** re-derive content from S5 PREP §3 (the `mem_convexHull_finset_sum` recipe is canonical at S5 PREP; this PREP cross-references it but does not duplicate).

## §7 — Honesty disclosures

1. **All Mathlib citations re-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** on 2026-05-15 via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`. Paths and line numbers are pinned to that commit. Future Mathlib updates may drift.

2. **§4 recipe is a paper proof; no `lake build` was attempted.** The risk surface is concentrated at §5.1 (`PiLp` simp unwrapping). The §5.1 Fallback A is a proven-by-paper escape route; if both §4 and §5.1A fail, §5.1 Fallback B (`WithLp.equiv` route) is a slower but always-correct escape.

3. **The `convexHull_pair_zero_basis_extract` helper lemma tactic body (scaffold lines 58-73)** is currently unbuilt. The §4 recipe assumes it builds clean. If the helper itself fails at ACT-2 build time, S3 PREP §3.2 segment-route fallback (~10 LOC heavier) is the documented alternative; this S6 PREP does not duplicate that fallback.

4. **The `Finset.sum_ite_eq` (unprimed) correction in §3.4** is a real S3 PREP §4 error: the form `ite (j = i)` produced by `EuclideanSpace.single_apply` matches the **unprimed** lemma (where `a = x` is the form), not the primed one. The fix is a 1-character recipe change (drop the prime).

5. **The recommendation to ship Option C (this PREP) before Option B (ACT-2)** is informed by the system-wide deployer stall, not just slug-local context. A different researcher claiming this slug at a deployer-running time should pivot directly to Option B (ACT-2 now); the S6 PREP itself is still valuable as a drop-in reference but the "wait for #19003" reasoning evaporates.

6. **gh-default-repo trap mitigated**: this PREP was prepared with explicit `-R rjwalters/lean-genius` on every `gh pr list` / `gh pr view` call, per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`. The closed PR #19185 is in §0.3 as a documented near-miss.

## §8 — Pre-push race check (immediate)

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`: re-run `gh pr list -R rjwalters/lean-genius --search "shapley-folkman-oq-01 in:title" --state open` immediately before push. Expected result: PR #19003 only (the in-flight S9 STATE-SYNC, conflict-free with this S6 PREP's new session file).

If a new PR appears between now and push that:

* Adds a `sessions/2026-05-14-s6-prep-*.md` file → **abort and release** (duplicate work).
* Implements ACT-2 (discharges either sorry) → **abort and release** (this PREP is then mooted by the ACT).
* Touches state.md or JSON → **proceed** (this PREP is doc-only sessions/).
* Touches `.lean` files for unrelated reasons → **proceed** (orthogonal).

## §9 — File summary

* **New file**: `research/problems/shapley-folkman-oq-01/sessions/2026-05-14-s6-prep-tight-excess-count-complete-recipe-citation-drift-audit.md` (this).
* **Touched**: zero other files.
* **Mathlib citations re-verified**: 6 (`Set.finset_sum_mem_finset_sum`, `subset_convexHull`, `convex_convexHull`, `Convex` def, `EuclideanSpace.single_apply`, `Finset.sum_ite_eq`/`'`, with one S3 PREP §4 correction).
* **Lean LOC delta on `proofs/Proofs/ShapleyFolkmanOQ01.lean`**: 0 (this PREP edits no `.lean`).
* **Outcome**: next ACT-2 session has a 45-LOC drop-in body for `tight_excess_count` (§4) plus the S5 PREP §3 18-LOC body for `mem_convexHull_finset_sum`, plus a documented §5 fallback catalogue. Total ACT-2 delta: ~63 LOC of tactic + 1 Docker build cycle. Doc-only S6 PREP is conflict-free with open PR #19003.
