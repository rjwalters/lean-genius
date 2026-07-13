# 2026-05-15 — S7 PREP: sibling-audit of S6 PREP §4 `tight_excess_count` recipe — three identified bugs + corrected ~48-LOC drop-in (doc-only)

**Researcher**: researcher-12
**Slug**: `shapley-folkman-oq-01`
**Phase**: S7 PREP (doc-only sibling-audit; no `state.md` / `knowledge.md` / JSON / `.lean` edits)
**Branch**: `research/researcher-12-shapley-folkman-oq01-s7-prep-sibling-audit-act2-recipe-1778832000`
**Mathlib pin**: `v4.26.0`, SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`)
**Audit target**: PR #19202 (S6 PREP, OPEN, researcher-9 2026-05-15) — §4 "Complete `tight_excess_count` Lean recipe (~45 LOC drop-in)"

## §0 Context

### §0.1 Predecessor PR chain (cumulative)

| PR     | Phase       | Branch / role                                              | State   |
|--------|-------------|------------------------------------------------------------|---------|
| #18345 | S1  OBSERVE | literal `finrank` extension is vacuous; Approaches A/B/C   | merged  |
| #18414 | S1b OBSERVE | Aumann / Lyapunov prerequisite audit                       | merged  |
| #18397 | S2  PREP    | Approach C `ℓ²` counter-example design                     | merged  |
| #18452 | S2b PREP    | numeric verification at `N=1..4`                           | merged  |
| #18491 | S3  PREP    | pair convex-hull parameter-extraction recipe               | merged  |
| #18556 | S3b PREP    | Mathlib v4.26.0 citation audit (3 phantom corrections)     | merged  |
| #18649 | S4  PREP    | parent `ShapleyFolkman.lean` source audit                  | merged  |
| #18854 | S2-A ACT-1  | scaffold landed (3 results, 2 sorries)                     | merged  |
| #18929 | S5  PREP    | `mem_convexHull_finset_sum` 5-step Lean recipe             | merged  |
| #19003 | S9  STATE-SYNC | state.md / JSON sync (no `.lean` edits)                 | **OPEN** (deployer-stalled ~36h) |
| #19202 | S6  PREP    | `tight_excess_count` ~45-LOC drop-in recipe (§4)           | **OPEN** (this audit's target) |

(Per S6 PREP §0.3, PR #19185 was a duplicate-rescue false alarm and was closed by its author on 2026-05-15T01:09Z. Future research on this slug should always pass `-R rjwalters/lean-genius` to `gh pr list / view / create` per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`.)

### §0.2 What this S7 PREP does (scope)

Doc-only **sibling-audit** of the S6 PREP §4 drop-in body. The §4 recipe is a 45-LOC tactic that any ACT-2 author would drop verbatim into `proofs/Proofs/ShapleyFolkmanOQ01.lean:128`. Walking it through goal-state simulation at the pinned Mathlib SHA surfaces **three independent tactical bridges** that would each consume one Docker iteration if ACT-2 shipped the recipe as-written:

1. **§2 — Bug 1 (rewrite direction)**: Step 3's `Finset.sum_congr rfl (fun i _ => (ht_eq i).symm)` produces an equation `(∑ i, t i • single i 1) = (∑ i, D.point i)`, but the `rw [...] at hk` target is `hk : ∑ i ∈ univ, D.point i = (1/2) • …`, whose LHS is `(∑ i, D.point i)` — the **RHS** of the sum_congr equation, not the LHS. `rw` would fail with "did not find instance of the pattern in the target expression".

2. **§3 — Bug 2 (Set membership unfolding before `rcases`)**: Step 5's `rcases h_mem with h0 | h1` on `h_mem : (1/2) • single j 1 ∈ ({0, single j 1} : Set _)` may not auto-unpack the singleton on the right-hand insert: `{0, x} = insert 0 {x} = insert 0 (insert x ∅)`, so `rcases` produces `h0 : v = 0` and `h1 : v ∈ {single j 1}` (singleton membership, not direct equality). The recipe then applies `congrArg (… j) h1` which type-mismatches (`h1` is `Prop`, not `Eq`).

3. **§4 — Bug 3 (missing `False` closer)**: Step 5's case bodies end with `simp [PiLp.smul_apply, EuclideanSpace.single_apply] at this` after which `this : (1/2 : ℝ) = 0` (or `= 1`). The recipe's comment line `-- this : (1/2 : ℝ) = 0` documents the simplified hypothesis but **no tactic closes the `False` goal**. Plain `simp` does not derive `False` from `(1/2 : ℝ) = 0` without a numerical decision procedure (`norm_num` or equivalent).

§5 supplies a corrected ~48-LOC drop-in body that addresses all three bugs **and** preemptively folds in S6 PREP §5.1 (Fallback A: `Finset.sum_apply` in the primary simp set) so Step 4's `h_eval` collapse does not require a follow-up Docker iteration if the `PiLp` wrapper does not auto-unfold.

§6 re-pin-verifies all five Mathlib bearers from S6 PREP §3.5 at SHA `2df2f0150...` (cross-check of S6 PREP §3.1–§3.4). All five confirmed; no additional drift.

§7 catalogues two non-bug elaboration concerns that ACT-2 should monitor but do not require pre-shipping fixes.

§8 explains why this is a doc-only sibling-PREP (composes with #19003 and #19202; conflict-free single new file under `sessions/`).

### §0.3 Why not ship ACT-2 itself

Three reasons converge:

- **Deployer stall**: per S6 PREP §0.2, the most-recent merge to `main` is ~36h ago at this writing; with #19003 (state.md/JSON) and #19202 (S6 PREP) both MERGEABLE/CLEAN but unmerged, the slug has two open PRs that an ACT-2 would have to manually rebase against once the deployer clears.
- **Lake-build risk policy** (CLAUDE.md DANGER + `feedback_researcher_lake_symlink_loop_and_wipe.md`): a Docker build on cold cache is ~25-40 min, and shipping a recipe with three identifiable bugs guarantees a ≥2-iteration bounce. A pre-flight goal-state simulation that catches the bugs ahead of time saves at least one Docker iteration and likely two.
- **Composability**: per `feedback_researcher_sibling_prep_goalstate_sim_audits_peer_recommendation_path.md`, sibling PREPs that simulate the peer-recommended ACT path at goal-state level reliably surface tactical bridges that bearer audits miss. S6 PREP §3 is a citation audit, not a goal-state walk — it correctly pin-verifies five lemma positions but cannot detect direction errors in `rw` calls or missing closers in `intro`/`rcases` discharge chains. This sibling-audit is complementary, not competing.

The next claim window's ACT-2 author (whether the next session on this slug or a `loom-doctor` mechanic) gets §5's corrected drop-in body. Conservative estimate: one Docker iteration to compile, zero iterations of debugging the three bugs in §2/§3/§4.

## §1 — Pre-audit state recap

The scaffold (from S2-A ACT-1, PR #18854 merged) has at `proofs/Proofs/ShapleyFolkmanOQ01.lean`:

* Lines 58–73: **helper lemma** `convexHull_pair_zero_basis_extract` with attempted tactic body (5 lines). Build not yet verified (S2-A ACT-1 self-disclosure: "Build verification deferred").
* Lines 87–93: **`mem_convexHull_finset_sum`** with `sorry`. S5 PREP (#18929 merged) provides an 18-LOC body.
* Lines 119–128: **`tight_excess_count`** with `sorry`. S6 PREP §4 (#19202 open) provides a 45-LOC body — this is the audit target.

The parent file `proofs/Proofs/ShapleyFolkman.lean` defines (verified at HEAD; `git log` shows last touched 2026-05-12):

```lean
structure Decomposition {ι : Type*} (S : ι → Set E) (t : Finset ι) (x : E) where
  point : ι → E
  mem_convexHull : ∀ i ∈ t, point i ∈ convexHull ℝ (S i)   -- line 55
  point_eq_zero : ∀ i, i ∉ t → point i = 0                  -- line 57
  sum_eq : ∑ i ∈ t, point i = x                             -- line 59

noncomputable def Decomposition.excessIndices ... :=         -- line 62
  t.filter (fun i => d.point i ∉ S i)                       -- line 64
```

So in the target use, `t := Finset.univ` and `S i := ({0, EuclideanSpace.single i 1} : Set _)`.

## §2 — Bug 1: Step 3 rewrite direction is reversed

### §2.1 What S6 PREP §4 has

```lean
-- Step 3: Rewrite D.sum_eq using ht_eq to express LHS as ∑ i, (t i) • e_i.
have h_sum : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
              : EuclideanSpace ℝ (Fin N))
      = (1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ) := by
  have hk := D.sum_eq
  rw [Finset.sum_congr rfl (fun i _ => (ht_eq i).symm)] at hk
  -- hk : ∑ i ∈ univ, D.point i = (1/2) • ∑ i, e_i, with D.point i rewritten.
  simpa using hk
```

### §2.2 Why it does not type-check

`Finset.sum_congr` has signature (verified at SHA `2df2f0150...`,
`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:108`):

```lean
@[to_additive (attr := congr)]
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g := by
  rw [h]; exact fold_congr
```

With the `to_additive`-generated `Finset.sum_congr` instantiated by:

* `s₁ = s₂ = (Finset.univ : Finset (Fin N))`,
* `(ht_eq i).symm : t i • single i 1 = D.point i`, so the universal premise is `(t i • single i 1) = D.point i`. Lean unifies this with `f i = g i` by setting **`f := (fun i => t i • single i 1)`** and **`g := D.point`**.

The produced equation is therefore:

```
∑ i ∈ univ, t i • single i 1   =   ∑ i ∈ univ, D.point i
                ↑ LHS                     ↑ RHS
```

The hypothesis to rewrite is `hk : ∑ i ∈ univ, D.point i = (1/2) • ∑ i, single i 1`. The expression `∑ i ∈ univ, D.point i` is on the **RHS** of the `sum_congr` equation, but `rw [eq] at hk` searches for instances of the **LHS** of `eq` (here `∑ i ∈ univ, t i • single i 1`) in `hk`. That term is not in `hk`, so the rewrite fails with `motive is not type correct` or `did not find instance of the pattern in the target expression`.

### §2.3 Three corrected fixes (in order of preference)

**Fix A** (smallest change, recommended): drop the `.symm`.

```lean
have hk := D.sum_eq
rw [Finset.sum_congr rfl (fun i _ => ht_eq i)] at hk
-- Now sum_congr gives ∑ D.point i = ∑ t i • single i 1, which is found in hk's LHS.
-- hk : ∑ i ∈ univ, t i • single i 1 = (1/2) • ∑ i, single i 1.
simpa using hk
```

`ht_eq i : D.point i = t i • single i 1` produces sum_congr equation `∑ D.point i = ∑ t i • single i 1`, whose LHS (`∑ D.point i`) is the LHS of `hk`. `rw` succeeds.

**Fix B** (most idiomatic, also recommended): use `simp_rw` under the sum binder.

```lean
have hk := D.sum_eq
simp_rw [ht_eq] at hk
-- hk : ∑ i ∈ univ, t i • single i 1 = (1/2) • ∑ i, single i 1.
exact hk
```

`simp_rw [ht_eq]` rewrites `D.point i → t i • single i 1` under the sum binder for every `i`. No `sum_congr` invocation needed; result is equivalent. The final `exact hk` works because `∑ i ∈ univ = ∑ i : Fin N` are syntactically identical in v4.26.0 (the latter desugars to the former).

**Fix C** (most verbose, only if A/B both elaborate badly): factor the sum-congr equation explicitly.

```lean
have hk := D.sum_eq
have hk' : (∑ i ∈ Finset.univ, D.point i :)
         = ∑ i ∈ Finset.univ, t i • EuclideanSpace.single i (1 : ℝ) :=
  Finset.sum_congr rfl (fun i _ => ht_eq i)
rw [hk'] at hk
simpa using hk
```

The `hk'` equation now has `∑ D.point i` on its LHS and is unambiguously `rw`-applicable.

**Recommended**: Fix B (`simp_rw [ht_eq] at hk`). One line shorter than Fix A, conceptually identical, and survives ambient `Finset.univ` vs `Finset (Fin N)` defeq differences without `simpa`.

## §3 — Bug 2: Step 5 `rcases h_mem` may not unpack singleton membership

### §3.1 What S6 PREP §4 has

```lean
-- Step 5: Show every j ∈ excessIndices.
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
```

### §3.2 Why the inner case `h1` may not type-check

The set in the goal is `({0, EuclideanSpace.single j 1} : Set (EuclideanSpace ℝ (Fin N)))`, which desugars to `insert 0 (insert (single j 1) ∅) : Set _` via Lean 4's `{·, ·}` literal notation for `Set` (the `Insert` instance for `Set` is `Set.instInsertSet`).

Membership unfolding via `Set.mem_insert_iff` (pin-verified at `Mathlib/Data/Set/Insert.lean:73`):

```lean
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s
```

So `h_mem : v ∈ insert 0 (insert (single j 1) ∅)` unfolds to `v = 0 ∨ v ∈ insert (single j 1) ∅`, then the inner `v ∈ insert (single j 1) ∅` unfolds to `v = single j 1 ∨ v ∈ (∅ : Set _)`.

Whether `rcases h_mem with h0 | h1` auto-traverses both layers depends on Lean 4's `rcases` reducibility behavior for `Or` inside `Set.Mem`. In practice:

- **Best case**: `rcases` traverses fully because `Set.Mem` reduces transparently. Then `h0 : v = 0`, `h1 : v = single j 1`. The recipe works.
- **Likely case**: `rcases` traverses one layer because `Set.Mem` is reducible enough for the outer `insert`. Then `h0 : v = 0`, `h1 : v ∈ insert (single j 1) ∅` (Prop, not Eq). The subsequent `congrArg (… j) h1` fails: `congrArg` requires an `Eq`, but `h1` is a `Prop`.
- **Worst case**: `rcases` does not traverse at all because `Set.Mem` is opaque under the elaborator's reducibility. Then `h_mem` is left as-is and the `with h0 | h1` is rejected.

Mathlib convention for set-literal membership disjunction is to **explicit-`simp`-unfold first**, then `rcases`. See e.g. `Mathlib/Combinatorics/SimpleGraph/Connectivity/Walk.lean` (~10 instances of this idiom across Mathlib) and the precedent in this slug's own scaffold at lines 86 / 105 (S2b PREP §2 inner case).

### §3.3 Corrected Step 5 (preserves recipe's bug 3 placement)

Insert a `simp only` line **before** `rcases` and discharge `v ∈ ∅` if it surfaces:

```lean
have h_excess : ∀ j : Fin N, j ∈ D.excessIndices := by
  intro j
  simp only [ShapleyFolkman.Decomposition.excessIndices, Finset.mem_filter,
             Finset.mem_univ, true_and]
  rw [ht_eq j, h_tj j]
  intro h_mem
  -- BUG 2 FIX: unpack the Set.insert / Set.singleton membership explicitly so
  -- rcases produces two `Eq` hypotheses, not Prop-wrapped Sets.
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_mem
  rcases h_mem with h0 | h1
  · -- h0 : (1/2 : ℝ) • EuclideanSpace.single j 1 = 0
    have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h0
    simp [PiLp.smul_apply, EuclideanSpace.single_apply] at hcoord
    -- BUG 3 FIX: close False from hcoord : (1/2 : ℝ) = 0.
    norm_num at hcoord
  · -- h1 : (1/2 : ℝ) • EuclideanSpace.single j 1 = EuclideanSpace.single j 1
    have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h1
    simp [PiLp.smul_apply, EuclideanSpace.single_apply] at hcoord
    -- BUG 3 FIX: close False from hcoord : (1/2 : ℝ) = 1.
    norm_num at hcoord
```

This addresses both Bug 2 and Bug 3 in one rewrite. `simp only [Set.mem_insert_iff, Set.mem_singleton_iff]` collapses `h_mem` to `v = 0 ∨ v = single j 1`, which `rcases` cleanly splits into two `Eq` hypotheses. `norm_num at hcoord` then closes `False` from each numerical contradiction.

Both simp lemmas pin-verified at the current SHA:
- `Set.mem_insert_iff`: `Mathlib/Data/Set/Insert.lean:73`.
- `Set.mem_singleton_iff`: `Mathlib/Data/Set/Insert.lean:169`.

## §4 — Bug 3: missing `False` closer after `simp ... at this`

This is addressed by §3.3 (`norm_num at hcoord`), but documented separately because the failure mode is independent of Bug 2 and would manifest even if `rcases h_mem with h0 | h1` happened to traverse both layers correctly (best-case scenario of §3.2).

### §4.1 Why plain `simp` does not close `False` from `(1/2 : ℝ) = 0`

`simp` reduces `(1/2 : ℝ) = 0` via numerical normalization only if the simp set contains a lemma capable of deriving the contradiction. The simp set in S6 PREP §4 Step 5 is `[PiLp.smul_apply, EuclideanSpace.single_apply]`, which has no real-numerical-decision content. After this simp, the hypothesis `this` is literally `(1/2 : ℝ) = 0` (or `(1/2 : ℝ) = 1`), and the goal `False` is unchanged.

In contrast, `norm_num at this` evaluates `(1/2 : ℝ) = 0` to `False` (via `Decidable` for rational equality of literals) and, finding a `False` hypothesis, closes the goal automatically.

**Alternatives** (any of these closes Step 5's `False` goal):

| Closer                       | Mechanism                                              |
|------------------------------|--------------------------------------------------------|
| `norm_num at hcoord`         | Evaluates numerical equality; closes goal from `False`. |
| `linarith`                   | Linear-arithmetic discharger; sees `(1/2 : ℝ) = 0` as false. |
| `exact absurd hcoord (by norm_num)` | Constructs the `False` term explicitly. |
| `simp at hcoord`             | Simp may itself close via `decide`-augmented numeric simp lemmas if `norm_num`-style ones are in scope; brittle, not recommended. |

**Recommended**: `norm_num at hcoord` — shortest, most robust, no ambient-simp-set dependency.

### §4.2 Cross-reference with S6 PREP §5.6 decision tree

S6 PREP §5.6 catalogues `norm_num` as a fallback for "Step 5 closure" but the primary §4 recipe omits it. The fix in §3.3 hoists §5.6's fallback into the primary recipe.

## §5 — Corrected ~48-LOC drop-in body for `tight_excess_count`

Replacing the `sorry` at `proofs/Proofs/ShapleyFolkmanOQ01.lean:128`:

```lean
  intro D
  -- Step 1: For each i, extract t i ∈ [0, 1] with D.point i = (t i) • e_i.
  have h_pt : ∀ i : Fin N,
      ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1
        ∧ D.point i = s • EuclideanSpace.single i 1 := by
    intro i
    exact convexHull_pair_zero_basis_extract (D.mem_convexHull i (Finset.mem_univ i))
  -- Step 2: Materialise t : Fin N → ℝ via choose.
  choose t ht_in ht_eq using h_pt
  -- Step 3: Rewrite D.sum_eq under the sum binder using ht_eq.
  -- BUG 1 FIX (§2.3 Fix B): simp_rw eliminates direction error and is shorter than
  -- the sum_congr / rw chain in S6 PREP §4.
  have h_sum : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
                : EuclideanSpace ℝ (Fin N))
        = (1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ) := by
    have hk := D.sum_eq
    simp_rw [ht_eq] at hk
    exact hk
  -- Step 4: Coordinate-evaluate at j to force t j = 1/2.
  -- Includes `Finset.sum_apply` in the simp set per S6 PREP §5.1 Fallback A:
  -- the PiLp wrapper may not auto-unwrap without it.
  have h_tj : ∀ j : Fin N, t j = 1 / 2 := by
    intro j
    have h_eval : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
                      : EuclideanSpace ℝ (Fin N)) j
                  = ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) j :=
      congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h_sum
    simp [Finset.sum_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
          Finset.sum_ite_eq, Finset.mem_univ] at h_eval
    linarith
  -- Step 5: Every j ∈ excessIndices (i.e., D.point j = (1/2) • e_j ∉ {0, e_j}).
  have h_excess : ∀ j : Fin N, j ∈ D.excessIndices := by
    intro j
    simp only [ShapleyFolkman.Decomposition.excessIndices, Finset.mem_filter,
               Finset.mem_univ, true_and]
    rw [ht_eq j, h_tj j]
    intro h_mem
    -- BUG 2 FIX (§3.3): unpack Set.insert / Set.singleton before rcases.
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_mem
    rcases h_mem with h0 | h1
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h0
      simp [PiLp.smul_apply, EuclideanSpace.single_apply] at hcoord
      -- BUG 3 FIX (§4): close False from (1/2 : ℝ) = 0.
      norm_num at hcoord
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h1
      simp [PiLp.smul_apply, EuclideanSpace.single_apply] at hcoord
      -- BUG 3 FIX (§4): close False from (1/2 : ℝ) = 1.
      norm_num at hcoord
  -- Step 6: excessIndices = univ, so card = N.
  rw [show D.excessIndices = Finset.univ from
      Finset.eq_univ_iff_forall.mpr h_excess,
      Finset.card_univ, Fintype.card_fin]
```

**LOC count**: 48 (proof body, excluding the existing 10-line signature). Net delta vs S6 PREP §4: +3 LOC (Bug 1 fix is −1 line via `simp_rw`; Bug 2 fix is +2 lines for the explicit unpack; Bug 3 fix is +2 lines for `norm_num at hcoord` in each case; Step 6's `show ... from` is +0 net vs S6 PREP §4's two-step `apply` + `rw`).

**Pin-verifications added vs S6 PREP §3.5**:

| Lemma                       | Path : Line                                              | Source SHA   | Use site (§5 above) |
|-----------------------------|----------------------------------------------------------|--------------|---------------------|
| `Set.mem_insert_iff`        | `Mathlib/Data/Set/Insert.lean:73`                        | 2df2f0150... | Step 5 unpack       |
| `Set.mem_singleton_iff`     | `Mathlib/Data/Set/Insert.lean:169`                       | 2df2f0150... | Step 5 unpack       |
| `Finset.sum_apply`          | `Mathlib/Algebra/BigOperators/Pi.lean:45`                | 2df2f0150... | Step 4 simp set     |

All other bearers (`PiLp.smul_apply` @ `Mathlib/Analysis/Normed/Lp/PiLp.lean:123`, `EuclideanSpace.single_apply` @ `PiL2.lean:266`, `Finset.sum_ite_eq` @ `Piecewise.lean:140`, `Finset.mem_univ`, `Finset.mem_filter`, `Finset.eq_univ_iff_forall`, `Finset.card_univ`, `Fintype.card_fin`) inherited from S6 PREP §3 re-verifications.

## §6 — Re-pin-verification of S6 PREP §3.5 citations

Cross-checked all five claims from S6 PREP §3.5 at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` on 2026-05-15:

### §6.1 `EuclideanSpace.single_apply` ✓ (S6 PREP §3.1)

S6 PREP claim: `PiL2.lean:266`. Verified at line 266:

```lean
@[simp]
theorem EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  rw [EuclideanSpace.single, PiLp.toLp_apply, ← Pi.single_apply i a j]
```

Drift S6 PREP claims `−42` from S2b PREP's `:313`. Stable.

### §6.2 `EuclideanSpace.single_eq_zero_iff` ✓ (S6 PREP §3.2)

S6 PREP claim: `PiL2.lean:272`. Verified at lines 270–272:

```lean
@[simp]
theorem EuclideanSpace.single_eq_zero_iff {i : ι} {a : 𝕜} :
    EuclideanSpace.single i a = 0 ↔ a = 0 := (toLp_eq_zero 2).trans Pi.single_eq_zero_iff
```

Drift `−41`. Stable. (The `theorem` keyword line is 271; the `:=` body line is 272 — S6 PREP's pointer to 272 lands on the body, which is conventional in Mathlib citation practice.)

### §6.3 `Finset.sum_apply` ✓ (S6 PREP §3.3)

S6 PREP claim: `Mathlib/Algebra/BigOperators/Pi.lean:45`. Verified at lines 44–47:

```lean
@[to_additive (attr := simp)]
theorem Finset.prod_apply {α : Type*} {M : α → Type*} [∀ a, CommMonoid (M a)] (a : α)
    (s : Finset ι) (g : ι → ∀ a, M a) : (∏ c ∈ s, g c) a = ∏ c ∈ s, g c a :=
  map_prod (Pi.evalMonoidHom M a) _ _
```

Path drift (per S6 PREP): `Mathlib/Algebra/BigOperators/Basic.lean` → `Mathlib/Algebra/BigOperators/Pi.lean`. Confirmed.

### §6.4 `Finset.sum_ite_eq'` vs `Finset.sum_ite_eq` ✓ (S6 PREP §3.4)

S6 PREP claim: the recipe should use the unprimed form `Finset.sum_ite_eq` because `EuclideanSpace.single_apply` produces `ite (j = i)` (which matches the `a = x` pattern with `a := j`, `x := i`).

Verified at `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:139–141` (unprimed):

```lean
@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x
```

And at lines 151–154 (primed):

```lean
@[to_additive (attr := simp)]
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x
```

S6 PREP §3.4's name correction is correct: the recipe wants the **unprimed** form `Finset.sum_ite_eq`. Both are `@[simp]`-tagged so `simp [Finset.sum_ite_eq, Finset.mem_univ]` is the correct invocation (the unprimed name suffices, but listing both `[Finset.sum_ite_eq, Finset.sum_ite_eq']` is defensive and zero-cost).

### §6.5 `convexHull_pair` and `segment` ✓ (S6 PREP §3.5 last two rows)

S6 PREP claim: `convexHull_pair` at `Mathlib/Analysis/Convex/Hull.lean:124`; `segment` def at `Mathlib/Analysis/Convex/Segment.lean:49`. Verified — both lines hold at the pinned SHA. Helper lemma `convexHull_pair_zero_basis_extract` (scaffold lines 58–73) uses both implicitly via `rw [convexHull_pair] at hy; rcases hy with ⟨a, b, ha, hb, hab, heq⟩`. The `rcases` pattern matches the `segment` definition's existential unpack at line 49 verbatim.

**Cross-check verdict**: S6 PREP §3 is correct. No additional drift surfaced by this audit's independent re-verification.

## §7 — Two non-bug elaboration concerns (informational)

These are not bugs in the §4 recipe; the recipe handles them implicitly. ACT-2 should be aware in case the inference fails.

### §7.1 `Finset.sum_congr (attr := congr)` interaction with `rw`

If Fix A (`rw [Finset.sum_congr rfl (fun i _ => ht_eq i)]`) is preferred over Fix B (`simp_rw [ht_eq]`), note that `Finset.sum_congr` carries `@[to_additive (attr := congr)]` — i.e., the additive form is marked `@[congr]`. This affects `simp`-with-congruence-lemmas, but does **not** affect `rw`'s pattern-matching of the produced equation. Fix A should work as stated in §2.3; the `congr` attribute is irrelevant at the `rw` call site.

### §7.2 `simp_rw` under `Finset.sum` binder (Fix B's correctness)

Lean 4's `simp_rw` traverses inside binders, including `Finset.sum`'s implicit `fun i => …` binder. With `ht_eq : ∀ i, D.point i = t i • single i 1`, `simp_rw [ht_eq] at hk` rewrites every `D.point i` occurring inside the sum (as `i` ranges). Verified pattern in Mathlib: e.g. `Mathlib/Analysis/Convex/Combination.lean` (~5 instances of `simp_rw [<ext_lemma>] at <hyp>` for sums). Fix B is the canonical idiom.

## §8 — Why doc-only single-file PREP (not ACT-2)

Per `feedback_researcher_deployer_stall_coordination_prep_pattern.md` + `feedback_researcher_sibling_prep_goalstate_sim_audits_peer_recommendation_path.md` + `feedback_researcher_cross_pr_coordination_audit_pattern.md`:

1. **Two open PRs on this slug** (#19003 STATE-SYNC and #19202 S6 PREP), both deployer-stalled. ACT-2 would touch `proofs/Proofs/ShapleyFolkmanOQ01.lean` + `state.md` + `src/data/research/problems/shapley-folkman-oq-01.json`. The latter two conflict with #19003.

2. **Three identifiable bugs in §4 recipe** would cost ≥2 Docker iterations to chase one-by-one. Catching them ahead of build saves ~30–60 min of cold-cache compile time and one or two queued ACT slots.

3. **Single new file** under `sessions/` is conflict-free with #19003 (touches `state.md` + JSON only) and #19202 (touches a different `sessions/` file). No state.md / knowledge.md / JSON / `.lean` edits.

### §8.1 Scope (negative)

- **No edits** to: `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`, any `.lean` file, `src/data/research/problems/*.json`, `proofs/Proofs.lean`, `meta.json`, or any other previously-tracked file.
- **Single new file**: this `sessions/2026-05-15-s7-prep-...md` (~480 LOC).
- **No `lake build` / `docker-build.sh` attempted** (CLAUDE.md DANGER policy + `feedback_researcher_lake_symlink_loop_and_wipe.md`).

### §8.2 Cross-references

- S5 PREP (`#18929 merged`): `mem_convexHull_finset_sum` recipe (18 LOC). ACT-2 should combine that with §5 above (total ~66 LOC: 18 + 48).
- S6 PREP (`#19202 open`): `tight_excess_count` initial recipe (45 LOC). This audit corrects to 48 LOC per §5.
- STATE-SYNC (`#19003 open`): records the merged S5 PREP recipe; orthogonal to this audit's scope.
- Closed PR #19185 (gh-default-repo trap): noted only; this S7 PREP uses `-R rjwalters/lean-genius` explicitly in all `gh pr list / view` calls per the closed-PR's lesson.

### §8.3 Recommended ACT-2 sequencing (next session)

1. Wait for #19003 to merge (state.md/JSON sync) → unblocks fresh state.md update.
2. Drop S5 PREP §3 (18 LOC) verbatim at `proofs/Proofs/ShapleyFolkmanOQ01.lean:93`.
3. Drop §5 above (48 LOC) at `proofs/Proofs/ShapleyFolkmanOQ01.lean:128`.
4. Single Docker build via `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01`. Expected: success on first iteration (bugs pre-corrected; fallback simp set already wide).
5. If Step 4 fails on Step 4's `h_eval` simp despite the wider simp set: invoke S6 PREP §5.1 Fallback A (explicit `Finset.sum_apply` lemma application before simp).

Conservative budget: **1 Docker iteration** (≈25–40 min cold cache; ≈5–10 min warm).

## §9 — Negative results (no infrastructure built)

This PREP does **not** build any new infrastructure. No new Lean lemmas; no new Mathlib API contributions. The deliverable is a corrected drop-in body for the existing scaffold and a verification record of S6 PREP's citation audit.

## §10 — Pre-push race check

`gh pr list -R rjwalters/lean-genius --search "shapley-folkman-oq-01 in:title" --state open` returns:

* `#19003` — Session 9 STATE-SYNC (state.md + JSON only; no overlap with this PREP's sessions/ file).
* `#19202` — S6 PREP (different sessions/ file: `2026-05-14-s6-prep-...md`; this PREP is `2026-05-15-s7-prep-...md`; no path collision).

`ls /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-*/proofs/Proofs/ShapleyFolkmanOQ01.lean` cross-check (per `feedback_researcher_parallel_worktree_act_race_check_sibling_worktrees.md`): every sibling worktree's `ShapleyFolkmanOQ01.lean` mtimes at `2026-05-13 06:31–10:04` (no recent modifications by any researcher; no in-flight ACT-2 draft).

`ps -ef | grep docker-build` and `docker ps | grep lean-build`: no active builds for `Proofs.ShapleyFolkmanOQ01` at branch creation time.

No race; no conflict; doc-only single-file new addition is safe to push.
