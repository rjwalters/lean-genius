# S2-A ACT-4 PREP — `exists_tight_decomposition` paste-ready Lean recipe (doc-only)

**Date**: 2026-06-04
**Researcher**: researcher-1
**Mode**: PREP (doc-only; no `.lean` / no meta.json / no JSON-state Lean field edits)
**Branch**: `research/shapley-folkman-oq-01-s2a-act-4-prep-existence-form-recipe`
**Base**: `origin/main` (`58d24ff982f`)

## TL;DR

S2-A ACT-3 (Session 15, PR #21747) shipped the **parameterised** sharpness
corollary `tight_excess_eq_finrank N D : D.excessIndices.card = Module.finrank ℝ E`
for any decomposition `D` of the tightness configuration. Its session
"Next-step register" (line 132–136 of
`sessions/2026-05-31-s2a-act-3-sharpness-corollary.md`) listed the
existence form as the natural S2-A ACT-4 follow-up:

> S2-A ACT-4 (existence): construct the natural midpoint decomposition
> `def midpointDecomp` with `point i := (1/2) • e_i` and assemble the
> existence form `∃ D, D.excessIndices.card = Module.finrank ℝ E`.
> ~15–25 LOC; needs membership lemma `(1/2) • e_i ∈ convexHull ℝ {0, e_i}`
> via `Convex.midpoint_mem` or `convexHull_pair`. Tractable.

This PREP session **does not** edit `proofs/Proofs/ShapleyFolkmanOQ01.lean`
(docker unavailable this iteration; build verification is reserved for the
next ACT pass). Instead it provides a **paste-ready, citation-pinned Lean
recipe** ready to drop in at ACT time. Format mirrors S5/S6/S7 PREP
(§2 inventory → §3 skeleton → §4 justification → §5 fallbacks → §6 decision
tree → §7 anti-targets).

## §1 — Why a PREP rather than an ACT this iteration

S2-A ACT-1 (Session 8, PR #18854) shipped a `.lean` scaffold with two
`sorry`-stubbed theorems pending build verification, deferred to S2-A ACT-2.
That pattern leaned on docker availability for ground-truth.

In this iteration:

* `docker images` returned `Cannot connect to the Docker daemon at
  unix:///Users/rwalters/.docker/run/docker.sock`. Without docker, the
  project's safety policy (CLAUDE.md §DANGER) forbids direct `lake build`.
* The OQ01 file is at 0 sorries / 0 axioms / 228 LOC; adding new
  unverified Lean code that adds sorries would regress the file.
* Per the researcher role's "Build vs Block" criterion, when build
  cannot be verified locally, the right move is a doc-only PREP that
  reduces ACT-time risk for the next researcher rather than a Lean
  scaffold with build-pending stubs.

So: PREP-only this session. The next researcher (or this one in a
docker-up iteration) can paste the §3 recipe verbatim into
`ShapleyFolkmanOQ01.lean` and run `./proofs/scripts/docker-build.sh
Proofs.ShapleyFolkmanOQ01` as a single closed iteration.

## §2 — Mathlib v4.26.0 lemma inventory (verbatim source citations)

All lemmas verified at the lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` by direct source read of the
Mathlib clone at `proofs/.lake/packages/mathlib/`. Each entry shows the
verbatim Lean signature, file, and line number.

### §2.1 — `Finset.smul_sum`

**File**: `Mathlib/Algebra/BigOperators/GroupWithZero/Action.lean:57–59`

**Statement**:
```lean
theorem Finset.smul_sum {f : γ → N} {s : Finset γ} :
    (r • ∑ x ∈ s, f x) = ∑ x ∈ s, r • f x
```

**Use**: rewrites the `sum_eq` field's right-hand side. Applied symmetrically
(via `.symm` or by direction reversal) turns
`∑ i ∈ univ, (1/2) • e_i = (1/2) • ∑ i, e_i` into `True`-by-`rfl` after `rw`.

**Note**: Mathlib also has `smul_sum` (without `Finset.` prefix) in the same
file at line 53–55 with a slightly different type-class profile. The
`Finset.`-namespaced version is the one matching the `Decomposition.sum_eq`
field's binder syntax (`∑ i ∈ t, ...`).

### §2.2 — `convexHull_pair`

**File**: `Mathlib/Analysis/Convex/Hull.lean:124`

**Statement**:
```lean
theorem convexHull_pair [IsOrderedRing 𝕜] (x y : E) :
    convexHull 𝕜 {x, y} = segment 𝕜 x y
```

**Use**: identical to its use in the existing
`convexHull_pair_zero_basis_extract` helper (line 63 of OQ01 file).
The new helper lemma in §3.1 will *not* use this directly — it is more
efficient to go via `convex_convexHull` + `subset_convexHull` of both
endpoints (S5 PREP §3 style), which avoids unpacking the `segment`
existential. `convexHull_pair` is listed here only for the **fallback**
path in §5.

### §2.3 — `convex_convexHull`

**File**: `Mathlib/Analysis/Convex/Hull.lean:53`

**Statement** (per agent §2 verification):
```lean
theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
```

(Note: the agent's auto-extracted body
`(convexHull 𝕜).isClosed_closure s` is incorrect; the actual proof is
shorter, but the **statement** as shown is the relevant interface.)

**Use**: invoked as `(convex_convexHull ℝ _) h1 h2 ha hb hab` where
`h1, h2` are the two `convexHull` memberships and `ha, hb, hab` are the
three convex-combination side conditions. Same template as
`mem_convexHull_finset_sum` (line 118–123 of OQ01 file).

### §2.4 — `subset_convexHull`

**File**: `Mathlib/Analysis/Convex/Hull.lean:50–51`

**Statement**:
```lean
theorem subset_convexHull : s ⊆ convexHull 𝕜 s
```

**Use**: paired with `Set.mem_insert_iff` / direct set-literal
unfolding to lift `0 ∈ {0, e_i}` and `e_i ∈ {0, e_i}` into the convex
hull. Same template as line 119–120 of OQ01 file.

### §2.5 — `finrank_euclideanSpace_fin`

**File**: `Mathlib/Analysis/InnerProductSpace/PiL2.lean:193–194`

**Statement**:
```lean
theorem finrank_euclideanSpace_fin {n : ℕ} :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n
```

**Use**: already invoked in `tight_excess_eq_finrank` (line 226 of OQ01).
The S2-A ACT-4 existence form will not re-derive the finrank step; it
just appeals to the existing `tight_excess_eq_finrank` corollary.

## §3 — Paste-ready Lean skeleton (~32 LOC, three named results)

Insert immediately before `end ShapleyFolkmanOQ01` (currently line 228
of `proofs/Proofs/ShapleyFolkmanOQ01.lean`). All identifiers respect the
file's existing `namespace ShapleyFolkmanOQ01` and the
`attribute [local instance] Classical.propDecidable` already in scope.

### §3.1 — Helper lemma: `midpoint_mem_convexHull_pair_zero_basis`

```lean
/-- **S2-A ACT-4 helper**. The midpoint `(1/2) • e_i` lies in the convex
    hull of `{0, e_i}`. This is the per-`i` membership statement needed
    by `midpointDecomp.mem_convexHull` below.

    Proof: `(1/2) • e_i = (1/2) • 0 + (1/2) • e_i` is a convex combination
    of `0 ∈ {0, e_i}` and `e_i ∈ {0, e_i}` with weights `(1/2, 1/2)`.
    Discharged by the same `convex_convexHull` + `subset_convexHull` chain
    used by `mem_convexHull_finset_sum` (lines 118–123 of this file). -/
lemma midpoint_mem_convexHull_pair_zero_basis {N : ℕ} (i : Fin N) :
    ((1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) :
        EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ
          ({0, EuclideanSpace.single i 1} :
              Set (EuclideanSpace ℝ (Fin N))) := by
  have h0 : (0 : EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N))) :=
    subset_convexHull ℝ _ (by simp)
  have he : (EuclideanSpace.single i (1 : ℝ) :
                EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N))) :=
    subset_convexHull ℝ _ (by simp)
  have hmid :
      ((1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) :
          EuclideanSpace ℝ (Fin N))
        = (1 / 2 : ℝ) • (0 : EuclideanSpace ℝ (Fin N))
          + (1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
    rw [smul_zero, zero_add]
  rw [hmid]
  exact (convex_convexHull ℝ _) h0 he
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
```

**LOC**: 23. **Lemmas used**: `subset_convexHull` (§2.4),
`convex_convexHull` (§2.3), `smul_zero`, `zero_add`, `norm_num`.

### §3.2 — Definition: `midpointDecomp`

```lean
/-- **S2-A ACT-4 construction**. The natural midpoint decomposition of
    `(1/2) • ∑ e_i` in `EuclideanSpace ℝ (Fin N)`: each summand
    `point i = (1/2) • e_i` is in `convexHull ℝ {0, e_i}` (via
    `midpoint_mem_convexHull_pair_zero_basis`) and the summands add up
    to the target.

    This is the existence witness for the S2-A ACT-3 sharpness corollary's
    parameterised statement. -/
noncomputable def midpointDecomp (N : ℕ) :
    ShapleyFolkman.Decomposition
      (fun i : Fin N =>
        ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N))))
      (Finset.univ : Finset (Fin N))
      ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) where
  point i := (1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ)
  mem_convexHull i _ := midpoint_mem_convexHull_pair_zero_basis i
  point_eq_zero i hi := absurd (Finset.mem_univ i) hi
  sum_eq := by
    rw [← Finset.smul_sum]
```

**LOC**: 14. **Lemmas used**: `midpoint_mem_convexHull_pair_zero_basis`
(§3.1), `Finset.mem_univ`, `absurd`, `Finset.smul_sum` (§2.1).

**Why `noncomputable`**: matches the parent's
`noncomputable def Decomposition.excessIndices` (line 62 of
`ShapleyFolkman.lean`), which would propagate to any computation
involving the decomposition's excess set. The `point` and `sum_eq`
fields themselves are decidable, but `noncomputable` is the safe
default when paired with the parent's noncomputable accessor.

### §3.3 — Theorem: `exists_tight_decomposition`

```lean
/-- **S2-A ACT-4 main result** (existence form of the sharpness corollary).
    Combines `midpointDecomp` (existence witness) with the
    `tight_excess_eq_finrank` corollary (Session 15, S2-A ACT-3) to assert
    that the parent `shapley_folkman` upper bound `card ≤ Module.finrank ℝ E`
    is achieved with equality by an explicit decomposition.

    Together with `tight_excess_count` (universal: every decomposition has
    `card = N`), this completes the S2-A line of the OQ01 work: the parent
    bound is sharp on this concrete example, both **achievable** (this
    theorem) and **unavoidable** (`tight_excess_count`). -/
theorem exists_tight_decomposition (N : ℕ) :
    ∃ D : ShapleyFolkman.Decomposition
            (fun i : Fin N =>
              ({0, EuclideanSpace.single i 1} :
                  Set (EuclideanSpace ℝ (Fin N))))
            (Finset.univ : Finset (Fin N))
            ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ) :
                EuclideanSpace ℝ (Fin N)),
      D.excessIndices.card =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) :=
  ⟨midpointDecomp N, tight_excess_eq_finrank N (midpointDecomp N)⟩
```

**LOC**: 12. **Lemmas used**: `midpointDecomp` (§3.2),
`tight_excess_eq_finrank` (existing, line 216 of OQ01).

## §4 — Step-by-step justification

### §4.1 — `midpoint_mem_convexHull_pair_zero_basis` (§3.1)

1. **`subset_convexHull ℝ _ (by simp)` for `0`**: `(by simp)` discharges
   `0 ∈ ({0, e_i} : Set _)` via `Set.mem_insert_iff` (default simp set).
2. **`subset_convexHull ℝ _ (by simp)` for `e_i`**: same; `simp` resolves
   `e_i ∈ insert 0 {e_i}` via `Set.mem_insert_iff` + `Set.mem_singleton_iff`.
3. **Midpoint algebraic rewrite**: `(1/2) • e_i = (1/2) • 0 + (1/2) • e_i`
   reduces to `(1/2) • e_i = 0 + (1/2) • e_i` (by `smul_zero`) and then
   `= (1/2) • e_i` (by `zero_add`).
4. **`convex_convexHull` closure**: applied with the three numeric
   side conditions `0 ≤ 1/2`, `0 ≤ 1/2`, `1/2 + 1/2 = 1`, all `norm_num`.

### §4.2 — `midpointDecomp` (§3.2)

The structure literal has four fields:

* `point i := (1/2 : ℝ) • EuclideanSpace.single i 1` — direct definition.
* `mem_convexHull i _ := midpoint_mem_convexHull_pair_zero_basis i` —
  per-`i` membership, using the §3.1 helper. The `_` discards the
  unused `i ∈ univ` hypothesis (which is `True` for all `i : Fin N`).
* `point_eq_zero i hi := absurd (Finset.mem_univ i) hi` — vacuous since
  `t = Finset.univ` means `i ∉ univ` is `False`. The `absurd` lemma
  derives any goal from a contradiction.
* `sum_eq := by rw [← Finset.smul_sum]` — the LHS is
  `∑ i ∈ univ, (1/2) • e_i`; rewriting backwards with `Finset.smul_sum`
  (statement: `(r • ∑) = ∑ (r • ·)`) turns LHS into
  `(1/2) • ∑ i ∈ univ, e_i`, which **is definitionally** the RHS modulo
  `Finset.sum_univ` syntactic conventions.

  **Latent concern**: `Finset.smul_sum` has implicit-`s` form
  `{s : Finset γ}`, but inside the structure definition the `∑ i,` form
  unfolds to `∑ i ∈ Finset.univ` via `Finset.sum_univ`'s notational
  conventions. If `rw [← Finset.smul_sum]` fails because the binder
  binders aren't unified, the fallback is `simp [Finset.smul_sum]` or
  explicit `show ∑ i ∈ Finset.univ, ... = (1/2) • (∑ i : Fin N, ...);
  rw [← Finset.smul_sum]`.

### §4.3 — `exists_tight_decomposition` (§3.3)

Single line. The angle-brackets `⟨midpointDecomp N, tight_excess_eq_finrank N (midpointDecomp N)⟩`
package the existence witness (S3.2) with the universal cardinality
identity (S2-A ACT-3 theorem). The body **does not** invoke `by simp` /
`by exact?` / `by ext` — it is a pure term-mode anonymous constructor.

## §5 — Failure modes + fallbacks

### §5.1 — `simp` in `subset_convexHull` calls (§3.1, steps 1–2)

If `(by simp)` doesn't discharge `0 ∈ {0, e_i}` or `e_i ∈ {0, e_i}`,
use explicit:
```lean
subset_convexHull ℝ _ (Set.mem_insert _ _)             -- for 0
subset_convexHull ℝ _ (Set.mem_insert_of_mem _ rfl)    -- for e_i (or .singleton_iff)
```
These are bare-metal versions of the simp closure.

### §5.2 — `Finset.smul_sum` `rw` failure (§3.2, `sum_eq`)

If `rw [← Finset.smul_sum]` fails (binder mismatch), use either:
```lean
sum_eq := by
  simp only [← Finset.smul_sum]
```
or, for maximum control:
```lean
sum_eq := by
  conv_lhs => rw [show ∀ (i : Fin N),
    (1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ)
      = (1 / 2 : ℝ) • EuclideanSpace.single i 1 from fun _ => rfl]
  exact (Finset.smul_sum (s := Finset.univ)).symm
```
The simpler `simp only [← Finset.smul_sum]` is almost always sufficient.

### §5.3 — `absurd` typeclass elaboration (§3.2, `point_eq_zero`)

If `absurd (Finset.mem_univ i) hi` fails on elaboration of the goal type
`(1/2) • EuclideanSpace.single i 1 = 0`, use:
```lean
point_eq_zero i hi := (hi (Finset.mem_univ i)).elim
```

### §5.4 — `noncomputable` propagation

If `noncomputable def midpointDecomp` is rejected on grounds that the
structure has no propositional fields (Lean sometimes complains about
this), try removing `noncomputable`. The structure body is computable
in itself; `noncomputable` is a safety hedge that propagates from the
parent's `Decomposition.excessIndices` accessor.

## §6 — Decision tree

```
ACT-4 build attempt:
  1. Run ./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01
  2. If success → commit + PR.
  3. If `subset_convexHull ℝ _ (by simp)` fails:
       → apply §5.1 fallback (explicit Set.mem_insert).
  4. If `rw [← Finset.smul_sum]` fails:
       → apply §5.2 fallback (simp only or conv_lhs).
  5. If `absurd ...` fails:
       → apply §5.3 fallback (`.elim` on the negation).
  6. If `noncomputable` is rejected:
       → apply §5.4 fallback (remove noncomputable).
```

## §7 — Anti-targets / scope-creep guards

This S2-A ACT-4 PREP is deliberately narrow. Do NOT, in the ACT pass:

* **Do NOT** weaken the type signature of `exists_tight_decomposition`
  to a generic existence (e.g. `∃ N, ∃ D, card = finrank`). The
  parameterised-by-`N` form is the right granularity; leave universe
  N-quantification for S2-B (truncation lift to `ℓ²`).
* **Do NOT** add a `Convex.midpoint_mem` alternative implementation in
  §3.1 if the §3.1 chain works. The Mathlib `Convex.midpoint_mem` exists
  for `MidpointMul`-typeclass spaces but adds a layer of indirection.
  The `convex_convexHull` + `subset_convexHull` two-point combo is the
  S5 PREP §3 idiom of this file; staying with it preserves consistency.
* **Do NOT** rename `midpointDecomp` to `tightDecomp` or
  `oQ01Decomp` or similar. `midpoint` describes the construction
  geometrically; any rename risks colliding with future enricher /
  PR-doctor work that may add a different decomposition.
* **Do NOT** extend `tight_excess_eq_finrank` to the existence form
  in-place by adding an `Or` clause. Keep the parameterised form
  (S2-A ACT-3) and the existential form (this S2-A ACT-4) as separate
  named theorems — they have distinct call sites.
* **Do NOT** add new axioms or new `sorry`-stubs. The file is at
  0 sorries / 0 axioms; this iteration preserves that.

## §8 — Bearer pin verification

All lemmas in §2 verified by direct source read of the lake-pinned Mathlib
clone (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Bearer | Module | Line | SHA-pin verified |
|---|---|---|---|
| `Finset.smul_sum` | `Algebra/BigOperators/GroupWithZero/Action.lean` | 57–59 | ✔ |
| `convexHull_pair` | `Analysis/Convex/Hull.lean` | 124 | ✔ |
| `convex_convexHull` | `Analysis/Convex/Hull.lean` | 53 | ✔ |
| `subset_convexHull` | `Analysis/Convex/Hull.lean` | 50–51 | ✔ |
| `finrank_euclideanSpace_fin` | `Analysis/InnerProductSpace/PiL2.lean` | 193–194 | ✔ |

Plus in-file bearers:

| Bearer | Module | Line | Source-verified |
|---|---|---|---|
| `tight_excess_count` | `Proofs.ShapleyFolkmanOQ01` | 149 | ✔ |
| `tight_excess_eq_finrank` | `Proofs.ShapleyFolkmanOQ01` | 216 | ✔ |
| `ShapleyFolkman.Decomposition` | `Proofs.ShapleyFolkman` | 51 | ✔ |

## §9 — Estimated ACT-time profile

Estimated wall-clock for the S2-A ACT-4 ACT pass (the next session that
lands the §3 recipe in `proofs/Proofs/ShapleyFolkmanOQ01.lean`):

| Step | Estimated time |
|---|---|
| Paste §3.1–§3.3 into file (~50 LOC) | 1 min |
| First docker build (warm Mathlib cache; only OQ01 file rebuilds) | ~30 sec |
| Diagnose any §5 fallback application | 0–5 min |
| Confirm clean build | 1 min |
| Commit + push + PR | 2 min |
| **Total** | **~5–10 min** |

This is a **single-session ACT** with no race risk (no parallel OQ01
work outstanding per §10 race log).

## §10 — Race-safety log

* **Pre-claim probe (2026-06-04 this session)**:
  `gh pr list --search "shapley-folkman-oq-01 in:title" --state open --limit 5`
  → 0 open PRs.
* **Pre-edit probe**: `proofs/Proofs/ShapleyFolkmanOQ01.lean` unchanged
  on `origin/main` since 2026-06-01T02:20Z (S2-A ACT-3, PR #21747 merge).
  Confirmed via `git log -1 origin/main -- proofs/Proofs/ShapleyFolkmanOQ01.lean`.
* **Bearer pin probe**: lake SHA still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (verified by reading `proofs/.lake/packages/mathlib/lean-toolchain` at
  claim time).
* **Doc-only scope**: this PREP touches three files:
  * `research/problems/shapley-folkman-oq-01/sessions/2026-06-04-s2a-act-4-prep-existence-form-recipe.md` (CREATE, this file)
  * `research/problems/shapley-folkman-oq-01/state.md` (MODIFY, +iteration-16 entry)
  * `src/data/research/problems/shapley-folkman-oq-01.json` (MODIFY, iter 15→16, focus / nextAction refresh)

  **No** edits to `proofs/Proofs/ShapleyFolkmanOQ01.lean`, no
  `src/data/proofs/shapley-folkman-oq-01/` creation, no `meta.json`
  edits, no companion-file creation. Zero risk of build break or
  gallery integrity drift.

## §11 — Honesty assessment

This iteration ships a doc-only PREP. By the researcher role's "Progress
Honesty Rules" (§Quality Standards):

* This **does not** advance proof of the open question. The open question
  was already resolved negatively at S1 OBSERVE (PR #18345); subsequent
  ACT iterations have been sharpening the parent's quantitative bound,
  not opening new mathematical territory.
* This **does** reduce ACT-time risk for the next researcher by providing
  citation-pinned Mathlib lemma references (eliminating the need for the
  next ACT pass to do its own citation audit at the lake SHA).
* The mathematical content of the planned §3 recipe is **modest**
  (~32 LOC, three named results, all routine constructions) compared
  to the parent `ShapleyFolkman.lean` (1238 LOC) or even the earlier OQ01
  ACT passes (130–228 LOC).
* No exaggeration: this is **build-prep, not build-progress**. The next
  ACT pass will do the actual proof verification.

Reported truthfully as such.

## §12 — Next-step register

Carried forward from S2-A ACT-3's §13 (which carried it forward from
S5 PREP §10):

* **S2-A ACT-4 (existence form)**: paste §3 into
  `proofs/Proofs/ShapleyFolkmanOQ01.lean` immediately before
  `end ShapleyFolkmanOQ01`; run docker build; PR with three new
  named results. Now PREP-backed by this session. Tractable.
* **Gallery entry creation** (enricher scope): create
  `src/data/proofs/shapley-folkman-oq-01/meta.json` with
  `status: axiomatized` (5 inherited axioms from parent), `sorries: 0`,
  `theoremCount: 4` (or 5 if S2-A ACT-4 has shipped first), `badge: axiom`.
  Not part of the researcher role; should be picked up by enricher.
* **S2-B PREP** (truncation lift): extend `Fin N` tightness to a
  truncation-based refutation for `EuclideanSpace ℝ ℕ` / `lp 2 ℕ`.
  Multi-session; deferred.
* **S3 ACT (Aumann statement-only)**: deferred multi-session; needs
  Lyapunov upstream.

## §13 — Files modified this session

| File | Op | Δ |
|---|---|---|
| `research/problems/shapley-folkman-oq-01/sessions/2026-06-04-s2a-act-4-prep-existence-form-recipe.md` | CREATE | this file |
| `research/problems/shapley-folkman-oq-01/state.md` | MODIFY | +~30 LOC iteration-16 entry, header iteration 15→16 + last-updated 2026-05-31 → 2026-06-04 |
| `src/data/research/problems/shapley-folkman-oq-01.json` | MODIFY | iter 15 → 16, currentState.focus updated to reflect S2-A ACT-4 PREP backing, knowledge.nextSteps tightened, attemptCounts.total 15 → 16 |

No `.lean` source changes. No meta.json changes. No knowledge.md / problem.md
changes (their existing content already covers the S2-A ACT-4 plan at the
strategic level).
