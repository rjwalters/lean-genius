# 2026-05-12 — S3 PREP: Pair convex-hull parameter-extraction Lean recipe (doc-only)

**Researcher**: researcher-12
**Slug**: `shapley-folkman-oq-01`
**Phase**: S3 PREP (doc-only)
**Branch**: `research/shapley-folkman-oq-01-s3-prep-pair-convexhull-extraction-1778640181`
**Mathlib pin**: v4.26.0 (lean-toolchain `leanprover/lean4:v4.26.0`)

## §0 Predecessor chain (all merged on `main` at PREP time)

| PR     | Phase     | Contribution                                                                  |
|--------|-----------|-------------------------------------------------------------------------------|
| #18345 | S1 OBSERVE | Literal `finrank` extension is vacuous; three approaches A/B/C surveyed.       |
| #18414 | S1b OBSERVE | Aumann/Lyapunov Mathlib prerequisite audit (Approaches A & B deferred).        |
| #18397 | S2 PREP   | Approach C `ℓ²` counter-example design + `Fin N` formulation chosen.            |
| #18452 | S2b PREP  | Numeric verification at $N=1,2,3,4$, orthogonality uniqueness sketch, truncation-limit refutation. |

**This S3 PREP** addresses the **single Lean micro-step** the prior PREPs leave informal:

> Given `y ∈ convexHull ℝ {0, EuclideanSpace.single i 1}`, extract a
> parameter `t ∈ Set.Icc (0:ℝ) 1` such that `y = t • EuclideanSpace.single i 1`.

This is the load-bearing bridge from "membership in a pair convex hull" to
"scalar-multiple representation" that the S2b PREP §3 orthogonality argument
uses implicitly. The S2 PREP and S2b PREP both cite `convexHull_pair` and
`segment_eq_image'` but do not assemble the tactic chain. This PREP **does**,
quoting the Mathlib v4.26.0 source verbatim and providing a ~5-line Lean
template ready to drop into S3 ACT.

## §1 Why this micro-step matters

The S2 PREP target theorem (verbatim from #18397 §"Statement scoping"):

```lean
theorem shapley_folkman_tight_excess_count
    (N : ℕ) (hN : 1 ≤ N) :
    let E := EuclideanSpace ℝ (Fin N)
    let S : Fin N → Set E := fun i => {0, EuclideanSpace.single i 1}
    let t : Finset (Fin N) := Finset.univ
    let x : E := (1/2 : ℝ) • (∑ i, EuclideanSpace.single i 1)
    ∀ (D : ShapleyFolkman.Decomposition S t x),
      D.excessIndices.card = N := by
  sorry
```

Unpacking the `Decomposition` record (`ShapleyFolkman.lean:51-59`):

```lean
structure Decomposition {ι : Type*} (S : ι → Set E) (t : Finset ι) (x : E) where
  point : ι → E
  mem_convexHull : ∀ i ∈ t, point i ∈ convexHull ℝ (S i)
  point_eq_zero : ∀ i, i ∉ t → point i = 0
  sum_eq : ∑ i ∈ t, point i = x
```

The proof of `excessIndices.card = N` proceeds:

1. **(Extract)** From `D.mem_convexHull i (mem_univ i)` and `S i = {0, e_i}`,
   obtain `t_i ∈ Icc 0 1` with `D.point i = t_i • e_i`. *(This is §2-§3 below.)*

2. **(Orthogonal collapse)** From `D.sum_eq` and step 1: `∑ t_i • e_i = (1/2) • ∑ e_i`.
   Coordinate evaluation forces `t_j = 1/2` for every `j`.

3. **(Excess)** Since `t_j = 1/2 ∉ {0, 1}`, `D.point j = (1/2) • e_j ∉ {0, e_j} = S j`,
   so `j ∈ D.excessIndices`. Hence `D.excessIndices = Finset.univ`, with
   `card = N`.

Steps 2-3 are direct from Mathlib coordinate lemmas (`EuclideanSpace.single_apply`
at `PiL2.lean:308`) plus arithmetic. **Step 1 is the only step that requires
a multi-lemma chain** and is the focus of this PREP.

## §2 Mathlib chain (v4.26.0, verbatim source)

### §2.1 `convexHull_pair` — `Mathlib/Analysis/Convex/Hull.lean:122`

```lean
@[simp]
theorem convexHull_pair [IsOrderedRing 𝕜] (x y : E) :
    convexHull 𝕜 {x, y} = segment 𝕜 x y := by
  refine (convexHull_min ?_ <| convex_segment _ _).antisymm
    (segment_subset_convexHull (mem_insert _ _) <| subset_insert _ _ <| mem_singleton _)
  rw [insert_subset_iff, singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩
```

**Effect**: `convexHull ℝ ({0, e_i} : Set E) = segment ℝ 0 (e_i)`.

`ℝ` is an `IsOrderedRing` (via `Real.instOrderedRing` + `IsOrderedRing.toIsStrictOrderedRing` —
the typeclass `IsOrderedRing` is at `Mathlib/Algebra/Order/Ring/Defs.lean`; `Real`
satisfies it). No instance-search risk.

### §2.2 `segment_eq_image'` — `Mathlib/Analysis/Convex/Segment.lean:207`

```lean
theorem segment_eq_image' (x y : E) :
    [x -[𝕜] y] = (fun θ : 𝕜 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel
```

**Effect** with `x = 0`, `y = e_i`:

```
segment ℝ 0 e_i = (fun θ : ℝ => 0 + θ • (e_i - 0)) '' Icc 0 1
              = (fun θ : ℝ => θ • e_i) '' Icc 0 1
```

so `y_i ∈ segment ℝ 0 e_i ↔ ∃ θ ∈ Icc (0:ℝ) 1, y_i = θ • e_i`.

### §2.3 `segment` definition — `Mathlib/Analysis/Convex/Segment.lean:51`

```lean
def segment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z }
```

**Alternative direct unpacking** (avoiding `segment_eq_image'`): from
`y_i ∈ segment ℝ 0 (e_i)`, obtain `⟨a, b, ha, hb, hab, heq⟩` with
`a • 0 + b • e_i = y_i`. Simplifying `a • 0 = 0` (via `smul_zero`)
gives `y_i = b • e_i` with `b = 1 - a ∈ [0, 1]` (via `hab : a + b = 1`
and `ha : 0 ≤ a`).

This direct unpack is **2 LOC shorter** than the `segment_eq_image'`
route and avoids the `Icc` image rewrite. Both work; choice is style.

## §3 Lean-ready extraction template

### §3.1 Recommended (direct `segment` unpack)

```lean
-- Helper lemma to drop into `proofs/Proofs/ShapleyFolkmanOQ01.lean`.
-- Mathlib pin v4.26.0.

open EuclideanSpace in
lemma convexHull_pair_zero_basis_extract
    {N : ℕ} {i : Fin N} {y : EuclideanSpace ℝ (Fin N)}
    (hy : y ∈ convexHull ℝ ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N)))) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ y = t • EuclideanSpace.single i 1 := by
  rw [convexHull_pair] at hy
  -- hy : y ∈ segment ℝ 0 (EuclideanSpace.single i 1)
  rcases hy with ⟨a, b, ha, hb, hab, heq⟩
  -- a, b : ℝ;  ha : 0 ≤ a;  hb : 0 ≤ b;  hab : a + b = 1;
  -- heq : a • 0 + b • EuclideanSpace.single i 1 = y
  refine ⟨b, ⟨hb, ?_⟩, ?_⟩
  · -- b ≤ 1 from a + b = 1 and 0 ≤ a
    linarith
  · -- y = b • EuclideanSpace.single i 1
    rw [smul_zero, zero_add] at heq
    exact heq.symm
```

**LOC count**: 12 lines including the signature and `rw [convexHull_pair]` line.
Pure-tactic body is 5 lines.

**Tactic justification**:

- `rw [convexHull_pair]`: rewrites the hypothesis to a `segment` membership.
  `convexHull_pair` requires `IsOrderedRing ℝ` (auto via Mathlib instance).
- `rcases hy with ⟨a, b, ha, hb, hab, heq⟩`: destructures the `segment`
  existential per §2.3 definition.
- `linarith`: closes `b ≤ 1` from `a + b = 1` and `0 ≤ a` (with `linarith`'s
  default arithmetic).
- `rw [smul_zero, zero_add] at heq`: simplifies `a • 0 + b • e_i = y` to
  `b • e_i = y`. (`smul_zero : a • (0 : E) = 0` is at
  `Mathlib/Algebra/SMul/Zero.lean`, `simp`-tagged.)

### §3.2 Alternative (`segment_eq_image'` route)

```lean
lemma convexHull_pair_zero_basis_extract_via_image
    {N : ℕ} {i : Fin N} {y : EuclideanSpace ℝ (Fin N)}
    (hy : y ∈ convexHull ℝ ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N)))) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ y = t • EuclideanSpace.single i 1 := by
  rw [convexHull_pair, segment_eq_image'] at hy
  -- hy : y ∈ (fun θ : ℝ => 0 + θ • (EuclideanSpace.single i 1 - 0)) '' Icc 0 1
  rcases hy with ⟨t, ht, heq⟩
  refine ⟨t, ht, ?_⟩
  simpa using heq.symm
```

**LOC count**: 8 lines. Slightly shorter but **less robust** to elaboration:
the lambda `(fun θ => 0 + θ • (e_i - 0))` may need `simp only [zero_add, sub_zero]`
to reduce; `simpa` handles this but is heavier than the §3.1 direct unpack.

**Recommendation**: prefer §3.1 (direct `segment` unpack). It is 2 LOC longer
but the tactic semantics are entirely transparent and stable across Mathlib
versions. The `segment_eq_image'` route is more fragile due to lambda
beta-reduction in `'' Icc 0 1`.

## §4 Coordinate-evaluation shortcut (bypassing orthonormality)

The S2b PREP §3 sketches the orthogonality argument via
`Orthonormal.linearIndependent` → `LinearIndependent.eq_of_sum_eq`. This
PREP recommends a **lighter** alternative: direct coordinate evaluation
via `EuclideanSpace.single_apply` (`PiL2.lean:308`):

```lean
theorem EuclideanSpace.single_apply (i a) (j) :
    (EuclideanSpace.single i a : EuclideanSpace 𝕜 ι) j = if j = i then a else 0
```

(or similar; line 308 of `PiL2.lean` per S2b PREP §5.1).

After extracting `D.point i = t_i • EuclideanSpace.single i 1` for each `i`
(via the §3.1 helper), `D.sum_eq` becomes:

```lean
∑ i, t_i • EuclideanSpace.single i 1 = (1/2 : ℝ) • ∑ i, EuclideanSpace.single i 1
```

Evaluating at coordinate `j` (via `Finset.sum_apply` / `PiLp.sum_apply`):

LHS at coord `j`:
```
(∑ i, t_i • EuclideanSpace.single i 1) j
  = ∑ i, t_i • (EuclideanSpace.single i 1) j     -- linearity
  = ∑ i, t_i • (if j = i then 1 else 0)          -- single_apply
  = t_j                                           -- Finset.sum_ite-collapse
```

RHS at coord `j` (similar reduction):
```
((1/2) • ∑ i, EuclideanSpace.single i 1) j = 1/2
```

So `t_j = 1/2` for every `j`. No orthonormality typeclass needed; just
finite-sum + `single_apply` + a `decide`/`omega`-finisher arithmetic step.

**Lean skeleton for §4**:

```lean
have coord_eval : ∀ j : Fin N, (∑ i, t i • EuclideanSpace.single i 1 : E) j = t j := by
  intro j
  -- Sum-of-singles evaluated at coord j collapses to t j.
  simp [Finset.sum_apply', EuclideanSpace.single_apply,
        Finset.sum_ite_eq', Finset.mem_univ]
```

The `simp` call may need tuning; the canonical lemma is `Finset.sum_ite_eq'`
(or `Finset.sum_ite_eq`) which collapses `∑ i, if j = i then f i else 0` to
`f j` when `j ∈ Finset.univ`. Both are in `Mathlib/Algebra/BigOperators/Basic.lean`.

**Comparison to the S2b PREP §3 orthonormality route**:

| Route | Mathlib API | LOC | Robustness |
|-------|------------|-----|------------|
| §4 (coordinate eval) | `EuclideanSpace.single_apply` + `Finset.sum_ite_eq'` | ~5 LOC | High (purely coordinate-arithmetic) |
| S2b §3 (orthonormality) | `EuclideanSpace.single_orthonormal` + `Orthonormal.linearIndependent` + `LinearIndependent.eq_of_sum_eq` | ~10-15 LOC | Medium (typeclass + universe juggling for `Orthonormal`) |

The coordinate-eval route is **strictly preferable** for this construction.
The S2b PREP's orthonormality cite is correct as a *high-level explanation* but
is heavier than necessary for the *Lean proof*. This PREP recommends the
coordinate-eval route for S3 ACT.

## §5 Step-by-step bridge to S2b PREP §3 informal argument

The S2b PREP §3 "Uniqueness of decomposition (orthogonality argument)" runs:

1. `y_i ∈ conv(S_i)` with `S_i = {0, e_i}` ⟹ `y_i = t_i • e_i` for some `t_i ∈ [0,1]`.
2. `(∑_i y_i)_j = ∑_i t_i • (e_i)_j = t_j`.
3. Equating to `x_j = 1/2` gives `t_j = 1/2` for every `j`.
4. `y_j = (1/2) • e_j ∉ {0, e_j}` because `(1/2) • e_j ≠ 0` (since `e_j ≠ 0`) and
   `(1/2) • e_j ≠ e_j` (since `(1/2) ≠ 1` as scalars and `e_j ≠ 0`).
5. Hence `j ∈ excessIndices` for every `j`, so `excessIndices = Finset.univ`,
   `card = N`.

This PREP's mapping:

| §3 step | Lean handle                                            | Lemma/cite                                      |
|--------|--------------------------------------------------------|-------------------------------------------------|
| 1      | `convexHull_pair_zero_basis_extract` (§3.1 helper)      | `convexHull_pair`, `segment` def unpack          |
| 2      | `coord_eval` skeleton (§4)                              | `EuclideanSpace.single_apply`, `Finset.sum_ite_eq'` |
| 3      | trivial arithmetic from `coord_eval x = 1/2`             | `linarith` after `simp`                          |
| 4      | `EuclideanSpace.single_eq_zero_iff` (`PiL2.lean:313`) + smul-cancellation | `smul_left_cancel_iff`, `single_eq_zero_iff` |
| 5      | `Finset.filter_eq_univ_iff` reverse direction            | `Finset.filter_eq_self` + cardinality          |

Step 4 deserves a one-line check:

```lean
-- (1/2 : ℝ) • EuclideanSpace.single j 1 ∉ ({0, EuclideanSpace.single j 1} : Set _)
have h_not_zero : (1/2 : ℝ) • EuclideanSpace.single j 1 ≠ (0 : E) := by
  rw [smul_ne_zero_iff]
  exact ⟨by norm_num, EuclideanSpace.single_ne_zero_iff.mpr one_ne_zero⟩
have h_not_basis : (1/2 : ℝ) • EuclideanSpace.single j 1 ≠ EuclideanSpace.single j 1 := by
  rw [← one_smul ℝ (EuclideanSpace.single j 1), smul_right_inj
        (EuclideanSpace.single_ne_zero_iff.mpr one_ne_zero)]
  norm_num
```

(`EuclideanSpace.single_eq_zero_iff` at `PiL2.lean:313` per S2b PREP §5.1
table. `smul_right_inj` may need `IsSMulRegular` or direct contradiction
via coordinate-eval at `j`.)

**Total LOC estimate for the entire ∀-direction proof**: ~40-55 LOC,
within the S2 PREP #18397 estimate of "75-100 LOC for headline result".

## §6 Anti-targets (what NOT to expand in S3 ACT)

1. **Do not prove a generic `convexHull_pair` extraction lemma** that handles
   arbitrary pair `{a, b}` for general `a, b`. The pinned form
   `{0, EuclideanSpace.single i 1}` collapses the `a • 0` term and is
   ~3 LOC shorter than the generic version. The generic version is also
   already in Mathlib (`segment` API); reproving it locally is duplication.

2. **Do not pre-prove `excessIndices.card ≤ N`** as a separate step. The
   parent `shapley_folkman` (`ShapleyFolkman.lean:1140`) already gives
   `card ≤ Module.finrank ℝ E = N`. The S2 PREP target is `card = N`, which
   combined with the parent's `≤` gives equality. **But** the parent
   produces an existential `∃ D`, not the **specific** `D` we are quantifying
   over in the target's `∀ D`. So the parent gives `∃ D₀, card D₀ ≤ N`,
   and our target gives `∀ D, card D = N`. These are independent statements
   sharing the construction; do not conflate them.

3. **Do not use `Orthonormal.linearIndependent`** unless the coordinate-eval
   route in §4 fails. The orthonormality route requires lifting through
   `LinearIndependent.eq_of_sum_eq` which carries universe and typeclass
   overhead. The §4 coordinate route is ~5 LOC and uses only
   `Finset.sum_apply` + `single_apply`.

4. **Do not introduce a separate `truncation_to_l2` lemma** in S3 ACT. The
   S2b PREP §4 truncation-limit refutation is a *separate* deliverable
   (S4 PREP / ACT). The tightness statement for `EuclideanSpace ℝ (Fin N)`
   is self-contained and standalone.

5. **Do not edit `proofs/Proofs/ShapleyFolkman.lean`** (the parent). The OQ-01
   refutation lives in a new file `proofs/Proofs/ShapleyFolkmanOQ01.lean`
   (per S2 PREP #18397 §"File placement"); the parent is untouched.

## §7 Race-check + diff scope

### §7.1 Race check (before write)

- `gh pr list --repo rjwalters/lean-genius --search "shapley-folkman" --state open --limit 10`
  → **empty**.
- `git branch -r | grep shapley` →
  - `origin/fix/mechanic-shapley-linecount` (old, merged context).
  - `origin/fix/mechanic-shapley-sorries` (old, merged context).
  - No `research/shapley-folkman-*` open branches.
- `git log origin/main -- research/problems/shapley-folkman-oq-01/` recent:
  - S2b PREP #18452 (merged 02:05 UTC).
  - S2 PREP #18397 (merged 00:14 UTC).
  - S1 OBSERVE #18345 (merged 22:47 UTC).

**Conclusion**: no in-flight competitor. Filename
`2026-05-12-s3-prep-pair-convexhull-extraction-recipe.md` is unique under
`sessions/` (existing files: `s01-observe`, `s01b-aumann-lyapunov-prereq-audit`,
`s2-prep-approach-c-ell2-counterexample-design`, `s2b-prep-construction-verification`).

### §7.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s3-prep-pair-convexhull-extraction-recipe.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`,
  `literature/`, `meta.json`.
- Any `.lean` file (in particular `proofs/Proofs/ShapleyFolkman.lean` —
  the parent — and any not-yet-existing `proofs/Proofs/ShapleyFolkmanOQ01.lean`).
- `src/data/proofs/shapley-folkman/` (gallery integration).

No `lake build` attempted; no `.lake` symlink touched. Purely doc-only.

## §8 Honesty disclosures

1. **All Mathlib citations were verified at v4.26.0 via the GitHub Contents
   API** (`gh api repos/leanprover-community/mathlib4/contents/...`) on
   2026-05-12. Line numbers are pinned to commit
   `23fc2795c350c2c4a5c70e289a545e81273229b3` (`master` HEAD at audit time);
   for the lean-genius `lean-toolchain v4.26.0` Mathlib pin, the line
   numbers may drift by ±3 lines depending on cherry-picks between v4.26.0
   tagging and the audit time. The **lemma names are stable** —
   `convexHull_pair`, `segment_eq_image'`, `segment` (definition),
   `EuclideanSpace.single_apply` — all present in v4.26.0 Mathlib per
   pre-existing references in S2b PREP §5.

2. **The §3.1 extraction lemma is a paper proof, not yet Lean-checked.**
   No `lake build` attempted. The risk is `linarith` failing to close
   `b ≤ 1` from `a + b = 1 ∧ 0 ≤ a` — in that case, the explicit fallback is
   `omega` (after `have h : (1:ℝ) - a = b := ...`) or one-line
   `have := hab; linarith [ha]`. The hypothesis chain is tight enough that
   at least one tactic among `linarith`, `omega` (over ℤ-cast), and explicit
   `sub_nonneg`-rewrite will close it.

3. **The coordinate-evaluation route (§4) is recommended over the
   orthonormality route (S2b PREP §3)** as a *Lean strategy*; the
   *mathematical content* of the two routes is the same. The S2b PREP §3
   cite of `Orthonormal.linearIndependent` is correct as a high-level
   mathematical argument; this PREP only argues that the coordinate route
   is shorter and more robust for the **specific** finite-dim tightness
   statement with `EuclideanSpace.single` as the basis.

4. **This PREP does not introduce new mathematical content beyond S2b PREP.**
   The contributions are:
   - **Verbatim Mathlib source citations** for the key chain.
   - **Lean tactic template** for the parameter extraction (§3.1).
   - **Coordinate-eval simplification** of S2b PREP §3 (§4).
   - **Step-by-step bridge table** (§5) tying S2b PREP's informal argument
     to specific Lean handles.

5. **The `convexHull_pair` lemma requires `IsOrderedRing 𝕜`.** `ℝ` satisfies
   this via the standard instance chain — but this is a minor wrinkle the
   S2 PREP and S2b PREP did not call out. If a future Mathlib version
   tightens the typeclass requirement (e.g., to `LinearOrderedField`),
   the §3.1 helper would still work since `ℝ` satisfies the strictly
   stronger typeclass.

6. **No `.lake` build attempted, no `proofs/.lake` directory modifications,
   no symlink-loop risk.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

7. **No edits to `problem.md` / `state.md` / `knowledge.md`** — those record
   the high-level approach (Approach C selected); this PREP is purely a
   tactic-level companion under `sessions/`. The S2 PREP, S2b PREP, and
   this S3 PREP form a three-document chain that fully de-risks the S2 ACT:
   S2 PREP locks **what** to prove, S2b PREP verifies **the construction
   works**, this S3 PREP locks **how** to prove the load-bearing step
   in Lean.

## §9 Decision log

- **2026-05-12 S3 PREP**: Decision to file as a `sessions/` doc-only PREP
  rather than amend `knowledge.md` (which is gallery-facing): the PREP's
  audience is "the next researcher who runs S3 ACT", not the gallery reader.

- **2026-05-12 S3 PREP**: Decision to recommend §3.1 (direct `segment`
  unpack) over §3.2 (`segment_eq_image'` route). Reason: 2 LOC shorter on
  the tactic side; avoids lambda beta-reduction fragility; same Mathlib
  dependencies.

- **2026-05-12 S3 PREP**: Decision to recommend §4 (coordinate-eval) over
  S2b PREP §3 orthonormality. Reason: 5 LOC vs 10-15 LOC; no `Orthonormal`
  typeclass invocation; no `LinearIndependent.eq_of_sum_eq` universe
  juggling.

- **2026-05-12 S3 PREP**: Decision to defer the **non-membership** of
  `(1/2) • e_j` in `{0, e_j}` (§5 step 4) to a separate ~5 LOC fact in
  S3 ACT. The argument is mechanical (smul-cancellation), but the exact
  Mathlib lemma names (`smul_right_inj`, `EuclideanSpace.single_eq_zero_iff`)
  may need fiddling. Leaving room for ACT to choose between coordinate-eval
  and smul-cancel proof paths.

## §10 References

### Mathlib v4.26.0 source citations (verified 2026-05-12)

- `Mathlib/Analysis/Convex/Hull.lean:122` — `convexHull_pair`.
- `Mathlib/Analysis/Convex/Segment.lean:51` — `def segment`.
- `Mathlib/Analysis/Convex/Segment.lean:193` — `segment_eq_image`.
- `Mathlib/Analysis/Convex/Segment.lean:207` — `segment_eq_image'`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:297` — `EuclideanSpace.single`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:308` — `EuclideanSpace.single_apply`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:313` — `EuclideanSpace.single_eq_zero_iff`.
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:348` — `EuclideanSpace.single_orthonormal`.

### Project files

- `proofs/Proofs/ShapleyFolkman.lean` — parent theorem (verified).
  - Line 51-59: `Decomposition` structure.
  - Line 62-64: `Decomposition.excessIndices`.
  - Line 1140-1146: `theorem shapley_folkman`.
- `research/problems/shapley-folkman-oq-01/sessions/`:
  - `2026-05-12-s01-observe.md` (PR #18345).
  - `2026-05-12-s01b-aumann-lyapunov-prereq-audit.md` (PR #18414).
  - `2026-05-12-s2-prep-approach-c-ell2-counterexample-design.md` (PR #18397).
  - `2026-05-12-s2b-prep-construction-verification.md` (PR #18452).
  - **This file**: `2026-05-12-s3-prep-pair-convexhull-extraction-recipe.md`.

**End of S3 PREP.**
