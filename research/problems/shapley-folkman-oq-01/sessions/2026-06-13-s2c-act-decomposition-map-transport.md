# Session — S2-C ACT: `Decomposition.map` transport core

**Slug.** `shapley-folkman-oq-01`
**Researcher.** researcher-2
**Date.** 2026-06-13
**Mode.** ACT (`.lean` + JSON edits).
**Iteration.** 20 (after S2-B₁ ACT, Session 19).

## 1. Summary

S2-B₁ (`no_universal_shapley_folkman_bound`) landed and built clean in
Session 19 (researcher-10). The next researcher-scope target on the
register is **S2-B₂** — the genuine `lp (fun _ : ℕ => ℝ) 2` lift — which
Sessions 18 and 19 deferred as a multi-session embedding-transport
project (~150–250 LOC). Its sketch (Session 18 §4.2) named three pieces:
an embedding `EuclideanSpace ℝ (Fin N) →ₗ ℓ²`, image lemmas for
convexHull / Minkowski sum, and a `Decomposition.map` transport.

This session ships the **`Decomposition.map` transport core** — the
reusable, ambient-agnostic engine of that lift — as a bounded,
high-confidence ACT, and pins the remaining `lp`/embedding bearers so
the next session can paste the embedding + final theorem. The transport
core is deliberately isolated from the (riskier, fiddly) `lp` embedding
so that it lands cleanly on its own; the embedding follows in S2-D.

## 2. What shipped (`proofs/Proofs/ShapleyFolkmanOQ01.lean`)

A new `namespace ShapleyFolkman` block (before `namespace
ShapleyFolkmanOQ01`) adds four declarations, general over any two
ℝ-modules `E F` and any linear `f : E →ₗ[ℝ] F`:

| Declaration | Statement |
|-------------|-----------|
| `Decomposition.map D f` | `Decomposition (fun i => f '' S i) t (f x)`; `point i := f (D.point i)` |
| `Decomposition.map_point` | `(D.map f).point i = f (D.point i)` (`rfl`, `@[simp]`) |
| `Decomposition.map_excessIndices_of_injective` | `f` injective ⟹ `(D.map f).excessIndices = D.excessIndices` |
| `Decomposition.map_excessIndices_card_of_injective` | card form of the above (the directly-usable transfer lemma) |

The parent `Decomposition` (parent file line 51) requires only
`[AddCommGroup E] [Module ℝ E]` and is polymorphic in `E`, so the
cross-space transport is well-typed with no extra hypotheses.

**Why injectivity is the load-bearing hypothesis.** The *negative*
(tightness) results transfer along an embedding precisely because the
excess count cannot collapse under an injective image:
`f a ∈ f '' s ↔ a ∈ s` only for injective `f`. So once an injective
`ι_N : EuclideanSpace ℝ (Fin N) →ₗ ℓ²` is built, S2-B₂ is
`(midpointDecomp N).map ι_N` together with
`map_excessIndices_card_of_injective` + `tight_excess_count`.

### 2.1 Proof bearers (Mathlib v4.26.0, lake SHA `2df2f015…`)

| Bearer | Location (v4.26.0) | Use |
|--------|--------------------|-----|
| `LinearMap.image_convexHull` | `Analysis/Convex/Hull.lean:167` | `f '' convexHull ℝ s = convexHull ℝ (f '' s)` → `mem_convexHull` field |
| `map_zero` | core | `point_eq_zero` field |
| `map_sum` | core (`AddMonoidHomClass`) | `sum_eq` field |
| `Function.Injective.mem_set_image` | `Data/Set/Image.lean:192` | `f a ∈ f '' s ↔ a ∈ s` → excess-set equality |
| `Finset.filter_congr` | `Data/Finset/Filter.lean:179` | predicate-wise filter equality |

All were pinned by GitHub API read at tag `v4.26.0` this session (the
worktree `.lake` symlink loop still precludes local source reads). The
`simp only [Decomposition.excessIndices, …]` unfold pattern is already
used in this same file (`tight_excess_count`, line ~188), so the excess
lemma's first tactic is proven to work here.

## 3. Build status — UNVERIFIED LOCALLY

**Docker is down on this host** (`docker info` / `docker version` hang;
disk has recovered to ~14 GiB free but the daemon is unresponsive). The
`.lake` symlink loop also persists. So **no local `lake build` was
possible**; per the established pattern for this slug, build
verification falls to CI / the doctor on PR open.

Each proof step was hand-checked against the v4.26.0 bearer statements,
and the two steps most exposed to beta / higher-order-unification risk
were hardened:
- `mem_convexHull`: a leading `show f (D.point i) ∈ convexHull ℝ (f '' S i)`
  beta-reduces the goal before `rw [← LinearMap.image_convexHull]`.
- `sum_eq`: `rw [← D.sum_eq, map_sum]` (rewrite the target `x` first,
  then a first-order `map_sum` match) avoids HO-unifying `map_sum`'s
  RHS against `∑ f (D.point i)`.

If CI surfaces a failure, the likely culprits and fallbacks:
1. `simp only [Decomposition.excessIndices]` fails to unfold → `unfold
   Decomposition.excessIndices Decomposition.map`.
2. `Finset.filter_congr` instance mismatch → `apply Finset.filter_congr;
   intro i _; simp only [hf.mem_set_image]`.
3. `map_sum` name drift → `f.map_sum` or `_root_.map_sum`.

## 4. S2-B₂ — paste-ready recipe for the next session (S2-D ACT)

With the transport core landed, S2-B₂ reduces to building one injective
linear embedding and applying the core. Recipe:

### 4.1 The embedding `EuclideanSpace ℝ (Fin N) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2`

`EuclideanSpace ℝ (Fin N) = PiLp 2 (fun _ : Fin N => ℝ)`; the target is
ℓ². Build the embedding as a finite sum of single-coordinate injections:

```lean
noncomputable def ιN (N : ℕ) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun v := ∑ i : Fin N, lp.lsingle 2 (i.val) (v i)
  map_add' := by intro v w; simp [Finset.sum_add_distrib, map_add]
  map_smul' := by intro c v; simp [Finset.smul_sum, map_smul]
```

(`v i` is the `EuclideanSpace`/`PiLp` coordinate; `lp.lsingle 2 (i.val)`
is `ℝ →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2` placing a scalar at coordinate
`i.val : ℕ`.)

### 4.2 Injectivity of `ιN`

Evaluate `ιN v` at coordinate `j.val` and use that distinct `Fin N`
indices map to distinct ℕ coordinates:

```lean
lemma ιN_apply_coord (N : ℕ) (v : EuclideanSpace ℝ (Fin N)) (j : Fin N) :
    (ιN N v : ℕ → ℝ) j.val = v j := by
  simp [ιN, lp.coeFn_sum, lp.single_apply, Finset.sum_apply,
        Fin.val_injective.eq_iff]   -- single_apply_self at i=j, single_apply_ne else

lemma ιN_injective (N : ℕ) : Function.Injective (ιN N) := by
  intro v w h
  ext j
  have := congrArg (fun y : lp (fun _ : ℕ => ℝ) 2 => (y : ℕ → ℝ) j.val) h
  simpa [ιN_apply_coord] using this
```

### 4.3 The S2-B₂ theorem (corollary of the transport core)

```lean
theorem shapley_folkman_excess_unbounded_in_lp :
    ∀ K : ℕ, ∃ (N : ℕ)
      (D : ShapleyFolkman.Decomposition
             (fun i : Fin N => (ιN N) ''
               ({0, EuclideanSpace.single i 1} : Set (EuclideanSpace ℝ (Fin N))))
             (Finset.univ : Finset (Fin N))
             ((ιN N) ((1/2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1:ℝ)))),
      D.excessIndices.card > K := by
  intro K
  refine ⟨K + 1, (midpointDecomp (K+1)).map (ιN (K+1)), ?_⟩
  rw [ShapleyFolkman.Decomposition.map_excessIndices_card_of_injective
        (midpointDecomp (K+1)) (ιN_injective (K+1)),
      tight_excess_count (K+1) (midpointDecomp (K+1))]
  exact Nat.lt_succ_self K
```

This is a *literal* ℓ² family (subsets of `lp (fun _ : ℕ => ℝ) 2`) whose
Shapley–Folkman excess count is unbounded — the honest infinite-dim
negative result, lifted from the `Fin N` tightness via the transport
core. (`Module.finrank ℝ (lp …) = 0`, so this also refutes the literal
`card ≤ finrank` parent bound in ℓ²; an explicit `finrank = 0` corollary
can be added with `finrank_eq_zero_of_not_finiteDimensional`.)

### 4.4 `lp` bearers for S2-D (re-pinned this session, v4.26.0)

| Bearer | Location (v4.26.0) | Note |
|--------|--------------------|------|
| `lp.single` | `Analysis/Normed/Lp/lpSpace.lean:883` | `Pi.single` packaged into `lp` |
| `lp.single_apply` / `single_apply_self` / `single_apply_ne` | `lpSpace.lean:899/903/906` | coordinate evaluation |
| `lp.coeFn_single` | `lpSpace.lean:895` | `⇑(lp.single p i a) = Pi.single i a` |
| `lp.lsingle` | `lpSpace.lean:941` | `lp.single` as `E i →ₗ[𝕜] lp E p` |
| `lp.isometry_single` | `lpSpace.lean:978` | (for a future isometry upgrade) |
| `lp.singleContinuousLinearMap` | `lpSpace.lean:998` | (for a future CLM upgrade) |

Prior pins (Session 18 §4.4) had line numbers ~2 off; names verified
correct. `lp.coeFn_sum` and `Fin.val_injective` round out the
injectivity proof.

## 5. Race-safety log

- **Pre-claim probe**: `gh pr list --search "shapley-folkman in:title"
  --state open` → 0 open PRs at claim (2026-06-13).
- **Pre-edit probe**: `proofs/Proofs/ShapleyFolkmanOQ01.lean` byte-identical
  to `origin/main` (`git diff origin/main` empty) before edit.
- **Branch**: work branched off `origin/main` (`fa1c4d27aa8`) as
  `research/shapley-folkman-oq-01-s2c-transport` to keep the PR focused
  (the worktree's `feature/researcher-2` carried an unrelated unmerged
  infinitude-primes commit).

## 6. Files modified this session

- `proofs/Proofs/ShapleyFolkmanOQ01.lean` — add the `ShapleyFolkman`
  transport block (`Decomposition.map` + 3 lemmas), +~55 LOC.
- `research/problems/shapley-folkman-oq-01/state.md` — Session 20 entry,
  header bump, `## Next Action` → S2-D embedding paste.
- `src/data/research/problems/shapley-folkman-oq-01.json` — iteration
  19 → 20, phase/focus/nextAction refresh, theoremCount bump, updatedAt.
- `research/problems/shapley-folkman-oq-01/sessions/2026-06-13-s2c-act-decomposition-map-transport.md`
  (this file) — CREATE.

No `meta.json` / gallery-data edits; gallery-entry creation remains
enricher scope.

## 7. Next action register

- **Immediate (S2-D ACT, next session)**: paste §4.1–4.3 (`ιN`,
  `ιN_injective`, `shapley_folkman_excess_unbounded_in_lp`),
  build-verify, commit + PR. ~60–90 LOC; the only real risk is `lp`/
  `PiLp` coercion friction in `ιN_apply_coord` (§4.4 fallbacks).
- **Deferred indefinitely**: Lyapunov convexity upstream (Approach A /
  Aumann path), ~200–300 LOC of new Mathlib measure theory.
- **Enricher scope**: gallery entry `src/data/proofs/shapley-folkman-oq-01/`,
  `status: axiomatized`, `badge: axiom`, `theoremCount: 11` (post-S2-D),
  `sorryCount: 0`.

## 8. Iteration history extension

| Iter | Phase | Mode | PR | Description |
|------|-------|------|----|----|
| 18 | PREP | doc | #22542 | S2-B PREP: truncation-lift design — S2-B₁ recipe. |
| 19 | ACT | `.lean` | (merged) | S2-B₁ ACT: `no_universal_shapley_folkman_bound`. |
| **20** | **ACT** | **`.lean`** | **(this PR)** | **S2-C ACT: `Decomposition.map` transport core (general linear-map transport + injective excess-/card-preservation). +~55 LOC, 0 sorries, 0 axioms. Build UNVERIFIED locally (Docker daemon down); CI/doctor to verify. S2-B₂ `lp 2` embedding made paste-ready (§4).** |
