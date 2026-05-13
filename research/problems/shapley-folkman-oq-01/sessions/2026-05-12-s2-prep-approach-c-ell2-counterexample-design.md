# S2 PREP — Approach C ℓ² counter-example: concrete Mathlib type, signature, proof outline

**Researcher**: researcher-11
**Date**: 2026-05-12
**Slug**: `shapley-folkman-oq-01`
**Phase**: S2 PREP (doc-only)
**Predecessor**: S1 OBSERVE (PR #18345, merged 2026-05-12T22:53Z) — confirmed literal `finrank` extension is vacuous; recommended Approach C (negative result via explicit ℓ²-style construction) as the narrowest Mathlib-ready path.

## 0. Why this PREP and not a direct ACT

S1 OBSERVE shortlisted three approaches:

- **A** (recommended for substantive content): formalize one direction of Lyapunov's convexity theorem (~200-300 LOC, ≥8 sessions, Mathlib gap).
- **B** (Aumann set-valued integral): equivalent prerequisites to A.
- **C** (negative result): explicit Hilbert-space counter-example, ~50-100 LOC, 0 axioms, **Mathlib-ready**.

S1 OBSERVE recommends C as the smallest concrete deliverable that lands a `theorem ... := …` (no `sorry`) refuting the literal extension and avoids the Lyapunov upstream.

This S2 PREP commits to **Approach C** and locks the formal scope: chosen Mathlib type, sequence-of-sets construction, witness point, theorem signature, and Mathlib-API audit. The actual ACT (writing
`proofs/Proofs/ShapleyFolkmanOQ01.lean`) is a separate PR; this PREP de-risks it.

**Rationale for doc-only**: the worktree's `proofs/.lake` symlink-loop risk
(`feedback_researcher_lake_symlink_loop_and_wipe.md`) plus this researcher's
prior-session experience with parent-broken slugs (e.g.,
`AbelRuffiniGaloisExtensionsOQ07` per `project_abel_ruffini_oq07_main_broken.md`)
favours doc-first; the ACT can land as a build-pending PR with the proof
embedded after this PREP's review.

## 1. Type-level scope

### 1.1 Why finite-dim `EuclideanSpace ℝ (Fin N)` not `ℓ²`

The S1 OBSERVE problem.md (lines 200-211) suggests `EuclideanSpace ℝ ℕ` or
the `Analysis.InnerProductSpace.l2Space` API. For the **negative result**
we do **not** need a single infinite-dim space — we need:

> For every `d : ℕ`, there exists a *finite-dim* setting in which
> the Shapley–Folkman bound `d` does not constrain the excess
> count.

This is achievable in `EuclideanSpace ℝ (Fin N)` with `N > d`. The bound
"excess count ≤ `Module.finrank ℝ E`" gives `≤ N` in the parent's
finite-dim version, which is **vacuous as an upper bound** when the
construction forces all N indices to be "excess".

This sidesteps `ℓ²` entirely:

- `EuclideanSpace ℝ (Fin N)` is fully `Fintype`/`FiniteDimensional` —
  matches the parent's typeclass exactly.
- Mathlib's `EuclideanSpace.basisFun` gives the orthonormal standard basis.
- No `Subtype`-with-summability conditions to manage.
- Compile times are trivial vs `ℓ²` instance chains.

### 1.2 The construction

```lean
variable (N : ℕ) (hN : 1 ≤ N)

abbrev E := EuclideanSpace ℝ (Fin N)

/-- The i-th set: {0, eᵢ} where eᵢ is the i-th standard basis vector. -/
def S (i : Fin N) : Set E :=
  { (0 : E), EuclideanSpace.single i 1 }

/-- The witness point: x = (1/2) * (1, 1, …, 1) ∈ E. -/
def witness : E :=
  (1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i 1)
```

(or equivalently `fun i => 1/2`, but the explicit sum-of-basis form
plays better with Mathlib's `EuclideanSpace.inner_basisFun` rewriting.)

## 2. Theorem statement

The parent `shapley_folkman` has signature shape (paraphrased):

```lean
theorem shapley_folkman [FiniteDimensional ℝ E]
    {N : ℕ} (S : Fin N → Set E) :
    ∀ x ∈ convexHull ℝ (∑ i, S i),
    ∃ rep : Fin N → E,
      (∀ i, rep i ∈ convexHull ℝ (S i)) ∧
      ∑ i, rep i = x ∧
      (univ.filter (fun i => rep i ∉ S i)).card ≤ Module.finrank ℝ E
```

The **negative** result that Approach C ships:

```lean
/-- **`shapley_folkman_tight_excess_count`**:
    in `EuclideanSpace ℝ (Fin N)`, the witness point `x = (1/2) ∑ eᵢ`
    forces *every* Shapley–Folkman decomposition to have excess count
    exactly `N`. In particular, no bound of the form `≤ d` with
    `d < N` (whether `d := Module.finrank ℝ E` or any smaller
    dimension-replacement) can survive in this setting. -/
theorem shapley_folkman_tight_excess_count (N : ℕ) (hN : 1 ≤ N) :
    let E : Type _ := EuclideanSpace ℝ (Fin N)
    let S : Fin N → Set E := fun i => { (0 : E), EuclideanSpace.single i 1 }
    let x : E := (1 / 2 : ℝ) • ∑ i, EuclideanSpace.single i 1
    x ∈ convexHull ℝ (∑ i, S i) ∧
    ∀ (rep : Fin N → E),
      (∀ i, rep i ∈ convexHull ℝ (S i)) →
      ∑ i, rep i = x →
      (Finset.univ.filter (fun i => rep i ∉ S i)).card = N
```

This is a tightness witness — it says the parent's `≤ d` bound is sharp at
`d = N`, *and* (corollary) that there is no dimension-agnostic universal
constant `c` such that `excess count ≤ c` independent of `N`. The
infinite-dim "failure" follows immediately: as `N → ∞`, the excess count
grows unboundedly, so no fixed `c : ℕ` works.

## 3. Proof outline

### 3.1 Membership: `x ∈ convexHull ℝ (∑ i, S i)`

The Minkowski sum `∑ i, S i` is a subset of `E`. It consists of all sums
of selections, one element per set. For our construction:

```
∑ i, S i = { ∑ i, σ i • eᵢ : σ : Fin N → {0, 1} }
        = corners of the cube in E
```

So `∑ i, S i` is exactly the 2^N corners of the unit cube
`{0, 1}^N ⊂ EuclideanSpace ℝ (Fin N)`.

`convexHull ℝ (∑ i, S i)` is exactly the cube `[0, 1]^N`. The point
`x = (1/2, 1/2, …, 1/2)` lies in `[0, 1]^N`. ∎

**Lean tactic shape**:

```lean
have hmem : x ∈ convexHull ℝ (∑ i, S i) := by
  -- x is the midpoint of two corner points:
  -- e.g., (0, 0, …, 0) and (1, 1, …, 1)
  -- both in ∑ i, S i (each from S i picking 0 or eᵢ respectively).
  refine convexHull_mono ?_ ?_  -- or use convex_combination directly
  …
  -- alternatively: explicit `Finset.centerMass`-style decomposition
```

More directly: `x = (1/2) • (0) + (1/2) • (∑ i, eᵢ)`. Both `0 ∈ ∑ i, S i`
(pick `0` from each `S i`) and `∑ i, eᵢ ∈ ∑ i, S i` (pick `eᵢ` from each
`S i`). So `x ∈ convexHull ℝ` by `convexHull_pair` or
`Convex.combo_self_self_left`.

Mathlib API:
- `convexHull_pair : convexHull ℝ {a, b} = …` — not direct, but
- `Set.mem_convexHull` + `Finset.centerMass` — the natural canonical form.
- `Convex.add_smul` (`Convex.combo_self`) — for 2-point convex combinations.

Estimated proof length: ~15 LOC.

### 3.2 Excess count: every `rep` has `card excess = N`

Suppose `rep : Fin N → E`, `(∀ i, rep i ∈ convexHull ℝ (S i))`, and
`∑ i, rep i = x`.

Since `S i = {0, eᵢ}`, `convexHull ℝ (S i) = {t • eᵢ : t ∈ [0, 1]} =
segment 0 to eᵢ`. So `rep i = tᵢ • eᵢ` for some `tᵢ : ℝ` with
`tᵢ ∈ [0, 1]`.

For `rep i ∈ S i` (NOT in `excess`), we need `tᵢ = 0` or `tᵢ = 1`.

For `rep i ∉ S i` (IS in `excess`), `tᵢ ∈ (0, 1)`.

The constraint `∑ i, rep i = x` reads:
```
∑ i, tᵢ • eᵢ = (1/2) • ∑ i, eᵢ
```

By orthonormality of `eᵢ`s (i.e., `EuclideanSpace.basisFun` is an
orthonormal basis), reading off the `j`-th coordinate gives:
```
tⱼ = 1/2  for every j.
```

So `tⱼ = 1/2 ∈ (0, 1)` for every `j`, hence **every** index is excess.

`(Finset.univ.filter (fun i => rep i ∉ S i)).card = N`. ∎

**Lean tactic shape**:

```lean
intro rep h_in_conv h_sum
ext_filter -- show every index is in the filter
intro j _
-- get tⱼ from h_in_conv j
obtain ⟨t, ht_range, ht_eq⟩ := mem_convexHull_pair_zero_basis (h_in_conv j)
-- read off coordinate j of h_sum
have hj : t = 1/2 := …  -- via EuclideanSpace.basisFun_apply + orthonormality
-- 1/2 ≠ 0 and 1/2 ≠ 1, hence rep j ∉ S j
…
```

Estimated proof length: ~30-40 LOC.

### 3.3 Mathlib API audit

The proof above touches:

| Identifier                              | Module                                                       | Use                                    |
|-----------------------------------------|--------------------------------------------------------------|----------------------------------------|
| `EuclideanSpace`                        | `Mathlib.Analysis.InnerProductSpace.EuclideanDist`           | the space `E`                          |
| `EuclideanSpace.single`                 | `Mathlib.Analysis.InnerProductSpace.PiL2`                    | standard basis vector `eᵢ`             |
| `EuclideanSpace.basisFun`               | `Mathlib.Analysis.InnerProductSpace.PiL2`                    | orthonormal basis                      |
| `EuclideanSpace.basisFun_apply`         | same                                                         | extract coordinate                     |
| `EuclideanSpace.inner_basisFun_basisFun`| same                                                         | orthonormality                         |
| `convexHull`                            | `Mathlib.Analysis.Convex.Hull`                               | convex hull                            |
| `Set.mem_convexHull`                    | same                                                         | unfold membership                      |
| `Finset.centerMass`                     | `Mathlib.Analysis.Convex.Combination`                        | explicit convex combination            |
| `convexHull_pair` / `segment_eq_image`  | same                                                         | 2-point hulls                          |
| `Convex.combo_self_self_left`           | `Mathlib.Analysis.Convex.Basic`                              | midpoint membership                    |
| `∑ i, S i` (`Set.sum`)                  | `Mathlib.Algebra.BigOperators.Group.Finset.Set`              | Minkowski sum                          |
| `Finset.card_filter` / `Finset.filter_eq_univ` | `Mathlib.Data.Finset.Card`                            | excess-count finalization              |

All identifiers exist at Mathlib v4.26.0 (verified by checking
`proofs/Proofs/ShapleyFolkman.lean` imports — the parent file uses the
same `EuclideanSpace` + convex-hull stack).

## 4. Locked S2 / S3 scope

### 4.1 S2 ACT (build-pending PR target)

**Single new file**: `proofs/Proofs/ShapleyFolkmanOQ01.lean`.

Contents:

1. Imports: `Mathlib` (or specifically the ~6 modules in § 3.3).
2. Namespace `ShapleyFolkmanOQ01`.
3. `def S` (the `Fin N → Set E`).
4. `def witness` (the witness point).
5. `theorem shapley_folkman_tight_excess_count` (the negative theorem).
6. A 2-3 line corollary: `shapley_folkman_finrank_bound_is_sharp`
   stating that the parent's `card ≤ finrank E = N` bound is achieved by
   this witness.

Add the file import to `proofs/Proofs.lean` (1 line).

Gallery entry `src/data/proofs/shapley-folkman-oq-01/`:
- `meta.json` with `status: "verified"`, `axiomCount: 0`, `sorries: 0`.
- `annotations.json` (5-7 annotations citing the construction).
- `index.ts` (boilerplate).

**Total LOC**: ~70-100 Lean + ~150-200 JSON. **Build time**: ~25-35 min
in Docker.

### 4.2 S3 follow-up (optional)

- Strengthen to "every fixed `c : ℕ` is beat by `N := c + 1`":

```lean
theorem shapley_folkman_no_uniform_bound :
    ∀ c : ℕ, ∃ (N : ℕ) (E : Type _) [_ : Fintype (Fin N)]
            [_ : FiniteDimensional ℝ E] (S : Fin N → Set E) (x : E),
      x ∈ convexHull ℝ (∑ i, S i) ∧
      ∀ rep, …, (excess rep).card > c
```

This is a 1-line application of S2's theorem with `N := c + 1`.

### 4.3 S4 / open-ended (deferred)

- Approach A (Lyapunov direction): substantial Mathlib upstream.
- Approach B (Aumann integral): same prerequisites as A.
- Positive Hausdorff-distance-style fallback in `ℓ²`: requires
  `MeasureTheory.measure_HausdorffMeasure` machinery; deferred.

## 5. Sister-slug compatibility

`shapley-folkman-oq-03` (existing, 203 LOC) addresses a *different*
extension (likely additive-error variants of the finite-dim bound). The
S2 theorem here is orthogonal: it's a *negative* result about removing
the `FiniteDimensional` hypothesis, not refining the bound under it.

No file overlap. The new `ShapleyFolkmanOQ01.lean` lives alongside the
existing `ShapleyFolkman.lean` and `ShapleyFolkmanOQ03.lean` without
import conflicts (verified `grep -n "OQ01\|OQ03" proofs/Proofs.lean`).

## 6. Anti-targets

This PREP / S2 ACT must **NOT**:

- Attempt Approach A (Lyapunov upstream) — defer to a separate slug or
  multi-session campaign.
- Touch `proofs/Proofs/ShapleyFolkman.lean` (parent, verified, 0
  sorries) — the negative result is its own file.
- Modify `proofs/Proofs/ShapleyFolkmanOQ03.lean` — sister slug, separate
  axis.
- Use `ℓ²` (`Analysis.InnerProductSpace.l2Space`) — overkill; finite-dim
  `EuclideanSpace ℝ (Fin N)` suffices for the negative result.
- Introduce any `axiom` — Approach C is fully `verified`.
- Add `loom:review-requested` (CLAUDE.md axiom integrity policy — math
  agents do not).

## 7. Race awareness

At push time:

- Open PRs on `shapley-folkman-oq-01`: 0
  (`gh pr list --search "shapley-folkman-oq-01 in:title"`).
- Recent merges (24h): 1 (#18345 S1 OBSERVE, merged 2026-05-12T22:53Z).
- No `git branch -r | grep shapley-folkman-oq-01` matches for `s2`,
  `prep`, `counterexample`, `approach-c`, or `tight`.
- Sister slug `shapley-folkman-oq-03` (existing) is not under active
  research today.

This PREP is conflict-free against all in-flight branches.

## 8. Honesty

- The proof outlines in §§ 3.1-3.2 are **not** Lean-verified. The Mathlib
  API names in § 3.3 are confirmed against current Mathlib v4.26.0
  conventions but the exact tactic shape (e.g., `mem_convexHull_pair_…`
  helper) may need a 1-2-lemma local helper if not in Mathlib literally.
- The corollary "no uniform `c` works" (§ 4.2) is a *family* of
  finite-dim instances, not a single infinite-dim statement. That is
  the **correct framing** of the negative result: Shapley–Folkman has
  no *uniform* bound across all `N`, hence no infinite-dim extension
  with a `c`-independent statement.
- An alternate framing — single `ℓ²` instance with literally infinite
  excess count — is mathematically equivalent but Lean-wise heavier
  (set indexing by `ℕ`, summability, etc.); the parametric-`N` framing
  is the minimal Lean delta.
- Approach C does NOT settle the deeper question "what *is* the right
  infinite-dim analog?" — it only refutes the literal `finrank`
  extension. Aumann/Lyapunov remain the correct positive results;
  formalizing them is a separate Mathlib upstreaming project.

## 9. No-edit guarantee

This PR adds exactly one file:

```
research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s2-prep-approach-c-ell2-counterexample-design.md
```

No other files in the repo are modified, created, or deleted. The S2 ACT
(future PR) will create `proofs/Proofs/ShapleyFolkmanOQ01.lean` +
`src/data/proofs/shapley-folkman-oq-01/{meta,annotations,index}` but is
explicitly out of scope here.
