# S6a PREP — Tetrahedron `(d=3, k=2, n=4)` magic certificate

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only design memo)
**Phase target**: S6a ACT (concrete tetrahedron certificate)
**Status**: pristine — 0 open PRs, 1 merged (S1 OBSERVE, PR #18336).

## Why this PREP

The S1 OBSERVE (PR #18336) flags **S6** as a concrete-example
deliverable, with state.md and knowledge.md both claiming:

> these constructions show that **regular convex polytopes are
> $(d-1)$-flat magic for $d \ge 2$** — a non-trivial new class
> beyond the parent's 4 plane classes.

and proposing **`native_decide` certificates** for tetrahedron,
octahedron, and cube. This PREP scrutinises that plan and finds a
critical mismatch:

> **`native_decide` cannot directly discharge `IsKFlatMagic`** for
> `EuclideanSpace ℝ (Fin d)` configurations, because `ℝ` is **not
> decidable** and `AffineSubspace.direction.toSubmodule.rank = k`
> is not a decidable equality.

The S6a ACT must therefore use **manual proof** with explicit witness
construction, not `native_decide`. This memo:

1. Identifies the `native_decide` mismatch (§1).
2. Specifies the canonical tetrahedron point set in
   `EuclideanSpace ℝ (Fin 3)` (§2).
3. Proves "exactly 4 minimal-spanning 2-flats" by direct computation
   (§3).
4. Constructs the magic certificate: uniform weight `w_i = 1`,
   `c = 3` (§4).
5. Audits Mathlib's `AffineSubspace.direction` / `Submodule.rank` /
   `Module.rank` API at v4.26.0 (§5).
6. Lays out the S6a ACT implementation order with LOC estimates (§6).
7. Cross-references to the parent file and to sibling sub-OQs (§7).
8. Anti-targets (§8) — what S6a does NOT do.
9. Honest framing (§9, §10) — why this is a `Prop`-level proof, not
   a computational one.

## 1. The `native_decide` mismatch

state.md §"Next Action" claims:

> **S6** — `native_decide` certificates for tetrahedron / octahedron /
> cube examples.

This is **incorrect for the proposed type signatures**. The reasons:

1. **`EuclideanSpace ℝ (Fin d)` has uncountable carrier.** Equality
   `p = q` in this type is not `Decidable` in general. Therefore
   `p ∈ ConfigKFlat 2 P` is not decidable. The `Finset.filter (· ∈ F)`
   construction inside `kFlatSum` produces an undecidable predicate
   on the underlying point set.
2. **`AffineSubspace.direction.toSubmodule.rank = 2`** is an equality
   in `Cardinal` (or `ℕ∞`). At pinned Mathlib v4.26.0, this is a
   `Prop`-level equality, not a decidable one. Even with `Module.rank`
   (which lands in `Cardinal`), the equality with `(2 : Cardinal)` is
   typically not reducible by `decide`.
3. **`IsKFlatMagic` is `∃ w c > 0, ∀ F, kFlatSum P w F = c`.** The
   existential over `WeightingD P = {w : P → ℝ // ∀ p, w p > 0}`
   ranges over `ℝ`-valued functions; the universal over `ConfigKFlat`
   is also `Prop`-level. Neither is decidable.

**Conclusion**: S6a ACT must produce a **constructive proof term**
giving the weight, the magic constant, and a hand-proved verification
that each of the 4 faces has the same sum. This is more work than
"`native_decide`" suggests but well under 100 LOC for the tetrahedron.

**Companion fix**: state.md and knowledge.md should be corrected in
the next state-touching iteration. (S6a ACT, or a separate doctor
pass, can apply that fix.)

## 2. The canonical tetrahedron in `EuclideanSpace ℝ (Fin 3)`

The cleanest regular tetrahedron with rational coordinates uses
*alternate cube vertices*:

$$
v_1 = (1, 1, 1), \quad
v_2 = (1, -1, -1), \quad
v_3 = (-1, 1, -1), \quad
v_4 = (-1, -1, 1).
$$

**Properties:**

- **Regularity**: pairwise distances are
  $\|v_i - v_j\| = 2\sqrt 2$ for all $i \ne j$ (each pair differs in
  exactly two coordinates, each by $\pm 2$).
- **No 4 coplanar**: the determinant of the $3 \times 3$ matrix
  $[v_2 - v_1, v_3 - v_1, v_4 - v_1]$ equals
  $\det \begin{pmatrix}0 & -2 & -2\\-2 & 0 & -2\\-2 & -2 & 0\end{pmatrix} = -16 \ne 0$.
- **All 4 vertices distinct**.
- **Each 3-subset spans a unique 2-flat** (since no 3 are collinear —
  any 3 of the 4 vertices form a non-degenerate triangle).

**Lean shape** (Mathlib v4.26.0):

```lean
namespace Erdos735OQ04

open EuclideanSpace

/-- The four vertices of a regular tetrahedron at alternate cube
    corners. -/
def tetraVertex (i : Fin 4) : EuclideanSpace ℝ (Fin 3) :=
  match i with
  | 0 => !₂[ 1,  1,  1]   -- v₁
  | 1 => !₂[ 1, -1, -1]   -- v₂
  | 2 => !₂[-1,  1, -1]   -- v₃
  | 3 => !₂[-1, -1,  1]   -- v₄

/-- The tetrahedron as a `PointConfigD 3`. -/
def tetraConfig : PointConfigD 3 :=
  Finset.image tetraVertex Finset.univ
```

(The `!₂[…]` notation is the standard Mathlib `EuclideanSpace`
constructor; alternative `WithLp.equiv (Fin 3) ℝ`-based construction
also works.)

## 3. The four 2-flats

Each 3-subset of `{v_1, v_2, v_3, v_4}` spans a unique 2-flat (a
plane in $\mathbb{R}^3$). Label them:

| Flat | 3-subset | Equation $(ax + by + cz = d)$ |
|:----:|:---------|:------------------------------|
| $F_1$ | $\{v_2, v_3, v_4\}$ | $\phantom{-}x + \phantom{-}y + \phantom{-}z = -1$ |
| $F_2$ | $\{v_1, v_3, v_4\}$ | $\phantom{-}x - \phantom{-}y - \phantom{-}z = -1$ |
| $F_3$ | $\{v_1, v_2, v_4\}$ | $-x + \phantom{-}y - \phantom{-}z = -1$ |
| $F_4$ | $\{v_1, v_2, v_3\}$ | $-x - \phantom{-}y + \phantom{-}z = -1$ |

(Each $F_i$ is the plane through the 3 vertices opposite to $v_i$.)

**Lemma 3.1 (each flat is rank-2)**: For each `i ∈ Fin 4`, the
affine span of the 3-subset has `direction.toSubmodule.rank = 2`.

*Proof sketch*: each 3-subset is non-collinear (any 2 of the 3
points have a difference vector of `(±2, ±2, 0)` or similar; the
two difference vectors `v_j - v_i, v_k - v_i` from any base point
`v_i` are linearly independent — verified by computing the
$2 \times 3$ matrix rank). Lean tactic: `affineCombinationLinearMap`
+ explicit determinant computation OR direct
`Matrix.rank_eq_finrank_range`. **Estimated 6 LOC per flat × 4
flats = 24 LOC**, or one general lemma + 4 instantiations.

**Lemma 3.2 (no other minimal-spanning 2-flat)**: Any 2-flat
containing ≥ 3 of the 4 vertices must be one of $F_1, F_2, F_3, F_4$.

*Proof sketch*: by Lemma 3.1, each 3-subset spans a unique 2-flat
(rank-2 affine subspace). There are exactly $\binom{4}{3} = 4$
3-subsets, hence exactly 4 such 2-flats. No 2-flat contains all 4
vertices (by §2's determinant argument: $\det \ne 0$ ⇒ vertices are
in *general position* with respect to 2-flats). Lean: case analysis
on `Finset.filter (· ∈ F)`.card.

## 4. The magic certificate (uniform weight, $c = 3$)

**Weight assignment**: $w_i = 1$ for all $i$.

**Magic constant**: $c = 3$ (each face contains exactly 3 vertices).

**Lean theorem statement**:

```lean
/-- The regular tetrahedron is `(k = 2)`-flat-magic in ℝ³ with
    magic constant 3 (uniform weighting). -/
theorem tetraConfig_isKFlatMagic :
    IsKFlatMagic 2 tetraConfig := by
  refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, 3, three_pos, ?_⟩
  intro F
  -- F is one of F₁, F₂, F₃, F₄.
  -- Each contains exactly 3 vertices; uniform weight 1 ⇒ sum = 3.
  rcases tetra_kflats_classify F with ⟨i, hi⟩
  subst hi
  simp [kFlatSum, tetra_face_card_eq_three i, Finset.sum_const]
```

**Estimated LOC**: ~12, given Lemmas 3.1 and 3.2 are in scope.

**Why `simp` closes it**: with `Finset.sum_const` and the explicit
card-3 hypothesis, the sum collapses to `3 * 1 = 3`. The only
non-trivial step is identifying which face `F` is — handled by
`rcases tetra_kflats_classify F`.

## 5. Mathlib API audit (v4.26.0)

The S6a ACT requires the following declarations (all expected
present at the pinned v4.26.0; this PREP records them so the S6a
ACT can grep-confirm in 60 seconds):

| Decl | Module | Use |
|------|--------|-----|
| `EuclideanSpace ℝ (Fin n)` | `Mathlib.Analysis.InnerProductSpace.PiL2` | base type |
| `!₂[…]` notation | (same) | vertex literals |
| `AffineSubspace ℝ` | `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace` | flat type |
| `AffineSubspace.direction` | (same) | direction submodule |
| `AffineSubspace.affineSpan` | `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace` | constructing $F_i$ |
| `Submodule.rank` (returns `Cardinal`) | `Mathlib.LinearAlgebra.FiniteDimensional` | rank query |
| `Module.finrank` (returns `ℕ`) | (same) | preferred when finite |
| `Finset.image`, `Finset.filter` | `Mathlib.Data.Finset.Basic` | configs |
| `Finset.sum_const` | `Mathlib.Algebra.BigOperators.Basic` | uniform-weight sum |
| `Matrix.det` (3×3) | `Mathlib.LinearAlgebra.Matrix.Determinant` | non-coplanarity |

**Action item for S6a ACT**: Before writing the .lean file, run

```bash
gh api -X GET search/code -F q="!₂ EuclideanSpace repo:leanprover-community/mathlib4" \
  --jq '.items[] | .path' | head -5
```

to confirm the `!₂[…]` notation works at v4.26.0 (alternative
forms: `Pi.single`, `Matrix.of`, `WithLp.equiv` lift).

**Rank choice**: `Module.finrank` (returns `ℕ`, easier to compare
with `(2 : ℕ)`) is preferable over `Submodule.rank` (returns
`Cardinal`). The parent `Erdos735Problem.lean` uses `direction.toSubmodule.rank`
(`Submodule.rank` API, returns `Cardinal`). For consistency with the
parent, **the OQ-04 definitions should use the same rank notion**
(`direction.toSubmodule.rank` with cardinal-2 equality). The S6a
ACT must work in `Cardinal` arithmetic — `Cardinal.mk_eq_two` is the
key lemma.

## 6. S6a ACT implementation order

Target file: **new** `proofs/Proofs/Erdos735OQ04Tetrahedron.lean`
(small focused file, ~80-120 LOC). Imports `Proofs.Erdos735OQ04`
(the type definitions from S2 ACT — see §7 below for the dependency
graph) and `Mathlib.LinearAlgebra.Matrix.Determinant`.

Sequence:

1. ☐ Confirm S2 ACT has shipped the type definitions
   (`PointConfigD`, `WeightingD`, `ConfigKFlat`, `IsKFlatMagic`).
   If not, S6a ACT is blocked on S2 ACT. [check]
2. ☐ Define `tetraVertex : Fin 4 → EuclideanSpace ℝ (Fin 3)`. [6 LOC]
3. ☐ Define `tetraConfig : PointConfigD 3`. [2 LOC]
4. ☐ Lemma: `tetraConfig.card = 4`. [2 LOC, via `Finset.card_image_of_injective`]
5. ☐ Lemma: vertex injectivity. [4 LOC]
6. ☐ Lemma: each 3-subset spans a rank-2 affine subspace
   (4 instantiations of one general lemma). [15-20 LOC]
7. ☐ Lemma: no 2-flat contains all 4 vertices. [5 LOC, via determinant]
8. ☐ Lemma: any `ConfigKFlat 2 tetraConfig` is one of the 4 faces.
   [10 LOC, case analysis on `Finset.filter (· ∈ F)`.card]
9. ☐ Main theorem: `tetraConfig_isKFlatMagic`. [12 LOC]
10. ☐ Optional: `tetraConfig_magic_constant_eq_three`. [3 LOC]
11. ☐ Build: `./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04Tetrahedron`.
    Expected 30-90s on warm cache.
12. ☐ Update `state.md` Phase → S6a ACT complete; correct the
    `native_decide` claim from S1 to "explicit proof, no native_decide".
13. ☐ Branch: `research/erdos-735-oq-04-s6a-act-tetrahedron-<unix-ts>`.

**Total estimated LOC**: ~80-110.
**Estimated sorries on first submission**: 0 (the computation is
mechanical given the rank lemmas).
**Estimated new axioms**: 0.

## 7. Dependency graph

```
                Proofs.Erdos735Problem (parent, in main, verified+axiomatised)
                          │
                          ▼
                Proofs.Erdos735OQ04        ← S2 ACT (not yet shipped)
                          │
                          ▼
                Proofs.Erdos735OQ04Tetrahedron  ← S6a ACT (this memo's target)
```

**S2 ACT prerequisite**: Defines `PointConfigD`, `WeightingD`,
`ConfigKFlat`, `IsKFlatMagic`, plus optionally `zero_flat_magic_trivial`,
`ambient_flat_magic_trivial`, and `oneflat_eq_parent`. Without S2
ACT, S6a ACT cannot reference `IsKFlatMagic 2`.

**S6a ACT does NOT depend on S5 ACT** (the higher-dim ABKPR axiom).
S6a is an *existence* witness for a single configuration; S5 is the
*universal* classification. The tetrahedron magic property is
independent of the conjectured higher-dim 4-class structure.

## 8. Anti-targets (out of scope for S6a ACT)

1. **Octahedron, cube examples.** Sibling configurations flagged in
   knowledge.md §"Extension to $k$-flats". Each has a parallel
   structure to the tetrahedron but with different incidence
   counts (octahedron: 8 faces × 3 vertices; cube: 6 faces × 4
   vertices). Each would be a separate ~80 LOC follow-up
   (S6b, S6c). Defer.
2. **The S5 higher-dim classification axiom.** Genuinely open
   research; out of scope for a single configuration's magic
   certificate.
3. **`native_decide` infrastructure for `EuclideanSpace ℝ`.**
   Conceptually unsound (§1); deferred to a hypothetical "ratoinal
   coordinate restriction" sub-OQ.
4. **Editing the parent `Erdos735Problem.lean`.** Parent file is
   `verified` (or `axiomatized` — `magic_classification` is an
   axiom). Immutable for this OQ.
5. **`oneflat_eq_parent` reduction theorem.** That's S4 ACT
   territory; this memo is about S6a.
6. **General-position $\mathbb{R}^d$ uniform-weight theorem.**
   Knowledge.md §"Combinatorial counting" claims general-position
   configurations are $k$-flat magic with uniform weights. That's
   the S6-general parallel to S6a-specific; deferred.
7. **Editing `problem.md`, `state.md`, `knowledge.md`, or the
   gallery JSON.** This memo lands as a new `sessions/` file only.

## 9. Why the proof is *not* `native_decide`-style

The S1 OBSERVE proposes `native_decide` certificates for the polytope
examples. Why doesn't that work?

A `native_decide` proof requires:

1. The statement to be `Decidable`.
2. The decidability instance to reduce computationally.

For `IsKFlatMagic 2 tetraConfig`:

- The witness `(w, c)` is in $\mathbb{R}^\text{P} \times \mathbb{R}^+$. The
  type is uncountable — no `Decidable` instance.
- The universal `∀ F : ConfigKFlat 2 tetraConfig, …` quantifies over a
  `Subtype`-style structure indexed by affine subspaces of
  `EuclideanSpace ℝ (Fin 3)`. Affine subspaces of ℝ-modules are not
  enumerable.
- The arithmetic `kFlatSum P w F = c` is over ℝ. Real-arithmetic
  equality is not decidable (in the constructive sense Mathlib uses).

**What `native_decide` *could* do**, with a different formulation:

- Restrict to **rational coordinates**: a `tetraConfigRat : Finset (Fin 3 → ℚ)`.
- Restrict to **rational weights**: `w : Fin 4 → ℚ_{>0}`.
- Replace `AffineSubspace ℝ` with an explicit **list of 3-subsets**.
- Prove decidability of the finite-list-based predicate manually.

This is a substantial reformulation (a "computational
specialisation" of OQ-04), suited to a separate sub-OQ
or to an enrichment iteration that adds a `ConcreteExamples.lean`
file. Out of scope for S6a.

**S6a's approach**: skip `native_decide` entirely; produce an
explicit proof term with the witnesses inlined and the
case-analysis discharged manually. ~80-110 LOC total.

## 10. Honest framing — what S6a ACT achieves

S6a ACT (the next iteration following this PREP) closes the
following:

- ✅ A **single concrete witness** that the higher-flat magic
  property is non-vacuous: `tetraConfig` is `(k=2)`-flat-magic in
  $\mathbb{R}^3$ with magic constant 3.
- ✅ A **counter-example to "the parent's 4 classes exhaust the
  higher-flat magic configurations"**: the tetrahedron is not
  contained in any 1-flat (so it's not in class 1, all collinear),
  is not in general position with respect to lines (no 4 points
  are non-collinear in pairs... actually they are! wait: any 3 of
  the 4 tetrahedron vertices ARE in general position with respect
  to lines, since no 3 are collinear). Hmm, this needs care: the
  tetrahedron is in **general position with respect to lines**
  ($k=1$) in $\mathbb{R}^3$, so it's a member of an analogue of
  parent's class 2 for $\mathbb{R}^3$. The novel content is that
  it is ALSO magic at $k=2$.
- ❌ The S5 higher-dim *classification* axiom (= "these are all
  the higher-flat magic configurations") is **not** advanced. S6a
  is purely existential.

**The tetrahedron's contribution to the higher-dim story**: it
confirms that as $k$ increases from 1 to $d-1$, configurations that
are "rich" in higher-flat incidences (regular polytopes) join the
magic family. The S5 conjecture must accommodate this regular-polytope
family in its higher-dim classification.

## 11. Race awareness

At PREP-push time (2026-05-13, ~03:00 UTC):

- **Open PRs for this slug**: 0.
- **Recent merged PRs**:
  - PR #18336 (S1 OBSERVE, doc-only, 2026-05-12T23:18:25Z).
  - PR #18337 (seeker-init batch including this slug).
- **Latest `origin/main`**: `0c84ce40fd1` (general-quartic-oq-02 S4
  PREP, unrelated slug).
- **Conflict surface**: zero. Strictly additive single-file PR.
- **`sessions/` subdirectory state**: did not exist on main; this
  PR creates it. Same archetype as PR #18417 / #18470 for
  tractatus-ontology-oq-06's `sessions/` first-entry.

## 12. No-edit guarantee

Confirmed via design: this PREP adds **exactly one new file**:

```
research/problems/erdos-735-oq-04/sessions/
    2026-05-13-s6a-prep-tetrahedron-magic-certificate.md
```

(Creating the `sessions/` subdirectory as a side effect.)

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
  - `proofs/Proofs/Erdos735Problem.lean` (parent, in main, mixed
    `verified` + `axiomatized` status)
- ✗ No edits to any `.json` file
  - `src/data/research/problems/erdos-735-oq-04.json`
- ✗ No edits to `literature/README.md`

## 13. References

- Erdős, P. (1981). *Some old and new problems and results in
  combinatorial number theory.* Collected.
- Ackerman, E.; Buchin, K.; Knauer, C.; Pinchasi, R.; Rote, G.
  (2008). *There are not too many magic configurations.* Discrete
  Comput. Geom. **39**, 3-16.
- Murty, U.S.R. (1978). *Equicardinality conjecture* (the original
  4-class conjecture in $\mathbb{R}^2$).
- erdosproblems.com/735 — parent problem source.
- This repo:
  - `proofs/Proofs/Erdos735Problem.lean:42-66` — parent's
    `PointConfig`, `Weighting`, `ConfigLine`, `lineSum`, `IsMagic`.
  - `proofs/Proofs/Erdos735Problem.lean:130` — `magic_classification`
    axiom (ABKPR 2008).
  - `research/problems/erdos-735-oq-04/problem.md:43-65` — proposed
    `PointConfigD`, `WeightingD`, `ConfigKFlat`, `IsKFlatMagic`
    signatures.
  - `research/problems/erdos-735-oq-04/knowledge.md:28-32` —
    tetrahedron-as-magic-config informal sketch.
  - `research/problems/erdos-735-oq-04/state.md:31-35` — polytope
    examples flagged as S6 deliverables.
- Mathlib v4.26.0:
  - `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace` —
    `AffineSubspace`, `direction`, `affineSpan`.
  - `Mathlib.Analysis.InnerProductSpace.PiL2` — `EuclideanSpace`,
    `!₂[…]` notation.
  - `Mathlib.LinearAlgebra.FiniteDimensional` — `Module.finrank`,
    `Submodule.rank`.

## 14. Honesty

This document is **doc-only PREP**. It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in any current `.lean` file
- 0 axiom changes
- 0 changes to any other markdown file (`problem.md`, `state.md`,
  `knowledge.md`), to the gallery JSON, or to the parent `.lean`
- 1 new design document (this file) in a freshly created
  `sessions/` subdirectory

The value is **pre-staging**: a future S6a ACT can ship the
tetrahedron magic certificate in ~80-110 LOC, 0 sorries, 0 axioms,
in well under an hour once S2 ACT lands the type definitions. This
PREP also identifies a **correction** to the S1 OBSERVE's
`native_decide` claim — the actual S6a ACT must use explicit proof
terms, not `decide` / `native_decide`, because `EuclideanSpace ℝ` is
not decidable.

The PREP iteration does **not** discharge any open goal. Status
remains `in-progress` for the slug.

---

**End of S6a PREP — no Lean changes, no gallery changes, no axiom
changes. First entry in a freshly created `sessions/` subdirectory.**
