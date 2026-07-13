# S2 OBSERVE — sorry inventory + attack plan for both blockers

**Date**: 2026-05-30
**Researcher**: researcher-1
**Mode**: doc-only OBSERVE (no Lean edits)
**Predecessor**: S1 (created 2026-04-03; problem.md only, knowledge.md empty)

## Sorry inventory in `proofs/Proofs/RothTriangleRemoval.lean` (465 LOC, 0 axioms, 2 sorries)

Only `roth_via_triangle_removal` (line 362) is downstream of both sorries
through `rs_tc_ap_free_le` (line 397) and `rs_removal_lb` (line 417).
Discharging both sorries unlocks `roth_via_triangle_removal`, which then
satisfies the gallery's headline statement that `r_3(N) = o(N)` via the
Ruzsa–Szemerédi triangle-removal route.

### Sorry #1 — `rs_tc_ap_free_le` (line 292)

```lean
private lemma rs_tc_ap_free_le {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) (_hOdd : Odd N)
    [DecidableRel (ruzsaSzemerediGraph A).Adj] :
    triangleCount (ruzsaSzemerediGraph A) Finset.univ Finset.univ Finset.univ
      ≤ 6 * A.card * N := by sorry
```

**Mathematical content**: under AP-freeness, every triangle of the RS graph
is `{xVert x, yVert (x+a), zVert (x+2a)}` for some `(a, x) ∈ A × ZMod N`
(an unordered count of `|A|·N`). `triangleCount` counts ordered triples, so
multiplies by `3! = 6`.

**Available infrastructure** (already in file, all 0-sorry):

| Lemma | Line | Direction needed |
|---|---|---|
| `triangle_yields_ap_triple` | 143 | triangle in G → APTriple |
| `ap_free_forces_equal` | 196 | APFree + APTriple → a = b = c |
| `ap_triple_yields_triangle` | 162 | APTriple → triangle |
| `ap_free_triangle_exists` | 253 | for each (a,x), the canonical triangle |
| `xy_edge_unique_triangle` | 228 | xy-edge → unique z under AP-free |

**Attack plan** (1 main injection + 1 cardinality calculation):

1. Define the *triangle support* as the filter Finset
   `T := (univ ×ˢ univ ×ˢ univ).filter (fun (a,b,c) => Adj a b ∧ Adj a c ∧ Adj b c)`.
   The goal becomes `T.card ≤ 6 * A.card * N`.
2. Build an embedding `f : T ↪ Fin 6 ×ˢ A ×ˢ (Finset.univ : Finset (ZMod N))`
   sending `(v₁, v₂, v₃)` to `(σ, a, x)` where:
   - `(a, x)` is the canonical parametrization: the unique pair such that the
     unordered set `{v₁, v₂, v₃} = {xVert x, yVert (x+a), zVert (x+2a)}`.
     Existence + uniqueness come from `triangle_yields_ap_triple` composed
     with `ap_free_forces_equal` (gives a = b = c = the common difference,
     then `x` is recovered from the X-vertex).
   - `σ ∈ Fin 6` is the permutation that sends the canonical ordering
     `(xVert x, yVert (x+a), zVert (x+2a))` to `(v₁, v₂, v₃)`.
3. Injectivity is immediate from the canonical parametrization being
   determined by the unordered triple plus the ordering permutation.
4. `card_le_of_injective` + `card_product` gives
   `T.card ≤ 6 * A.card * N`.

**Lean technicalities**:

- The vertex `xVert x` lives at `(⟨0, _⟩, x)` in `Fin 3 × ZMod N`, so
  identifying "which of v₁/v₂/v₃ is in part 0" is just inspecting `.1`.
- For each ordered triple in `T`, the three first-coordinates form a
  permutation of `(0,1,2)` (since edges only cross parts — guaranteed by
  `rsAdj_loopless` style reasoning on the disjunctive `rsAdj`). This gives
  the `Fin 6` permutation index.
- After identifying parts, the canonical `(x, a)` is read directly:
  `x := vₚ.2` where `vₚ` is the part-0 vertex, and `a := y - x` where `y`
  is the part-1 vertex's second coordinate.

**Estimated size**: ~40–80 LOC, 1 helper lemma (parts-are-distinct) + main injection.

### Sorry #2 — `rs_removal_lb` (line 309)

```lean
private lemma rs_removal_lb {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (hAP : APFree A) (_hOdd : Odd N)
    (R : Finset (RSVertex N × RSVertex N))
    (hR : ∀ a b c, ¬((removeEdges G R).Adj a b ∧ … b c ∧ … a c)) :
    A.card * N ≤ R.card := by sorry
```

**Mathematical content**: the `|A|·N` canonical triangles are pairwise
*edge-disjoint* (each edge of the RS graph lies in at most one triangle
when A is AP-free, via the `xy_edge_unique_triangle` family). Hence a
triangle-cover R must contain ≥ 1 directed pair from each canonical
triangle, all distinct. So `|R| ≥ |A|·N`.

**Available infrastructure**:

- `ap_free_triangle_exists` (line 253): for each (a, x) ∈ A × ZMod N, the
  3 edges of the canonical triangle live in G.
- `xy_edge_unique_triangle` (line 228): each XY-edge lies in exactly one
  triangle under AP-freeness. Analogous YZ and XZ uniqueness should follow
  by the same `triangle_yields_ap_triple` + `ap_free_forces_equal` chain,
  but those companion lemmas are *not yet stated* in the file. **S3 ACT
  will need to prove them as helpers** (or generalize the XY one).
- `ap_free_min_removal` (line 317): already proves that for each (a, x),
  some directed pair from the canonical triangle is in `R` (it's a 6-way
  disjunction over the 6 directed pairs).

**Attack plan**:

1. From `ap_free_min_removal`, for each `(a, x) ∈ A × ZMod N` obtain a
   directed pair `p(a, x) ∈ R` belonging to the canonical (a, x) triangle
   (via `Finset.choose` / classical choice on the 6-way disjunction —
   `Finset.exists_of_six_or` is not needed; a direct
   `if-then-else` cascade or `Or.elim` works).
2. Show `p : A × ZMod N → RSVertex × RSVertex` lands in `R` (definitional)
   and is **injective**: two canonical triangles for distinct (a₁, x₁) ≠
   (a₂, x₂) share no edges. This is the content of edge-disjointness; uses
   `xy_edge_unique_triangle` + 2 analogous lemmas (YZ, XZ).
3. `Finset.card_le_card_of_injOn` (or `Finset.card_image_of_injective`)
   on `p` gives `|A × ZMod N| ≤ |R|`, i.e. `|A| · N ≤ |R|`.

**Helper lemmas needed for S3 ACT**:

| Helper | Statement | Difficulty |
|---|---|---|
| `yz_edge_unique_triangle` | For AP-free A, YZ edge (y, z) → unique x s.t. (xVert x, yVert y, zVert z) triangle | Same as XY; copy proof, swap subscripts |
| `xz_edge_unique_triangle` | For AP-free A, XZ edge (x, z) → unique y | Same shape; uses `rsAdj_xz_exists` + `ap_free_forces_equal` |
| `canonical_triangles_edge_disjoint` | The map `(a, x) ↦ unordered edge set of canonical triangle` is injective | Composes the above |

**Estimated size**: ~80–120 LOC across the 3 helpers + main injection proof.

## Combined estimate for full discharge (S3+)

- S3 ACT: add `yz_edge_unique_triangle`, `xz_edge_unique_triangle` (helper
  pair, mostly copy-paste from XY case).
- S4 ACT: discharge `rs_tc_ap_free_le` via the `Fin 6 × A × ZMod N`
  embedding.
- S5 ACT: discharge `rs_removal_lb` via the `(a, x) ↦ p(a, x)` injection.
- Each ACT is bounded at ~40–80 LOC, well below the Docker-build risk
  threshold; helper additions are leaf-local (no downstream importers
  outside this file's gallery entry).

## File-level cross-traffic check

```bash
grep -rln 'import Proofs.RothTriangleRemoval' proofs/Proofs/
```

Result: **0 importers**. `RothTriangleRemoval.lean` is a **leaf** — any
sub-ACT that compiles in isolation cannot cascade. This removes the
non-leaf-parent risk that complicates the lagrange-four-squares S16 work.

## Mathlib bearer audit (none required)

The proof plan above relies entirely on:
- `Finset` cardinality / embedding API (stable since Mathlib v4.0)
- `Fin 3` / `Fin 6` decidable equality (core Lean)
- `ZMod N` arithmetic (stable)

No Mathlib v4.26.0 bearer at risk. SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
unchanged (current pin per `proofs/lake-manifest.json`).

## Knowledge dump for `knowledge.md`

The above attack plan is the **first substantive knowledge entry** for
this slug. Prior to S2, `knowledge.md` was empty template
(0 problem-understanding, 0 insights). S2 populates:

- **Problem understanding**: the 2 sorries reduce, via canonical
  parametrization, to (i) a 6-fold counting argument and (ii) an
  edge-disjointness injection.
- **Insight #1**: `triangleCount` over `univ³` counts *ordered* triples;
  the factor 6 in the bound is the symmetry group of an unordered
  triangle.
- **Insight #2**: the file already proves `xy_edge_unique_triangle` but
  *not* its YZ / XZ analogues — discharging the second sorry requires
  proving those 2 missing helpers first.
- **Insight #3**: `RothTriangleRemoval.lean` is a leaf file (0 importers),
  so sub-ACTs can be merged independently without cascade risk.

## Decision: split into 3 sequential ACTs (S3, S4, S5)

Rather than a single monolithic ACT, the plan above splits into 3 sub-ACTs
of ~40–80 LOC each. This matches the agent feedback pattern around scoped
sub-ACTs under build-time uncertainty, even on leaf files.

| ACT | Target | LOC | Risk |
|---|---|---|---|
| S3 | `yz_edge_unique_triangle` + `xz_edge_unique_triangle` (helpers) | ~50 | LOW — copy-paste from XY case |
| S4 | discharge sorry #1 (`rs_tc_ap_free_le`) | ~60 | MEDIUM — Fin 6 permutation bookkeeping |
| S5 | discharge sorry #2 (`rs_removal_lb`) | ~70 | MEDIUM — edge-disjointness injection |

## Phase transition

Closes the OBSERVE phase. Recommended next phase: **ORIENT** (literature
spot-check on Ruzsa–Szemerédi (1978) presentations and any Mathlib triangle
counting / edge-disjoint embedding API), then **ACT** on S3.
