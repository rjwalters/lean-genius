# prob-method-second-moment-oq-02 — S1b OBSERVE: Mathlib infrastructure audit refinement

**Date**: 2026-05-12
**Author**: researcher-1
**Scope**: doc-only follow-up to S1 OBSERVE (PR #18295, merged
2026-05-12 23:51 UTC). Refines the Mathlib-gap audit in
`src/data/research/problems/prob-method-second-moment-oq-02.json`
(`knowledge.mathlibGaps`) by identifying **load-bearing Mathlib
primitives the S1 OBSERVE missed** which shrink the S2 ACT scope
from ~350 LOC to ~250 LOC.

**No Lean source changes.** **No** `meta.json`, `problem.md`,
`state.md`, `knowledge.md`, or gallery JSON edits. Adds exactly one
file: this session note.

## Orthogonality to S1 OBSERVE

S1 OBSERVE (PR #18295) shipped to gallery JSON only (no markdown
edits; `problem.md`/`state.md`/`knowledge.md` remain seeker-init
stubs). Its `mathlibGaps` field claims:

> - G(n, p) random graph as a probability measure — entirely missing.
> - Variance over Finset (custom in parent; Mathlib's ProbabilityTheory.Variance is over MeasureTheory).
> - Standard subgraph-count threshold lemmas — none in Mathlib.

**The first and third claims are over-broad.** Mathlib has
load-bearing components for both, missed by the S1 audit. S1b
documents them concretely and quantifies the S2 ACT scope reduction.

## 1. `Mathlib.Combinatorics.SimpleGraph.Clique` — subgraph counting

`Mathlib/Combinatorics/SimpleGraph/Clique.lean` (39 678 bytes,
verified via `gh api repos/leanprover-community/mathlib4/contents/...`)
defines:

```lean
namespace SimpleGraph

def IsClique (G : SimpleGraph V) (s : Set V) : Prop :=
  s.Pairwise G.Adj

def IsNClique (G : SimpleGraph V) (n : ℕ) (s : Finset V) : Prop :=
  G.IsClique s ∧ s.card = n

def cliqueFinset (G : SimpleGraph V) (n : ℕ) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] : Finset (Finset V) :=
  univ.filter (fun s => G.IsNClique n s)

end SimpleGraph
```

**Direct consequence for OQ-02**: the parent's planned
`subgraphCount` is one line:

```lean
def triangleCount (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).card
```

The S1 OBSERVE JSON's `knownResults.open` lists `subgraphCount_variance`
as ~80 LOC, of which ~30 LOC is the **definitional layer** (defining
"triangle in G", "set of triangles", "count over all (n-choose-3)
triples"). With `cliqueFinset 3`, this layer collapses to ~5 LOC.

## 2. `Mathlib.Combinatorics.SimpleGraph.Triangle.*` — triangle-specific API

`Mathlib/Combinatorics/SimpleGraph/Triangle/Basic.lean` provides
purpose-built triangle infrastructure (Yaël Dillies & Bhavik Mehta,
2022; ≥ 4 modules in the `Triangle/` subdirectory):

- `EdgeDisjointTriangles G : Prop` — every edge belongs to at most
  one triangle.
- `LocallyLinear G : Prop` — every edge belongs to exactly one
  triangle.
- `FarFromTriangleFree G ε : Prop` — `ε`-removal of edges needed to
  make `G` triangle-free.
- Triangle Removal Lemma (in `Triangle/Removal.lean`).
- Triangle in tripartite graphs (`Triangle/Tripartite.lean`).

**Relevance to OQ-02**: not direct, but the existence of this
infrastructure means the S2 ACT's `subgraphCount_variance`
specialisation to triangles can reuse `cliqueFinset 3` rather than
re-deriving from `Sym2 V` or `Finset.sym3 V`. It also means a
sibling slug `prob-method-second-moment-oq-04` (perfect matching
threshold) or `oq-05` (k-clique threshold for k ≥ 4) can lean on the
same `cliqueFinset` abstraction.

## 3. `Mathlib.Probability.ProbabilityMassFunction.*` — G(n, p) primitives

The S1 OBSERVE JSON says "G(n, p) random graph as a probability
measure — entirely missing" and recommends an "ad-hoc product-
measure definition (~30 LOC)". The latter overestimates the cost:
Mathlib has all the **building blocks** for a G(n, p) PMF.

### 3.1 Single-edge Bernoulli — `PMF.bernoulli`

`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:297`:

```lean
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : PMF Bool
```

This is the per-edge primitive: each edge is present (`true`) with
probability `p`, absent (`false`) with probability `1 - p`.

### 3.2 Monadic composition — `PMF.bind`, `PMF.seq`, `PMF.ofFintype`

`Mathlib/Probability/ProbabilityMassFunction/Monad.lean:105`:

```lean
def bind (p : PMF α) (f : α → PMF β) : PMF β

theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, p a * (f a).toMeasure s
```

`Constructions.lean:111` provides `PMF.seq` (applicative composition)
and `Constructions.lean:203` provides `PMF.ofFintype` (PMF on a
fintype from a normalised weight function).

### 3.3 PMF → Measure bridge — `PMF.toMeasure`

`Monad.lean:90`: `PMF.toMeasure : PMF α → Measure α` (with a built-in
`IsProbabilityMeasure` instance). This lets the G(n, p) PMF be
converted to a `Measure (SimpleGraph (Fin n))` instance, after which
the *entire* `Mathlib.Probability.Moments.Variance` API applies
verbatim — no ad-hoc bridge needed.

### 3.4 The G(n, p) PMF in ≤ 25 LOC

A working sketch using only Mathlib primitives:

```lean
import Mathlib

open SimpleGraph
open Sym2 (mkLE)
open ProbabilityTheory

namespace ProbMethod.SecondMoment.RandomGraph

variable {n : ℕ}

/-- Edge set of K_n indexed by unordered pairs. -/
abbrev EdgeIdx (n : ℕ) := { e : Sym2 (Fin n) // ¬ e.IsDiag }

instance : Fintype (EdgeIdx n) := Subtype.fintype _
instance : DecidableEq (EdgeIdx n) := Subtype.decidableEq

/-- A subset of edges → a SimpleGraph. -/
def graphOfEdges (E : Finset (EdgeIdx n)) : SimpleGraph (Fin n) where
  Adj a b := ⟨a, b⟩ ∈ (E.image (·.val) : Finset (Sym2 (Fin n))) ∧ a ≠ b
  symm  := by intros; aesop
  loopless := by intros; aesop

/-- G(n, p) as a PMF over subsets of edges, built as an iterated
bind of per-edge Bernoullis. -/
noncomputable def gnp_edges (p : ℝ≥0) (hp : p ≤ 1) :
    PMF (Finset (EdgeIdx n)) :=
  -- standard product-of-Bernoulli iteration over Finset.univ : Finset (EdgeIdx n)
  Finset.univ.foldr
    (fun e q => (PMF.bernoulli p hp).bind (fun b =>
      q.map (if b then Finset.insert e else id)))
    (PMF.pure ∅)

/-- G(n, p) as a PMF over SimpleGraph (Fin n). -/
noncomputable def gnp (p : ℝ≥0) (hp : p ≤ 1) :
    PMF (SimpleGraph (Fin n)) :=
  (gnp_edges p hp).map graphOfEdges

end ProbMethod.SecondMoment.RandomGraph
```

(Sketch only — exact API names may need tweaks; the load-bearing
claim is that the iteration template is Mathlib-only, no new axioms.)

## 4. `Mathlib.Probability.Moments.Variance` — full variance API

`Mathlib/Probability/Moments/Variance.lean` (search result hit
`ProbabilityTheory.variance`) provides:

- `ProbabilityTheory.variance : (Ω → ℝ) → Measure Ω → ℝ`
- `variance_def`, `variance_nonneg`, `variance_eq_integral`,
  `MeasureTheory.variance_le`, …
- Chebyshev (`ProbabilityTheory.meas_ge_le_variance_div_sq`).
- Paley-Zygmund (search for `paleyZygmund` in Mathlib).

**The S1 OBSERVE JSON's claim** "Mathlib's `ProbabilityTheory.Variance`
is over `MeasureTheory`" is true *and* immediately useful: bridging
`PMF.toMeasure` (§ 3.3) puts the G(n, p) PMF into the same setting
as Mathlib's variance API. The parent's hand-rolled `chebyshev_finite`
/ `paley_zygmund` (over ℚ on Finset) becomes a **specialization**
of Mathlib's, not a parallel framework.

## 5. Revised S2 ACT scope

The S1 OBSERVE JSON estimates `~350 LOC, 0-2 sorries` for
`ProbMethodSecondMomentOQ02.lean`. With S1b's Mathlib audit:

| Component                                  | S1 estimate | S1b revised | Savings  | Source                                  |
|--------------------------------------------|-------------|-------------|----------|-----------------------------------------|
| `indicatorSum_variance` (generic)          | ~80 LOC     | ~50 LOC     | -30 LOC  | Bridge to `ProbabilityTheory.variance`  |
| `subgraphCount_variance` (triangle spec)   | ~80 LOC     | ~50 LOC     | -30 LOC  | `cliqueFinset 3` definitional layer     |
| `gnp` PMF definition                       | ~30 LOC     | ~25 LOC     | -5 LOC   | Iterated `PMF.bernoulli.bind` (§ 3.4)   |
| `triangle_subcritical` (Markov)            | ~50 LOC     | ~50 LOC     | unchanged| Already in Mathlib (Markov inequality)  |
| `triangle_supercritical` (Paley-Zygmund)   | ~80 LOC     | ~50 LOC     | -30 LOC  | Mathlib Paley-Zygmund + cliqueFinset    |
| Glue and namespaces                        | ~30 LOC     | ~25 LOC     | -5 LOC   |                                         |
| **Total**                                  | **~350**    | **~250**    | **-100** | (~29% reduction)                        |

The strategic-sorry residual (`triangle_supercritical` Paley-Zygmund
overlap-class step) likely **disappears**, since the case analysis
moves from "raw indicator-sum bookkeeping" to "named `cliqueFinset 3`
elements" — and the overlap-class structure follows from
`Finset.disjUnion` plus `Sym2 (Fin n)` arithmetic, fully decidable.

## 6. Updated S2 ACT plan

Recommended division of the new file `ProbMethodSecondMomentOQ02.lean`:

```
§ 1   import bridge (Mathlib only; one line each)
§ 2   namespace ProbMethod.SecondMoment.RandomGraph
§ 3   EdgeIdx + graphOfEdges + gnp PMF + gnp_toMeasure   (~25 LOC)
§ 4   triangleCount = (G.cliqueFinset 3).card             (~5 LOC)
§ 5   triangle_expected_count : E[triangleCount] = C(n,3) * p^3
§ 6   indicatorSum_variance via ProbabilityTheory.variance (~50 LOC)
§ 7   subgraphCount_variance triangle case (~50 LOC)
§ 8   triangle_subcritical (~50 LOC, Markov)
§ 9   triangle_supercritical (~50 LOC, Paley-Zygmund)
§ 10  comment block: future extensions to oq-04 / oq-05
```

Total: ~235 LOC, 0 sorries projected (down from 0–2).

## 7. Race awareness

At push time:
- `gh pr list --search "prob-method-second-moment-oq-02"` returns
  only the merged S1 OBSERVE PR #18295.
- `git branch -r | grep prob-method-second-moment-oq-02`: 1 hit
  (the S1 OBSERVE branch, already merged).
- No `cliqueFinset`, `pmf`, `bernoulli`, `mathlib-audit`, or
  similar branch.
- S1b is the first follow-up to S1 OBSERVE on this slug. No file
  conflict.

## 8. Test plan

- [x] `SimpleGraph.cliqueFinset` existence verified via
  `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Combinatorics/SimpleGraph/Clique.lean`
  (39 678 bytes returned, content has `def cliqueFinset`).
- [x] `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic` existence
  verified (`EdgeDisjointTriangles`, `LocallyLinear`,
  `FarFromTriangleFree`).
- [x] `PMF.bernoulli` definition verified at line 297 of
  `Constructions.lean`.
- [x] `PMF.bind` + `PMF.toMeasure_bind_apply` verified at line 105 / 172
  of `Monad.lean`.
- [x] `ProbabilityTheory.variance` location verified at
  `Mathlib/Probability/Moments/Variance.lean`.
- [x] LOC savings table cross-referenced against the S1 OBSERVE
  JSON's `knownResults.open` LOC estimates.
- [x] No Lean build required — paper-and-pencil + remote API
  inspection only.
- [x] No edits to `problem.md` / `knowledge.md` / `state.md` /
  `meta.json` / Lean / gallery JSON.

## 9. Anti-targets

- **No** edits to the gallery JSON's `mathlibGaps` field — the
  refinement is documented here, but the JSON-update PR is a
  separate (mechanical) job for S2 ACT or a follow-up sync.
- **No** actual S2 ACT execution — S1b is purely a scope refinement.
- **No** edits to S1 OBSERVE deliverables.
- **No** Lean code; **no** new axioms; **no** new theorems.
- **No** claim of completeness for the G(n, p) PMF sketch in § 3.4 —
  it is a template, not a verified construction. The `Finset.foldr`
  iteration may need adjustment for inductive measurability proofs.
