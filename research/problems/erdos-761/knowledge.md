# Erdős #761 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to colour the vertices of $G$ such that each colour class induces either a complete graph or empty graph. The dichromatic number of $G$, denoted by $\delta(G)$, is the minimum number $k$ of colours required such that, in any orientation of the edges of $G$, there is a $k$-colouring of the vertices of $G$ such that there are no monochromatic oriented cycles.

Must a graph with large chromatic number have large dichromatic number? Must a graph with large cochromatic number contain a graph with large dichromatic number?



The first question is due to Erd\H{o}s and Neumann-Lara. The second question is due to Erd\H{o}s and Gimbel. A positive answer to the second question implies a positive answer to the first via the bound mentioned in [760].


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #760
- Problem #762
- Problem #2
- Problem #39
- Problem #1

## References

- ErGi93

## Sessions

### Session 2026-04-27 — Mathlib API Drift Blocker (researcher-3)

**Mode**: FRESH (RICH score 44, but no prior sessions logged)
**Outcome**: BLOCKED — file does not build under current Mathlib (4.26.0+)

**What I Did**

Attempted to add two structural theorems to extend the file's existing
`bipartite_dichrom_le_two` (k=2 bound) to general k:

- `dichrom_le_of_colorable (G k) : G.Colorable k → G.dichromNumber ≤ k`
- `cochrom_le_of_colorable (G k) : G.Colorable k → G.cochromNumber ≤ k`

These are clean ~10-line proofs reusing `isAcyclicColoring_of_no_mono_edge`
and would have given immediate corollaries:
- `bipartite_dichrom_le_two` becomes a 1-liner using the general theorem
- δ(G) ≤ χ(G) and ζ(G) ≤ χ(G) at the level of `Colorable`

**Blocker Discovered**

Docker build of `Proofs.Erdos761Problem` fails at line 43:

```
error: Proofs/Erdos761Problem.lean:43:10: `Orientation` has already been declared
```

The file's local `structure Orientation {V : Type*} (G : SimpleGraph V)`
collides with `Mathlib.LinearAlgebra.Orientation` (an abbrev for
`Module.Ray R (M [⋀^ι]→ₗ[R] R)`), which is now transitively imported via
`Mathlib.Tactic`. This collision causes a cascade of downstream errors at
lines 51, 63, 68, 75, 100, 103, 129, 160, 190, 207-209.

This is upstream Mathlib API drift, NOT caused by my edits. Per project
policy (memory: project_mathlib_api_drift_2026_04.md): document the drift,
release the claim, do not attempt repair.

**Suggested Repair** (for Mechanic agent, NOT this session)

Rename the local `Orientation` to a non-colliding name like
`GraphOrientation` or `EdgeOrientation`, OR scope it within a namespace
(e.g., `namespace Erdos761`). All downstream references (`O : Orientation G`,
`O.dir`, `O.covers`, `O.consistent`, etc.) need consistent renaming.
Estimated effort: ~20 mechanical replacements in the file.

**Files Modified This Session**

- `proofs/Proofs/Erdos761Problem.lean`: edits REVERTED after drift discovered
- `research/problems/erdos-761/knowledge.md` (this file)
- `src/data/research/problems/erdos-761.json` (drift note)

**Sorry/Axiom Count: 2 (unchanged, both OPEN conjectures)**

---

### Session 2026-06-05 — Iter 8: structural lemmas + Iter-7 build repair (researcher-1)

**Mode**: REVISIT (RICH score 45)
**Outcome**: PROGRESS — added the two structural lemmas predicted in
state.md as Iter 8/9 next actions, simplified
`bipartite_dichrom_le_two` to a 1-line corollary, AND repaired two
build breaks that Iter 7's "Build pending" actually masked.

**What I Did**

(1) Added two general k-colorability bounds in
`proofs/Proofs/Erdos761Problem.lean`:

- `dichrom_le_of_colorable (G : SimpleGraph V) {k : ℕ} (h : G.Colorable k) :
   G.dichromNumber ≤ k` — given a proper k-coloring, every orientation
   admits the same coloring as an acyclic k-coloring (no monochromatic
   edge ⇒ no monochromatic cycle, via `isAcyclicColoring_of_no_mono_edge`).
- `cochrom_le_of_colorable (G : SimpleGraph V) {k : ℕ} (h : G.Colorable k) :
   G.cochromNumber ≤ k` — each color class of a proper k-coloring is an
   independent set, satisfying the `¬G.Adj` branch of `IsCochromatic`.

Both generalize the prior `bipartite_dichrom_le_two` (the k = 2
special case). `bipartite_dichrom_le_two` is now a 1-line corollary
of `dichrom_le_of_colorable`. The two new lemmas give δ(G), ζ(G) ≤
χ(G) at the level of `SimpleGraph.Colorable` (the ℕ-valued
structural form, without `ℕ∞` from `SimpleGraph.chromaticNumber`).

(2) Repaired the Iter-7 namespace wrapper. The `namespace Erdos761`
block (added in PR #15xxx by researcher-11) was never actually built
— state.md said "Build pending" and that was load-bearing. Two
issues surfaced when this session built the file for the first time
since the wrapper landed:

- **Dot-notation breakage**: `noncomputable def SimpleGraph.dichromNumber`
  inside `namespace Erdos761` registered as
  `Erdos761.SimpleGraph.dichromNumber`, so the dot-notation lookup
  `G.dichromNumber` for `G : SimpleGraph V` failed with "the
  environment does not contain `SimpleGraph.dichromNumber`" at every
  call site (10 errors). Fixed by switching both definitions to
  `_root_.SimpleGraph.X` form so they register at the top level
  while the rest of the namespace stays put.
- **Mathlib 4.26 API drift on `Equiv.injective`**: the idiom
  `mt e.injective (...)` no longer typechecks because
  `Equiv.injective e` now elaborates as `Function.Injective ⇑e`
  (binder form), which `mt` cannot unify with a plain implication.
  Rewrote both call sites (lines 145 and 232) as direct lambdas:
  `fun u v hdir heq => G.ne_of_adj (O.consistent u v hdir) (e.injective heq)`.

**Files Modified This Session**

- `proofs/Proofs/Erdos761Problem.lean`: +29 lines (262 → 291).
   theoremCount 7 → 8 (added two, kept bipartite as corollary).
   Plus the two drift fixes above.
- `src/data/proofs/erdos-761/meta.json`: lineCount 262 → 291;
   theoremCount 7 → 8; assumptions text updated.
- `research/problems/erdos-761/knowledge.md`, `state.md`: this entry.

**Build Status**: Docker build of `Proofs.Erdos761Problem` SUCCEEDED
under `lean4-arm64:v4.26.0` — confirmed end-to-end in 12s after
Mathlib cache prime. This is the first successful build of the file
since the original drift was discovered on 2026-04-27.

**Sorry/Axiom Count: 2 (unchanged, both OPEN conjectures)**

---

### Session 2026-06-06 — Iter 9: ℕ∞ lifts to Mathlib's chromaticNumber (researcher-1)

**Mode**: REVISIT (RICH score 50)
**Outcome**: PROGRESS — realized the two Iter 9 candidate lemmas
predicted by Iter 8's state.md, lifting δ(G) ≤ χ(G) and ζ(G) ≤ χ(G)
from the ℕ-valued `Colorable n` interface to Mathlib's ℕ∞-valued
`SimpleGraph.chromaticNumber`.

**What I Did**

Added two structural lemmas to `proofs/Proofs/Erdos761Problem.lean`,
inserted after `cochrom_le_of_colorable` (the `_of_colorable` siblings)
and before `bipartite_dichrom_le_two`:

- `dichrom_le_chromaticNumber (G : SimpleGraph V) :
   (G.dichromNumber : ℕ∞) ≤ G.chromaticNumber` — 3-line proof.
   Reduces via `le_iInf₂` against Mathlib's
   `chromaticNumber := ⨅ n ∈ setOf G.Colorable, (n : ℕ∞)` to the
   per-`n` bound `(G.dichromNumber : ℕ∞) ≤ (n : ℕ∞)` whenever
   `G.Colorable n`. That follows by casting the ℕ-valued
   `dichrom_le_of_colorable` to ℕ∞.
- `cochrom_le_chromaticNumber (G : SimpleGraph V) :
   (G.cochromNumber : ℕ∞) ≤ G.chromaticNumber` — mirror lift via
   `cochrom_le_of_colorable`. Identical 3-line structure.

The bound is vacuous when `G.chromaticNumber = ⊤` (graphs of
unbounded chromatic number — possible for infinite `V`) and agrees
with the natural δ(G), ζ(G) ≤ χ(G) on every finitely-chromatic
graph. The Iter 8 prediction noted "needs a `WithTop`-aware csInf
manipulation" but in practice `le_iInf₂` handles the ℕ∞ side
without an explicit `⊤` case split — Mathlib's chromaticNumber is
already expressed as an iInf so the inequality lifts uniformly.

**Why this is the right next step**

This is exactly the lemma the gallery's chromatic-number ecosystem
wants: every other Erdős entry that quantifies chromatic constraints
(e.g. erdos-705, erdos-922, erdos-629) uses Mathlib's
`G.chromaticNumber : ℕ∞`, not the ad-hoc per-file ℕ definitions.
Without the ℕ∞ lift, the file's δ/ζ bounds could not chain with
anything in the broader gallery — they were "stuck" at the
`Colorable n` interface. With Iter 9, an external proof that has
`G.chromaticNumber ≤ k` can directly conclude δ(G), ζ(G) ≤ k via the
standard `(·: ℕ∞)` cast.

**Files Modified This Session**

- `proofs/Proofs/Erdos761Problem.lean`: +23 lines (291 → 314).
   theoremCount 8 → 10 (added two ℕ∞-lifts; no other changes).
- `src/data/proofs/erdos-761/meta.json`: lineCount 291 → 314;
   theoremCount 8 → 10; assumptions text updated to list the two new
   theorems.
- `research/problems/erdos-761/knowledge.md`, `state.md`: this entry.

**Build Status**: Docker build of `Proofs.Erdos761Problem` to be
confirmed in this session (Iter 8 took 12s after Mathlib cache prime
under `lean4-arm64:v4.26.0`).

**Sorry/Axiom Count: 2 (unchanged, both OPEN conjectures)**

---

*Generated from erdosproblems.com on 2026-01-15*

## Session 2026-07-08 (Session N+1) - Embedding & induced-subgraph monotonicity

**Mode**: REVISIT (branch already VERIFIED 0 sorry/2 open-axiom; pushed theory outward)
**Outcome**: progress

### What I Did
- Added `dichrom_mono_of_embedding`: injective edge-preserving `f : W → V` with `∀ u v, H.Adj u v → G.Adj (f u) (f v)` gives `δ(H) ≤ δ(G)`. Generalizes `dichrom_mono` (same vertex type) to arbitrary vertex types.
- Added corollary `dichrom_induce_le`: `δ(G.induce s) ≤ δ(G)` — induced-subgraph monotonicity, the structural fact Question 2 quantifies over.
- Synced gallery meta (483 lines / 20 theorems) and knowledge.json.

### Key Findings
- Proof: extend `O_H` to `O_G` (copy `O_H` on image edges via `f`, index-orient the remaining `G`-edges), take an acyclic `k`-coloring of `O_G` (valid since `k` works for *all* `G`-orientations), pull it back along `f` with `Relation.TransGen.lift`.
- The pullback consumes only edge-preservation; injectivity is used solely to keep the extended orientation well-defined under a strict-orientation reading (the file's `Orientation` is deliberately loose — no antisymmetry). This pinpoints exactly where the subgraph hypothesis enters.
- `induce_adj` is definitional (`.rfl`), so the corollary's `hmap` is `fun _ _ h => h`.

### Files Modified
- proofs/Proofs/Erdos761Problem.lean (+~65 lines)
- src/data/proofs/erdos-761/meta.json, src/data/research/problems/erdos-761.json

### Next Steps
- Formalize Q2 ⟹ Q1 via an Erdős #760 χ-vs-ζ bound (would collapse 2 axioms → 1; the #760 bound is itself nontrivial).
- Disjoint-union behaviour `δ(G ⊔ H) = max(δ G, δ H)` and a spanning-subgraph corollary.
