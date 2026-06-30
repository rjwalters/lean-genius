/-
Erdős Problem #111 — Open Question 01:
Chromatic Number of ℵ₁-Chromatic Graphs and Bipartite Covers

Source (parent): https://erdosproblems.com/111
Status: the *core* equivalence below is fully verified; the ℵ₁ corollary is a
        clean consequence and is honestly scoped (see notes).

Background
----------
The parent problem (#111) concerns making large-chromatic graphs bipartite by
deleting few edges. A dual, equally classical viewpoint asks how many bipartite
graphs are needed to *cover* the edges of `G`. Define a graph `G` to be coverable
by a family of bipartite graphs `{B_i}_{i ∈ ι}` if every edge of `G` lies in at
least one `B_i`. Since each bipartite `B_i` is exactly a `Bool`-valued
2-coloring `c_i : V → Bool` (an edge of `B_i` joins the two parts), a bipartite
cover is precisely a family `c : ι → V → Bool` such that every edge `{u,v}` is
"separated" by some coordinate: `∃ i, c i u ≠ c i v`.

Main results (this file)
------------------------
1. `BipartiteCover.coloring`  — a bipartite cover indexed by `ι` yields a proper
   coloring of `G` with color set `ι → Bool` (the product/“binary expansion”
   coloring). This is the heart of the matter and holds for an arbitrary `ι`.

2. `colorable_of_bipartiteCover` — for a finite index set, `χ(G) ≤ 2^|ι|`.

3. `colorable_two_pow_iff_bipartiteCover` — the sharp finite equivalence:
   `G` has a bipartite cover by `k` graphs  ↔  `G.Colorable (2 ^ k)`.
   (Equivalently the bipartite cover number equals `⌈log₂ χ(G)⌉`.)

4. `chromaticNumber_le_of_bipartiteCover` and
   `not_nonempty_bipartiteCover_of_chromaticNumber_top` — the consequence for
   large chromatic graphs: a graph that is not finitely colorable (in particular
   one with chromatic number ℵ₁, whose Mathlib `ℕ∞`-valued `chromaticNumber`
   is `⊤`) admits **no finite bipartite cover**: it requires infinitely many
   bipartite graphs to cover its edges.

Honesty note
------------
Mathlib's `SimpleGraph.chromaticNumber` is `ℕ∞`-valued, so every uncountable
chromatic number (including ℵ₁) collapses to `⊤`. The corollary here therefore
states exactly the verifiable content — "not finitely colorable ⇒ no finite
bipartite cover" — which is the formalizable shadow of "χ(G) = ℵ₁ ⇒ infinitely
many bipartite graphs are needed". The finite equivalence (3) is the genuinely
sharp, fully machine-checked statement.

References
----------
- Erdős, Hajnal, Szemerédi (1982): "On almost bipartite large chromatic graphs"
- Folklore: a graph is coverable by `k` bipartite graphs iff `χ(G) ≤ 2^k`.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Defs

open SimpleGraph

namespace Erdos111OQ01

variable {V : Type*} {G : SimpleGraph V} {ι : Type*}

/--
**Bipartite cover.**
A bipartite cover of `G` indexed by `ι` is a family of `Bool`-valued
2-colorings (one per index) such that every edge of `G` is *separated* by at
least one coordinate. The `i`-th coordinate `part i` is the bipartition of the
`i`-th bipartite graph `B_i`; the edge `{u,v}` lies in `B_i` exactly when
`part i u ≠ part i v`, and `covers` says every edge lies in some `B_i`.
-/
structure BipartiteCover (G : SimpleGraph V) (ι : Type*) where
  /-- The `i`-th bipartition, viewed as a `Bool`-valued 2-coloring. -/
  part : ι → V → Bool
  /-- Every edge is separated by at least one bipartition. -/
  covers : ∀ ⦃u v⦄, G.Adj u v → ∃ i, part i u ≠ part i v

/--
The **product coloring** induced by a bipartite cover: send each vertex to the
tuple of its bits `v ↦ (part i v)_{i ∈ ι}`. Adjacent vertices differ in some
coordinate by the covering condition, so this is a proper coloring of `G` with
color set `ι → Bool`. Valid for an *arbitrary* index type `ι`.
-/
def BipartiteCover.coloring (c : BipartiteCover G ι) : G.Coloring (ι → Bool) :=
  Coloring.mk (fun v i => c.part i v) (by
    intro u v hadj heq
    obtain ⟨i, hi⟩ := c.covers hadj
    exact hi (congrFun heq i))

/--
The **converse** construction: any proper coloring of `G` with colors in
`ι → Bool` is a bipartite cover, taking `part i v` to be the `i`-th bit of the
color of `v`. Two adjacent vertices get distinct colors, hence differ in some bit.
-/
def bipartiteCoverOfColoring (C : G.Coloring (ι → Bool)) : BipartiteCover G ι where
  part i v := C v i
  covers _ _ h := Function.ne_iff.mp (C.valid h)

/--
**Finite bipartite cover ⇒ chromatic bound.**
If `G` has a bipartite cover indexed by a finite type `ι`, then `G` is colorable
with `2 ^ |ι|` colors.
-/
theorem colorable_of_bipartiteCover [Fintype ι] [DecidableEq ι]
    (c : BipartiteCover G ι) : G.Colorable (2 ^ Fintype.card ι) := by
  have h := c.coloring.colorable
  rwa [Fintype.card_fun, Fintype.card_bool] at h

/-- Explicit equivalence `Fin (2 ^ k) ≃ (Fin k → Bool)` used to recolor. -/
private def finPowEquiv (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) :=
  (finFunctionFinEquiv (m := 2) (n := k)).symm.trans
    (Equiv.arrowCongr (Equiv.refl (Fin k)) finTwoEquiv)

/--
**Sharp finite equivalence.**
The edges of `G` can be covered by `k` bipartite graphs **iff** `χ(G) ≤ 2 ^ k`.
Equivalently, the minimum number of bipartite graphs needed to cover `G` is
`⌈log₂ χ(G)⌉`. This is the central, fully verified statement.
-/
theorem colorable_two_pow_iff_bipartiteCover (k : ℕ) :
    G.Colorable (2 ^ k) ↔ Nonempty (BipartiteCover G (Fin k)) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨bipartiteCoverOfColoring ((G.recolorOfEquiv (finPowEquiv k)) C)⟩
  · rintro ⟨c⟩
    have h := colorable_of_bipartiteCover c
    simpa using h

/--
**Chromatic-number bound from a finite bipartite cover.**
A finite bipartite cover by `|ι|` graphs forces `χ(G) ≤ 2 ^ |ι| < ⊤`; in
particular the chromatic number is finite.
-/
theorem chromaticNumber_le_of_bipartiteCover [Fintype ι] [DecidableEq ι]
    (c : BipartiteCover G ι) : G.chromaticNumber ≤ (2 ^ Fintype.card ι : ℕ) :=
  (colorable_of_bipartiteCover c).chromaticNumber_le

/--
**The ℵ₁ corollary (verifiable shadow).**
If `G` is *not finitely colorable* — i.e. `G.chromaticNumber = ⊤`, which holds
for every graph with uncountable chromatic number, in particular `χ(G) = ℵ₁` —
then `G` has **no finite bipartite cover**. Covering the edges of an
ℵ₁-chromatic graph by bipartite graphs requires infinitely many of them.
-/
theorem not_nonempty_bipartiteCover_of_chromaticNumber_top
    (h : G.chromaticNumber = ⊤) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ¬ Nonempty (BipartiteCover G ι) := by
  rintro ⟨c⟩
  have hle := chromaticNumber_le_of_bipartiteCover c
  rw [h] at hle
  exact (not_le.mpr (WithTop.coe_lt_top _)) hle

end Erdos111OQ01
