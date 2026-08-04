import Proofs.CycleDoubleCoverPort.Basic
import Mathlib.Data.Finset.Card

/-
# Cycle Double Cover port, step 2b: exact indexed even covers in the cubic case

Second slice of the port of the openai/cdc-lean development (see #37507),
corresponding to upstream `CDCLean/EvenCover.lean`.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin. In particular
`pairIndicator_card` is proved structurally (identify the fibre as the two-element
set `{p, p + h}` and apply `Finset.card_pair`) rather than by exhaustive
decision over all sixty-four parameter pairs.

## Mathematical content

The object the whole proof is aiming at, in its cubic form: eight edge sets
indexed by `Gamma = F₂³`, each even at every vertex, with every edge belonging
to exactly two of the eight. Step 1 already showed how such a thing flattens
into a `CycleDoubleCover` once each even set is decomposed into circuits
(`FiniteGraph.IndexedEvenDoubleCover.toCycleDoubleCover`); this file records the
cubic-side version, whose `vertexEven` condition is phrased on the three local
slots rather than on edge ends.

`pairIndicator p h` is the `F₂`-indicator of the affine pair `{p, p + h}` inside
`Gamma`. The counting lemma `pairIndicator_card` — that this really is a pair,
i.e. has exactly two members, whenever the direction `h` is nonzero — is what
supplies the `coveredTwice` field once the labelling stage assigns each edge a
base point `p` and takes its flow value as the direction `h`. Nowhere-zeroness
of the flow is exactly the hypothesis `h ≠ 0` here, which is why an 8-flow
yields a *double* cover rather than the classically available quadruple cover.

## Deliberate omissions

Upstream's `cubic_even_double_cover`, which builds an `IndexedEvenDoubleCover`
from a `GammaFlow`, depends on the labelling construction in
`CDCLean/CubicLabeling.lean` and belongs to step 7 of the porting order. Only
the parts of `EvenCover.lean` that are independent of that construction are
ported here.
-/

namespace CycleDoubleCover

/-- The `F₂`-indicator of the affine pair `{p, p + h}` in `Gamma`: the two
points reachable from the base point `p` along the direction `h`. When `h = 0`
the "pair" degenerates to the single point `p`, which is precisely why the
flow used downstream must be nowhere zero. -/
def pairIndicator (p h s : Gamma) : F₂ := if s = p ∨ s = p + h then 1 else 0

@[simp]
theorem pairIndicator_base (p h : Gamma) : pairIndicator p h p = 1 := by
  simp [pairIndicator]

@[simp]
theorem pairIndicator_shift (p h : Gamma) : pairIndicator p h (p + h) = 1 := by
  simp [pairIndicator]

/-- `F₂` is nontrivial, so an indicator value determines its branch. -/
private theorem f2_zero_ne_one : (0 : F₂) ≠ 1 := by decide

/-- The fibre of `pairIndicator p h` over `1` is literally the pair
`{p, p + h}`. -/
theorem pairIndicator_filter (p h : Gamma) :
    (Finset.univ.filter fun s : Gamma => pairIndicator p h s = 1) = {p, p + h} := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, pairIndicator]
  by_cases hs : s = p ∨ s = p + h
  · simp [hs]
  · simp [hs, f2_zero_ne_one]

/-- A nondegenerate affine pair in `Gamma` has exactly two members. The
nondegeneracy hypothesis `h ≠ 0` is essential: it is what stops the two chosen
labels of an edge from collapsing, and hence what turns the eight-flow into an
exact *double* cover. -/
theorem pairIndicator_card (p h : Gamma) (hh : h ≠ 0) :
    (Finset.univ.filter fun s : Gamma => pairIndicator p h s = 1).card = 2 := by
  rw [pairIndicator_filter]
  refine Finset.card_pair ?_
  intro hpe
  exact hh (self_eq_add_right.mp hpe)

namespace CubicGraph

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Eight indexed edge sets on a cubic multigraph, given by their `F₂`
indicators: each is even at every vertex (`vertexEven`, read off the three local
slots) and every edge lies in exactly two of them (`coveredTwice`).

This is the cubic counterpart of `FiniteGraph.IndexedEvenDoubleCover` from step
1; the two differ only in how evenness at a vertex is expressed, since a cubic
graph presents the edge ends at `v` as the three slots `G.edgeAt v i`. -/
structure IndexedEvenDoubleCover (G : CubicGraph V E) where
  member : Gamma → E → F₂
  vertexEven : ∀ s v, ∑ i : Fin 3, member s (G.edgeAt v i) = 0
  coveredTwice : ∀ e,
    (Finset.univ.filter fun s : Gamma => member s e = 1).card = 2

namespace IndexedEvenDoubleCover

variable {G : CubicGraph V E}

/-- The edge set selected by one of the eight indices. -/
def support (C : G.IndexedEvenDoubleCover) (s : Gamma) : Finset E :=
  Finset.univ.filter fun e => C.member s e = 1

theorem mem_support {C : G.IndexedEvenDoubleCover} {s : Gamma} {e : E} :
    e ∈ C.support s ↔ C.member s e = 1 := by
  simp [support]

/-- Evenness at a vertex with the three slots spelled out. -/
theorem vertexEven_three (C : G.IndexedEvenDoubleCover) (s : Gamma) (v : V) :
    C.member s (G.edgeAt v 0) + C.member s (G.edgeAt v 1)
      + C.member s (G.edgeAt v 2) = 0 := by
  have h := C.vertexEven s v
  rwa [Fin.sum_univ_three] at h

/-- "Covered twice" unpacked: every edge lies in the supports of two *distinct*
indices. -/
theorem exists_pair_of_indices (C : G.IndexedEvenDoubleCover) (e : E) :
    ∃ s t : Gamma, s ≠ t ∧ e ∈ C.support s ∧ e ∈ C.support t := by
  obtain ⟨s, t, hst, hfib⟩ := Finset.card_eq_two.mp (C.coveredTwice e)
  have hs : s ∈ Finset.univ.filter fun r : Gamma => C.member r e = 1 := by
    rw [hfib]
    exact Finset.mem_insert_self _ _
  have ht : t ∈ Finset.univ.filter fun r : Gamma => C.member r e = 1 := by
    rw [hfib]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact ⟨s, t, hst, mem_support.mpr (Finset.mem_filter.mp hs).2,
    mem_support.mpr (Finset.mem_filter.mp ht).2⟩

end IndexedEvenDoubleCover

end CubicGraph

end CycleDoubleCover
