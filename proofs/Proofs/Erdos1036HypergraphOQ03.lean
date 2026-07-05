/-
Erdős Problem #1036 — Open Question oq-03: Hypergraph Analogue

Base problem (#1036, Shelah 1998): every non-Ramsey graph on n vertices
(no clique or independent set larger than c·log n) contains at least
2^{Ω_c(n)} pairwise non-isomorphic induced subgraphs.

**oq-03**: Does an analogous result hold for hypergraphs? That is, must a
non-Ramsey r-uniform hypergraph (no homogeneous — completely-full or
completely-empty — vertex set larger than c·log n) contain exponentially
many distinct induced sub-hypergraphs?

**Status**: OPEN. This file builds a verified r-uniform hypergraph framework
for the question, proves the structural facts one needs to even STATE it
correctly (complement symmetry of non-Ramseyness, the trivial 2^n ceiling,
and an honest hardness lemma explaining why cheap numeric invariants cannot
certify an exponential lower bound), and isolates the single open input as a
clearly-labelled axiom `shelah_hypergraph`.

What is VERIFIED here (0 sorry):
  * `induced_univ`                     — inducing on all vertices is the identity
  * `numDistinctInduced_pos`           — at least one induced sub-hypergraph
  * `numDistinctInduced_le_two_pow`    — trivial exponential ceiling 2^n
  * `homogeneous_compl` / `nonRamsey_compl`
                                       — complement symmetry (mirrors the r=2
                                         clique/independent-set symmetry of #1036)
  * `distinct_edgeCounts_le`           — HARDNESS: the induced edge-count invariant
                                         takes only ≤ |E|+1 (polynomially many)
                                         values, so no single numeric invariant
                                         can witness 2^{Ω(n)} distinct classes

What remains OPEN (axiomatized): `shelah_hypergraph`, the exponential lower
bound itself — the hypergraph generalization of Shelah (1998).

Note on the count. As in the base #1036 formalization, `numDistinctInduced`
counts distinct *labelled* induced sub-hypergraphs (distinct edge-sets); the
original Erdős question counts up to isomorphism. The labelled count is an
upper proxy for the isomorphism-class count, and closing that gap is part of
what makes the problem hard. The axiom is stated for this labelled proxy,
consistent with the gallery's treatment of #1036.

Reference: https://erdosproblems.com/1036
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Finset

namespace Erdos1036HyperOQ03

/-- An `r`-uniform hypergraph on `V`: a finite set of edges, each of which is
    an `r`-element subset of `V`. -/
structure UnifHypergraph (V : Type*) (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

variable {V : Type*} {r : ℕ}

/-- The induced sub-hypergraph on a vertex set `S`: keep exactly the edges that
    lie entirely inside `S`. Uniformity is inherited. -/
def UnifHypergraph.induced [DecidableEq V] (H : UnifHypergraph V r) (S : Finset V) :
    UnifHypergraph V r where
  edges := H.edges.filter (· ⊆ S)
  uniform := fun e he => H.uniform e (Finset.mem_of_mem_filter e he)

@[simp] theorem induced_edges [DecidableEq V] (H : UnifHypergraph V r) (S : Finset V) :
    (H.induced S).edges = H.edges.filter (· ⊆ S) := rfl

/-- The complement hypergraph: the `r`-subsets of `V` that are NOT edges of `H`. -/
def UnifHypergraph.compl [Fintype V] [DecidableEq V] (H : UnifHypergraph V r) :
    UnifHypergraph V r where
  edges := Finset.powersetCard r Finset.univ \ H.edges
  uniform := fun _ he => (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2

@[simp] theorem compl_edges [Fintype V] [DecidableEq V] (H : UnifHypergraph V r) :
    (H.compl).edges = Finset.powersetCard r Finset.univ \ H.edges := rfl

/-- A vertex set `S` is *homogeneous* for `H` if every `r`-subset of `S` is an
    edge, or every `r`-subset of `S` is a non-edge. For `r = 2` this is exactly
    "`S` is a clique or an independent set", the notion used in base problem #1036. -/
def UnifHypergraph.IsHomogeneous (H : UnifHypergraph V r) (S : Finset V) : Prop :=
  (∀ e, e ⊆ S → e.card = r → e ∈ H.edges) ∨ (∀ e, e ⊆ S → e.card = r → e ∉ H.edges)

/-- `H` is *non-Ramsey at level `c`* if every homogeneous set has at most
    `c·log n` vertices (`n = |V|`) — no large homogeneous set exists. -/
def UnifHypergraph.IsNonRamsey [Fintype V] (H : UnifHypergraph V r) (c : ℝ) : Prop :=
  ∀ S : Finset V, H.IsHomogeneous S → (S.card : ℝ) ≤ c * Real.log (Fintype.card V)

/-- The number of distinct (labelled) induced sub-hypergraphs of `H`, taken over
    all vertex subsets. This is the quantity the open question asks to bound below
    by `2^{Ω(n)}`; here it is an upper proxy for the isomorphism-class count. -/
def UnifHypergraph.numDistinctInduced [Fintype V] [DecidableEq V]
    (H : UnifHypergraph V r) : ℕ :=
  ((Finset.univ : Finset V).powerset.image (fun S => (H.induced S).edges)).card

/-! ## Basic structural facts (verified) -/

/-- Inducing on the full vertex set returns the original edge set. -/
theorem induced_univ [Fintype V] [DecidableEq V] (H : UnifHypergraph V r) :
    (H.induced Finset.univ).edges = H.edges := by
  simp only [induced_edges]
  exact Finset.filter_true_of_mem (fun e _ => Finset.subset_univ e)

/-- There is always at least one induced sub-hypergraph (e.g. the empty one). -/
theorem numDistinctInduced_pos [Fintype V] [DecidableEq V] (H : UnifHypergraph V r) :
    1 ≤ H.numDistinctInduced := by
  unfold UnifHypergraph.numDistinctInduced
  have hne : ((Finset.univ : Finset V).powerset).Nonempty :=
    ⟨∅, Finset.empty_mem_powerset _⟩
  exact (hne.image _).card_pos

/-- **Trivial exponential ceiling.** There are at most `2^n` distinct induced
    sub-hypergraphs, since they are indexed by vertex subsets. The content of the
    open question is a matching *lower* bound under the non-Ramsey hypothesis. -/
theorem numDistinctInduced_le_two_pow [Fintype V] [DecidableEq V]
    (H : UnifHypergraph V r) : H.numDistinctInduced ≤ 2 ^ Fintype.card V := by
  unfold UnifHypergraph.numDistinctInduced
  calc ((Finset.univ : Finset V).powerset.image (fun S => (H.induced S).edges)).card
      ≤ ((Finset.univ : Finset V).powerset).card := Finset.card_image_le
    _ = 2 ^ Fintype.card V := by rw [Finset.card_powerset, Finset.card_univ]

/-! ## Complement symmetry (verified)

For `r = 2` this specializes to the clique/independent-set symmetry of #1036:
a graph is non-Ramsey iff its complement is. We prove it for all `r`. -/

/-- Homogeneity is preserved by complementation: `S` is homogeneous for `H` iff it
    is homogeneous for `Hᶜ` (the "all edges" and "no edges" disjuncts swap). -/
theorem homogeneous_compl [Fintype V] [DecidableEq V] (H : UnifHypergraph V r)
    (S : Finset V) : (H.compl).IsHomogeneous S ↔ H.IsHomogeneous S := by
  have mem_iff : ∀ e : Finset V, e ⊆ S → e.card = r →
      (e ∈ (H.compl).edges ↔ e ∉ H.edges) := by
    intro e _ hecard
    rw [compl_edges, Finset.mem_sdiff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hecard⟩, h⟩
  constructor
  · rintro (h | h)
    · right; intro e heS hecard
      exact fun hmem => ((mem_iff e heS hecard).mp (h e heS hecard)) hmem
    · left; intro e heS hecard
      by_contra hmem
      exact h e heS hecard ((mem_iff e heS hecard).mpr hmem)
  · rintro (h | h)
    · right; intro e heS hecard hmem
      exact ((mem_iff e heS hecard).mp hmem) (h e heS hecard)
    · left; intro e heS hecard
      exact (mem_iff e heS hecard).mpr (h e heS hecard)

/-- A hypergraph is non-Ramsey iff its complement is. -/
theorem nonRamsey_compl [Fintype V] [DecidableEq V] (H : UnifHypergraph V r) (c : ℝ) :
    (H.compl).IsNonRamsey c ↔ H.IsNonRamsey c := by
  constructor
  · intro h S hS
    exact h S ((homogeneous_compl H S).mpr hS)
  · intro h S hS
    exact h S ((homogeneous_compl H S).mp hS)

/-! ## Why the problem is hard (verified)

The open question demands an *exponential* lower bound on the number of distinct
induced sub-hypergraphs. The following lemma explains why no single numeric
invariant of the induced sub-hypergraph can supply such a bound: the edge-count
invariant, though genuinely isomorphism-invariant, ranges over at most `|E| + 1`
values (polynomially many in `n`). Distinguishing `2^{Ω(n)}` classes therefore
requires the full combinatorial structure — the source of the difficulty. -/

/-- The induced edge-count invariant takes at most `|E(H)| + 1` distinct values as
    the vertex set ranges over all subsets. Since `|E(H)| ≤ binom(n,r)` is
    polynomial in `n`, this invariant alone cannot certify `2^{Ω(n)}` distinct
    induced sub-hypergraphs. -/
theorem distinct_edgeCounts_le [Fintype V] [DecidableEq V] (H : UnifHypergraph V r) :
    ((Finset.univ : Finset V).powerset.image
        (fun S => (H.induced S).edges.card)).card ≤ H.edges.card + 1 := by
  have hsub : (Finset.univ : Finset V).powerset.image (fun S => (H.induced S).edges.card)
      ⊆ Finset.range (H.edges.card + 1) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨S, _, rfl⟩ := hn
    rw [Finset.mem_range]
    have hle : (H.induced S).edges.card ≤ H.edges.card := by
      rw [induced_edges]; exact Finset.card_le_card (Finset.filter_subset _ _)
    omega
  calc ((Finset.univ : Finset V).powerset.image (fun S => (H.induced S).edges.card)).card
      ≤ (Finset.range (H.edges.card + 1)).card := Finset.card_le_card hsub
    _ = H.edges.card + 1 := Finset.card_range _

/-! ## The open core (axiomatized)

The exponential lower bound is the hypergraph generalization of Shelah (1998).
It is open (oq-03) and stated here as an axiom — the sole assumption of this file. -/

/-- **Hypergraph Shelah bound (OPEN, oq-03).** For every uniformity `r ≥ 2` and
    level `c > 0` there is `c' > 0` such that every non-Ramsey `r`-uniform
    hypergraph on `n` vertices has at least `2^{c'·n}` distinct induced
    sub-hypergraphs. The graph case `r = 2` is Shelah's 1998 theorem; the
    hypergraph case is open. -/
axiom shelah_hypergraph (r : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c > 0) :
    ∃ c' : ℝ, c' > 0 ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : UnifHypergraph V r),
      H.IsNonRamsey c → (H.numDistinctInduced : ℝ) ≥ 2 ^ (c' * Fintype.card V)

/-- Erdős #1036 oq-03, packaged: non-Ramsey `r`-uniform hypergraphs have
    exponentially many distinct induced sub-hypergraphs (conditional on the
    open `shelah_hypergraph` axiom). -/
theorem erdos_1036_oq03 (r : ℕ) (hr : 2 ≤ r) (c : ℝ) (hc : c > 0) :
    ∃ c' : ℝ, c' > 0 ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : UnifHypergraph V r),
      H.IsNonRamsey c → (H.numDistinctInduced : ℝ) ≥ 2 ^ (c' * Fintype.card V) :=
  shelah_hypergraph r hr c hc

end Erdos1036HyperOQ03
