import Proofs.RandomizedMaxCut
import Mathlib

/-!
# Randomized MaxCut — OQ-03: Tightness of the 1/2-approximation

## Research Problem: randomized-maxcut-oq-03

The parent file `Proofs.RandomizedMaxCut` proves the *lower bound* direction of the
randomized 1/2-approximation:

* `expected_cut_size` : `E[|C|] = |E|/2`
* `maxCut_le_edges`   : `MaxCut(G) ≤ |E|`
* `rand_approx_guarantee` : `E[|C|] ≥ MaxCut(G)/2`

OQ-03 asks for the *tightness* direction: a family of graphs where the ratio
`E[|C|] / MaxCut(G)` is exactly `1/2`. The answer is the **bipartite family**.

The mechanism is clean once stated abstractly:

* If some boolean assignment `f` cuts *every* edge of `G` (a "full cut"), then
  `MaxCut(G) = |E|` exactly: the full cut achieves `|E|`, and `maxCut_le_edges`
  gives the reverse inequality.
* Combined with the parent's `E[|C|] = |E|/2`, this yields
  `E[|C|] = MaxCut(G)/2` — the approximation ratio is tight.

A graph admits a full cut **iff** it is bipartite (admits a proper 2-colouring
`f : V → Bool` with `f u ≠ f v` for every edge `uv`). We package this as
`IsProper2Coloring` and ship a concrete witness: the complete bipartite family
`K_{m,n}`.

## Main results
* `maxCut_eq_edges_of_fullCut` : a full cut forces `MaxCut(G) = |E|`.
* `rand_approx_tight_of_fullCut` : tightness from any full cut.
* `rand_approx_tight_of_proper2Coloring` : tightness for any bipartite graph.
* `rand_approx_tight_completeBipartite` : concrete witness `K_{m,n}`.

0 sorries, 0 axioms. Builds on the parent file unchanged.

## Scope
Out of scope (sibling slugs): variance (oq-01), derandomisation (oq-02/oq-04),
Goemans-Williamson 0.878 analysis.
-/

namespace RandomizedMaxCutOQ03

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Edge-in-cut characterisation -/

/-- An edge `s(u, v)` is cut by the assignment-cut `ofAssignment f` exactly when
    `f` assigns its endpoints different colours. -/
lemma edgeInCut_ofAssignment_iff {G : SimpleGraph V} (f : V → Bool) (u v : V) :
    (Cut.ofAssignment (G := G) f).edgeInCut s(u, v) = true ↔ f u ≠ f v := by
  unfold Cut.edgeInCut Cut.ofAssignment
  simp only [Sym2.lift_mk, Finset.mem_filter, Finset.mem_univ, true_and]
  cases f u <;> cases f v <;> simp

/-! ## Full cuts force `MaxCut = |E|` -/

/-- `f` is a *full cut* of `G` when it cuts every edge. -/
def IsFullCut (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Bool) : Prop :=
  ∀ e ∈ G.edgeFinset, (Cut.ofAssignment (G := G) f).edgeInCut e = true

/-- If `f` cuts every edge then the maximum cut equals the edge count. -/
lemma maxCut_eq_edges_of_fullCut (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) (hf : IsFullCut G f) :
    maxCutValue G = G.edgeFinset.card := by
  refine le_antisymm (maxCut_le_edges G) ?_
  have hfilter :
      G.edgeFinset.filter (fun e => (Cut.ofAssignment (G := G) f).edgeInCut e)
        = G.edgeFinset := by
    apply Finset.filter_true_of_mem
    intro e he
    exact hf e he
  have hsize : (Cut.ofAssignment (G := G) f).size = G.edgeFinset.card := by
    unfold Cut.size
    rw [hfilter]
  rw [← hsize]
  unfold maxCutValue
  exact Finset.le_sup (f := fun g => (Cut.ofAssignment (G := G) g).size)
    (Finset.mem_univ f)

/-! ## Tightness theorems -/

/-- **Tightness from a full cut.** If `f` cuts every edge of `G`, then the
    expected cut size equals `MaxCut(G)/2` exactly: the randomized 1/2-approximation
    is tight on `G`. -/
theorem rand_approx_tight_of_fullCut (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) (hf : IsFullCut G f) :
    (∑ a : V → Bool, ((randomizedMaxCut (G := G) a).size : ℝ)) / (Fintype.card (V → Bool))
      = (maxCutValue G : ℝ) / 2 := by
  rw [expected_cut_size, maxCut_eq_edges_of_fullCut G f hf]

/-- `f` is a *proper 2-colouring* of `G` when adjacent vertices receive different
    colours. This is exactly the property that makes `G` bipartite. -/
def IsProper2Coloring (G : SimpleGraph V) (f : V → Bool) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → f u ≠ f v

/-- A proper 2-colouring cuts every edge. -/
lemma fullCut_of_proper2Coloring (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) (hf : IsProper2Coloring G f) : IsFullCut G f := by
  intro e
  induction e using Sym2.ind with
  | _ u v =>
    intro he
    have hadj : G.Adj u v := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact he
    rw [edgeInCut_ofAssignment_iff]
    exact hf hadj

/-- **Tightness on bipartite graphs.** Any graph with a proper 2-colouring (i.e.
    any bipartite graph) makes the randomized 1/2-approximation tight:
    `E[|C|] = MaxCut(G)/2`. -/
theorem rand_approx_tight_of_proper2Coloring (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) (hf : IsProper2Coloring G f) :
    (∑ a : V → Bool, ((randomizedMaxCut (G := G) a).size : ℝ)) / (Fintype.card (V → Bool))
      = (maxCutValue G : ℝ) / 2 :=
  rand_approx_tight_of_fullCut G f (fullCut_of_proper2Coloring G f hf)

/-! ## Concrete witness: the complete bipartite family `K_{m,n}` -/

/-- The complete bipartite graph `K_{m,n}` on `Fin m ⊕ Fin n`: two vertices are
    adjacent exactly when they lie on opposite sides. -/
def completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj u v := u.isLeft ≠ v.isLeft
  symm := fun _ _ h => Ne.symm h
  loopless := fun _ h => h rfl

instance (m n : ℕ) : DecidableRel (completeBipartite m n).Adj :=
  fun u v => inferInstanceAs (Decidable (u.isLeft ≠ v.isLeft))

/-- The left/right indicator is a proper 2-colouring of `K_{m,n}`. -/
lemma isProper2Coloring_completeBipartite (m n : ℕ) :
    IsProper2Coloring (completeBipartite m n) Sum.isLeft :=
  fun _ _ hadj => hadj

/-- **Concrete tightness witness.** For the complete bipartite graph `K_{m,n}`,
    the randomized algorithm's expected cut size equals `MaxCut/2` exactly. This
    exhibits the bipartite family demanded by OQ-03. -/
theorem rand_approx_tight_completeBipartite (m n : ℕ) :
    (∑ a : (Fin m ⊕ Fin n) → Bool,
        ((randomizedMaxCut (G := completeBipartite m n) a).size : ℝ))
      / (Fintype.card ((Fin m ⊕ Fin n) → Bool))
      = (maxCutValue (completeBipartite m n) : ℝ) / 2 :=
  rand_approx_tight_of_proper2Coloring (completeBipartite m n) Sum.isLeft
    (isProper2Coloring_completeBipartite m n)

#check @rand_approx_tight_of_fullCut
#check @rand_approx_tight_of_proper2Coloring
#check @rand_approx_tight_completeBipartite

end RandomizedMaxCutOQ03
