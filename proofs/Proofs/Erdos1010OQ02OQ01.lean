/-
Erdős Problem #1010, Open Question 2, Sub-question 1:
  Exact Minimum K_r Density for r ≥ 5

Parent open question (#1010 OQ2, `Erdos1010OQ02Problem.lean`) asks for the exact
minimum number of copies of K_r forced in a graph whose edge count exceeds the
Turán threshold ex(n, K_r).  It is known for r = 3 (Razborov 2010) and r = 4
(Reiher 2016) via flag algebras, and OPEN for r ≥ 5.

The parent formalization states the qualitative Turán forcing step as an
`axiom turan_theorem`.  This file DE-AXIOMATIZES that forcing step for every r,
using Mathlib's extremal-graph API, and establishes the rigorous *endpoints and
structural constraints* of the still-unknown K_r density curve g_r(d):

  * `exists_clique_of_extremalNumber_lt` — the general-r Turán forcing threshold:
    any graph with strictly more than `extremalNumber n (K_{r+1})` edges contains
    at least one K_{r+1}.  (This is exactly what the parent axiomatized.)

  * `turanGraph_cliqueDensity_eq_zero` — the LOWER endpoint of the density curve:
    the extremal Turán graph `turanGraph n r` contains **zero** copies of K_{r+1}
    and hence has K_{r+1}-density exactly 0.  The open problem is the shape of the
    curve strictly above this point.

  * `cliqueDensity_nonneg` / `cliqueDensity_le_one` — the density lives in [0,1].

  * `card_cliqueFinset_mono` — clique counts are monotone under adding edges, the
    structural monotonicity underlying every supersaturation argument.

Everything here is fully machine-checked with **no axioms** and no `sorry`.
It does not resolve the open problem; it pins down its provable boundary.

Reference: https://erdosproblems.com/1010 (open question 2)
-/

import Mathlib

open SimpleGraph Finset
open Fintype (card)

namespace Erdos1010OQ02OQ01

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Clique counting via Mathlib's `cliqueFinset`

We use Mathlib's `SimpleGraph.cliqueFinset G k`, the finset of `k`-cliques of `G`,
and its cardinality as the K_k count.  This is definitionally the same object the
parent problem counts by hand, but comes with a developed API.
-/

/-- The number of `k`-cliques of `G`. -/
def cliqueCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (G.cliqueFinset k).card

/-- The `k`-clique count never exceeds `C(n, k)`: a `k`-clique is in particular a
`k`-subset of the vertex set. -/
theorem cliqueCount_le_choose (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    cliqueCount G k ≤ (card V).choose k :=
  G.card_cliqueFinset_le

/-- **Monotonicity of clique counts.**  Adding edges can only create cliques, never
destroy them: if `G ≤ H` then every `k`-clique of `G` is a `k`-clique of `H`. This
is the structural backbone of all supersaturation arguments. -/
theorem cliqueCount_mono {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ≤ H) (k : ℕ) : cliqueCount G k ≤ cliqueCount H k :=
  Finset.card_le_card (G.cliqueFinset_mono h)

/-!
## The general-r Turán forcing threshold (de-axiomatizing `turan_theorem`)

`extremalNumber n H` is Mathlib's Turán-type extremal number: the maximum number of
edges of an `H`-free graph on `n` vertices.  For `H = K_{r+1} = ⊤ : SimpleGraph (Fin (r+1))`
this is `ex(n, K_{r+1})`.  Exceeding it forces a copy of `K_{r+1}`.
-/

/-- **General-r Turán forcing.** If a graph on `V` has strictly more than
`ex(n, K_{r+1})` edges, then it contains at least one copy of `K_{r+1}`, i.e. it is
not `(r+1)`-clique-free.  This is precisely the statement the parent problem posits
as `axiom turan_theorem`, here proved from Mathlib's extremal-graph theory. -/
theorem not_cliqueFree_of_extremalNumber_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ)
    (h : extremalNumber (card V) (⊤ : SimpleGraph (Fin (r + 1))) < G.edgeFinset.card) :
    ¬ G.CliqueFree (r + 1) := by
  have hcontained : (⊤ : SimpleGraph (Fin (r + 1))) ⊑ G :=
    IsContained.of_extremalNumber_lt_card_edgeFinset h
  -- `CliqueFree (r+1)` is exactly `⊤`-freeness for a vertex set of size `r+1`.
  have hiff : G.CliqueFree (r + 1) ↔ (⊤ : SimpleGraph (Fin (r + 1))).Free G := by
    have := cliqueFree_iff_top_free (G := G) (β := Fin (r + 1))
    simpa only [Fintype.card_fin] using this
  rw [hiff]
  exact fun hfree => hfree hcontained

/-- **Clique-count form of Turán forcing.** Exceeding `ex(n, K_{r+1})` edges forces
at least one `K_{r+1}`. -/
theorem one_le_cliqueCount_of_extremalNumber_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ)
    (h : extremalNumber (card V) (⊤ : SimpleGraph (Fin (r + 1))) < G.edgeFinset.card) :
    1 ≤ cliqueCount G (r + 1) := by
  have hnf : ¬ G.CliqueFree (r + 1) := not_cliqueFree_of_extremalNumber_lt G r h
  rw [← SimpleGraph.cliqueFinset_eq_empty_iff] at hnf
  have hne : (G.cliqueFinset (r + 1)).Nonempty := Finset.nonempty_of_ne_empty hnf
  have hpos : 0 < (G.cliqueFinset (r + 1)).card := hne.card_pos
  simp only [cliqueCount]
  omega

/-!
## The lower endpoint of the density curve: the Turán graph

`turanGraph n r` is the canonical balanced `r`-partite graph — the extremal
`K_{r+1}`-free graph.  It sits *at* the Turán threshold and contains **no** copies
of `K_{r+1}`, so its `K_{r+1}`-density is exactly `0`.  This is the lower endpoint
of the open density curve `g_{r+1}(d)`.
-/

/-- The Turán graph has no `(r+1)`-cliques (for `r ≥ 1`). -/
theorem turanGraph_cliqueFinset_eq_empty (n r : ℕ) (hr : 0 < r) :
    (turanGraph n r).cliqueFinset (r + 1) = ∅ :=
  (turanGraph_cliqueFree hr).cliqueFinset

/-- The `K_{r+1}` count of the Turán graph is exactly `0`. -/
theorem turanGraph_cliqueCount_eq_zero (n r : ℕ) (hr : 0 < r) :
    cliqueCount (turanGraph n r) (r + 1) = 0 := by
  unfold cliqueCount
  rw [turanGraph_cliqueFinset_eq_empty n r hr, Finset.card_empty]

/-!
## Clique density in [0,1]

The `k`-clique density `ρ_k(G) = (# K_k) / C(n, k)` is the normalized quantity whose
minimum over graphs of a given edge density the open problem seeks.
-/

/-- The `k`-clique density of `G`: `(# K_k) / C(n, k)`. -/
noncomputable def cliqueDensity (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℝ :=
  (cliqueCount G k : ℝ) / ((card V).choose k : ℝ)

theorem cliqueDensity_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    0 ≤ cliqueDensity G k := by
  unfold cliqueDensity
  positivity

theorem cliqueDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    cliqueDensity G k ≤ 1 := by
  unfold cliqueDensity
  rcases Nat.eq_zero_or_pos ((card V).choose k) with h0 | hpos
  · rw [h0]; simp
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast cliqueCount_le_choose G k

/-- **Lower endpoint of the K_{r+1} density curve.** The extremal Turán graph
realizes `K_{r+1}`-density exactly `0`. -/
theorem turanGraph_cliqueDensity_eq_zero (n r : ℕ) (hr : 0 < r) :
    cliqueDensity (turanGraph n r) (r + 1) = 0 := by
  unfold cliqueDensity
  rw [turanGraph_cliqueCount_eq_zero n r hr]
  simp

end Erdos1010OQ02OQ01
