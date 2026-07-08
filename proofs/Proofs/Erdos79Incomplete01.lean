/-
  Erdős Problem #79 — Companion (incomplete-01):
  Reducing the "all proper subgraphs of K₄ are size-linear" axiom to a FINITE CHECK.

  The parent file `Erdos79Problem.lean` axiomatizes

      K4_subgraphs_linear :
        ∀ H : SimpleGraph ℕ, isProperSubgraph H (completeGraphN 4) → isRamseySizeLinear H

  as a single sweeping hypothesis quantified over the *infinitely many* subgraphs
  `H` of `SimpleGraph ℕ` that happen to sit below K₄.  This companion shows that
  assumption is far stronger than necessary: because `ramseyNumber` is opaque the
  size-linearity of a *specific* graph can never be derived, but the *combinatorial
  reduction* below IS fully provable (0 axioms / 0 sorries) and cuts the assumption
  down to the six maximal proper subgraphs of K₄.

  Concrete finite check.  Every proper subgraph `H ⊊ K₄` is missing at least one
  of K₄'s six edges, hence sits inside the edge-deleted graph `K₄ − e` (the
  "diamond", two triangles glued on an edge).  Combined with the parent's heredity
  axiom `ramsey_linear_hereditary`, the sweeping `∀ H` axiom therefore follows from

      hdiamond : ∀ p q, (completeGraphN 4).Adj p q → isRamseySizeLinear (K4MinusEdge p q)

  a statement about a FINITE family (the 6 edges of K₄), all pairwise isomorphic.

  Main results (all 0 axioms / 0 sorries):
    • `properSubgraph_missing_edge`     : `H ⊊ K₄` omits some edge of K₄.
    • `properSubgraph_le_K4MinusEdge`   : `H ⊊ K₄` is contained in some `K₄ − e`.
    • `K4MinusEdge_properSubgraph`      : each `K₄ − e` is itself a proper subgraph.
    • `K4_subgraphs_linear_of_edgeDeleted` : the parent's sweeping subgraph axiom is
        a consequence of size-linearity of the six edge-deleted graphs + heredity.

  Reference: https://erdosproblems.com/79
-/

import Mathlib
import Proofs.Erdos79Problem

namespace Erdos79Incomplete01

open SimpleGraph
open Erdos79

/- ## K₄ with one edge removed -/

/-- `K4MinusEdge p q` is the complete graph on `{0,1,2,3}` with the single
    (unordered) edge `{p, q}` deleted.  When `{p,q}` is an actual edge of K₄ this
    is the "diamond" `K₄⁻`, a maximal proper subgraph of K₄. -/
def K4MinusEdge (p q : ℕ) : SimpleGraph ℕ where
  Adj u v := (completeGraphN 4).Adj u v ∧ ¬ ((u = p ∧ v = q) ∨ (u = q ∧ v = p))
  symm := by
    rintro u v ⟨h1, h2⟩
    exact ⟨h1.symm, fun h => h2 (by tauto)⟩
  loopless := by
    rintro u ⟨h1, -⟩
    exact (completeGraphN 4).loopless u h1

@[simp] theorem K4MinusEdge_adj (p q u v : ℕ) :
    (K4MinusEdge p q).Adj u v ↔
      (completeGraphN 4).Adj u v ∧ ¬ ((u = p ∧ v = q) ∨ (u = q ∧ v = p)) :=
  Iff.rfl

/-- `K₄ − e ≤ K₄`: deleting an edge only removes adjacencies. -/
theorem K4MinusEdge_le (p q : ℕ) : K4MinusEdge p q ≤ completeGraphN 4 := by
  intro a b hab
  exact hab.1

/- ## Every proper subgraph of K₄ omits an edge -/

/-- A proper subgraph of K₄ fails to contain at least one edge of K₄: otherwise it
    would contain every edge of K₄ and, being ≤ K₄, would equal K₄. -/
theorem properSubgraph_missing_edge {H : SimpleGraph ℕ}
    (hH : isProperSubgraph H (completeGraphN 4)) :
    ∃ p q, (completeGraphN 4).Adj p q ∧ ¬ H.Adj p q := by
  obtain ⟨hle, hne⟩ := hH
  by_contra hcon
  push_neg at hcon
  exact hne (le_antisymm hle fun a b hab => hcon a b hab)

/-- Consequently every proper subgraph `H ⊊ K₄` is contained in some `K₄ − e`. -/
theorem properSubgraph_le_K4MinusEdge {H : SimpleGraph ℕ}
    (hH : isProperSubgraph H (completeGraphN 4)) :
    ∃ p q, (completeGraphN 4).Adj p q ∧ H ≤ K4MinusEdge p q := by
  obtain ⟨p, q, hpq, hnpq⟩ := properSubgraph_missing_edge hH
  refine ⟨p, q, hpq, ?_⟩
  intro a b hab
  refine ⟨hH.1 hab, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact hnpq hab
  · exact hnpq hab.symm

/-- Each edge-deleted graph `K₄ − e` is itself a *proper* subgraph of K₄
    (it is strictly smaller, having lost the edge `{p,q}`). -/
theorem K4MinusEdge_properSubgraph {p q : ℕ} (hpq : (completeGraphN 4).Adj p q) :
    isProperSubgraph (K4MinusEdge p q) (completeGraphN 4) := by
  refine ⟨K4MinusEdge_le p q, ?_⟩
  intro h
  have hiff : (K4MinusEdge p q).Adj p q ↔ (completeGraphN 4).Adj p q := by rw [h]
  exact (hiff.mpr hpq).2 (Or.inl ⟨rfl, rfl⟩)

/- ## The finite-check reduction -/

/-- **Concrete finite check.**  The parent file's sweeping axiom
    `K4_subgraphs_linear` — size-linearity of *every* proper subgraph of K₄ — is a
    consequence of size-linearity of just the six edge-deleted graphs `K₄ − e`,
    together with the heredity axiom `ramsey_linear_hereditary`.

    This trades an assumption quantified over infinitely many `H : SimpleGraph ℕ`
    for a finite family indexed by the edges of K₄ (all six mutually isomorphic),
    which is the natural minimal hypothesis for the K₄ minimality claim. -/
theorem K4_subgraphs_linear_of_edgeDeleted
    (hdiamond : ∀ p q, (completeGraphN 4).Adj p q → isRamseySizeLinear (K4MinusEdge p q)) :
    ∀ H : SimpleGraph ℕ, isProperSubgraph H (completeGraphN 4) → isRamseySizeLinear H := by
  intro H hH
  obtain ⟨p, q, hpq, hle⟩ := properSubgraph_le_K4MinusEdge hH
  by_cases heq : H = K4MinusEdge p q
  · rw [heq]; exact hdiamond p q hpq
  · exact ramsey_linear_hereditary (K4MinusEdge p q) H ⟨hle, heq⟩ (hdiamond p q hpq)

/-- Restating the parent's minimality theorem `K4_is_minimal` from the reduced
    hypothesis: K₄ is minimally non-Ramsey-size-linear provided only that it is
    itself superlinear and each of its six edge-deleted graphs is size-linear. -/
theorem K4_is_minimal_of_edgeDeleted
    (hsuper : isRamseySizeSuperlinear (completeGraphN 4))
    (hdiamond : ∀ p q, (completeGraphN 4).Adj p q → isRamseySizeLinear (K4MinusEdge p q)) :
    isMinimallyNonLinear (completeGraphN 4) :=
  ⟨hsuper, K4_subgraphs_linear_of_edgeDeleted hdiamond⟩

end Erdos79Incomplete01
