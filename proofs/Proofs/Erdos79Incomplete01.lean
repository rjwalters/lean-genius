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

/- ## Making the finite check literal: the six named edges -/

/-- Unfolding lemma for the complete-graph adjacency (definitional, but convenient
    for `simp`). -/
theorem completeGraphN_adj (n u v : ℕ) :
    (completeGraphN n).Adj u v ↔ u ≠ v ∧ u < n ∧ v < n := Iff.rfl

/-- Deleting the edge `{p,q}` is symmetric in `p` and `q`: `K₄ − {p,q} = K₄ − {q,p}`.
    (The deletion predicate `¬((u=p∧v=q)∨(u=q∧v=p))` is symmetric under swapping
    `p` and `q`, so the two graphs are literally equal.) -/
theorem K4MinusEdge_comm (p q : ℕ) : K4MinusEdge p q = K4MinusEdge q p := by
  ext u v
  simp only [K4MinusEdge_adj]
  tauto

/-- **The finite check, made literal.**  The edge-deleted hypothesis
    `hdiamond` — quantified over the (infinitely many, but adjacency-constrained)
    pairs `p q` — is equivalent to the *explicit* six-fold conjunction over the
    six edges `{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}` of K₄.  This is the
    concrete finite check in its sharpest closed form: no quantifier over
    `SimpleGraph ℕ` and no quantifier over vertices remains. -/
theorem hdiamond_iff_six :
    (∀ p q, (completeGraphN 4).Adj p q → isRamseySizeLinear (K4MinusEdge p q)) ↔
      isRamseySizeLinear (K4MinusEdge 0 1) ∧ isRamseySizeLinear (K4MinusEdge 0 2) ∧
      isRamseySizeLinear (K4MinusEdge 0 3) ∧ isRamseySizeLinear (K4MinusEdge 1 2) ∧
      isRamseySizeLinear (K4MinusEdge 1 3) ∧ isRamseySizeLinear (K4MinusEdge 2 3) := by
  constructor
  · intro h
    exact ⟨h 0 1 ⟨by decide, by decide, by decide⟩, h 0 2 ⟨by decide, by decide, by decide⟩,
           h 0 3 ⟨by decide, by decide, by decide⟩, h 1 2 ⟨by decide, by decide, by decide⟩,
           h 1 3 ⟨by decide, by decide, by decide⟩, h 2 3 ⟨by decide, by decide, by decide⟩⟩
  · rintro ⟨h01, h02, h03, h12, h13, h23⟩ p q ⟨hne, hp, hq⟩
    interval_cases p <;> interval_cases q <;>
      first
        | exact absurd rfl hne
        | assumption
        | (rw [K4MinusEdge_comm]; assumption)

/- ## The sharp reduction: six edges to one, via edge-transitivity of K₄ -/

/-- **Relabelling isomorphism.**  Any permutation `σ` of `ℕ` that preserves the
    predicate `· < 4` (equivalently, permutes the vertex set `{0,1,2,3}` of K₄
    among itself and fixes the rest) carries `K₄ − {p,q}` isomorphically onto
    `K₄ − {σ p, σ q}`.  This is the mechanism behind the edge-transitivity of K₄:
    all six diamonds are graph-isomorphic. -/
noncomputable def diamondEquiv (σ : ℕ ≃ ℕ) (hσ : ∀ u, σ u < 4 ↔ u < 4) (p q : ℕ) :
    K4MinusEdge p q ≃g K4MinusEdge (σ p) (σ q) where
  toEquiv := σ
  map_rel_iff' := by
    intro a b
    simp only [K4MinusEdge_adj, completeGraphN_adj, ne_eq,
      EmbeddingLike.apply_eq_iff_eq, hσ]

/-- A transposition of two vertices below 4 preserves the predicate `· < 4`. -/
theorem swap_lt_four {a b : ℕ} (ha : a < 4) (hb : b < 4) (u : ℕ) :
    (Equiv.swap a b) u < 4 ↔ u < 4 := by
  rcases eq_or_ne u a with rfl | hua
  · rw [Equiv.swap_apply_left]; omega
  · rcases eq_or_ne u b with rfl | hub
    · rw [Equiv.swap_apply_right]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne hua hub]

/-- The `· < 4`-preserving property is closed under composition of permutations. -/
theorem comp_lt_four {σ τ : Equiv.Perm ℕ}
    (hσ : ∀ u, σ u < 4 ↔ u < 4) (hτ : ∀ u, τ u < 4 ↔ u < 4) (u : ℕ) :
    (σ * τ) u < 4 ↔ u < 4 := by
  rw [Equiv.Perm.mul_apply, hσ, hτ]

/-- Convenience: the `· < 4`-preservation hypothesis for a single transposition. -/
private theorem swap4 {a b : ℕ} (ha : a < 4) (hb : b < 4) :
    ∀ u, (Equiv.swap a b) u < 4 ↔ u < 4 := fun u => swap_lt_four ha hb u

/- The five relabelling isomorphisms carrying the reference diamond `K₄ − {0,1}`
   onto each of the other five diamonds.  Each permutation sends `0 ↦ p`, `1 ↦ q`
   while permuting `{0,1,2,3}` among itself — an explicit witness to S₄'s transitive
   action on the edges of K₄. -/

/-- `K₄ − {0,1} ≃g K₄ − {0,2}` via the transposition `(1 2)`. -/
noncomputable def diamond_iso_02 : K4MinusEdge 0 1 ≃g K4MinusEdge 0 2 := by
  have iso := diamondEquiv (Equiv.swap 1 2) (swap4 (by omega) (by omega)) 0 1
  simpa only [show (Equiv.swap 1 2) 0 = 0 from by decide,
    show (Equiv.swap 1 2) 1 = 2 from by decide] using iso

/-- `K₄ − {0,1} ≃g K₄ − {0,3}` via the transposition `(1 3)`. -/
noncomputable def diamond_iso_03 : K4MinusEdge 0 1 ≃g K4MinusEdge 0 3 := by
  have iso := diamondEquiv (Equiv.swap 1 3) (swap4 (by omega) (by omega)) 0 1
  simpa only [show (Equiv.swap 1 3) 0 = 0 from by decide,
    show (Equiv.swap 1 3) 1 = 3 from by decide] using iso

/-- `K₄ − {0,1} ≃g K₄ − {1,2}` via `(0 1)(1 2)` (a 3-cycle on `{0,1,2}`). -/
noncomputable def diamond_iso_12 : K4MinusEdge 0 1 ≃g K4MinusEdge 1 2 := by
  have iso := diamondEquiv (Equiv.swap 0 1 * Equiv.swap 1 2)
    (fun u => comp_lt_four (swap4 (by omega) (by omega)) (swap4 (by omega) (by omega)) u) 0 1
  simpa only [show ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm ℕ)) 0 = 1 from by decide,
    show ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm ℕ)) 1 = 2 from by decide] using iso

/-- `K₄ − {0,1} ≃g K₄ − {1,3}` via `(0 1)(1 3)`. -/
noncomputable def diamond_iso_13 : K4MinusEdge 0 1 ≃g K4MinusEdge 1 3 := by
  have iso := diamondEquiv (Equiv.swap 0 1 * Equiv.swap 1 3)
    (fun u => comp_lt_four (swap4 (by omega) (by omega)) (swap4 (by omega) (by omega)) u) 0 1
  simpa only [show ((Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm ℕ)) 0 = 1 from by decide,
    show ((Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm ℕ)) 1 = 3 from by decide] using iso

/-- `K₄ − {0,1} ≃g K₄ − {2,3}` via `(0 2)(1 3)`. -/
noncomputable def diamond_iso_23 : K4MinusEdge 0 1 ≃g K4MinusEdge 2 3 := by
  have iso := diamondEquiv (Equiv.swap 0 2 * Equiv.swap 1 3)
    (fun u => comp_lt_four (swap4 (by omega) (by omega)) (swap4 (by omega) (by omega)) u) 0 1
  simpa only [show ((Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm ℕ)) 0 = 2 from by decide,
    show ((Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm ℕ)) 1 = 3 from by decide] using iso

/-- **The sharpest reduction: six edges to one.**  Granting only the natural
    meta-principle that Ramsey size-linearity is invariant under graph isomorphism
    (`hcongr` — *not* an axiom, but an explicit hypothesis: over the opaque
    `ramseyNumber` it cannot be derived), the parent's sweeping subgraph axiom
    `K4_subgraphs_linear` follows from size-linearity of a **single** diamond
    `K₄ − {0,1}`.  This is because all six diamonds are graph-isomorphic
    (`diamond_iso_02 … diamond_iso_23`): K₄ is edge-transitive. -/
theorem K4_subgraphs_linear_of_single
    (hcongr : ∀ G G' : SimpleGraph ℕ, (G ≃g G') → isRamseySizeLinear G → isRamseySizeLinear G')
    (h01 : isRamseySizeLinear (K4MinusEdge 0 1)) :
    ∀ H : SimpleGraph ℕ, isProperSubgraph H (completeGraphN 4) → isRamseySizeLinear H := by
  apply K4_subgraphs_linear_of_edgeDeleted
  rw [hdiamond_iff_six]
  exact ⟨h01,
    hcongr _ _ diamond_iso_02 h01, hcongr _ _ diamond_iso_03 h01,
    hcongr _ _ diamond_iso_12 h01, hcongr _ _ diamond_iso_13 h01,
    hcongr _ _ diamond_iso_23 h01⟩

/-- K₄ is minimally non-Ramsey-size-linear from the **single-diamond** hypothesis:
    it suffices that K₄ is superlinear, that size-linearity is iso-invariant, and
    that the one diamond `K₄ − {0,1}` is size-linear. -/
theorem K4_is_minimal_of_single
    (hsuper : isRamseySizeSuperlinear (completeGraphN 4))
    (hcongr : ∀ G G' : SimpleGraph ℕ, (G ≃g G') → isRamseySizeLinear G → isRamseySizeLinear G')
    (h01 : isRamseySizeLinear (K4MinusEdge 0 1)) :
    isMinimallyNonLinear (completeGraphN 4) :=
  ⟨hsuper, K4_subgraphs_linear_of_single hcongr h01⟩

end Erdos79Incomplete01
