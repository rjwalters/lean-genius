/-
  Erdős Problem #79 — Companion (incomplete-01 · OQ01):
  Grounding the heredity axiom and the iso-invariance hypothesis in two ATOMIC
  structural properties of the primitive Ramsey number.

  The parent file `Erdos79Problem.lean` treats size-linearity heredity as a
  standalone axiom

      ramsey_linear_hereditary :
        isProperSubgraph H G → isRamseySizeLinear G → isRamseySizeLinear H

  and the sibling companion `Erdos79Incomplete01.lean` reduces the sweeping
  subgraph axiom to a single diamond `K₄ − {0,1}` but must carry an *explicit
  hypothesis* `hcongr` (iso-invariance of size-linearity) in its sharpest
  statement `K4_subgraphs_linear_of_single`, remarking that over the opaque
  `ramseyNumber` neither heredity nor iso-invariance can be derived.

  Both of those are meta-level assumptions about the *derived* predicate
  `isRamseySizeLinear`.  This file shows they are not independent: each is a
  one-step consequence of the corresponding ATOMIC property of the primitive
  `ramseyNumber` itself, namely

    • `ramseyNumber_mono_left`  — `G ≤ G' → R(G,·) ≤ R(G',·)`
        (a red copy of the larger `G'` contains one of the smaller `G`;
         Ramsey numbers are monotone in each argument), and
    • `ramseyNumber_congr_left` — `(G ≃g G') → R(G,·) = R(G',·)`
        (`R` depends only on the isomorphism type of its arguments).

  These are the two textbook facts that any honest definition of `ramseyNumber`
  satisfies; here they replace the bespoke `ramsey_linear_hereditary` /`hcongr`
  assumptions with canonical primitive-level ones.  From them we DERIVE (0 sorry):

    • `isRamseySizeLinear_hereditary` — heredity, now a theorem (was the parent
        axiom `ramsey_linear_hereditary`).
    • `isRamseySizeLinear_congr` — iso-invariance, now a theorem (was the
        companion's `hcongr` hypothesis).

  and re-derive the companion's flagship reduction using them, so that

    • `K4_is_minimal_from_single_diamond` : the minimality of K₄ follows from
        just K₄'s own superlinearity and the size-linearity of the SINGLE
        diamond `K₄ − {0,1}` — with heredity and iso-invariance no longer
        assumed but proved, and with NO dependence on the parent's
        `ramsey_linear_hereditary` or `K4_subgraphs_linear` axioms
        (see the `#print axioms` check at the end).

  Honest accounting.  This does NOT reduce the assumption count: the two atomic
  Ramsey properties are themselves axioms over the opaque `ramseyNumber` (the
  real content — that `R(K₄−e, H) = O(e(H))` — needs Ramsey theory beyond
  Mathlib).  The contribution is structural: the two size-linearity meta-axioms
  are shown to be *consequences* of the canonical monotonicity/iso-invariance of
  the Ramsey number, and become machine-checked theorems.

  Reference: https://erdosproblems.com/79
-/

import Mathlib
import Proofs.Erdos79Incomplete01

namespace Erdos79Incomplete01OQ01

open SimpleGraph
open Erdos79
open Erdos79Incomplete01

/- ## The two atomic structural properties of the primitive Ramsey number -/

/-- **Monotonicity of the Ramsey number in its first argument.**  If `G ≤ G'`
    (same host `ℕ`, `G` has a subset of `G'`'s adjacencies) then
    `R(G, K) ≤ R(G', K)` for every `K`: any 2-colouring of `K_n` that yields a
    red `G'` yields a red `G ≤ G'`, so a colouring witnessing `R(G', K)` also
    witnesses `R(G, K)`.  True for any concrete Ramsey number; kept as an axiom
    here only because `ramseyNumber` is opaque. -/
axiom ramseyNumber_mono_left (G G' K : SimpleGraph ℕ) :
    G ≤ G' → ramseyNumber G K ≤ ramseyNumber G' K

/-- **Isomorphism-invariance of the Ramsey number in its first argument.**  A
    graph isomorphism `G ≃g G'` (a relabelling of vertices) leaves the Ramsey
    number unchanged: `R(G, K) = R(G', K)`.  `R` depends only on the
    isomorphism type of its arguments.  Again true for any concrete Ramsey
    number; an axiom here only because `ramseyNumber` is opaque. -/
axiom ramseyNumber_congr_left (G G' K : SimpleGraph ℕ) :
    (G ≃g G') → ramseyNumber G K = ramseyNumber G' K

/- ## Heredity and iso-invariance of size-linearity, now derived -/

/-- **Heredity as a theorem.**  Size-linearity passes to smaller graphs: if
    `H ≤ G` and `G` is Ramsey size-linear then so is `H`, with the *same*
    linearity constant.  Derived from `ramseyNumber_mono_left` — this is the
    parent's `ramsey_linear_hereditary`, no longer assumed. -/
theorem isRamseySizeLinear_hereditary {G H : SimpleGraph ℕ}
    (hsub : H ≤ G) (h : isRamseySizeLinear G) : isRamseySizeLinear H := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun K hK => ?_⟩
  have hmono : ramseyNumber H K ≤ ramseyNumber G K := ramseyNumber_mono_left H G K hsub
  calc (ramseyNumber H K : ℝ)
      ≤ (ramseyNumber G K : ℝ) := by exact_mod_cast hmono
    _ ≤ C * edgeCount K := hbound K hK

/-- The parent-shaped restatement, on `isProperSubgraph` (recovering the exact
    signature of the parent axiom `ramsey_linear_hereditary`, now proved). -/
theorem ramsey_linear_hereditary_proved (G H : SimpleGraph ℕ)
    (hH : isProperSubgraph H G) (h : isRamseySizeLinear G) : isRamseySizeLinear H :=
  isRamseySizeLinear_hereditary hH.1 h

/-- **Iso-invariance as a theorem.**  Size-linearity is invariant under graph
    isomorphism, with the same linearity constant.  Derived from
    `ramseyNumber_congr_left` — this is the companion's `hcongr`, no longer an
    explicit hypothesis. -/
theorem isRamseySizeLinear_congr {G G' : SimpleGraph ℕ} (e : G ≃g G')
    (h : isRamseySizeLinear G) : isRamseySizeLinear G' := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun H hH => ?_⟩
  have hb := hbound H hH
  rwa [ramseyNumber_congr_left G G' H e] at hb

/- ## The flagship reduction, re-derived without assuming heredity or hcongr -/

/-- Size-linearity of every proper subgraph of K₄ follows from that of the six
    edge-deleted diamonds — using the *derived* heredity, not the parent axiom.
    (Cleaner than the companion's version: `isRamseySizeLinear_hereditary` is
    stated for `≤`, so the `H = K₄ − e` and `H ⊊ K₄ − e` cases merge.) -/
theorem K4_subgraphs_linear_of_edgeDeleted'
    (hdiamond : ∀ p q, (completeGraphN 4).Adj p q → isRamseySizeLinear (K4MinusEdge p q)) :
    ∀ H : SimpleGraph ℕ, isProperSubgraph H (completeGraphN 4) → isRamseySizeLinear H := by
  intro H hH
  obtain ⟨p, q, hpq, hle⟩ := properSubgraph_le_K4MinusEdge hH
  exact isRamseySizeLinear_hereditary hle (hdiamond p q hpq)

/-- Size-linearity of every proper subgraph of K₄ follows from that of the
    SINGLE diamond `K₄ − {0,1}` — using the *derived* iso-invariance
    (`isRamseySizeLinear_congr`) to transport it across the six isomorphic
    diamonds, with no `hcongr` hypothesis. -/
theorem K4_subgraphs_linear_of_single'
    (h01 : isRamseySizeLinear (K4MinusEdge 0 1)) :
    ∀ H : SimpleGraph ℕ, isProperSubgraph H (completeGraphN 4) → isRamseySizeLinear H := by
  apply K4_subgraphs_linear_of_edgeDeleted'
  rw [hdiamond_iff_six]
  exact ⟨h01,
    isRamseySizeLinear_congr diamond_iso_02 h01,
    isRamseySizeLinear_congr diamond_iso_03 h01,
    isRamseySizeLinear_congr diamond_iso_12 h01,
    isRamseySizeLinear_congr diamond_iso_13 h01,
    isRamseySizeLinear_congr diamond_iso_23 h01⟩

/-- **K₄ is minimally non-Ramsey-size-linear from a single diamond.**  Given
    only that K₄ is itself superlinear and that the one diamond `K₄ − {0,1}` is
    size-linear, K₄ is minimally non-linear.  Heredity and iso-invariance are
    *derived* (from `ramseyNumber_mono_left` / `ramseyNumber_congr_left`), not
    assumed; there is no dependence on the parent's `ramsey_linear_hereditary`
    or `K4_subgraphs_linear` axioms. -/
theorem K4_is_minimal_of_single'
    (hsuper : isRamseySizeSuperlinear (completeGraphN 4))
    (h01 : isRamseySizeLinear (K4MinusEdge 0 1)) :
    isMinimallyNonLinear (completeGraphN 4) :=
  ⟨hsuper, K4_subgraphs_linear_of_single' h01⟩

/-- Fully assembled with the parent's own superlinearity axiom `K4_not_linear`:
    the ONLY remaining input to K₄'s minimality (beyond the two atomic Ramsey
    properties) is the size-linearity of a single diamond `K₄ − {0,1}`. -/
theorem K4_is_minimal_from_single_diamond
    (h01 : isRamseySizeLinear (K4MinusEdge 0 1)) :
    isMinimallyNonLinear (completeGraphN 4) :=
  K4_is_minimal_of_single' K4_not_linear h01

/- ## Iso-invariance of superlinearity and of minimal non-linearity

   Erdős #79 asks whether there are infinitely many minimally non-linear graphs
   *up to isomorphism* (`erdos_79_question := minimalNonLinearGraphs.Infinite`),
   yet the whole gallery formalisation works with concrete graphs on the fixed
   vertex set `ℕ`.  For that count to be meaningful, the defining predicate
   `isMinimallyNonLinear` must be an isomorphism invariant.  We prove it is —
   grounded, like heredity and iso-invariance of size-linearity above, in the
   two atomic Ramsey properties alone (via `isRamseySizeLinear_congr`), with no
   new axioms. -/

/-- **Superlinearity is iso-invariant.**  The negation of an iso-invariant
    predicate is iso-invariant: transport size-linearity back along `e.symm`. -/
theorem isRamseySizeSuperlinear_congr {G G' : SimpleGraph ℕ} (e : G ≃g G')
    (h : isRamseySizeSuperlinear G) : isRamseySizeSuperlinear G' :=
  fun h' => h (isRamseySizeLinear_congr e.symm h')

/-- Relabelling `H'` by the isomorphism `e : G ≃g G'` (i.e. `SimpleGraph.comap ⇑e H'`)
    produces a graph isomorphic to `H'`: the bijection is `e` itself, and
    adjacency matches by the very definition of `comap`. -/
def comapIso {G G' : SimpleGraph ℕ} (e : G ≃g G') (H' : SimpleGraph ℕ) :
    SimpleGraph.comap ⇑e H' ≃g H' where
  toEquiv := e.toEquiv
  map_rel_iff' := Iff.rfl

/-- Pulling `G'` itself back along `e : G ≃g G'` returns `G`: `comap ⇑e G' = G`.
    This is just the defining property of an isomorphism. -/
theorem comap_self {G G' : SimpleGraph ℕ} (e : G ≃g G') :
    SimpleGraph.comap ⇑e G' = G := by
  ext a b
  simp only [SimpleGraph.comap_adj]
  exact e.map_rel_iff

/-- A proper subgraph `H' ⊊ G'` pulls back along `e : G ≃g G'` to a proper
    subgraph `comap ⇑e H' ⊊ G`.  Monotone (edges of `H'` map to edges of `G`)
    and proper (`comap ⇑e` is injective, so `comap ⇑e H' = G = comap ⇑e G'`
    would force `H' = G'`). -/
theorem comap_properSubgraph {G G' H' : SimpleGraph ℕ} (e : G ≃g G')
    (hH' : isProperSubgraph H' G') :
    isProperSubgraph (SimpleGraph.comap ⇑e H') G := by
  refine ⟨?_, ?_⟩
  · -- monotonicity: comap ⇑e H' ≤ G
    intro a b hab
    rw [SimpleGraph.comap_adj] at hab
    exact e.map_rel_iff.mp (hH'.1 hab)
  · -- properness: if `comap ⇑e H' = G` then `H' = G'`, contradicting `hH'.2`
    intro hEq
    apply hH'.2
    ext a' b'
    -- evaluate `hEq` at the preimages `e.symm a', e.symm b'`
    have key := congrArg (fun g : SimpleGraph ℕ => g.Adj (e.symm a') (e.symm b')) hEq
    simp only [SimpleGraph.comap_adj, RelIso.apply_symm_apply] at key
    -- `key : H'.Adj a' b' = G.Adj (e.symm a') (e.symm b')`
    -- and `hmap : G'.Adj a' b' ↔ G.Adj (e.symm a') (e.symm b')`
    have hmap := e.map_rel_iff (a := e.symm a') (b := e.symm b')
    simp only [RelIso.apply_symm_apply] at hmap
    rw [iff_of_eq key]
    exact hmap.symm

/-- **Minimal non-linearity is an isomorphism invariant.**  If `G ≃g G'` and
    `G` is minimally non-Ramsey-size-linear, then so is `G'`.  Both clauses
    transport: superlinearity via `isRamseySizeSuperlinear_congr`, and
    "every proper subgraph is linear" by pulling each proper subgraph `H' ⊊ G'`
    back to a proper subgraph `comap ⇑e H' ⊊ G` (linear by hypothesis) and
    pushing linearity forward across the iso `comap ⇑e H' ≃g H'`.  Derived from
    the two atomic Ramsey properties only — no new axioms. -/
theorem isMinimallyNonLinear_congr {G G' : SimpleGraph ℕ} (e : G ≃g G')
    (h : isMinimallyNonLinear G) : isMinimallyNonLinear G' := by
  obtain ⟨hsuper, hsub⟩ := h
  refine ⟨isRamseySizeSuperlinear_congr e hsuper, ?_⟩
  intro H' hH'
  have hlin : isRamseySizeLinear (SimpleGraph.comap ⇑e H') :=
    hsub _ (comap_properSubgraph e hH')
  exact isRamseySizeLinear_congr (comapIso e H') hlin

/-- The invariant set `minimalNonLinearGraphs` is closed under isomorphism:
    membership depends only on the isomorphism type.  A direct restatement of
    `isMinimallyNonLinear_congr` on the parent's set `minimalNonLinearGraphs`. -/
theorem minimalNonLinearGraphs_iso_closed {G G' : SimpleGraph ℕ} (e : G ≃g G')
    (hG : G ∈ minimalNonLinearGraphs) : G' ∈ minimalNonLinearGraphs :=
  isMinimallyNonLinear_congr e hG

/- Verified axiom basis (`#print axioms K4_is_minimal_from_single_diamond`):

     [propext, Classical.choice, Quot.sound,
      Erdos79.K4_not_linear,
      Erdos79Incomplete01OQ01.ramseyNumber_congr_left,
      Erdos79Incomplete01OQ01.ramseyNumber_mono_left]

   i.e. only the two atomic Ramsey properties of this file, K₄'s own
   superlinearity `K4_not_linear`, and the ordinary foundational axioms — and
   NOT the parent's `ramsey_linear_hereditary` or `K4_subgraphs_linear`
   (heredity and iso-invariance are derived here, not assumed).  The primitive
   `ramseyNumber` is `opaque`, so it is irreducible but does not itself appear
   in `#print axioms`. -/
-- #print axioms K4_is_minimal_from_single_diamond

/- Iso-invariance of minimal non-linearity has an even leaner basis
   (`#print axioms isMinimallyNonLinear_congr`):

     [propext, Classical.choice, Quot.sound,
      Erdos79Incomplete01OQ01.ramseyNumber_congr_left]

   i.e. only the single ATOMIC *congruence* property of the Ramsey number
   (monotonicity `ramseyNumber_mono_left` is not even needed) plus the ordinary
   foundational axioms.  So "minimally non-linear" being an isomorphism
   invariant — the well-posedness of Erdős #79's count of such graphs up to
   isomorphism (`minimalNonLinearGraphs.Infinite`) — reduces to nothing more
   than: the Ramsey number depends only on the isomorphism type of its first
   argument. -/
-- #print axioms isMinimallyNonLinear_congr

end Erdos79Incomplete01OQ01
