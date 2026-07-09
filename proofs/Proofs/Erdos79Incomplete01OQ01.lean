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

end Erdos79Incomplete01OQ01
