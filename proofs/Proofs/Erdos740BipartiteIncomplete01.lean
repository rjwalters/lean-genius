import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-!
# Erdős #740 (incomplete-01): the bipartite (`r = ∞`) case, done with real chromatic numbers

Erdős Problem #740 asks: if `G` has chromatic number `𝔪` (an infinite cardinal) and
`r ≥ 1`, must `G` contain a subgraph of chromatic number `𝔪` with **no odd cycle of
length `≤ r`**? Rödl proved the case `𝔪 = ℵ₀`, `r = 3`; the general case is open.

The existing gallery formalization (`Erdos740Problem.lean`) builds on a *placeholder*
chromatic number (`chromaticNumber V G := Cardinal.mk V`), so its statements — including
the open `no_infinite_bipartite` `sorry` — are not about the real invariant. This file
replaces that fragment with an honest, fully proved result using **Mathlib's genuine
`SimpleGraph.chromaticNumber`** (`ℕ∞`-valued) and `SimpleGraph.IsBipartite` (`= Colorable 2`).

The limiting case `r = ∞` of #740 is "no odd cycle of *any* length", i.e. the subgraph is
**bipartite**. We prove this case of #740 *fails*: a bipartite graph is `2`-colorable, so
it has chromatic number `≤ 2`; hence whenever `χ(G) > 2`, **no** induced bipartite subgraph
can realize `χ(G)`. (This matches what the placeholder file's `no_infinite_bipartite`
intended to say, but here it is a real theorem.)

## Main results

* `induce_chromaticNumber_le` : `χ(G.induce s) ≤ χ(G)` — induced subgraphs never raise `χ`.
* `bipartite_chromaticNumber_le_two` : a bipartite graph has `χ ≤ 2`.
* `no_bipartite_induced_realizes_chromatic` : if `χ(G) > 2` then no induced bipartite
  subgraph has `χ` equal to `χ(G)` — the `r = ∞` case of Erdős #740 fails.
* `triangle_chromaticNumber` / `triangle_has_no_bipartite_realization` : the triangle `K₃`
  (`χ = 3 > 2`) is an explicit, non-vacuous witness.
* `completeGraph_has_no_bipartite_realization` : the same for every `Kₙ`, `n ≥ 3`.
-/

namespace Erdos740Bipartite

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Induced-subgraph monotonicity.** The chromatic number of an induced subgraph never
    exceeds that of the ambient graph: any proper colouring of `G` restricts along the
    inclusion `G.induce s ↪g G` to one of `G.induce s`. -/
theorem induce_chromaticNumber_le (G : SimpleGraph V) (s : Set V) :
    (G.induce s).chromaticNumber ≤ G.chromaticNumber :=
  chromaticNumber_mono_of_hom (Embedding.induce s).toHom

/-- A bipartite graph (`IsBipartite := Colorable 2`) has chromatic number at most `2`. -/
theorem bipartite_chromaticNumber_le_two (h : G.IsBipartite) :
    G.chromaticNumber ≤ 2 := by
  simpa using h.chromaticNumber_le

/-- **The `r = ∞` (bipartite) case of Erdős #740 fails.**
    If `G` has chromatic number greater than `2`, then no induced *bipartite* subgraph of
    `G` realizes the chromatic number of `G`: a bipartite subgraph has `χ ≤ 2 < χ(G)`. -/
theorem no_bipartite_induced_realizes_chromatic (G : SimpleGraph V)
    (h : 2 < G.chromaticNumber) :
    ¬ ∃ s : Set V, (G.induce s).IsBipartite ∧
        (G.induce s).chromaticNumber = G.chromaticNumber := by
  rintro ⟨s, hbip, heq⟩
  have hle : G.chromaticNumber ≤ 2 := heq ▸ bipartite_chromaticNumber_le_two hbip
  exact absurd hle (not_le.mpr h)

/-- More generally, *any* bipartite induced subgraph has chromatic number `≤ 2`, regardless
    of the ambient graph — the structural obstruction behind the previous theorem. -/
theorem bipartite_induced_chromaticNumber_le_two (G : SimpleGraph V) (s : Set V)
    (h : (G.induce s).IsBipartite) : (G.induce s).chromaticNumber ≤ 2 :=
  bipartite_chromaticNumber_le_two h

-- ============================================================
-- Explicit witnesses: the bipartite case genuinely fails
-- ============================================================

/-- The triangle `K₃ = (⊤ : SimpleGraph (Fin 3))` has chromatic number `3`. -/
theorem triangle_chromaticNumber :
    (⊤ : SimpleGraph (Fin 3)).chromaticNumber = 3 := by
  rw [chromaticNumber_top]
  simp

/-- **Non-vacuous witness.** The triangle satisfies `χ > 2`, so by
    `no_bipartite_induced_realizes_chromatic` it has no bipartite induced subgraph of full
    chromatic number — concretely exhibiting the failure of the `r = ∞` case of #740. -/
theorem triangle_has_no_bipartite_realization :
    ¬ ∃ s : Set (Fin 3), ((⊤ : SimpleGraph (Fin 3)).induce s).IsBipartite ∧
        ((⊤ : SimpleGraph (Fin 3)).induce s).chromaticNumber =
          (⊤ : SimpleGraph (Fin 3)).chromaticNumber := by
  apply no_bipartite_induced_realizes_chromatic
  rw [triangle_chromaticNumber]
  decide

/-- The complete graph `Kₙ = (⊤ : SimpleGraph (Fin n))` has chromatic number `n`. -/
theorem completeGraph_chromaticNumber (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).chromaticNumber = n := by
  rw [chromaticNumber_top]
  simp

/-- **General witness.** For every `n ≥ 3` the complete graph `Kₙ` has `χ = n > 2`, so the
    bipartite (`r = ∞`) case of Erdős #740 fails for `Kₙ`: no bipartite induced subgraph
    realizes its chromatic number. -/
theorem completeGraph_has_no_bipartite_realization (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ s : Set (Fin n), ((⊤ : SimpleGraph (Fin n)).induce s).IsBipartite ∧
        ((⊤ : SimpleGraph (Fin n)).induce s).chromaticNumber =
          (⊤ : SimpleGraph (Fin n)).chromaticNumber := by
  apply no_bipartite_induced_realizes_chromatic
  rw [completeGraph_chromaticNumber]
  exact_mod_cast lt_of_lt_of_le (by norm_num) hn

end Erdos740Bipartite
