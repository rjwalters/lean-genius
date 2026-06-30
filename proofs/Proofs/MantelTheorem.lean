/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Mantel's Theorem (Maximum Edges in Triangle-Free Graphs)

Mantel's theorem (1907), the founding result of extremal graph theory and the `r = 2`
base case of Turán's theorem, states:

> A simple graph on `n` vertices with no triangle (`K₃`-free, i.e. `CliqueFree 3`) has at
> most `⌊n²/4⌋` edges, and the bound is attained by the balanced complete bipartite graph.

## Approach

Mathlib's `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan` develops Turán's theorem in full
generality. The general edge bound `SimpleGraph.CliqueFree.card_edgeFinset_le` specializes at
`r = 2` to

  `#G.edgeFinset ≤ (n² - (n % 2)²) · (2 - 1) / (2 · 2) + (n % 2).choose 2`

with `n = Fintype.card V`. The arithmetic identity `turan_two_simp` collapses that right-hand
side to the clean floor `n² / 4`, giving Mantel's bound (`mantel_card_edgeFinset_le`).

Sharpness is witnessed by `SimpleGraph.turanGraph n 2` — the canonical triangle-free graph —
whose edge count is exactly `n² / 4` (`card_edgeFinset_turanGraph_two`), so the bound is tight
(`mantel_bound_is_tight`).

The equality *characterization* (equality holds iff `G` is the balanced complete bipartite
graph) follows from `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph` but is not packaged
here; see the gallery notes for that future direction.
-/

open Finset Fintype SimpleGraph

namespace Mantel

/-- The Turán right-hand side at `r = 2` collapses to the floor `n² / 4`.

Concretely `(n² - (n % 2)²) · (2 - 1) / (2 · 2) + (n % 2).choose 2 = n² / 4`: the binomial term
vanishes because `n % 2 < 2`, and `n² - (n % 2)²` is a multiple of `4` equal to `n²` rounded
down. -/
theorem turan_two_simp (n : ℕ) :
    (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 = n ^ 2 / 4 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  have hc : (n % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt hlt
  have hB : (n % 2) ^ 2 < 4 := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> norm_num
  have hdecomp : n ^ 2 = 4 * ((n / 2) ^ 2 + (n / 2) * (n % 2)) + (n % 2) ^ 2 := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    ring
  rw [hc, add_zero, show (2 : ℕ) - 1 = 1 from rfl, mul_one, show (2 : ℕ) * 2 = 4 from rfl]
  omega

/-- **Mantel's theorem (edge bound).** A triangle-free (`K₃`-free) simple graph on `n` vertices
has at most `⌊n²/4⌋` edges. -/
theorem mantel_card_edgeFinset_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  have hb := CliqueFree.card_edgeFinset_le (r := 2) (G := G) h
  exact le_trans hb (le_of_eq (turan_two_simp _))

/-- The canonical Turán graph `turanGraph n 2` is triangle-free. -/
theorem turanGraph_two_cliqueFree (n : ℕ) : (turanGraph n 2).CliqueFree 3 :=
  turanGraph_cliqueFree (by norm_num)

/-- The Turán graph `turanGraph n 2` (balanced complete bipartite graph on `n` vertices) has
exactly `⌊n²/4⌋` edges. -/
theorem card_edgeFinset_turanGraph_two (n : ℕ) :
    (turanGraph n 2).edgeFinset.card = n ^ 2 / 4 := by
  rw [card_edgeFinset_turanGraph]
  exact turan_two_simp n

/-- **Sharpness of Mantel's bound.** For every `n` there is a triangle-free graph on `n`
vertices attaining `⌊n²/4⌋` edges, so the bound in `mantel_card_edgeFinset_le` cannot be
improved. -/
theorem mantel_bound_is_tight (n : ℕ) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.CliqueFree 3 ∧ G.edgeFinset.card = n ^ 2 / 4 :=
  ⟨turanGraph n 2, inferInstance, turanGraph_two_cliqueFree n, card_edgeFinset_turanGraph_two n⟩

end Mantel
