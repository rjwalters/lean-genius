/-
# Brouwer Fixed Point OQ-01-OQ-01: The 1D Sperner Lemma (Combinatorial IVT)

## Open Question (parent OQ-01, first sub-question)

OQ-01-OQ-01: "Prove 2D Brouwer via Sperner's Lemma — a fully elementary
combinatorial approach available in Lean 4."

## Scope and honest framing

Full 2D Brouwer via Sperner's lemma is a large formalization (simplicial
complexes, triangulations, vertex labelings, dimension-induction). Mathlib
currently has **no** Sperner's lemma of combinatorial topology (its
`Combinatorics.SetFamily` "Sperner" is the *antichain* theorem, unrelated).

This file formalizes the genuine combinatorial heart of that program: the
**1-dimensional Sperner lemma**, the base case of the dimension-induction and
the boundary-counting ingredient for the 2D version.

Concretely: color the vertices `0, 1, …, n` of a path by `c : ℕ → Bool`. An
edge `{i, i+1}` is *bichromatic* ("Sperner") when `c i ≠ c (i+1)`. Then:

* **`even_colorChanges_iff`** — the number of bichromatic edges has the same
  parity as `[c 0 ≠ c n]`: it is even iff the endpoints share a color. This is
  the discrete telescoping/parity identity.
* **`oddColorChanges_of_ne`** — if the endpoints differ, the count is **odd**.
* **`exists_sperner_edge`** — (1D Sperner lemma) a path from color `false` to
  color `true` has at least one bichromatic edge.

This is exactly the combinatorial shadow of the analytic IVT used in the
parent's 1D Brouwer proof: a discrete walk from region 0 to region 1 must cross
the boundary an odd — hence nonzero — number of times. Iterating this parity
count across dimensions is Sperner's lemma, and Sperner's lemma gives 2D
Brouwer. We do not claim 2D Brouwer here.

`0 sorries, 0 axioms.`
-/

import Mathlib

namespace BrouwerFixedPointOQ01OQ01

open Finset

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: BICHROMATIC EDGES OF A 1D COLORED PATH
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The set of bichromatic ("Sperner") edges `{i, i+1}` with `i < n`:
those whose two endpoints receive different colors under `c`. -/
def spernerEdges (c : ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (range n).filter (fun i => c i ≠ c (i + 1))

/-- The number of bichromatic edges among the first `n` edges of the path. -/
def colorChanges (c : ℕ → Bool) (n : ℕ) : ℕ :=
  (spernerEdges c n).card

/-- Recurrence: extending the path by one vertex adds a bichromatic edge iff
the new vertex differs in color from the previous one. -/
theorem colorChanges_succ (c : ℕ → Bool) (n : ℕ) :
    colorChanges c (n + 1)
      = colorChanges c n + (if c n = c (n + 1) then 0 else 1) := by
  unfold colorChanges spernerEdges
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : c n = c (n + 1)
  · -- new edge monochromatic: filter drops `n`
    rw [if_neg (by simpa using h), if_pos h, Nat.add_zero]
  · -- new edge bichromatic: filter inserts `n`, which is not already present
    rw [if_pos (by simpa using h), if_neg h,
        Finset.card_insert_of_notMem (by simp)]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: THE PARITY IDENTITY (DISCRETE TELESCOPING)

The parity of the bichromatic-edge count is determined entirely by the two
endpoint colors — every interior detail cancels. This is the discrete analogue
of "g changes sign an even number of times iff it ends where it started".
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Parity identity.** The number of bichromatic edges is even iff the two
endpoints of the path share a color. -/
theorem even_colorChanges_iff (c : ℕ → Bool) (n : ℕ) :
    Even (colorChanges c n) ↔ c 0 = c n := by
  induction n with
  | zero => simp [colorChanges, spernerEdges]
  | succ k ih =>
    rw [colorChanges_succ]
    by_cases h : c k = c (k + 1)
    · rw [if_pos h, Nat.add_zero, ih, h]
    · rw [if_neg h, Nat.even_add_one, ih]
      -- reduces to a Boolean tautology given `c k ≠ c (k+1)`
      revert h
      cases c 0 <;> cases c k <;> cases c (k + 1) <;> decide

/-- If the two endpoints differ, the number of bichromatic edges is **odd**. -/
theorem oddColorChanges_of_ne (c : ℕ → Bool) (n : ℕ) (h : c 0 ≠ c n) :
    Odd (colorChanges c n) := by
  rw [← Nat.not_even_iff_odd, even_colorChanges_iff]
  exact h

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: THE 1D SPERNER LEMMA (COMBINATORIAL IVT)

A path that starts in region `0` (`false`) and ends in region `1` (`true`)
must contain a bichromatic edge — the discrete intermediate value theorem.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **1D Sperner Lemma / Discrete IVT.** A 0/1-coloring of a path with
endpoints colored `false` and `true` has at least one bichromatic edge
`{i, i+1}` (`c i ≠ c (i+1)`). The parity identity makes the count odd, hence
positive, so the edge set is nonempty. -/
theorem exists_sperner_edge (c : ℕ → Bool) (n : ℕ)
    (h0 : c 0 = false) (hn : c n = true) :
    ∃ i < n, c i ≠ c (i + 1) := by
  have hne : c 0 ≠ c n := by rw [h0, hn]; decide
  have hodd : Odd (colorChanges c n) := oddColorChanges_of_ne c n hne
  have hpos : 0 < colorChanges c n :=
    Nat.pos_of_ne_zero (fun hz => by simp [hz] at hodd)
  unfold colorChanges spernerEdges at hpos
  rw [Finset.card_pos] at hpos
  obtain ⟨i, hi⟩ := hpos
  rw [Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨i, hi.1, hi.2⟩

/-- The number of bichromatic edges is in particular **positive** whenever the
endpoints differ — the quantitative form of the discrete IVT. -/
theorem colorChanges_pos_of_ne (c : ℕ → Bool) (n : ℕ) (h : c 0 ≠ c n) :
    0 < colorChanges c n :=
  Nat.pos_of_ne_zero (fun hz => by
    have := oddColorChanges_of_ne c n h; simp [hz] at this)

#check even_colorChanges_iff   -- parity identity
#check oddColorChanges_of_ne   -- odd count when endpoints differ
#check exists_sperner_edge     -- 1D Sperner lemma (discrete IVT)

end BrouwerFixedPointOQ01OQ01
