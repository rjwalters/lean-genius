/-
Markov equation — Open Question 02 (supplementary): degenerate Markov triples.

[UNVERIFIED — build pending. The host Docker / containerd content store is
corrupted (missing blobs, I/O errors) and the build disk is full, so this file
could not be machine-checked this session. The proof is hand-derived and builds
only on the *verified* parent `Proofs.MarkovEquation`; it is shipped as a DRAFT
for verification once the build infrastructure recovers.]

## Context

The classical Markov equation

    x² + y² + z² = 3xyz

is fully classified in `Proofs/MarkovEquation.lean` (`IsMarkov`, the Vieta jump,
the descent, and the tree rooted at the singular `(1,1,1)`). A natural structural
question — adjacent to the parent's open questions — is *which* Markov triples are
"degenerate", i.e. carry a **repeated coordinate**.

The answer is clean: up to permutation, the only positive Markov triples with two
equal coordinates are the singular `(1,1,1)` and its neighbour `(1,1,2)`. Every
other Markov triple has three pairwise-distinct coordinates.

This file proves the diagonal case `x = y`,

    IsMarkov x x z  →  x = 1 ∧ (z = 1 ∨ z = 2),

and derives the `y = z` and `x = z` cases from it via the verified symmetry
lemmas `markov_swap12` / `markov_swap23` of the parent.

## The argument

Fix the two equal coordinates `x`. The third coordinate `z` has Vieta conjugate
`w := 3x² − z`, and the Markov equation is exactly

    z + w = 3x²,    z · w = 2x².

Both `z` and `w` are **positive integers** (positivity of `w` is the standard
`z·w = 2x² > 0` argument). Integrality then gives `z ≥ 1` and `w ≥ 1`, so

    0 ≤ (z − 1)(w − 1) = z·w − (z + w) + 1 = 2x² − 3x² + 1 = 1 − x²,

hence `x² ≤ 1`, and with `x ≥ 1` this forces `x = 1`. Substituting `x = 1` reduces
the equation to `(z − 1)(z − 2) = 0`, so `z ∈ {1, 2}`. The crucial use of
integrality (`z, w ≥ 1`) is what makes the conclusion false over the reals, where
the same `z + w = 3x²`, `z·w = 2x²` has solutions for every `x`.

## Axioms / Sorries
None. Built only on Mathlib + `Proofs.MarkovEquation`.
-/

import Mathlib
import Proofs.MarkovEquation

namespace MarkovDegenerate

open MarkovEquation

/-- **Diagonal degeneracy.** A Markov triple whose first two coordinates are equal
must be the singular solution `(1,1,1)` or its neighbour `(1,1,2)`:

    IsMarkov x x z  →  x = 1 ∧ (z = 1 ∨ z = 2). -/
theorem markov_diag {x z : ℤ} (h : IsMarkov x x z) :
    x = 1 ∧ (z = 1 ∨ z = 2) := by
  obtain ⟨hx, _, hz, he⟩ := h
  -- `w` is the Vieta conjugate of `z` fixing the two equal coordinates `x`.
  obtain ⟨w, hw⟩ : ∃ w : ℤ, w = 3 * x * x - z := ⟨_, rfl⟩
  have hsum : z + w = 3 * x * x := by rw [hw]; ring
  have hprod : z * w = 2 * x ^ 2 := by rw [hw]; linear_combination -he
  clear hw
  -- `z·w = 2x² > 0` with `z > 0` forces `w > 0`.
  have hwpos : 0 < w := by nlinarith [hprod, hz, mul_pos hx hx]
  -- Integrality: each positive coordinate is `≥ 1`.
  have h1x : (1 : ℤ) ≤ x := by omega
  have hz1 : (1 : ℤ) ≤ z := by omega
  have hw1 : (1 : ℤ) ≤ w := by omega
  -- (z-1)(w-1) ≥ 0  expands to  2x² - 3x² + 1 = 1 - x² ≥ 0.
  have hkey : 0 ≤ (z - 1) * (w - 1) := mul_nonneg (by linarith) (by linarith)
  have hxsq : x ^ 2 ≤ 1 := by nlinarith [hkey, hprod, hsum]
  have hxle : x ≤ 1 := by
    nlinarith [hxsq, h1x, mul_nonneg (sub_nonneg.mpr h1x) (sub_nonneg.mpr h1x)]
  have hx1 : x = 1 := le_antisymm hxle h1x
  refine ⟨hx1, ?_⟩
  subst hx1
  -- With x = 1 the equation is (z-1)(z-2) = 0.
  have hfac : (z - 1) * (z - 2) = 0 := by linear_combination he
  rcases mul_eq_zero.mp hfac with h0 | h0
  · left; linarith
  · right; linarith

/-- The degenerate pair may sit in the last two coordinates (`y = z`). -/
theorem markov_diag_yz {x y : ℤ} (h : IsMarkov x y y) :
    y = 1 ∧ (x = 1 ∨ x = 2) := by
  -- Move the equal pair to the front: (x,y,y) → (y,x,y) → (y,y,x).
  have h' : IsMarkov y y x := markov_swap23 (markov_swap12 h)
  exact markov_diag h'

/-- The degenerate pair may sit in the outer coordinates (`x = z`). -/
theorem markov_diag_xz {x y : ℤ} (h : IsMarkov x y x) :
    x = 1 ∧ (y = 1 ∨ y = 2) := by
  -- (x,y,x) → (x,x,y).
  have h' : IsMarkov x x y := markov_swap23 h
  exact markov_diag h'

/-- **Pairwise distinctness.** A Markov triple whose coordinates are all `≥ 2` has
three pairwise-distinct coordinates. (Equivalently: whenever two coordinates of a
Markov triple coincide, their common value is `1`.) This isolates the two base
triples `(1,1,1)` and `(1,1,2)` as the *only* sources of a repeated coordinate. -/
theorem markov_pairwise_distinct {x y z : ℤ} (h : IsMarkov x y z)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) : x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  refine ⟨?_, ?_, ?_⟩
  · intro hxy; subst hxy
    obtain ⟨h1, _⟩ := markov_diag h; omega
  · intro hyz; subst hyz
    obtain ⟨h1, _⟩ := markov_diag_yz h; omega
  · intro hxz; subst hxz
    obtain ⟨h1, _⟩ := markov_diag_xz h; omega

end MarkovDegenerate

-- Export checks
#check @MarkovDegenerate.markov_diag
#check @MarkovDegenerate.markov_diag_yz
#check @MarkovDegenerate.markov_diag_xz
#check @MarkovDegenerate.markov_pairwise_distinct
