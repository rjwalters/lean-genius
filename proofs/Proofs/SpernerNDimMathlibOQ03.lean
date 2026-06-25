/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# Combinatorial Borsuk–Ulam in dimension one (Tucker's lemma, 1-D)

Answers **OQ-03** from `sperner-ndim-mathlib`:

> *Generalize to the Borsuk–Ulam theorem: does the abstract cell complex framework
> extend to antipodal colorings?*

The combinatorial (discrete) shadow of the Borsuk–Ulam theorem is **Tucker's lemma**.
Where Sperner's lemma colors the vertices of a triangulation with `Fin (d+1)` colors and
concludes the existence of a *panchromatic* cell, Tucker's lemma labels the vertices of an
*antipodally symmetric* triangulation of the ball `Bⁿ` with signed labels `{±1, …, ±n}`
that are antisymmetric on the boundary sphere, and concludes the existence of a
*complementary edge* — an edge whose two endpoints carry opposite labels `+k` and `−k`.

This file settles the **base case `n = 1`** and, more importantly, isolates the
*antipodal parity engine* that plays, for Tucker, exactly the role that
`SpernerAbstract.sperner_parity` plays for Sperner.

## The analogy with the Sperner framework

| Sperner framework (`SpernerNDimMathlib`)        | Antipodal framework (this file)                 |
| ----------------------------------------------- | ----------------------------------------------- |
| colors `Fin (d+1)`                              | signs `Bool` (`{+1, −1}`)                       |
| door = facet carrying all `d` low colors        | complementary edge = adjacent opposite signs    |
| interior doors pair off (FPF involution, even)  | (1-D) interior carries no parity obstruction    |
| `sperner_parity`: #panchromatic ≡ #boundary doors | `signChanges_odd_iff`: #complementary edges parity = boundary mismatch |
| odd boundary ⟹ a panchromatic cell exists       | antipodal boundary ⟹ a complementary edge exists |

The Sperner proof reduces a global count to a boundary count via a fixed-point-free
involution on interior doors (`even_card_fpf_invol`). In dimension one the "interior
involution" degenerates: a path `0—1—…—n` has no interior `(d−1)`-faces to pair, and the
parity of the complementary-edge count is governed *entirely* by the two boundary endpoints.
The clean statement of this is the **discrete fundamental theorem of calculus mod 2**
(`signChanges_odd_iff`): the number of sign changes along a path is odd iff the endpoints
disagree. Antipodal boundary data (`g 0 = ! g n`) forces a disagreement, hence an odd —
in particular nonzero — number of complementary edges. That is 1-D Tucker.

## Main statements

* `signChanges_odd_iff`  : the antipodal parity engine (sign-change count parity = boundary mismatch).
* `complementary_edges_odd` : antipodal boundary ⟹ the complementary-edge count is odd.
* `tucker_one_dim`       : a path with mismatched endpoints has a complementary edge.
* `tucker_one_dim_antipodal` : the explicit antipodal (`g 0 = ! g n`) phrasing.
* `tucker_one_dim_int`   : the `{±1}`-integer-labelled phrasing (`lbl 0 = − lbl n ⟹ ∃ edge with lbl i = − lbl (i+1)`).

## Scope / honest assessment

This is the **1-dimensional** case only. The full `n`-dimensional Tucker lemma does *not*
follow from the present `CellComplex` structure as-is: that structure carries no antipodal
involution on its boundary subcomplex, which is exactly the extra datum Tucker requires.
Extending the abstract framework to antipodal colorings in higher dimensions needs an
`AntipodalCellComplex` refinement (a free `ℤ/2`-action `α : Simplex → Simplex` with
`α∘α = id`, compatible with `adj` and `vertices`) plus the Freund–Todd / "special simplices"
labelling argument. The parity *engine* (`even_card_fpf_invol`) is reusable verbatim; the
*boundary bookkeeping* is the genuine higher-dimensional obstruction. See the project
knowledge notes for `sperner-ndim-mathlib-oq-03`.

## Tags

Tucker, Borsuk-Ulam, antipodal, combinatorics, parity, Sperner
-/

namespace CombinatorialBorsukUlam

open Finset

variable (g : ℕ → Bool)

/-- The number of **complementary edges** (sign-change edges) along the path
`0 — 1 — ⋯ — n`: indices `i < n` whose endpoints `g i` and `g (i+1)` carry opposite signs. -/
def signChanges (g : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => g i ≠ g (i + 1))).card

@[simp] lemma signChanges_zero : signChanges g 0 = 0 := by
  simp [signChanges]

/-- Peeling the last edge off the path. -/
lemma signChanges_succ (n : ℕ) :
    signChanges g (n + 1) =
      signChanges g n + (if g n ≠ g (n + 1) then 1 else 0) := by
  unfold signChanges
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : g n ≠ g (n + 1)
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

/-- **Antipodal parity engine** (discrete fundamental theorem of calculus, mod 2):
the number of complementary edges along a path is odd **iff** its two endpoints
carry opposite signs.

This is the antipodal counterpart of `SpernerAbstract.sperner_parity`: a global
edge count is pinned, mod 2, to pure boundary data. -/
theorem signChanges_odd_iff (n : ℕ) :
    Odd (signChanges g n) ↔ g 0 ≠ g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [signChanges_succ]
    by_cases h : g n = g (n + 1)
    · rw [if_neg (not_not.mpr h), add_zero, ← h]; exact ih
    · rw [if_pos h]
      have hbc : (g 0 ≠ g (n + 1)) ↔ ¬ (g 0 ≠ g n) := by
        revert h; cases g 0 <;> cases g n <;> cases g (n + 1) <;> decide
      rw [hbc, ← ih, Nat.odd_iff, Nat.odd_iff]; omega

/-- With antipodal boundary data the number of complementary edges is **odd**
(hence in particular nonzero). The combinatorial Borsuk–Ulam parity statement. -/
theorem complementary_edges_odd (n : ℕ) (hbdry : g 0 = ! g n) :
    Odd (signChanges g n) :=
  (signChanges_odd_iff g n).mpr (by rw [hbdry]; cases g n <;> decide)

/-- **Tucker's lemma, dimension one.** A path `0 — 1 — ⋯ — n` whose endpoints carry
opposite signs has a complementary edge: some `i < n` with `g i ≠ g (i+1)`. -/
theorem tucker_one_dim (n : ℕ) (hbdry : g 0 ≠ g n) :
    ∃ i, i < n ∧ g i ≠ g (i + 1) := by
  have hodd : Odd (signChanges g n) := (signChanges_odd_iff g n).mpr hbdry
  obtain ⟨k, hk⟩ := hodd
  have hpos : 0 < signChanges g n := by omega
  unfold signChanges at hpos
  rw [Finset.card_pos] at hpos
  obtain ⟨i, hi⟩ := hpos
  rw [Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨i, hi.1, hi.2⟩

/-- The explicit **antipodal** phrasing: if the boundary labels are genuine antipodes
(`g 0 = ! g n`), a complementary edge exists. -/
theorem tucker_one_dim_antipodal (n : ℕ) (hbdry : g 0 = ! g n) :
    ∃ i, i < n ∧ g i ≠ g (i + 1) :=
  tucker_one_dim g n (by rw [hbdry]; cases g n <;> decide)

/-- **Tucker's lemma, dimension one, `{±1}`-integer labels.** If every label is `±1`
and the boundary labels are antipodal (`lbl 0 = − lbl n`), then some edge is
complementary: `lbl i = − lbl (i+1)`. -/
theorem tucker_one_dim_int (lbl : ℕ → ℤ)
    (hsign : ∀ i, lbl i = 1 ∨ lbl i = -1) (n : ℕ)
    (hbdry : lbl 0 = - lbl n) :
    ∃ i, i < n ∧ lbl i = - lbl (i + 1) := by
  -- `decide (· = 1)` encodes a `±1` label as a sign bit; complementary edges
  -- (`lbl i = − lbl (i+1)`) are exactly the sign changes of this encoding.
  have key : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      ((decide (a = 1) ≠ decide (b = 1)) ↔ a = -b) := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> decide
  obtain ⟨i, hi, hne⟩ :=
    tucker_one_dim (fun i => decide (lbl i = 1)) n
      ((key (lbl 0) (lbl n) (hsign 0) (hsign n)).mpr hbdry)
  exact ⟨i, hi, (key (lbl i) (lbl (i + 1)) (hsign i) (hsign (i + 1))).mp hne⟩

end CombinatorialBorsukUlam
