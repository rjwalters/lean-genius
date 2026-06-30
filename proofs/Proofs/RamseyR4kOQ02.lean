/-
  RamseyR4kOQ02.lean

  Exact Ramsey number lower bound: R(4,3) ≥ 9.

  Open question OQ-02 from the `ramsey-r4k` gallery proof asks whether the exact
  off-diagonal Ramsey numbers R(4,3) = 9, R(4,4) = 18, R(4,5) = 25 can be verified
  in Lean 4. The parent proof `ramsey-r4k` establishes only the classical
  Erdős–Szekeres *upper* bounds (R(4,k) ≤ C(k+2,3), giving R(4,3) ≤ 10), not the
  exact values.

  This file contributes the *lower* half of the smallest case:

        R(4,3) ≥ 9,   i.e.   ¬ RamseyProp 8 4 3,

  the "exhibit an extremal coloring on n-1 = 8 vertices" direction mentioned in the
  open question. We give the explicit extremal 2-coloring of K₈ and verify by finite
  decision that it contains no red 4-clique and no blue 3-clique.

  The extremal coloring is the **Wagner graph** V₈ (the Möbius–Kantor 8-cycle with the
  four long diagonals), the unique triangle-free graph on 8 vertices with independence
  number 3. Encoding the Wagner edges as the *blue* color and all other edges as *red*:

    * blue is triangle-free   ⟹  no blue K₃,
    * α(Wagner) = 3           ⟹  the red graph (its complement) has clique number 3,
                                   hence no red K₄.

  Combined with the parent proof's machinery the exact value R(4,3) = 9 is bracketed
  from below; the matching exact upper bound R(4,3) ≤ 9 (sharpening the binomial
  bound of 10) remains open here.

  The clique-freeness facts are finite checks over all subsets of Fin 8, discharged by
  `decide`, so they are fully kernel-verified (no `native_decide`, no extra axioms).

  Source: Open question OQ-02 from the ramsey-r4k gallery proof.
  Tags: combinatorics, ramsey-theory, graph-theory, exact-ramsey-numbers, lower-bounds
-/

import Mathlib
import Proofs.RamseyR4k

namespace RamseyR4kOQ02

open Finset

/-! ## The extremal coloring of K₈ (the Wagner graph)

We work on the vertex set `Fin 8 ≅ ℤ/8ℤ`. The Wagner graph has an edge between
`i` and `j` exactly when their cyclic distance is `1` or `4` (equivalently the
circular difference `(i - j) mod 8 ∈ {1, 4, 7}`). We color these edges **blue**
(`false`) and every other edge **red** (`true`). Loops are colored blue to satisfy
the irreflexivity convention `f x x = false`.
-/

/-- The circular difference `(i - j) mod 8`, computed without subtraction underflow. -/
def cdiff (i j : Fin 8) : ℕ := (i.val + 8 - j.val) % 8

/-- The extremal 2-coloring of `K₈`: `false` (blue) on Wagner edges and loops,
    `true` (red) elsewhere. -/
def wagnerColor (i j : Fin 8) : Bool :=
  let d := cdiff i j
  !(d == 0 || d == 1 || d == 4 || d == 7)

/-- The coloring is symmetric (an undirected edge coloring). -/
theorem wagner_symm : ∀ x y, wagnerColor x y = wagnerColor y x := by decide

/-- The coloring is irreflexive: loops are blue. -/
theorem wagner_irrefl : ∀ x, wagnerColor x x = false := by decide

set_option maxRecDepth 4000 in
/-- No red 4-clique: the red graph (complement of the Wagner graph) has clique
    number 3, so there is no set of 4 vertices that are pairwise red. -/
theorem wagner_no_red_K4 :
    ¬ ∃ S : Finset (Fin 8), S.card ≥ 4 ∧
        ∀ x y, x ∈ S → y ∈ S → x ≠ y → wagnerColor x y = true := by decide

set_option maxRecDepth 4000 in
/-- No blue 3-clique: the Wagner (blue) graph is triangle-free. -/
theorem wagner_no_blue_K3 :
    ¬ ∃ S : Finset (Fin 8), S.card ≥ 3 ∧
        ∀ x y, x ∈ S → y ∈ S → x ≠ y → wagnerColor x y = false := by decide

/-! ## The lower bound R(4,3) ≥ 9 -/

/-- **R(4,3) ≥ 9.** There is a 2-coloring of `K₈` with no red 4-clique and no blue
    3-clique, so `K₈` does *not* have the Ramsey property `RamseyProp 8 4 3`. This is
    the lower-bound half of the exact value R(4,3) = 9. -/
theorem r43_lower : ¬ RamseyR4k.RamseyProp 8 4 3 := by
  intro h
  rcases h wagnerColor wagner_symm wagner_irrefl with hred | hblue
  · exact wagner_no_red_K4 hred
  · exact wagner_no_blue_K3 hblue

/-- Restated in the conventional Ramsey direction: every 2-coloring of `K₈`
    *can* avoid both a red 4-clique and a blue 3-clique. Concretely, the Wagner
    coloring witnesses this. -/
theorem r43_lower_witness :
    ∃ f : Fin 8 → Fin 8 → Bool,
      (∀ x y, f x y = f y x) ∧
      (∀ x, f x x = false) ∧
      (¬ ∃ S : Finset (Fin 8), S.card ≥ 4 ∧
          ∀ x y, x ∈ S → y ∈ S → x ≠ y → f x y = true) ∧
      (¬ ∃ S : Finset (Fin 8), S.card ≥ 3 ∧
          ∀ x y, x ∈ S → y ∈ S → x ≠ y → f x y = false) :=
  ⟨wagnerColor, wagner_symm, wagner_irrefl, wagner_no_red_K4, wagner_no_blue_K3⟩

end RamseyR4kOQ02
