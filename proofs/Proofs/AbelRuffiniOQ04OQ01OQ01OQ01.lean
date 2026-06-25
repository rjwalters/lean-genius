/-
  Erdős / Abel-Ruffini family — OQ-04-OQ-01-OQ-01-OQ-01
  The Dedekind mod-2 route for the alternate quintic x⁵ - x - 1.

  Parent (abel-ruffini-oq-04-oq-01-oq-01, file AbelRuffiniOQ04OQ01OQ01.lean)
  established that x⁵ - x - 1 is NOT an S₅ witness "by the same argument" as
  x⁵ - 4x + 2: it has exactly one real root, so complex conjugation acts as a
  *double* transposition (an even permutation in A₅), not a transposition. The
  parent then sketched the correct route to a transposition: reduce mod 2,
  where

      x⁵ - x - 1 ≡ (x² + x + 1)(x³ + x² + 1)   (over 𝔽₂),

  a product of an irreducible quadratic and an irreducible cubic. By Dedekind's
  theorem the Frobenius/decomposition cycle type for the prime 2 is therefore
  (2, 3); the cube of a (2,3)-cycle is a transposition, supplying the odd
  permutation the parent's conjugation argument could not.

  ## What is machine-checked below (0 sorries, 0 axioms)

  * `factor_mod2`            — the factorization x⁵ - x - 1 = (x²+x+1)(x³+x²+1)
                               holds identically in (ZMod 2)[X]
  * `quadratic_natDegree`    — x²+x+1 has degree 2 over 𝔽₂
  * `cubic_natDegree`        — x³+x²+1 has degree 3 over 𝔽₂
  * `quadratic_irreducible`  — x²+x+1 is irreducible over 𝔽₂ (no roots, deg 2)
  * `cubic_irreducible`      — x³+x²+1 is irreducible over 𝔽₂ (no roots, deg 3)
  * `factors_not_associated` — the two irreducible factors are distinct
                               (different degrees ⇒ not associate), so the
                               factorization is into *distinct* irreducibles —
                               exactly the squarefree input Dedekind's theorem
                               needs to read off the cycle type (2, 3).

  ## What is NOT formalized here (documented, not claimed)

  * Dedekind's theorem itself (cycle type of Frobenius = degrees of the
    irreducible factors mod p) is not formalized in Mathlib; we supply its
    concrete hypotheses for p = 2 only.
  * Irreducibility of x⁵ - x - 1 over ℚ (would follow from the mod-3 reduction,
    where the polynomial stays irreducible — a separate decidability question).
  * The full Gal(x⁵ - x - 1) ≅ S₅. The mod-2 data here gives an element of cycle
    type (2,3) (whose cube is a transposition) and the mod-3 data would give a
    5-cycle; a transposition together with a 5-cycle generate S₅.
-/
import Mathlib

open Polynomial

namespace AbelRuffiniOQ04OQ01OQ01OQ01

/-- The quadratic factor of x⁵ - x - 1 modulo 2. -/
noncomputable def a : (ZMod 2)[X] := X ^ 2 + X + 1

/-- The cubic factor of x⁵ - x - 1 modulo 2. -/
noncomputable def b : (ZMod 2)[X] := X ^ 3 + X ^ 2 + 1

/-- The reduction of the quintic x⁵ - x - 1 to (ZMod 2)[X]. -/
noncomputable def q2 : (ZMod 2)[X] := X ^ 5 - X - 1

/-- **The Dedekind factorization mod 2.** Over 𝔽₂, x⁵ - x - 1 splits as the
    product of the quadratic x²+x+1 and the cubic x³+x²+1. The off-diagonal
    cross terms collect into `2 · (x⁴+x³+x²+x+1)`, which vanishes in
    characteristic two. -/
theorem factor_mod2 : a * b = q2 := by
  unfold a b q2
  have hexpand :
      (X ^ 2 + X + 1) * (X ^ 3 + X ^ 2 + 1) - (X ^ 5 - X - 1 : (ZMod 2)[X])
        = 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) := by ring
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
  rw [h2, zero_mul] at hexpand
  exact sub_eq_zero.mp hexpand

/-- x²+x+1 has degree 2 over 𝔽₂. -/
theorem quadratic_natDegree : a.natDegree = 2 := by
  unfold a; compute_degree!

/-- x³+x²+1 has degree 3 over 𝔽₂. -/
theorem cubic_natDegree : b.natDegree = 3 := by
  unfold b; compute_degree!

/-- x²+x+1 has no root in 𝔽₂ (it evaluates to 1 at both 0 and 1). -/
theorem quadratic_no_roots : ∀ x : ZMod 2, ¬ a.IsRoot x := by
  intro x
  fin_cases x <;>
    simp only [a, IsRoot.def, eval_add, eval_pow, eval_X, eval_one] <;> decide

/-- x³+x²+1 has no root in 𝔽₂ (it evaluates to 1 at both 0 and 1). -/
theorem cubic_no_roots : ∀ x : ZMod 2, ¬ b.IsRoot x := by
  intro x
  fin_cases x <;>
    simp only [b, IsRoot.def, eval_add, eval_pow, eval_X, eval_one] <;> decide

/-- **x²+x+1 is irreducible over 𝔽₂.** A degree-2 polynomial over a field with
    no root is irreducible. -/
theorem quadratic_irreducible : Irreducible a := by
  apply irreducible_of_degree_le_three_of_not_isRoot (p := a)
  · rw [Finset.mem_Icc, quadratic_natDegree]; omega
  · exact quadratic_no_roots

/-- **x³+x²+1 is irreducible over 𝔽₂.** A degree-3 polynomial over a field with
    no root is irreducible. -/
theorem cubic_irreducible : Irreducible b := by
  apply irreducible_of_degree_le_three_of_not_isRoot (p := b)
  · rw [Finset.mem_Icc, cubic_natDegree]; omega
  · exact cubic_no_roots

/-- The two irreducible factors are not associate: they have different degrees,
    so the mod-2 factorization is into *distinct* irreducibles. This is the
    squarefreeness Dedekind's theorem needs to read off cycle type (2, 3). -/
theorem factors_not_associated : ¬ Associated a b := by
  intro h
  have hdeg : a.natDegree = b.natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h)
  rw [quadratic_natDegree, cubic_natDegree] at hdeg
  exact absurd hdeg (by norm_num)

end AbelRuffiniOQ04OQ01OQ01OQ01
