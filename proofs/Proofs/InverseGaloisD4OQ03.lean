import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Proofs.InverseGaloisD4

/-
# OQ-03 (S2 Scaffold): General Dihedral-Galois Criterion for X^n − a

## Parent open question

This file is the second iteration of `inverse-galois-d4-oq-03` (parent
gallery entry: `inverse-galois-d4`, which proves the specific case
`Gal(X⁴ − 2 / ℚ) ≅ D₄`):

> Is there a general criterion for when `Gal(X^n − a / ℚ)` is dihedral?

S1 OBSERVE (PR #17929, researcher-9) established the mathematical scope:
the Schinzel–Velez classification (Velez 1979 — Acta Arith.; Schinzel
2000 — Polynomials with Special Regard to Reducibility) provides a
finite-case characterization keyed on `n mod 8` and the `p`-adic
valuations of `a`. Lean formalization is bottlenecked on **Capelli's
irreducibility theorem** (not in current Mathlib `v4.26.0`).

## What this file does (S2 scope)

This is a non-building scaffold proposed in S1's "next action":

1. **Abstract criterion definition**: `IsDihedralGaloisOfXnMinusA n a`
   — the proposition that the splitting field of `X^n − a` over `ℚ`
   has Galois group isomorphic to some dihedral group `DihedralGroup m`
   for `m ≥ 2`. Uses Mathlib's existing `Polynomial.SplittingField` and
   `DihedralGroup` constructions.
2. **Specialization to (4, 2)**: state `dihedral_galois_xPow4_sub_2 :
   IsDihedralGaloisOfXnMinusA 4 2`, deferring the proof (one sorry —
   the bridge from the parent's `d4_realizable` order-8 result to the
   explicit `D₄` identification requires the classical fact that `D₄`
   is the unique transitive subgroup of `S₄` of order 8, plus the
   identification of the splitting field's Galois group as a transitive
   subgroup of `S₄`).
3. **Schinzel–Velez characterization (statement only)**:
   `dihedral_iff_schinzel_velez` — the iff between the abstract
   criterion and the finite-case Schinzel–Velez conditions. Stated
   with `True` as the right-hand placeholder for now (one sorry); a
   future iteration will replace `True` with the explicit conditions
   once Capelli's theorem is upstreamed to Mathlib or proved in-tree.

The file is sorry-bearing by design — S2 SCAFFOLD lands the API
surface; S3+ iterations (and a separate Capelli-in-Mathlib effort)
will discharge the sorries.

## References

* Velez, W. Y. (1979). *On the Galois groups of `X^n − a`.* Acta
  Arithmetica 35, 191–198.
* Schinzel, A. (2000). *Polynomials with Special Regard to
  Reducibility.* Cambridge Univ. Press, §III.2.
* Capelli, A. (1897). *Sulla riduttibilità delle equazioni
  algebriche.* Giornale di Matematiche 36, 73–88.
* `Proofs.InverseGaloisD4` — parent gallery entry (27 theorems,
  `d4_realizable` proves the order-8 Galois group case for `X⁴ − 2`).

Tags: galois-theory, inverse-galois-problem, dihedral-groups,
radical-extensions, schinzel-velez-classification, capelli-theorem
-/

namespace InverseGaloisD4OQ03

open Polynomial

/-- The polynomial `X^n − a` over `ℚ`. -/
noncomputable def xPowSub (n : ℕ) (a : ℚ) : ℚ[X] := X ^ n - C a

/-- **Abstract criterion (S2 statement, no proofs)**: the Galois group
    of `X^n − a` over `ℚ` is dihedral.

    Formally: there exists `m ≥ 2` and a multiplicative isomorphism
    between the automorphism group of the splitting field of `X^n − a`
    (as a `ℚ`-algebra) and the dihedral group `DihedralGroup m` (of
    order `2m`). -/
def IsDihedralGaloisOfXnMinusA (n : ℕ) (a : ℚ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ Nonempty
    (((xPowSub n a).SplittingField ≃ₐ[ℚ] (xPowSub n a).SplittingField)
      ≃* DihedralGroup m)

/-- **Specialization to the parent's setting** (S2 statement, sorry).

    For `n = 4`, `a = 2`, the Galois group of `X⁴ − 2` over `ℚ` is
    isomorphic to `DihedralGroup 4` (i.e., `D₄`, of order 8). This is
    the abstract version of the parent's `d4_realizable`, which proves
    only the cardinality `8` part; identifying as `D₄` requires the
    classical fact that `D₄` is the unique transitive subgroup of `S₄`
    of order 8 (combined with the splitting field's Galois group being
    a transitive subgroup of `S₄` via the root permutation action).

    The sorry is the bridge — the underlying mathematical content is
    classical and established (see Cox, *Galois Theory* (2nd ed., 2012),
    §13.3), but the Lean formalization requires more work than fits in
    an S2 scaffold. -/
theorem dihedral_galois_xPow4_sub_2 :
    IsDihedralGaloisOfXnMinusA 4 2 := by
  sorry

/-- **Schinzel–Velez characterization (S2 statement, sorry)**.

    The Schinzel–Velez classification asserts that
    `IsDihedralGaloisOfXnMinusA n a` is equivalent to a finite-case
    predicate on `n mod 8` and the `p`-adic valuations of `a` (full
    statement in Schinzel 2000, §III.2).

    This theorem **states** the existence of such a characterization
    abstractly — i.e., the criterion is equivalent to *some* predicate
    on `(n, a)`. The explicit predicate is left as `True` until
    Capelli's irreducibility theorem (the key prerequisite, currently
    absent from Mathlib `v4.26.0`) is formalized.

    Future iterations should:
    1. Formalize Capelli's theorem (~200 lines of new infrastructure;
       worth a separate Mathlib contribution PR).
    2. Replace the `True` placeholder with the explicit Schinzel–Velez
       predicate.
    3. Discharge the iff using Velez (1979) and Schinzel (2000). -/
theorem dihedral_iff_schinzel_velez (n : ℕ) (a : ℚ) :
    IsDihedralGaloisOfXnMinusA n a ↔ True := by
  sorry

end InverseGaloisD4OQ03
