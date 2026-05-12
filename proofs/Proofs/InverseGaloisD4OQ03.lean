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

/-- **Definitional unfolding (S3a)**: `xPowSub n a` is by definition
    `X^n − C a`. Useful for bridging to lemmas about the explicit
    polynomial form (e.g., the parent's `x4_sub_2_*` family, which is
    stated on `(X : ℚ[X])^4 - C 2` directly). -/
theorem xPowSub_def (n : ℕ) (a : ℚ) :
    xPowSub n a = X ^ n - C a := rfl

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
    an S2 scaffold. S3a (this iteration) supplies the cardinality lift
    `gal_card_xPowSub_4_2` toward this discharge; the remaining task is
    the order-8-transitive-S₄-subgroup classification. -/
theorem dihedral_galois_xPow4_sub_2 :
    IsDihedralGaloisOfXnMinusA 4 2 := by
  sorry

/-- **Cardinality lift (S3a, no sorry)**: the Galois group of
    `xPowSub 4 2 = X^4 − C 2` over `ℚ` has cardinality `8`. This is
    the parent's `x4_sub_2_gal_card` reused under the local
    `xPowSub` definition.

    This isolates the cardinality-input piece of the S3+ bridge from
    the harder "order-8 transitive S₄-subgroup is D₄" classification
    step. -/
theorem gal_card_xPowSub_4_2 :
    Fintype.card (xPowSub 4 2).Gal = 8 := by
  show Fintype.card ((X : ℚ[X]) ^ 4 - C 2).Gal = 8
  exact InverseGaloisExtensions.x4_sub_2_gal_card

/-- **Natural-degree bridge (S3b, no sorry)**: `xPowSub 4 2` has
    `natDegree = 4`. Reuses the parent's
    `x_fourth_sub_2_natDegree` under the local notation.

    Useful for any S4+ argument that needs the polynomial degree to
    set up the embedding `Gal ↪ S₄` (via `Polynomial.Gal.galActionHom`
    on the four-element root set). -/
theorem xPowSub_4_2_natDegree :
    (xPowSub 4 2).natDegree = 4 := by
  show ((X : ℚ[X]) ^ 4 - C 2).natDegree = 4
  exact InverseGaloisExtensions.x_fourth_sub_2_natDegree

/-- **Irreducibility bridge (S3b, no sorry)**: `xPowSub 4 2` is
    irreducible over `ℚ`. Reuses the parent's
    `x_fourth_sub_2_irreducible` (Eisenstein at `p = 2`).

    Irreducibility supplies the transitivity-of-the-Galois-action
    hypothesis used by the S4 bridge: `Polynomial.Gal.galActionHom`
    is injective (parent argument in `x4_sub_2_gal_card_dvd_24`), and
    the image acts transitively on the roots by irreducibility, so
    it embeds as a transitive subgroup of `S₄`. -/
theorem xPowSub_4_2_irreducible :
    Irreducible (xPowSub 4 2) := by
  show Irreducible ((X : ℚ[X]) ^ 4 - C 2)
  exact InverseGaloisExtensions.x_fourth_sub_2_irreducible

/-- **Separability bridge (S3b, no sorry)**: `xPowSub 4 2` is
    separable (every irreducible polynomial over a characteristic-0
    field is separable). -/
theorem xPowSub_4_2_separable :
    (xPowSub 4 2).Separable := by
  show ((X : ℚ[X]) ^ 4 - C 2).Separable
  exact InverseGaloisExtensions.x_fourth_sub_2_separable

/-- **Monicity bridge (S3b, no sorry)**: `xPowSub 4 2` is monic
    (leading coefficient `1`). Reuses the parent's
    `x_fourth_sub_2_monic`. -/
theorem xPowSub_4_2_monic :
    (xPowSub 4 2).Monic := by
  show ((X : ℚ[X]) ^ 4 - C 2).Monic
  exact InverseGaloisExtensions.x_fourth_sub_2_monic

/-- **`DihedralGroup 4` has 8 elements (S3b, no sorry)**: the order
    of the dihedral group `D₄` is `8 = 2 · 4`. Direct consequence of
    Mathlib's `DihedralGroup.card`.

    This is the cardinality target on the codomain side of the
    eventual S4 isomorphism `Gal(X⁴ − 2 / ℚ) ≃* DihedralGroup 4`. -/
theorem dihedralGroup_4_card :
    Fintype.card (DihedralGroup 4) = 8 :=
  DihedralGroup.card.trans (by norm_num)

/-- **Cardinality match (S3b, no sorry)**: the Galois group of
    `xPowSub 4 2` and `DihedralGroup 4` have equal cardinality (both
    `8`). Combines `gal_card_xPowSub_4_2` and `dihedralGroup_4_card`.

    Equal cardinality is *necessary* for the existence of a
    `MulEquiv` between two finite groups, but not sufficient — the
    S4 bridge still needs the structural identification that the
    Galois group is non-abelian and contains an order-`4` element
    (ruling out `(ℤ/2)³` and `(ℤ/2) × (ℤ/4)`, the only other groups
    of order `8` of relevance — `Q₈` is also order `8` but does not
    embed in `S₄` since `Q₈` has a unique involution while every
    order-`8` subgroup of `S₄` contains multiple involutions). -/
theorem gal_card_eq_dihedralGroup_4_card :
    Fintype.card (xPowSub 4 2).Gal = Fintype.card (DihedralGroup 4) := by
  rw [gal_card_xPowSub_4_2, dihedralGroup_4_card]

/-- **S4 entry point (S3b, no sorry)**: if a `MulEquiv` between the
    Galois group of `X⁴ − 2` and `DihedralGroup 4` is exhibited,
    then `IsDihedralGaloisOfXnMinusA 4 2` holds (using `m = 4`).

    This is the precise "remaining work" reduction for S4: instead
    of producing both the witness `m ≥ 2` and the `MulEquiv`, the
    S4 iteration only needs the concrete `MulEquiv`. The witness
    `m = 4` is supplied here. -/
theorem dihedral_galois_xPow4_sub_2_of_mulEquiv
    (φ : ((xPowSub 4 2).SplittingField ≃ₐ[ℚ] (xPowSub 4 2).SplittingField)
      ≃* DihedralGroup 4) :
    IsDihedralGaloisOfXnMinusA 4 2 :=
  ⟨4, by norm_num, ⟨φ⟩⟩

/-- **Schinzel–Velez characterization (existential form, S3a audit fix)**.

    The Schinzel–Velez classification asserts that there exists a
    predicate `P : ℕ → ℚ → Prop` such that
    `IsDihedralGaloisOfXnMinusA n a ↔ P n a` for all `n, a`. The
    *content* of Schinzel–Velez is that `P` is explicit, finite-case,
    and decidable on `(n mod 8)` and the `p`-adic valuations of `a`
    (Schinzel 2000, §III.2). The existence-of-a-predicate statement
    is vacuously true (take `P` to be the predicate itself); the
    explicit form requires Capelli's irreducibility theorem, which
    is not present in Mathlib `v4.26.0`.

    **Audit fix (S3a).** This replaces the prior `S2` statement
    `dihedral_iff_schinzel_velez (n a) : IsDihedralGaloisOfXnMinusA n a
    ↔ True`, which was unprovable as written — the iff fails for any
    `(n, a)` outside the dihedral case (e.g., `n = 1`, or
    `n = 5, a = 2` with Galois group `F₂₀`). The original sorry hid
    a falsity rather than a deferred-but-true bridge.

    Future iterations should replace this existential with the
    explicit Schinzel–Velez predicate once Capelli's theorem is
    formalized (~200 lines of upstream infrastructure). -/
theorem schinzel_velez_characterization_exists :
    ∃ P : ℕ → ℚ → Prop,
      ∀ n a, IsDihedralGaloisOfXnMinusA n a ↔ P n a :=
  ⟨IsDihedralGaloisOfXnMinusA, fun _ _ => Iff.rfl⟩

end InverseGaloisD4OQ03
