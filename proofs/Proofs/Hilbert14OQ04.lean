import Mathlib

/-!
# Hilbert 14: Effective Algorithms for Non-Reductive Invariants (OQ-04)

OQ-04 is the meta-mathematical question of effective algorithms for finite
generation of non-reductive invariant rings. The OQ-04 conjecture itself is
not formalizable as a single Lean theorem (it concerns the existence of
uniform algorithms across infinite classes of groups).

This file scaffolds the algorithmically refinable sibling target:
**Hilbert finiteness** for invariant rings of finite-group linear actions on
`MvPolynomial`. Per the S2g PREP audit (PR #18750), the proof chains through
five Mathlib bearers (all signatures pinned at v4.26.0,
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

  1. `Algebra.IsInvariant B R G`             — definitional via membership
  2. `Algebra.IsInvariant.isIntegral`        — `Invariant/Basic.lean:174`
  3. `Algebra.FiniteType.of_restrictScalars_finiteType`
                                             — `FiniteType.lean:77`
  4. `Algebra.IsIntegral.finite`             — `IntegralClosure/Basic.lean:93`
  5. Artin-Tate `fg_of_fg_of_fg`             — `Adjoin/Tower.lean:150`
     plus `Subalgebra.fg_iff_finiteType`     — `FiniteType.lean:213`

## Scope

- IN scope: Hilbert finiteness (qualitative half of Noether 1916).
- OUT (deferred to S3-bound): Noether's degree bound
  (`generators ⊆ deg ≤ |G|`).
- OUT: locally nilpotent derivations (Weitzenböck); Nagata counterexample.
-/

namespace Hilbert14OQ04

open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}
variable {G : Type*} [Group G] [Fintype G]
variable [MulSemiringAction G (MvPolynomial (Fin n) k)]
variable [SMulCommClass G k (MvPolynomial (Fin n) k)]

/-- The `Algebra.IsInvariant` predicate is definitionally satisfied by the
fixed-points subalgebra: every fixed point lies in the image of the
subalgebra inclusion. -/
instance isInvariant_fixedPoints :
    Algebra.IsInvariant
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
      (MvPolynomial (Fin n) k) G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-- Integrality of `R / R^G` for finite `G`: every element of `R` satisfies
its `G`-orbit polynomial, which is monic of degree `|G|` and has invariant
coefficients (Mathlib bearer `Algebra.IsInvariant.isIntegral`). -/
instance isIntegral_fixedPoints :
    Algebra.IsIntegral
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
      (MvPolynomial (Fin n) k) :=
  Algebra.IsInvariant.isIntegral _ _ G

/-- **Hilbert finiteness** for finite-group linear actions on `MvPolynomial`:
the invariant subring `R^G` is finitely generated as a `k`-algebra.

This is the qualitative half of Emmy Noether's 1916 theorem. The
quantitative half (`generators ⊆ deg ≤ |G|`) is deferred to a later
S3-bound ACT iteration.

**Proof outline**: chain Hilbert basis / Artin-Tate (`fg_of_fg_of_fg`) on
the tower `k → R^G → R`. The integrality of `R / R^G` gives
`Module.Finite (R^G) R`; `MvPolynomial`'s built-in `Algebra.FiniteType k R`
restricts to `Algebra.FiniteType (R^G) R`; Artin-Tate then concludes
`(⊤ : Subalgebra k (R^G)).FG`, which translates to
`Algebra.FiniteType k (R^G)` via `Subalgebra.fg_iff_finiteType`. -/
theorem hilbert_finiteness :
    Algebra.FiniteType k
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) := by
  set R := MvPolynomial (Fin n) k with hR_def
  set B := FixedPoints.subalgebra k R G with hB_def
  -- Step 3: Upgrade `Algebra.FiniteType k R` (automatic) to
  -- `Algebra.FiniteType B R` via the restrict-scalars bearer.
  haveI hFT_BR : Algebra.FiniteType B R :=
    Algebra.FiniteType.of_restrictScalars_finiteType k B R
  -- Step 4: `Module.Finite B R` from integrality + algebra-finiteness.
  haveI hMF_BR : Module.Finite B R := Algebra.IsIntegral.finite
  -- Step 5a: algebra hypothesis for Artin-Tate
  --          (k → R is f.g. as algebras).
  have h_kR_fg : (⊤ : Subalgebra k R).FG :=
    (inferInstance : Algebra.FiniteType k R).out
  -- Step 5b: module hypothesis for Artin-Tate
  --          (R is f.g. as a B-module).
  have h_BR_fg : (⊤ : Submodule B R).FG := Module.Finite.fg_top
  -- Step 5c: injectivity of the subalgebra inclusion B ↪ R.
  have h_BR_inj : Function.Injective (algebraMap B R) :=
    Subtype.val_injective
  -- Step 5d: apply Artin-Tate `fg_of_fg_of_fg` (Adjoin/Tower.lean:150).
  have h_kB_fg : (⊤ : Subalgebra k B).FG :=
    fg_of_fg_of_fg k B R h_kR_fg h_BR_fg h_BR_inj
  -- Step 5e: translate Subalgebra.FG back to Algebra.FiniteType.
  exact ⟨h_kB_fg⟩

end Hilbert14OQ04
