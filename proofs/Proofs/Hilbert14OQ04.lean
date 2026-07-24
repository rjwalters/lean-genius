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

/-!
## S5 ACT — toward Noether's degree bound: charpoly coefficient API (Stages 1–3)

The quantitative half of Noether 1916 (`generators ⊆ deg ≤ |G|`) factors through
the orbit characteristic polynomial `MulSemiringAction.charpoly G b = ∏ g, (X - C (g • b))`
(PREP-2/PREP-3 design, PRs #19294 + follow-up). This section lands the three
self-contained stages:

* **Stage 1** — every coefficient of `charpoly G b` is `G`-invariant, i.e. lies in
  `FixedPoints.subalgebra k R G` (from Mathlib's `smul_coeff_charpoly`);
* **Stage 2** — `(charpoly G b).natDegree = |G|` (product of `|G|` monic linear factors);
* **Stage 3** — with the graded-action hypothesis
  `h_graded : ∀ g p, (g • p).totalDegree ≤ p.totalDegree` (NOT automatic from
  `MulSemiringAction`; PREP-3 §2 Option A), the `j`-th coefficient has total degree
  at most `(|G| - j) · deg b`, via Vieta (`Multiset.prod_X_sub_C_coeff`) and the
  elementary symmetric expansion (`Finset.esymm_map_val`).

Stage 5 (Reynolds-operator extraction of a generating set in degree `≤ |G|`,
requiring `¬ (ringChar k ∣ |G|)`) remains for a dedicated S6 iteration.
-/

section DegreeBound

open MulSemiringAction

/-- **Stage 1**: every coefficient of the orbit characteristic polynomial
`charpoly G b = ∏ g, (X - C (g • b))` is fixed by the `G`-action, hence lies in
the invariant subalgebra. This is the source of the integrality relations that
the eventual degree-bound generating set is drawn from. -/
theorem coeff_charpoly_mem_fixedPoints (b : MvPolynomial (Fin n) k) (j : ℕ) :
    (charpoly G b).coeff j ∈
      FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G :=
  fun g => smul_coeff_charpoly b j g

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- **Stage 2**: the orbit characteristic polynomial has `natDegree` exactly
`|G|` — it is a product of `|G|` monic linear factors. -/
theorem natDegree_charpoly (b : MvPolynomial (Fin n) k) :
    (charpoly G b).natDegree = Fintype.card G := by
  rw [charpoly_eq,
    Polynomial.natDegree_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)]
  simp

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- **Stage 3**: under a degree-nonincreasing (graded) action — the standard
Noether-1916 setting of a linear action on the variables, stated as the explicit
hypothesis `h_graded` per PREP-3 §2 (it is NOT implied by `MulSemiringAction`
alone) — the `j`-th coefficient of `charpoly G b` has total degree at most
`(|G| - j) · deg b`.

Route: Vieta expresses the coefficient as `(-1)^(|G|-j) · esymm_{|G|-j}` of the
orbit multiset `{g • b}`; the elementary symmetric function is a sum over
`(|G|-j)`-subsets of products of orbit elements, each of total degree
`≤ deg b` by `h_graded`. -/
theorem totalDegree_coeff_charpoly_le
    (h_graded : ∀ (g : G) (p : MvPolynomial (Fin n) k),
      (g • p).totalDegree ≤ p.totalDegree)
    (b : MvPolynomial (Fin n) k) (j : ℕ) (hj : j ≤ Fintype.card G) :
    ((charpoly G b).coeff j).totalDegree
      ≤ (Fintype.card G - j) * b.totalDegree := by
  classical
  -- the orbit multiset
  set s : Multiset (MvPolynomial (Fin n) k) :=
    Finset.univ.val.map (fun g : G => g • b) with hs
  have hcard : Multiset.card s = Fintype.card G := by
    rw [hs, Multiset.card_map]
    exact Finset.card_univ
  -- charpoly as a multiset product of linear factors
  have hprod : charpoly G b =
      (s.map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [charpoly_eq, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
    rfl
  -- Vieta: the coefficient is a signed elementary symmetric function
  have hcoeff : (charpoly G b).coeff j =
      (-1) ^ (Fintype.card G - j) * s.esymm (Fintype.card G - j) := by
    rw [hprod, Multiset.prod_X_sub_C_coeff s (by rw [hcard]; exact hj), hcard]
  rw [hcoeff]
  set m : ℕ := Fintype.card G - j with hm
  -- the sign factor is a constant
  have hsign : ((-1 : MvPolynomial (Fin n) k) ^ m).totalDegree = 0 := by
    have hC : ((-1 : MvPolynomial (Fin n) k) ^ m) =
        MvPolynomial.C ((-1 : k) ^ m) := by
      rw [map_pow, map_neg, map_one]
    rw [hC, MvPolynomial.totalDegree_C]
  -- the esymm factor: sum over m-subsets of degree-bounded products
  have hesymm : (s.esymm m).totalDegree ≤ m * b.totalDegree := by
    rw [hs, Finset.esymm_map_val]
    refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
    refine Finset.sup_le fun t ht => ?_
    have htcard : t.card = m := (Finset.mem_powersetCard.mp ht).2
    refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
    calc ∑ g ∈ t, ((g • b).totalDegree)
        ≤ ∑ _g ∈ t, b.totalDegree := Finset.sum_le_sum fun g _ => h_graded g b
      _ = t.card * b.totalDegree := by rw [Finset.sum_const, smul_eq_mul]
      _ = m * b.totalDegree := by rw [htcard]
  calc ((-1 : MvPolynomial (Fin n) k) ^ m * s.esymm m).totalDegree
      ≤ ((-1 : MvPolynomial (Fin n) k) ^ m).totalDegree
          + (s.esymm m).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (s.esymm m).totalDegree := by rw [hsign, zero_add]
    _ ≤ m * b.totalDegree := hesymm

end DegreeBound

section Reynolds

/-! ### S6 — the Reynolds operator (non-modular averaging projection)

The engine of the Stage-5 Noether-bound extraction: the averaging map
`p ↦ |G|⁻¹ • Σ_g g • p`. Whenever `|G| ≠ 0` in `k` (the non-modular case,
supplied by `card_ne_zero_of_char_not_dvd` from `ringChar k ∤ |G|`) it is an
additive projection of `MvPolynomial (Fin n) k` onto the invariant
subalgebra that does not raise total degree. The remaining S7 leg is the
extraction proper: applying `reynolds` to a monomial generating set of the
degree-`≤ |G|` piece and showing the images generate the invariant ring. -/

variable (G) in
/-- The **Reynolds operator**: the average of the `G`-orbit of `p`. -/
noncomputable def reynolds (p : MvPolynomial (Fin n) k) : MvPolynomial (Fin n) k :=
  (Fintype.card G : k)⁻¹ • ∑ g : G, g • p

/-- Non-modularity bridge: if `ringChar k ∤ |G|` then `|G| ≠ 0` in `k`. -/
theorem card_ne_zero_of_char_not_dvd (h_char : ¬ ringChar k ∣ Fintype.card G) :
    (Fintype.card G : k) ≠ 0 :=
  fun h => h_char ((ringChar.spec (Fintype.card G)).mp h)

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- Orbit sums are invariant under right translation of the argument. -/
theorem sum_smul_of_smul (g : G) (p : MvPolynomial (Fin n) k) :
    ∑ h : G, h • (g • p) = ∑ h : G, h • p := by
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ (fun h => h • p) (fun h => rfl)

/-- The Reynolds operator is constant on `G`-orbits. -/
theorem reynolds_smul (g : G) (p : MvPolynomial (Fin n) k) :
    reynolds G (g • p) = reynolds G p := by
  unfold reynolds
  rw [sum_smul_of_smul]

/-- The Reynolds average is a fixed point of the action. -/
theorem smul_reynolds (g : G) (p : MvPolynomial (Fin n) k) :
    g • reynolds G p = reynolds G p := by
  unfold reynolds
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ (fun h => h • p) (fun h => rfl)

/-- The Reynolds average lies in the invariant subalgebra. -/
theorem reynolds_mem_fixedPoints (p : MvPolynomial (Fin n) k) :
    reynolds G p ∈ FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G :=
  fun g => smul_reynolds g p

/-- On invariants the Reynolds operator is the identity (non-modular case) —
the projection property. -/
theorem reynolds_of_mem_fixedPoints (hG : (Fintype.card G : k) ≠ 0)
    {p : MvPolynomial (Fin n) k}
    (hp : p ∈ FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) :
    reynolds G p = p := by
  unfold reynolds
  have hfix : ∀ g : G, g • p = p := hp
  simp_rw [hfix]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
    smul_smul, inv_mul_cancel₀ hG, one_smul]

/-- The Reynolds operator is additive. -/
theorem reynolds_add (p q : MvPolynomial (Fin n) k) :
    reynolds G (p + q) = reynolds G p + reynolds G q := by
  unfold reynolds
  simp_rw [smul_add, Finset.sum_add_distrib]

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- The Reynolds operator does not raise total degree (under the graded
hypothesis `h_graded` of the Stage-3 coefficient bound). -/
theorem totalDegree_reynolds_le
    (h_graded : ∀ (g : G) (p : MvPolynomial (Fin n) k),
      (g • p).totalDegree ≤ p.totalDegree)
    (p : MvPolynomial (Fin n) k) :
    (reynolds G p).totalDegree ≤ p.totalDegree := by
  refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  exact Finset.sup_le fun g _ => h_graded g p

end Reynolds

end Hilbert14OQ04
