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

omit [Group G] [MulSemiringAction G (MvPolynomial (Fin n) k)]
  [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- Non-modularity bridge: if `ringChar k ∤ |G|` then `|G| ≠ 0` in `k`. -/
theorem card_ne_zero_of_char_not_dvd (h_char : ¬ ringChar k ∣ Fintype.card G) :
    (Fintype.card G : k) ≠ 0 :=
  fun h => h_char ((ringChar.spec k (Fintype.card G)).mp h)

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- Orbit sums are invariant under right translation of the argument. -/
theorem sum_smul_of_smul (g : G) (p : MvPolynomial (Fin n) k) :
    ∑ h : G, h • (g • p) = ∑ h : G, h • p := by
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ (fun h => h • p) (fun h => rfl)

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
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

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- The Reynolds operator is additive. -/
theorem reynolds_add (p q : MvPolynomial (Fin n) k) :
    reynolds G (p + q) = reynolds G p + reynolds G q := by
  unfold reynolds
  simp_rw [smul_add, Finset.sum_add_distrib]
  exact smul_add _ _ _

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

section ReynoldsSpan

/-! ### S7a — the spanning layer: invariants are `k`-combinations of Reynolds
images of monomials

The first (linear-algebra) half of the Stage-5 extraction. In the non-modular
case the projection property `reynolds_of_mem_fixedPoints` plus `k`-linearity
of the Reynolds operator decompose EVERY invariant `p` as the `k`-combination
of the Reynolds images of the monomials in `p`'s own support:

  `p = ∑ m ∈ p.support, coeff m p • reynolds G (monomial m 1)`.

Since support monomials have degree `≤ p.totalDegree`, the degree-`d` filtered
piece of the invariant ring is `k`-spanned by
`{reynolds (monomial m 1) : deg m ≤ d}` (`mem_span_reynolds_monomial_of_totalDegree_le`).

What this does NOT yet give is Noether's bound proper: that the images with
`deg m ≤ |G|` generate the invariants as a `k`-ALGEBRA. That multiplicative
reduction (rewriting `reynolds (monomial m 1)` for `deg m > |G|` as a
polynomial in lower-degree images — the symmetrization/power-sum trick,
needing `|G|!` invertible in the classical argument) is the remaining S7b+
leg and is deliberately not claimed here. -/

variable (G) in
/-- The Reynolds operator commutes with the `k`-scalar action
(`SMulCommClass G k` moves the scalar past each orbit translate). -/
theorem reynolds_smul_k (c : k) (p : MvPolynomial (Fin n) k) :
    reynolds G (c • p) = c • reynolds G p := by
  unfold reynolds
  have h1 : ∀ g : G, g • (c • p) = c • (g • p) := fun g => smul_comm g c p
  simp_rw [h1]
  rw [← Finset.smul_sum, smul_comm ((Fintype.card G : k)⁻¹) c]

variable (G) in
/-- The Reynolds operator packaged as a `k`-linear endomorphism of the
polynomial ring. -/
noncomputable def reynoldsₗ :
    MvPolynomial (Fin n) k →ₗ[k] MvPolynomial (Fin n) k where
  toFun := reynolds G
  map_add' := reynolds_add
  map_smul' c p := reynolds_smul_k G c p

@[simp] theorem reynoldsₗ_apply (p : MvPolynomial (Fin n) k) :
    reynoldsₗ G p = reynolds G p :=
  rfl

/-- **The spanning decomposition**: in the non-modular case every invariant
is the `k`-combination of the Reynolds images of the monomials in its own
support (projection property + `k`-linearity). -/
theorem eq_sum_reynolds_monomial (hG : (Fintype.card G : k) ≠ 0)
    {p : MvPolynomial (Fin n) k}
    (hp : p ∈ FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) :
    p = ∑ m ∈ p.support,
      MvPolynomial.coeff m p • reynolds G (MvPolynomial.monomial m 1) := by
  conv_lhs => rw [← reynolds_of_mem_fixedPoints hG hp, MvPolynomial.as_sum p]
  rw [← reynoldsₗ_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show (MvPolynomial.monomial m) (MvPolynomial.coeff m p)
        = MvPolynomial.coeff m p • (MvPolynomial.monomial m) (1 : k) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    map_smul, reynoldsₗ_apply]

/-- **Degree-filtered spanning**: an invariant of total degree `≤ d` lies in
the `k`-span of the Reynolds images of the monomials of degree `≤ d`.
Combined with `totalDegree_reynolds_le`, the degree-`≤ d` piece of the
invariant ring is exactly `k`-spanned by degree-`≤ d` Reynolds images. -/
theorem mem_span_reynolds_monomial_of_totalDegree_le
    (hG : (Fintype.card G : k) ≠ 0) {p : MvPolynomial (Fin n) k}
    (hp : p ∈ FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
    {d : ℕ} (hd : p.totalDegree ≤ d) :
    p ∈ Submodule.span k
      ((fun m : Fin n →₀ ℕ => reynolds G (MvPolynomial.monomial m 1)) ''
        {m : Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ d}) := by
  rw [eq_sum_reynolds_monomial hG hp]
  refine Submodule.sum_mem _ fun m hm => ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨m, le_trans (MvPolynomial.le_totalDegree hm) hd, rfl⟩)

/-- **Unfiltered spanning**: the invariant subalgebra, as a `k`-submodule, is
contained in the span of all Reynolds images of monomials. -/
theorem fixedPoints_le_span_reynolds_monomial
    (hG : (Fintype.card G : k) ≠ 0) :
    Subalgebra.toSubmodule
        (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) ≤
      Submodule.span k
        (Set.range fun m : Fin n →₀ ℕ =>
          reynolds G (MvPolynomial.monomial m 1)) := by
  intro p hp
  rw [eq_sum_reynolds_monomial hG (show p ∈ FixedPoints.subalgebra k
    (MvPolynomial (Fin n) k) G from hp)]
  exact Submodule.sum_mem _ fun m _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

omit [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- Under the graded hypothesis, each spanning generator
`reynolds (monomial m 1)` has total degree at most `deg m` — so the
degree-filtered span really is generated in the stated degrees. -/
theorem totalDegree_reynolds_monomial_le
    (h_graded : ∀ (g : G) (p : MvPolynomial (Fin n) k),
      (g • p).totalDegree ≤ p.totalDegree)
    (m : Fin n →₀ ℕ) :
    (reynolds G (MvPolynomial.monomial m (1 : k))).totalDegree
      ≤ m.sum fun _ e => e := by
  refine le_trans (totalDegree_reynolds_le h_graded _) ?_
  rw [MvPolynomial.totalDegree_monomial m (one_ne_zero (α := k))]

end ReynoldsSpan

section NoetherReduction

/-! ### S7b-prep — the Noether bound reduced to a single multiplicative kernel

S7a's spanning layer shows the invariants are `k`-SPANNED by all Reynolds
monomial images.  Noether's bound needs more: the degree-`≤ |G|` images must
generate the invariants as a `k`-ALGEBRA.  This section packages that gap as
one clean statement.

`noetherCandidate` is the subalgebra generated by the Reynolds images of the
monomials of total degree `≤ |G|` — a finite generating set, since there are
only finitely many exponent vectors of bounded total degree
(`finite_degreeBounded_exponents`).  Unconditionally it sits inside the
invariants (`noetherCandidate_le_fixedPoints`).  The reduction theorem
`fixedPoints_eq_noetherCandidate_of_kernel` shows the reverse inclusion — and
hence Noether's degree bound, in the strong form "the invariant ring is a
finitely generated `k`-algebra with explicit generators in degree `≤ |G|`"
(`fg_of_kernel`) — follows from the single **multiplicative kernel**:

> for every monomial `m` of total degree `> |G|`, the Reynolds image
> `reynolds G (monomial m 1)` lies in `noetherCandidate`.

The kernel is the classical symmetrization/power-sum step of Noether's 1916
proof (expand `(Σᵢ (g • xᵢ) tᵢ)^e` in auxiliary variables and apply Newton's
identities, which need `|G|!` invertible).  It is deliberately NOT claimed
here — it is the S7b ACT target, with `Mathlib.RingTheory.MvPolynomial.
Symmetric.NewtonIdentities` and `...Symmetric.FundamentalTheorem` as the
intended upstream tools.  Everything in this section is unconditional except
where the kernel is an explicit named hypothesis (`hker`). -/

variable (G) in
/-- The **Noether candidate subalgebra**: generated by the Reynolds images of
the monomials of total degree at most `|G|`. -/
noncomputable def noetherCandidate : Subalgebra k (MvPolynomial (Fin n) k) :=
  Algebra.adjoin k
    ((fun m : Fin n →₀ ℕ => reynolds G (MvPolynomial.monomial m 1)) ''
      {m : Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ Fintype.card G})

/-- Low-degree Reynolds images are generators of the candidate. -/
theorem reynolds_monomial_mem_noetherCandidate_of_le
    {m : Fin n →₀ ℕ} (hm : (m.sum fun _ e => e) ≤ Fintype.card G) :
    reynolds G (MvPolynomial.monomial m 1) ∈ noetherCandidate G :=
  Algebra.subset_adjoin ⟨m, hm, rfl⟩

/-- **Unconditional inclusion**: the candidate subalgebra consists of
invariants (each generator is a Reynolds image, hence invariant). -/
theorem noetherCandidate_le_fixedPoints :
    noetherCandidate G ≤ FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G := by
  refine Algebra.adjoin_le ?_
  rintro x ⟨m, -, rfl⟩
  exact reynolds_mem_fixedPoints _

/-- **The reduction**: modulo the multiplicative kernel (high-degree Reynolds
monomial images lie in the candidate), the invariant ring IS the candidate.
Proof: `≥` is `noetherCandidate_le_fixedPoints`; for `≤`, decompose an
invariant by S7a's `eq_sum_reynolds_monomial` and place each summand in the
candidate — by generation when `deg m ≤ |G|`, by the kernel otherwise. -/
theorem fixedPoints_eq_noetherCandidate_of_kernel
    (hG : (Fintype.card G : k) ≠ 0)
    (hker : ∀ m : Fin n →₀ ℕ, Fintype.card G < (m.sum fun _ e => e) →
      reynolds G (MvPolynomial.monomial m 1) ∈ noetherCandidate G) :
    FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G = noetherCandidate G := by
  refine le_antisymm ?_ noetherCandidate_le_fixedPoints
  intro p hp
  rw [eq_sum_reynolds_monomial hG hp]
  refine Subalgebra.sum_mem _ fun m _ => Subalgebra.smul_mem _ ?_ _
  rcases le_or_lt (m.sum fun _ e => e) (Fintype.card G) with hm | hm
  · exact reynolds_monomial_mem_noetherCandidate_of_le hm
  · exact hker m hm

omit [Group G] [MulSemiringAction G (MvPolynomial (Fin n) k)]
  [SMulCommClass G k (MvPolynomial (Fin n) k)] in
/-- There are only finitely many exponent vectors of bounded total degree:
the map `m ↦ ⇑m` embeds them into the finite product `Π i, [0, D]`. -/
theorem finite_degreeBounded_exponents (D : ℕ) :
    {m : Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ D}.Finite := by
  have hsub : {m : Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ D} ⊆
      (fun f : Fin n → ℕ => Finsupp.equivFunOnFinite.symm f) ''
        Set.pi Set.univ (fun _ : Fin n => Set.Iic D) := by
    intro m hm
    refine ⟨⇑m, fun i _ => ?_, Equiv.symm_apply_apply _ m⟩
    have hm' : ∑ j ∈ m.support, m j ≤ D := hm
    by_cases hi : i ∈ m.support
    · exact le_trans
        (Finset.single_le_sum (f := fun j => m j) (fun _ _ => Nat.zero_le _) hi)
        hm'
    · simpa [Finsupp.notMem_support_iff.mp hi] using Nat.zero_le D
  exact (((Set.Finite.pi fun _ => Set.finite_Iic D).image _).subset hsub)

/-- The candidate's generating set is finite. -/
theorem finite_noetherGenerators :
    ((fun m : Fin n →₀ ℕ => reynolds G (MvPolynomial.monomial m 1)) ''
      {m : Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ Fintype.card G}).Finite :=
  (finite_degreeBounded_exponents _).image _

/-- **Conditional Noether finiteness**: modulo the multiplicative kernel, the
invariant ring is a finitely generated `k`-algebra — with the explicit finite
generating set `{reynolds (monomial m 1) : deg m ≤ |G|}`.  This is the
degree-bounded strong form of Hilbert's finiteness theorem for finite groups
in the non-modular case, reduced to the S7b ACT kernel. -/
theorem fg_of_kernel
    (hG : (Fintype.card G : k) ≠ 0)
    (hker : ∀ m : Fin n →₀ ℕ, Fintype.card G < (m.sum fun _ e => e) →
      reynolds G (MvPolynomial.monomial m 1) ∈ noetherCandidate G) :
    (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G).FG := by
  rw [fixedPoints_eq_noetherCandidate_of_kernel hG hker]
  exact Subalgebra.fg_def.mpr ⟨_, finite_noetherGenerators, rfl⟩

end NoetherReduction

end Hilbert14OQ04
