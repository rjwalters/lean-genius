import Mathlib
import Proofs.Erdos89Problem
import Proofs.Erdos89WIP01
import Proofs.Erdos89WIP01Ngon

/-
# Erdős #89 — the planar two-distance-set theorem and `g(7) = 3`
# (erdos-89-wip-01)

## The result

**A two-distance set in the plane has at most 6 points**: if all pairwise
distances of a finite set `S ⊆ ℝ²` take at most two values, then `|S| ≤ 6`
(`card_le_six_of_numDistinctDistances_le_two`). This is the planar case of the
Larman–Rogers–Seidel/Blokhuis bound `(d+1)(d+2)/2` for two-distance sets in
`ℝ^d`. (The sharp planar bound is `5`, attained by the regular pentagon; `6` is
what the rank argument gives, and it is exactly enough for the ladder payoff
below.)

## The ladder payoff: `g(7) = 3`

`minDistinctDistances_seven : g(7) = 3` — the FIRST new exact value of Erdős's
distinct-distance function beyond the classical table `g(0..5)`:

* `g(7) ≤ 3` is the regular heptagon (`minDistinctDistances_seven_le_three`,
  from `Erdos89WIP01Ngon`);
* `g(7) ≥ 3`: a 7-point set with at most 2 distinct distances would be a
  two-distance set of size `7 > 6` — impossible by the theorem above.

Bonus: `minDistinctDistances_eight_mem_Icc : g(8) ∈ [3, 4]` (monotonicity +
octagon), and `three_le_minDistinctDistances_of_seven_le : 3 ≤ g(n)` for all
`n ≥ 7`.

## Method (Blokhuis's augmentation of the polynomial method)

Work in `MvPolynomial (Fin 2) ℝ`. For a point `p` and target squared distances
`α, β > 0`, let

  `F_p(x) = (‖x − p‖² − α) · (‖x − p‖² − β)`   (`blokhuisPoly`).

If all squared pairwise distances of `S` lie in `{α, β}` then `F_p(q) = 0` for
`p ≠ q ∈ S` while `F_p(p) = αβ ≠ 0`. Each `F_p` lies in the 9-dimensional space
`W` spanned by

  `A², A·x, A·y, x², xy, y², x, y, 1`   (`A = x² + y²`, `twoDistSpace`).

**Blokhuis's trick**: the family `{F_p : p ∈ S} ∪ {x, y, 1}` is linearly
independent in `W`, so `|S| + 3 ≤ 9`. Independence: in a vanishing combination
`∑ c_p F_p + β₀x + β₁y + β₂ = 0`,

1. the coefficient of `x⁴` gives `∑ c_p = 0`;
2. the coefficients of `x³` and `y³` give `∑ c_p p = 0`;
3. evaluating at `q ∈ S` gives `c_q·αβ + ℓ(q) = 0` with `ℓ = β₀x + β₁y + β₂`;
4. multiplying (3) by `c_q` and summing, `αβ·∑ c_q² = −∑ c_q ℓ(q) = 0` by
   (1)–(2), so all `c_q = 0`; then `ℓ = 0` at three affinely independent
   points kills `β₀, β₁, β₂`.

This is the "materially new mechanism" that reopens the registered blocker on
the lower-bound side of the ladder: no coordinate geometry, no trigonometry —
only linear algebra in a fixed 9-dimensional polynomial space.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Built over the gallery defs.
-/

open Finset MvPolynomial

namespace Erdos89

/-! ### Squared distances for the custom `Erdos89.dist` -/

/-- The custom gallery distance is symmetric. -/
theorem dist_comm' (p q : EuclideanSpace ℝ (Fin 2)) :
    Erdos89.dist p q = Erdos89.dist q p := by
  unfold Erdos89.dist
  exact norm_sub_rev p q

/-- Coordinate formula for the squared distance. -/
theorem dist_sq (p q : EuclideanSpace ℝ (Fin 2)) :
    Erdos89.dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  unfold Erdos89.dist
  rw [← dist_eq_norm, EuclideanSpace.dist_eq, Fin.sum_univ_two,
    Real.sq_sqrt (by positivity)]
  simp only [Real.dist_eq, sq_abs]

/-! ### The Blokhuis polynomial family -/

/-- The squared-distance-to-`p` polynomial `(x − p₀)² + (y − p₁)²`. -/
noncomputable def distSqPoly (p : EuclideanSpace ℝ (Fin 2)) :
    MvPolynomial (Fin 2) ℝ :=
  (X 0 - C (p 0)) ^ 2 + (X 1 - C (p 1)) ^ 2

/-- Blokhuis's polynomial `F_p = (‖x − p‖² − α)(‖x − p‖² − β)` for target
squared distances `α, β`. -/
noncomputable def blokhuisPoly (α β : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    MvPolynomial (Fin 2) ℝ :=
  (distSqPoly p - C α) * (distSqPoly p - C β)

theorem eval_distSqPoly (p q : EuclideanSpace ℝ (Fin 2)) :
    eval (fun i => q i) (distSqPoly p) = Erdos89.dist q p ^ 2 := by
  simp only [distSqPoly, map_add, map_sub, map_pow, eval_X, eval_C]
  rw [dist_sq]

theorem eval_blokhuisPoly (α β : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) :
    eval (fun i => q i) (blokhuisPoly α β p)
      = (Erdos89.dist q p ^ 2 - α) * (Erdos89.dist q p ^ 2 - β) := by
  simp only [blokhuisPoly, map_mul, map_sub, eval_C, eval_distSqPoly]

/-- On the diagonal, `F_p(p) = αβ`. -/
theorem eval_blokhuisPoly_self (α β : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    eval (fun i => p i) (blokhuisPoly α β p) = α * β := by
  rw [eval_blokhuisPoly]
  have h0 : Erdos89.dist p p ^ 2 = 0 := by rw [dist_sq]; ring
  rw [h0]
  ring

/-! ### The 9-dimensional ambient space -/

/-- The nine spanning polynomials `A², Ax, Ay, x², xy, y², x, y, 1`
(`A = x² + y²`). -/
noncomputable def twoDistBasis : Fin 9 → MvPolynomial (Fin 2) ℝ
  | 0 => (X 0 ^ 2 + X 1 ^ 2) ^ 2
  | 1 => (X 0 ^ 2 + X 1 ^ 2) * X 0
  | 2 => (X 0 ^ 2 + X 1 ^ 2) * X 1
  | 3 => X 0 ^ 2
  | 4 => X 0 * X 1
  | 5 => X 1 ^ 2
  | 6 => X 0
  | 7 => X 1
  | 8 => 1

/-- The 9-dimensional space that hosts every `F_p` together with `x, y, 1`. -/
noncomputable def twoDistSpace : Submodule ℝ (MvPolynomial (Fin 2) ℝ) :=
  Submodule.span ℝ (Set.range twoDistBasis)

instance : FiniteDimensional ℝ twoDistSpace :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range twoDistBasis)

theorem finrank_twoDistSpace_le : Module.finrank ℝ twoDistSpace ≤ 9 := by
  classical
  have h : twoDistSpace
      = Submodule.span ℝ ((Finset.image twoDistBasis Finset.univ : Finset _) :
          Set (MvPolynomial (Fin 2) ℝ)) := by
    rw [twoDistSpace, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [h]
  refine le_trans (finrank_span_finset_le_card _) ?_
  refine le_trans Finset.card_image_le ?_
  simp

/-- **Expansion of `F_p` over the nine generators.** With `s = ‖p‖²`, the
coefficients are `1, −4p₀, −4p₁, 2s−α−β+4p₀², 8p₀p₁, 2s−α−β+4p₁²,
−2(2s−α−β)p₀, −2(2s−α−β)p₁, (s−α)(s−β)`. -/
theorem blokhuisPoly_expand (α β : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    blokhuisPoly α β p =
      (X 0 ^ 2 + X 1 ^ 2) ^ 2
      + C (-4 * p 0) * ((X 0 ^ 2 + X 1 ^ 2) * X 0)
      + C (-4 * p 1) * ((X 0 ^ 2 + X 1 ^ 2) * X 1)
      + C (2 * (p 0 ^ 2 + p 1 ^ 2) - α - β + 4 * p 0 ^ 2) * (X 0 ^ 2)
      + C (8 * p 0 * p 1) * (X 0 * X 1)
      + C (2 * (p 0 ^ 2 + p 1 ^ 2) - α - β + 4 * p 1 ^ 2) * (X 1 ^ 2)
      + C (-2 * (2 * (p 0 ^ 2 + p 1 ^ 2) - α - β) * p 0) * X 0
      + C (-2 * (2 * (p 0 ^ 2 + p 1 ^ 2) - α - β) * p 1) * X 1
      + C ((p 0 ^ 2 + p 1 ^ 2 - α) * (p 0 ^ 2 + p 1 ^ 2 - β)) := by
  simp only [blokhuisPoly, distSqPoly, map_mul, map_add, map_sub, map_neg,
    map_pow, map_ofNat]
  ring

/-- Every `F_p` lies in the 9-dimensional space. -/
theorem blokhuisPoly_mem (α β : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    blokhuisPoly α β p ∈ twoDistSpace := by
  have hbasis : ∀ i : Fin 9, twoDistBasis i ∈ twoDistSpace := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hC : ∀ (c : ℝ) (q : MvPolynomial (Fin 2) ℝ), q ∈ twoDistSpace →
      C c * q ∈ twoDistSpace := fun c q hq => by
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ c hq
  have hCone : ∀ c : ℝ, (C c : MvPolynomial (Fin 2) ℝ) ∈ twoDistSpace := fun c => by
    have h1 : (1 : MvPolynomial (Fin 2) ℝ) ∈ twoDistSpace := hbasis 8
    simpa [smul_eq_C_mul] using Submodule.smul_mem twoDistSpace c h1
  rw [blokhuisPoly_expand]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.add_mem _ (hbasis 0) (hC _ _ (hbasis 1)))
        (hC _ _ (hbasis 2))) (hC _ _ (hbasis 3)))) (hC _ _ (hbasis 4)))
          (hC _ _ (hbasis 5))) (hC _ _ (hbasis 6))) (hC _ _ (hbasis 7)))
            (hCone _)

/-! ### Coefficient extraction

The three coefficients that drive Blokhuis's argument: `x⁴` (leading), `x³`,
`y³`. All computations are mechanical: rewrite products of `X`'s into
`monomial` form and compare exponent vectors pointwise (`Fin.forall_fin_two`).
-/

private theorem X_def (i : Fin 2) :
    (X i : MvPolynomial (Fin 2) ℝ) = monomial (Finsupp.single i 1) 1 := rfl

private theorem coeff_x4_blokhuis (α β : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    coeff (Finsupp.single 0 4) (blokhuisPoly α β p) = 1 := by
  rw [blokhuisPoly_expand]
  simp only [coeff_add, coeff_C_mul, coeff_C, pow_two, add_mul, mul_add,
    X_def, monomial_mul, coeff_monomial, one_mul, mul_one]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply,
    Finsupp.add_apply]

private theorem coeff_x3_blokhuis (α β : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    coeff (Finsupp.single 0 3) (blokhuisPoly α β p) = -4 * p 0 := by
  rw [blokhuisPoly_expand]
  simp only [coeff_add, coeff_C_mul, coeff_C, pow_two, add_mul, mul_add,
    X_def, monomial_mul, coeff_monomial, one_mul, mul_one]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply,
    Finsupp.add_apply]

private theorem coeff_y3_blokhuis (α β : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    coeff (Finsupp.single 1 3) (blokhuisPoly α β p) = -4 * p 1 := by
  rw [blokhuisPoly_expand]
  simp only [coeff_add, coeff_C_mul, coeff_C, pow_two, add_mul, mul_add,
    X_def, monomial_mul, coeff_monomial, one_mul, mul_one]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply,
    Finsupp.add_apply]

/-! ### Blokhuis's augmented independence -/

/-- **The heart of the proof.** If all squared pairwise distances of `S` lie in
`{α, β}` with `α, β > 0`, the family `{F_p : p ∈ S} ∪ {x, y, 1}` is linearly
independent. -/
theorem blokhuis_augmented_linearIndependent (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      Erdos89.dist p q ^ 2 = α ∨ Erdos89.dist p q ^ 2 = β) :
    LinearIndependent ℝ
      (Sum.elim (fun p : {x // x ∈ S} => blokhuisPoly α β p.1)
        ![X 0, X 1, (1 : MvPolynomial (Fin 2) ℝ)]) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Sum.elim_inl,
    Sum.elim_inr] at hg
  have hv0 : (![X 0, X 1, (1 : MvPolynomial (Fin 2) ℝ)]) 0 = X 0 := rfl
  have hv1 : (![X 0, X 1, (1 : MvPolynomial (Fin 2) ℝ)]) 1 = X 1 := rfl
  have hv2 : (![X 0, X 1, (1 : MvPolynomial (Fin 2) ℝ)]) 2 = 1 := rfl
  rw [hv0, hv1, hv2] at hg
  -- hg : ∑ p, g (inl p) • F_p + (g (inr 0) • X 0 + g (inr 1) • X 1 + g (inr 2) • 1) = 0
  -- Step 1: coefficient of x⁴ ⟹ ∑ c_p = 0.
  have hs0 : ∑ p : {x // x ∈ S}, g (Sum.inl p) = 0 := by
    have h := congrArg (coeff (Finsupp.single 0 4)) hg
    simp only [coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, coeff_zero, coeff_x4_blokhuis, coeff_X', coeff_one, mul_one] at h
    simpa [Finsupp.single_eq_single_iff, Finsupp.single_eq_zero] using h
  -- Step 2: coefficients of x³ and y³ ⟹ ∑ c_p · p = 0.
  have hsx : ∑ p : {x // x ∈ S},
      g (Sum.inl p) * (p : EuclideanSpace ℝ (Fin 2)) 0 = 0 := by
    have h := congrArg (coeff (Finsupp.single 0 3)) hg
    simp only [coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, coeff_zero, coeff_x3_blokhuis, coeff_X', coeff_one] at h
    have hclean : ∑ p : {x // x ∈ S},
        g (Sum.inl p) * (-4 * (p : EuclideanSpace ℝ (Fin 2)) 0) = 0 := by
      simpa [Finsupp.single_eq_single_iff, Finsupp.single_eq_zero] using h
    have hneg : (-4 : ℝ) * ∑ p : {x // x ∈ S},
        g (Sum.inl p) * (p : EuclideanSpace ℝ (Fin 2)) 0
        = ∑ p : {x // x ∈ S},
            g (Sum.inl p) * (-4 * (p : EuclideanSpace ℝ (Fin 2)) 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hclean] at hneg
    have := mul_eq_zero.mp hneg
    simpa using this
  have hsy : ∑ p : {x // x ∈ S},
      g (Sum.inl p) * (p : EuclideanSpace ℝ (Fin 2)) 1 = 0 := by
    have h := congrArg (coeff (Finsupp.single 1 3)) hg
    simp only [coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      smul_eq_mul, coeff_zero, coeff_y3_blokhuis, coeff_X', coeff_one] at h
    have hclean : ∑ p : {x // x ∈ S},
        g (Sum.inl p) * (-4 * (p : EuclideanSpace ℝ (Fin 2)) 1) = 0 := by
      simpa [Finsupp.single_eq_single_iff, Finsupp.single_eq_zero] using h
    have hneg : (-4 : ℝ) * ∑ p : {x // x ∈ S},
        g (Sum.inl p) * (p : EuclideanSpace ℝ (Fin 2)) 1
        = ∑ p : {x // x ∈ S},
            g (Sum.inl p) * (-4 * (p : EuclideanSpace ℝ (Fin 2)) 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hclean] at hneg
    have := mul_eq_zero.mp hneg
    simpa using this
  -- Step 3: evaluation at q ∈ S ⟹ c_q·αβ + ℓ(q) = 0.
  have heval : ∀ (q : EuclideanSpace ℝ (Fin 2)) (hq : q ∈ S),
      g (Sum.inl ⟨q, hq⟩) * (α * β)
        + (g (Sum.inr 0) * q 0 + g (Sum.inr 1) * q 1 + g (Sum.inr 2)) = 0 := by
    intro q hq
    have h := congrArg (eval (fun i : Fin 2 => q i)) hg
    simp only [map_add, map_sum, smul_eval, eval_X, map_one, map_zero,
      mul_one] at h
    rw [Finset.sum_eq_single (⟨q, hq⟩ : {x // x ∈ S})] at h
    · rw [eval_blokhuisPoly_self] at h
      exact h
    · intro p _ hne
      rw [eval_blokhuisPoly]
      have hpq : (p : EuclideanSpace ℝ (Fin 2)) ≠ q := fun he =>
        hne (Subtype.ext he)
      have hd : Erdos89.dist q (p : EuclideanSpace ℝ (Fin 2)) ^ 2 = α ∨
          Erdos89.dist q (p : EuclideanSpace ℝ (Fin 2)) ^ 2 = β := by
        rw [dist_comm']
        exact hS _ p.2 q hq hpq
      rcases hd with hd | hd
      · rw [hd, sub_self, zero_mul, mul_zero]
      · rw [hd, sub_self, mul_zero, mul_zero]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  -- Step 4: weighted sum of Step 3 ⟹ all c_q = 0.
  have hc : ∀ p : {x // x ∈ S}, g (Sum.inl p) = 0 := by
    have h0 : ∑ p : {x // x ∈ S}, g (Sum.inl p) *
        (g (Sum.inl p) * (α * β)
          + (g (Sum.inr 0) * (p : EuclideanSpace ℝ (Fin 2)) 0
            + g (Sum.inr 1) * (p : EuclideanSpace ℝ (Fin 2)) 1
            + g (Sum.inr 2))) = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [heval (p : EuclideanSpace ℝ (Fin 2)) p.2, mul_zero]
    have hexp : ∑ p : {x // x ∈ S}, g (Sum.inl p) *
        (g (Sum.inl p) * (α * β)
          + (g (Sum.inr 0) * (p : EuclideanSpace ℝ (Fin 2)) 0
            + g (Sum.inr 1) * (p : EuclideanSpace ℝ (Fin 2)) 1
            + g (Sum.inr 2))) =
        (α * β) * (∑ p : {x // x ∈ S}, g (Sum.inl p) ^ 2)
          + g (Sum.inr 0) * (∑ p : {x // x ∈ S},
              g (Sum.inl p) * (p : EuclideanSpace ℝ (Fin 2)) 0)
          + g (Sum.inr 1) * (∑ p : {x // x ∈ S},
              g (Sum.inl p) * (p : EuclideanSpace ℝ (Fin 2)) 1)
          + g (Sum.inr 2) * (∑ p : {x // x ∈ S}, g (Sum.inl p)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hexp, hsx, hsy, hs0, mul_zero, mul_zero, mul_zero, add_zero, add_zero,
      add_zero] at h0
    have hαβ : α * β ≠ 0 := by positivity
    have hzero : ∑ p : {x // x ∈ S}, g (Sum.inl p) ^ 2 = 0 :=
      (mul_eq_zero.mp h0).resolve_left hαβ
    intro p
    have hp := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (g (Sum.inl i)))).mp hzero p (Finset.mem_univ p)
    exact sq_eq_zero_iff.mp hp
  -- Step 5: with all c_q = 0, the affine part dies at three points.
  have hg' : g (Sum.inr 0) • (X 0 : MvPolynomial (Fin 2) ℝ)
      + g (Sum.inr 1) • (X 1 : MvPolynomial (Fin 2) ℝ)
      + g (Sum.inr 2) • (1 : MvPolynomial (Fin 2) ℝ) = 0 := by
    have hsum0 : ∑ p : {x // x ∈ S},
        g (Sum.inl p) • blokhuisPoly α β (p : EuclideanSpace ℝ (Fin 2)) = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [hc p, zero_smul]
    rw [hsum0, zero_add] at hg
    exact hg
  have hb2 : g (Sum.inr 2) = 0 := by
    have h := congrArg (eval (fun _ : Fin 2 => (0 : ℝ))) hg'
    simpa [smul_eval] using h
  have hb0 : g (Sum.inr 0) = 0 := by
    have h := congrArg (eval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) hg'
    simpa [smul_eval, hb2] using h
  have hb1 : g (Sum.inr 1) = 0 := by
    have h := congrArg (eval (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)) hg'
    simpa [smul_eval, hb2] using h
  rintro (p | j)
  · exact hc p
  · fin_cases j
    · exact hb0
    · exact hb1
    · exact hb2

/-! ### The two-distance-set theorem -/

/-- **Core bound (squared form).** If all squared pairwise distances of `S`
lie in `{α, β}` with `α, β > 0`, then `|S| ≤ 6`. -/
theorem card_le_six_of_sq_two_distances (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      Erdos89.dist p q ^ 2 = α ∨ Erdos89.dist p q ^ 2 = β) :
    S.card ≤ 6 := by
  classical
  have hli := blokhuis_augmented_linearIndependent α β hα hβ S hS
  have hmem : ∀ i : {x // x ∈ S} ⊕ Fin 3,
      Sum.elim (fun p : {x // x ∈ S} => blokhuisPoly α β p.1)
        ![X 0, X 1, (1 : MvPolynomial (Fin 2) ℝ)] i ∈ twoDistSpace := by
    rintro (p | j)
    · exact blokhuisPoly_mem α β p.1
    · fin_cases j
      · exact Submodule.subset_span ⟨6, rfl⟩
      · exact Submodule.subset_span ⟨7, rfl⟩
      · exact Submodule.subset_span ⟨8, rfl⟩
  have hli' : LinearIndependent ℝ (fun i : {x // x ∈ S} ⊕ Fin 3 =>
      (⟨Sum.elim (fun p : {x // x ∈ S} => blokhuisPoly α β p.1)
        ![X 0, X 1, (1 : MvPolynomial (Fin 2) ℝ)] i, hmem i⟩ : twoDistSpace)) :=
    LinearIndependent.of_comp twoDistSpace.subtype hli
  have hcard := hli'.fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] at hcard
  have h9 := finrank_twoDistSpace_le
  omega

/-- **Two-distance-set theorem (distance form).** If all pairwise distances of
`S ⊆ ℝ²` take at most the two positive values `a, b`, then `|S| ≤ 6`. -/
theorem card_le_six_of_two_distances (S : Finset (EuclideanSpace ℝ (Fin 2)))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      Erdos89.dist p q = a ∨ Erdos89.dist p q = b) :
    S.card ≤ 6 := by
  refine card_le_six_of_sq_two_distances (a ^ 2) (b ^ 2) (by positivity)
    (by positivity) S fun p hp q hq hpq => ?_
  rcases h p hp q hq hpq with h' | h'
  · exact Or.inl (by rw [h'])
  · exact Or.inr (by rw [h'])

/-! ### Hooking into the gallery counting objects -/

/-- Members of `distinctDistances` are positive (they survive the filter). -/
theorem pos_of_mem_distinctDistances {S : Finset (EuclideanSpace ℝ (Fin 2))}
    {x : ℝ} (hx : x ∈ distinctDistances S) : 0 < x := by
  unfold distinctDistances at hx
  exact (Finset.mem_filter.mp hx).2

/-- The distance between two distinct members of `S` is a distinct distance. -/
theorem dist_mem_distinctDistances {S : Finset (EuclideanSpace ℝ (Fin 2))}
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    Erdos89.dist p q ∈ distinctDistances S := by
  unfold distinctDistances
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩,
      dist_pos_of_ne hpq⟩

/-- **Two-distance-set theorem (counting form).** A planar set realising at
most `2` distinct distances has at most `6` points. -/
theorem card_le_six_of_numDistinctDistances_le_two
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (h : numDistinctDistances S ≤ 2) : S.card ≤ 6 := by
  by_contra hcard
  push_neg at hcard
  obtain ⟨p₀, hp₀, q₀, hq₀, hne⟩ := Finset.one_lt_card.mp
    (by omega : 1 < S.card)
  have hDne : (distinctDistances S).Nonempty :=
    ⟨_, dist_mem_distinctDistances hp₀ hq₀ hne⟩
  unfold numDistinctDistances at h
  have h1 : 1 ≤ (distinctDistances S).card := Finset.card_pos.mpr hDne
  have hcases : (distinctDistances S).card = 1 ∨
      (distinctDistances S).card = 2 := by omega
  rcases hcases with h1' | h2'
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1'
    have hpa : 0 < a := pos_of_mem_distinctDistances
      (by rw [ha]; exact Finset.mem_singleton_self a)
    have h6 : S.card ≤ 6 := by
      refine card_le_six_of_two_distances S hpa hpa fun p hp q hq hpq => ?_
      have hmem := dist_mem_distinctDistances hp hq hpq
      rw [ha, Finset.mem_singleton] at hmem
      exact Or.inl hmem
    omega
  · obtain ⟨a, b, hab, hD⟩ := Finset.card_eq_two.mp h2'
    have hpa : 0 < a := pos_of_mem_distinctDistances (by rw [hD]; simp)
    have hpb : 0 < b := pos_of_mem_distinctDistances (by rw [hD]; simp)
    have h6 : S.card ≤ 6 := by
      refine card_le_six_of_two_distances S hpa hpb fun p hp q hq hpq => ?_
      have hmem := dist_mem_distinctDistances hp hq hpq
      rw [hD] at hmem
      rcases Finset.mem_insert.mp hmem with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Finset.mem_singleton.mp h')
    omega

/-- **Seven points force three distances.** Contrapositive of the
two-distance-set theorem through the counting object. -/
theorem three_le_numDistinctDistances_of_seven_le_card
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (h7 : 7 ≤ S.card) :
    3 ≤ numDistinctDistances S := by
  by_contra h
  push_neg at h
  have := card_le_six_of_numDistinctDistances_le_two S (by omega)
  omega

/-! ### The ladder payoff: `g(7) = 3` -/

/-- **`g(7) ≥ 3`.** Every 7-point configuration realises at least three
distinct distances. -/
theorem three_le_minDistinctDistances_seven : 3 ≤ minDistinctDistances 7 := by
  have hne : {k | ∃ S : Finset (EuclideanSpace ℝ (Fin 2)),
      ∃ _ : S.card = 7, numDistinctDistances S = k}.Nonempty := by
    obtain ⟨S, hS⟩ := exists_card_eq 7
    exact ⟨numDistinctDistances S, S, hS, rfl⟩
  obtain ⟨U, hUcard, hUeq⟩ := Nat.sInf_mem hne
  rw [minDistinctDistances, ← hUeq]
  exact three_le_numDistinctDistances_of_seven_le_card U (le_of_eq hUcard.symm)

/-- **`g(7) = 3`** — the first new exact value of Erdős's distinct-distance
function beyond the classical table: the heptagon gives `≤ 3`
(`Erdos89WIP01Ngon`), the two-distance-set theorem gives `≥ 3`. -/
theorem minDistinctDistances_seven : minDistinctDistances 7 = 3 :=
  le_antisymm minDistinctDistances_seven_le_three
    three_le_minDistinctDistances_seven

/-- `3 ≤ g(n)` for every `n ≥ 7`, by monotonicity. -/
theorem three_le_minDistinctDistances_of_seven_le {n : ℕ} (hn : 7 ≤ n) :
    3 ≤ minDistinctDistances n :=
  le_trans three_le_minDistinctDistances_seven (minDistinctDistances_mono hn)

/-- **Sandwich `3 ≤ g(8) ≤ 4`.** The lower half lifts `g(7) = 3` through
monotonicity; the upper half is the regular octagon. The true value is
`g(8) = 4`; closing it needs a sharp three-distance-set bound (`≤ 7` points),
beyond the rank method used here. -/
theorem minDistinctDistances_eight_mem_Icc :
    minDistinctDistances 8 ∈ Set.Icc 3 4 := by
  constructor
  · exact three_le_minDistinctDistances_of_seven_le (by norm_num)
  · have h := minDistinctDistances_le_half 8
    norm_num at h
    exact h

end Erdos89
