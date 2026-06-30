import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

/-!
# AM-GM OQ-02 → OQ-01 → OQ-01 → OQ-01: power sums are a complete invariant

The parent (`amgm-inequality-oq-02-oq-01-oq-01`) packages Mathlib's Newton–Girard recurrence
`k·eₖ = (−1)^{k+1} Σ_{i+j=k, i<k} (−1)ⁱ eᵢ pⱼ` (`MvPolynomial.mul_esymm_eq_sum`).  A sibling
(`…-oq-02`) used the *inverted* recurrence over a ℚ-algebra to show that the power sums and the
elementary symmetric polynomials generate the same subalgebra.

This entry answers a different open question of the parent: **to what extent do the power sums
determine the rest of the symmetric data?**  We prove the moment-determinacy (complete-invariant)
theorem:

> over any characteristic-zero commutative ring `K`, if two families `v, w : σ → K` have equal
> power sums `Σᵢ vᵢʲ = Σᵢ wᵢʲ` for every `1 ≤ j ≤ n`, then they have equal elementary symmetric
> functions `eₖ(v) = eₖ(w)` for every `k ≤ n`.

The proof is a single strong induction running the *forward* Newton recurrence: at stage `k` the
right-hand side involves only lower elementary symmetric functions (equal by the inductive
hypothesis) and power sums `pⱼ`, `1 ≤ j ≤ k` (equal by hypothesis), so `k·eₖ(v) = k·eₖ(w)`, and
`k ≠ 0` in characteristic zero cancels.  Specialising at `n = |σ|`, where the elementary
symmetric functions of degree `> |σ|` both vanish, shows that the first `|σ|` power sums determine
**all** elementary symmetric functions — equivalently the monic polynomial `∏ᵢ (X − vᵢ)` — so the
power sums `p₁, …, p_{|σ|}` are a complete invariant of an unordered `|σ|`-tuple.

The symmetric polynomials are taken over `ℤ`; evaluation lands in any characteristic-zero `K`
(`ℚ`, `ℝ`, `ℂ`, `ℤ`, …), where the necessary division by `k` happens in `K`.  `0` axioms.

## Main results

* `aeval_mul_esymm_eq_sum`         — the forward Newton identity evaluated at a point.
* `esymm_eval_eq_of_psum_eval_eq`  — equal power sums (`1 ≤ j ≤ n`) ⟹ equal `eₖ` (`k ≤ n`).
* `esymm_eval_eq_of_psum_eval_eq_card` — at `n = |σ|`, *all* `eₖ` agree.
* `prod_X_sub_C_eq_of_psum_eval_eq` — the monic polynomials `∏ᵢ (X − vᵢ)` agree: power sums
  `p₁, …, p_{|σ|}` are a complete invariant.
-/

namespace AmgmInequalityOQ02OQ01OQ01OQ01

open MvPolynomial Finset

variable {σ : Type*} [Fintype σ] {K : Type*} [CommRing K]

/-- Elementary symmetric functions of degree exceeding the number of variables vanish: there are
no squarefree monomials of degree `> |σ|`. -/
theorem esymm_eval_eq_zero (v : σ → K) {k : ℕ} (hk : Fintype.card σ < k) :
    aeval v (esymm σ ℤ k) = 0 := by
  rw [esymm, Finset.powersetCard_eq_empty.mpr (by rwa [Finset.card_univ]), Finset.sum_empty,
    map_zero]

/-- **The forward Newton identity, evaluated at a point.** Applying the evaluation algebra
homomorphism `aeval v` to Mathlib's `mul_esymm_eq_sum` turns the `MvPolynomial` identity into the
numerical Newton–Girard recurrence for the symmetric functions of the family `v : σ → K`:

`k · eₖ(v) = (−1)^{k+1} Σ_{i+j=k, i<k} (−1)ⁱ eᵢ(v) pⱼ(v)`. -/
theorem aeval_mul_esymm_eq_sum (v : σ → K) (k : ℕ) :
    (k : K) * aeval v (esymm σ ℤ k)
      = (-1) ^ (k + 1) *
        ∑ a ∈ antidiagonal k with a.1 < k,
          (-1) ^ a.1 * aeval v (esymm σ ℤ a.1) * aeval v (psum σ ℤ a.2) := by
  have h := congrArg (aeval (R := ℤ) v) (mul_esymm_eq_sum σ ℤ k)
  simpa [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] using h

variable [IsDomain K] [CharZero K]

/-- **Power sums determine elementary symmetric functions (moment determinacy).** If two families
`v, w : σ → K` over a characteristic-zero ring have equal power sums `pⱼ(v) = pⱼ(w)` for every
`1 ≤ j ≤ n`, then their elementary symmetric functions agree, `eₖ(v) = eₖ(w)`, for every `k ≤ n`.

The proof is a strong induction on `k`: the forward Newton recurrence expresses `k·eₖ` through
elementary symmetric functions of degree `< k` (equal by the inductive hypothesis) and power sums
`pⱼ` with `1 ≤ j ≤ k ≤ n` (equal by hypothesis); cancelling the nonzero scalar `k` (a nonzero
element of the domain `K`, by characteristic zero) gives the claim. -/
theorem esymm_eval_eq_of_psum_eval_eq (v w : σ → K) (n : ℕ)
    (hp : ∀ j, 1 ≤ j → j ≤ n → aeval v (psum σ ℤ j) = aeval w (psum σ ℤ j)) :
    ∀ k, k ≤ n → aeval v (esymm σ ℤ k) = aeval w (esymm σ ℤ k) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkn
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [esymm_zero]
    · have hkne : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      have hsum :
          (∑ a ∈ antidiagonal k with a.1 < k,
              (-1) ^ a.1 * aeval v (esymm σ ℤ a.1) * aeval v (psum σ ℤ a.2))
            = ∑ a ∈ antidiagonal k with a.1 < k,
              (-1) ^ a.1 * aeval w (esymm σ ℤ a.1) * aeval w (psum σ ℤ a.2) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [mem_filter, mem_antidiagonal] at ha
        obtain ⟨hsum, hlt⟩ := ha
        have he : aeval v (esymm σ ℤ a.1) = aeval w (esymm σ ℤ a.1) :=
          ih a.1 hlt (le_trans hlt.le hkn)
        have hpe : aeval v (psum σ ℤ a.2) = aeval w (psum σ ℤ a.2) :=
          hp a.2 (by omega) (by omega)
        rw [he, hpe]
      have hk_eq : (k : K) * aeval v (esymm σ ℤ k) = (k : K) * aeval w (esymm σ ℤ k) := by
        rw [aeval_mul_esymm_eq_sum v k, aeval_mul_esymm_eq_sum w k, hsum]
      exact mul_left_cancel₀ hkne hk_eq

/-- **The first `|σ|` power sums determine every elementary symmetric function.** Beyond degree
`|σ|` the elementary symmetric polynomials vanish, so agreement of the power sums `p₁, …, p_{|σ|}`
forces agreement of `eₖ(v)` and `eₖ(w)` for *all* `k`, not merely `k ≤ |σ|`. -/
theorem esymm_eval_eq_of_psum_eval_eq_card (v w : σ → K)
    (hp : ∀ j, 1 ≤ j → j ≤ Fintype.card σ → aeval v (psum σ ℤ j) = aeval w (psum σ ℤ j)) :
    ∀ k, aeval v (esymm σ ℤ k) = aeval w (esymm σ ℤ k) := by
  intro k
  rcases le_or_gt k (Fintype.card σ) with hk | hk
  · exact esymm_eval_eq_of_psum_eval_eq v w (Fintype.card σ) hp k hk
  · rw [esymm_eval_eq_zero v hk, esymm_eval_eq_zero w hk]

/-- **Power sums are a complete invariant of an unordered tuple.** If two families
`v, w : σ → K` over a characteristic-zero domain have equal power sums `pⱼ(v) = pⱼ(w)` for every
`1 ≤ j ≤ |σ|`, then they define the *same monic polynomial* `∏ᵢ (X + vᵢ) = ∏ᵢ (X + wᵢ)`.

By Vieta's formulas the coefficients of `∏ᵢ (X + vᵢ)` are precisely the elementary symmetric
functions `eⱼ(v)`, which agree with `eⱼ(w)` by `esymm_eval_eq_of_psum_eval_eq_card`. Hence
`p₁, …, p_{|σ|}` determine the multiset `{vᵢ}` up to reordering — equivalently the roots of the
polynomial — which is the sharp form of Newton's identities as a moment problem for finite
multisets. -/
theorem prod_X_add_C_eq_of_psum_eval_eq (v w : σ → K)
    (hp : ∀ j, 1 ≤ j → j ≤ Fintype.card σ → aeval v (psum σ ℤ j) = aeval w (psum σ ℤ j)) :
    ∏ i, (Polynomial.X + Polynomial.C (v i)) = ∏ i, (Polynomial.X + Polynomial.C (w i)) := by
  have key : ∀ u : σ → K, (∏ i, (Polynomial.X + Polynomial.C (u i)))
      = ∑ j ∈ Finset.range (Fintype.card σ + 1),
          Polynomial.C (aeval u (esymm σ ℤ j)) * Polynomial.X ^ (Fintype.card σ - j) := by
    intro u
    rw [Finset.prod,
      show (fun i => Polynomial.X + Polynomial.C (u i))
          = (fun r => Polynomial.X + Polynomial.C r) ∘ u from rfl,
      ← Multiset.map_map, Multiset.prod_X_add_C_eq_sum_esymm]
    have hcard : Multiset.card (Finset.univ.val.map u) = Fintype.card σ := by
      rw [Multiset.card_map, ← Finset.card_def, Finset.card_univ]
    rw [hcard]
    exact Finset.sum_congr rfl fun j _ => by rw [aeval_esymm_eq_multiset_esymm]
  rw [key v, key w]
  exact Finset.sum_congr rfl fun j _ => by
    rw [esymm_eval_eq_of_psum_eval_eq_card v w hp j]

end AmgmInequalityOQ02OQ01OQ01OQ01
