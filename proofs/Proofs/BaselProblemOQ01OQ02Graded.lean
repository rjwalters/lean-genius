import Proofs.BaselProblemOQ01OQ02

/-
# The even zeta values form a rationally-graded multiplicative system

`BaselProblemOQ01OQ02` develops the axiom-free structure theorem
`ζ(2n) = qₙ·π^(2n)` (`zeta_even_eq_rat_mul_pi_pow`, `qₙ ∈ ℚ∖{0}`) and its
consequences: products, ratios, and cross-powers all land in `ℚ·π^(even)`.
Those lemmas relate an even zeta *value* to a *power of π*.

This file records the complementary — and previously unstated — fact that the
even zeta values are closed among **themselves** up to rational multiples, in a
way that respects the additive index grading:

    `ζ(2n) · ζ(2m) = q · ζ(2(n+m))`   for some `q ∈ ℚ∖{0}`.

Because `ζ(2n)·ζ(2m) = qₙqₘ·π^(2n+2m)` and `ζ(2(n+m)) = q_{n+m}·π^(2(n+m))`
share the identical power `π^(2(n+m)) = π^(2n+2m)`, the π-factors cancel and the
product of two even zeta values is a *nonzero rational multiple of the single
even zeta value at the summed index*. Equivalently, the map `n ↦ ζ(2n)` is
multiplicative up to `ℚ∖{0}`: the graded pieces `ℚ∖{0}·ζ(2n)` multiply
`(n) ⊗ (m) → (n+m)`. This is the value-level shadow of the transcendence-degree-1
structure of `ℚ(π)`; it uses only Euler's closed form, **no** `hermite_lindemann`.

0 sorries, 0 axioms.
-/

open Real

namespace BaselProblemOQ01OQ02

/-- **Graded multiplicativity of even zeta values — axiom-free.**  The product of the
    even zeta values at indices `n` and `m` is a nonzero-rational multiple of the even
    zeta value at the summed index `n + m`:

    `ζ(2n) · ζ(2m) = q · ζ(2(n+m))`,  `q ∈ ℚ∖{0}`.

    Unlike `zeta_even_product_eq_rat_mul_pi_pow` (which lands on a *power of π*), this stays
    inside the even zeta values themselves: multiplication respects the additive index grading
    `(n) ⊗ (m) → (n+m)` up to `ℚ∖{0}`.  The shared factor `π^(2(n+m)) = π^(2n+2m)` cancels
    exactly.  Uses only Euler's closed form, **no** `hermite_lindemann`. -/
theorem zeta_even_mul_eq_rat_mul_zeta_even_add (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))
        = (q : ℝ) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * (n + m))) := by
  obtain ⟨qp, hqp, hprod⟩ := zeta_even_product_eq_rat_mul_pi_pow n m hn hm
  obtain ⟨qs, hqs, hsum_eq⟩ := zeta_even_eq_rat_mul_pi_pow (n + m) (by omega)
  have hqsR : (qs : ℝ) ≠ 0 := by exact_mod_cast hqs
  refine ⟨qp / qs, div_ne_zero hqp hqs, ?_⟩
  rw [hprod, hsum_eq, show 2 * (n + m) = 2 * n + 2 * m by ring]
  push_cast
  field_simp

/-- **Graded ratio form — axiom-free.**  The ratio `ζ(2n)·ζ(2m) / ζ(2(n+m))` of the product
    of two even zeta values by the even zeta value at the summed index is a nonzero rational.
    This is the division form of `zeta_even_mul_eq_rat_mul_zeta_even_add`, valid because
    `ζ(2(n+m)) ≠ 0`.  It exhibits the even zeta values as a *rationally* graded multiplicative
    system: dividing the product back by the summed-index value returns to `ℚ`.  **No**
    `hermite_lindemann`. -/
theorem zeta_even_mul_div_zeta_even_add_rational (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))
          / (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * (n + m))) = (q : ℝ) := by
  obtain ⟨q, hq, hmul⟩ := zeta_even_mul_eq_rat_mul_zeta_even_add n m hn hm
  obtain ⟨qs, hqs, hsum_eq⟩ := zeta_even_eq_rat_mul_pi_pow (n + m) (by omega)
  have hden : (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * (n + m))) ≠ 0 := by
    rw [hsum_eq]
    exact mul_ne_zero (by exact_mod_cast hqs) (pow_ne_zero _ Real.pi_ne_zero)
  refine ⟨q, hq, ?_⟩
  rw [hmul, mul_div_assoc, div_self hden, mul_one]

end BaselProblemOQ01OQ02
