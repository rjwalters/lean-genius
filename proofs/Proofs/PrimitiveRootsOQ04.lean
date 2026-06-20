/-
  The primitive-root vertex-product identity and its geometric reading
  ====================================================================

  For a primitive `m`-th root of unity `μ` in an integral domain,
                ∏_{k=1}^{m-1} (1 - μ^k) = m.
  Mathlib proves this (`IsPrimitiveRoot.prod_one_sub_pow_eq_order`, stated with
  `m = n+1` to dodge the side condition `m ≠ 0`) together with its sign-flipped
  companion `∏ (μ^k - 1)` and the divisibility `(μ-1)^k ∣ m`. What Mathlib does
  *not* record is the analytic/geometric reading of the identity over `ℂ`.

  This entry supplies it:

  * `prod_one_sub_pow`          — the order identity (re-export, attributed).
  * `neg_one_pow_mul_prod_pow_sub` — the sign companion (re-export, attributed).
  * `prod_norm_one_sub_pow`     — **new**: taking moduli over `ℂ`,
        ∏_{k=1}^{m-1} ‖1 - μ^k‖ = m.
      Geometrically: the product of the distances from one vertex of a regular
      `m`-gon inscribed in the unit circle to the other `m-1` vertices is `m`.
      (Not stated in Mathlib.)
  * `prod_one_sub_exp`          — **new**: the explicit instantiation at the
      standard primitive root `μ = exp(2πi/m)`,
        ∏_{k=0}^{m-2} (1 - exp(2πi(k+1)/m)) = m.
  * `prod_norm_one_sub_exp`     — **new**: the regular-polygon chord product in
      fully explicit form.

  Concrete checks `m = 2, 3` close the file.
-/
import Mathlib

open Finset Complex Real

namespace PrimitiveRootsOQ04

variable {R : Type*} [CommRing R] [IsDomain R]

/-! ### The order identity over an integral domain (Mathlib core) -/

/-- **Vertex product identity.** For a primitive `(n+1)`-th root of unity `μ`,
`∏_{k=0}^{n-1} (1 - μ^{k+1}) = n+1`; equivalently `∏_{j=1}^{m-1}(1 - μ^j) = m`
with `m = n+1`. Direct re-export of `IsPrimitiveRoot.prod_one_sub_pow_eq_order`;
the `n+1` form avoids the side condition `m ≠ 0`. -/
theorem prod_one_sub_pow {n : ℕ} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    ∏ k ∈ range n, (1 - μ ^ (k + 1)) = (n + 1 : R) :=
  hμ.prod_one_sub_pow_eq_order

/-- **Sign companion.** `(-1)^n · ∏_{k=0}^{n-1} (μ^{k+1} - 1) = n+1`. Re-export of
`IsPrimitiveRoot.prod_pow_sub_one_eq_order`. -/
theorem neg_one_pow_mul_prod_pow_sub {n : ℕ} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    (-1) ^ n * ∏ k ∈ range n, (μ ^ (k + 1) - 1) = (n + 1 : R) :=
  hμ.prod_pow_sub_one_eq_order

/-! ### The geometric corollary over `ℂ` (new) -/

/-- **Regular-polygon chord product.** Over `ℂ`, taking moduli in the vertex-product
identity: for a primitive `(n+1)`-th root of unity `μ`,
`∏_{k=0}^{n-1} ‖1 - μ^{k+1}‖ = n+1`.

Geometrically, the `m = n+1` points `μ^0, μ^1, …, μ^{m-1}` are the vertices of a
regular `m`-gon inscribed in the unit circle; the product of the distances from the
vertex `1 = μ^0` to all `m-1` other vertices equals `m`. This norm form is not
stated in Mathlib. -/
theorem prod_norm_one_sub_pow {n : ℕ} {μ : ℂ} (hμ : IsPrimitiveRoot μ (n + 1)) :
    ∏ k ∈ range n, ‖1 - μ ^ (k + 1)‖ = (n + 1 : ℝ) := by
  rw [← norm_prod, hμ.prod_one_sub_pow_eq_order]
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring]
  rw [Complex.norm_natCast]
  push_cast; ring

/-! ### Explicit instantiation at `exp(2πi/m)` (new) -/

/-- **Explicit vertex product.** With the standard primitive `(n+1)`-th root
`μ = exp(2πi/(n+1))`, the identity reads
`∏_{k=0}^{n-1} (1 - exp(2πi(k+1)/(n+1))) = n+1`. -/
theorem prod_one_sub_exp (n : ℕ) :
    ∏ k ∈ range n, (1 - Complex.exp (2 * π * I * (k + 1) / (n + 1))) = (n + 1 : ℂ) := by
  have hμ := Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)
  -- Rewrite each factor as `1 - μ^(k+1)` with `μ = exp(2πi/(n+1))` *before* applying the
  -- order identity, so the `n+1` in the exponent's denominator is not touched.
  have step : ∏ k ∈ range n, (1 - Complex.exp (2 * π * I * (k + 1) / (n + 1)))
      = ∏ k ∈ range n, (1 - Complex.exp (2 * ↑π * I / ↑(n + 1)) ^ (k + 1)) := by
    refine Finset.prod_congr rfl (fun k _ => ?_)
    have hk : Complex.exp (2 * π * I * (k + 1) / (n + 1))
        = Complex.exp (2 * ↑π * I / ↑(n + 1)) ^ (k + 1) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hk]
  rw [step]
  exact hμ.prod_one_sub_pow_eq_order

/-- **Explicit regular-polygon chord product.** With `μ = exp(2πi/(n+1))`,
`∏_{k=0}^{n-1} ‖1 - exp(2πi(k+1)/(n+1))‖ = n+1`: the product of the chord lengths
from one vertex of a regular `(n+1)`-gon to the others. -/
theorem prod_norm_one_sub_exp (n : ℕ) :
    ∏ k ∈ range n, ‖1 - Complex.exp (2 * π * I * (k + 1) / (n + 1))‖ = (n + 1 : ℝ) := by
  rw [← norm_prod, prod_one_sub_exp n]
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring]
  rw [Complex.norm_natCast]
  push_cast; ring

/-! ### Concrete values -/

/-- `m = 2`: the two square roots of unity are `±1`, and `1 - (-1) = 2`. -/
example {μ : R} (hμ : IsPrimitiveRoot μ 2) : ∏ k ∈ range 1, (1 - μ ^ (k + 1)) = (2 : R) := by
  rw [prod_one_sub_pow (n := 1) hμ]; norm_num

/-- `m = 3`: `(1 - μ)(1 - μ²) = 3` for a primitive cube root of unity. -/
example {μ : R} (hμ : IsPrimitiveRoot μ 3) :
    ∏ k ∈ range 2, (1 - μ ^ (k + 1)) = (3 : R) := by
  rw [prod_one_sub_pow (n := 2) hμ]; norm_num

end PrimitiveRootsOQ04
