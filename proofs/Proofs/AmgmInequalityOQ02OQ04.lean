/-
  Newton's Inequalities for Three Variables — the n=3 Maclaurin Chain, Axiom-Free
  Open Question: amgm-inequality-oq-02-oq-04

  Parent: amgm-inequality-oq-02 (Maclaurin's Inequalities via Elementary Symmetric
  Polynomials), which proves the k=1 Newton inequality from scratch but AXIOMATIZES
  the general `newton_log_concavity` (Newton's inequalities) and, through it, the
  full Maclaurin chain Mₖ ≥ Mₖ₊₁.

  This file DISCHARGES that axiom completely for n = 3: both Newton inequalities and
  the full three-variable Maclaurin chain M₁ ≥ M₂ ≥ M₃ are proved with zero axioms
  (no `sorry`, no `newton_log_concavity`). The engine is exactly Maclaurin's own
  "equal-variable symmetrization", which for three variables is an explicit
  sum-of-squares identity — see oq-02-oq-04.

  Elementary symmetric polynomials of x, y, z:
    e₁ = x + y + z,   e₂ = xy + yz + zx,   e₃ = xyz.
  Normalized Maclaurin means:
    M₁ = e₁/3,   M₂ = √(e₂/3),   M₃ = (e₃)^(1/3).

  Newton's inequalities (n = 3):
    (N1)  p₁² ≥ p₀·p₂   ⟺   e₁² ≥ 3·e₂
    (N2)  p₂² ≥ p₁·p₃   ⟺   e₂² ≥ 3·e₁·e₃
  where pₖ = eₖ/C(3,k). Both are exact sum-of-squares statements:
    e₁² − 3e₂ = ½·[(x−y)² + (y−z)² + (z−x)²]           (holds for all reals)
    e₂² − 3e₁e₃ = ½·[(xy−yz)² + (yz−zx)² + (zx−xy)²]    (holds for all reals)

  Maclaurin chain steps (non-negative x, y, z):
    (M12)  M₁ ≥ M₂   ⟺   e₁² ≥ 3·e₂                    (= N1)
    (M23)  M₂ ≥ M₃   ⟺   e₂³ ≥ 27·e₃²                  (AM–GM on xy, yz, zx)

  References:
  - Maclaurin, C. (1729): A Second Letter to Martin Folkes, Esq.
  - Hardy–Littlewood–Pólya, "Inequalities" (1934) §2.22
  - Newton, I. (1707): Arithmetica Universalis
-/

import Mathlib

open Real

namespace AmgmOQ02OQ04

/-! ## Part I: Newton's inequalities for n = 3 (sum-of-squares, all reals)

Both Newton inequalities for three variables are unconditional polynomial
identities up to a manifestly non-negative remainder, so they hold for ALL real
inputs, not merely non-negative ones. The remainders are the equal-variable
symmetrization sums of squares. -/

/-- **Newton's inequality N1 for n = 3.** `e₁² ≥ 3·e₂`, i.e.
    `(x+y+z)² ≥ 3(xy+yz+zx)`. Exact remainder `½·∑ (x−y)²`. Holds for all reals. -/
theorem newton_n3_k1 (x y z : ℝ) :
    (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-- **Newton's inequality N2 for n = 3.** `e₂² ≥ 3·e₁·e₃`, i.e.
    `(xy+yz+zx)² ≥ 3(x+y+z)·xyz`. Exact remainder `½·∑ (xy−yz)²`.
    Holds for all reals (no non-negativity needed). -/
theorem newton_n3_k2 (x y z : ℝ) :
    (x * y + y * z + z * x) ^ 2 ≥ 3 * (x + y + z) * (x * y * z) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x),
    sq_nonneg (z * x - x * y)]

/-- The exact SOS identity behind `newton_n3_k1`: the gap is `½·∑(x−y)²`. -/
theorem newton_n3_k1_identity (x y z : ℝ) :
    (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x)
      = ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / 2 := by
  ring

/-- The exact SOS identity behind `newton_n3_k2`: the gap is `½·∑(xy−yz)²`. -/
theorem newton_n3_k2_identity (x y z : ℝ) :
    (x * y + y * z + z * x) ^ 2 - 3 * (x + y + z) * (x * y * z)
      = ((x * y - y * z) ^ 2 + (y * z - z * x) ^ 2 + (z * x - x * y) ^ 2) / 2 := by
  ring

/-! ## Part II: The Maclaurin chain in polynomial (radical-free) form

The chain `M₁ ≥ M₂ ≥ M₃` is equivalent, after clearing the radicals, to two
polynomial inequalities. `M12` is exactly `newton_n3_k1`. `M23` is AM–GM applied
to the three products `xy, yz, zx`. -/

/-- Three-variable AM–GM in cubed form: for non-negative `a, b, c`,
    `(a+b+c)³ ≥ 27·a·b·c`. Base lemma for the `M₂ ≥ M₃` step. -/
theorem amgm3_cubed (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 3 ≥ 27 * (a * b * c) := by
  nlinarith [mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (a - c)),
    mul_nonneg hc (sq_nonneg (a - b)), mul_nonneg (mul_nonneg ha hb) hc,
    mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- **Maclaurin step M₁ ≥ M₂, polynomial form.** `e₁² ≥ 3·e₂`
    (this is precisely Newton N1; squaring `M₁ ≥ M₂` clears the `√`). -/
theorem maclaurin_n3_12_poly (x y z : ℝ) :
    (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) :=
  newton_n3_k1 x y z

/-- **Maclaurin step M₂ ≥ M₃, polynomial form.** For non-negative `x, y, z`,
    `e₂³ ≥ 27·e₃²`, i.e. `(xy+yz+zx)³ ≥ 27·(xyz)²`. Obtained from `amgm3_cubed`
    with `a=xy, b=yz, c=zx` (note `a·b·c = (xyz)²`). -/
theorem maclaurin_n3_23_poly (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x * y + y * z + z * x) ^ 3 ≥ 27 * (x * y * z) ^ 2 := by
  have h := amgm3_cubed (x * y) (y * z) (z * x)
    (mul_nonneg hx hy) (mul_nonneg hy hz) (mul_nonneg hz hx)
  -- a·b·c = (xy)(yz)(zx) = (xyz)²
  nlinarith [h]

/-! ## Part III: The Maclaurin chain in radical (mean) form

We now state the chain for the honest Maclaurin means using `Real.sqrt` and
`Real.rpow`. Everything below is derived from the polynomial forms above; there
are no new axioms. -/

/-- First Maclaurin mean `M₁ = e₁/3`. -/
noncomputable def M1 (x y z : ℝ) : ℝ := (x + y + z) / 3

/-- Second Maclaurin mean `M₂ = √(e₂/3)`. -/
noncomputable def M2 (x y z : ℝ) : ℝ := Real.sqrt ((x * y + y * z + z * x) / 3)

/-- Third Maclaurin mean `M₃ = (e₃)^(1/3)`. -/
noncomputable def M3 (x y z : ℝ) : ℝ := (x * y * z) ^ ((1 : ℝ) / 3)

/-- **Maclaurin chain, step 1 → 2 (mean form).** `M₁ ≥ M₂` for non-negative inputs. -/
theorem maclaurin_n3_M1_ge_M2 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    M1 x y z ≥ M2 x y z := by
  unfold M1 M2
  have hsum : 0 ≤ x + y + z := by positivity
  -- √(e₂/3) ≤ √((e₁/3)²) = e₁/3, using e₂/3 ≤ (e₁/3)² from Newton N1.
  have hkey : (x * y + y * z + z * x) / 3 ≤ ((x + y + z) / 3) ^ 2 := by
    nlinarith [newton_n3_k1 x y z]
  calc Real.sqrt ((x * y + y * z + z * x) / 3)
      ≤ Real.sqrt (((x + y + z) / 3) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = (x + y + z) / 3 := by
        rw [Real.sqrt_sq (by positivity)]

/-- **Maclaurin chain, step 2 → 3 (mean form).** `M₂ ≥ M₃` for non-negative inputs.

    Both means are rewritten as the `1/6`-power of a non-negative quantity:
    `M₂ = ((e₂/3)³)^(1/6)` and `M₃ = (e₃²)^(1/6)`. The comparison then follows
    from `maclaurin_n3_23_poly` (`(e₂/3)³ ≥ e₃²`) by monotonicity of `rpow`. -/
theorem maclaurin_n3_M2_ge_M3 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    M2 x y z ≥ M3 x y z := by
  unfold M2 M3
  have he2n : 0 ≤ (x * y + y * z + z * x) / 3 := by positivity
  have he3n : 0 ≤ x * y * z := by positivity
  -- (e₂/3)³ ≥ (e₃)² , the polynomial Maclaurin step, rescaled by 27.
  have hpoly : ((x * y + y * z + z * x) / 3) ^ 3 ≥ (x * y * z) ^ 2 := by
    have h := maclaurin_n3_23_poly x y z hx hy hz
    nlinarith [h]
  -- M₃ = (e₃²)^(1/6)
  have hM3 : (x * y * z) ^ ((1 : ℝ) / 3)
      = ((x * y * z) ^ 2) ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_natCast (x * y * z) 2, ← Real.rpow_mul he3n]
    norm_num
  -- M₂ = √(e₂/3) = ((e₂/3)³)^(1/6)
  have hM2 : Real.sqrt ((x * y + y * z + z * x) / 3)
      = (((x * y + y * z + z * x) / 3) ^ 3) ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((x * y + y * z + z * x) / 3) 3,
      ← Real.rpow_mul he2n]
    norm_num
  rw [hM3, hM2]
  exact Real.rpow_le_rpow (by positivity) hpoly (by norm_num)

/-- **The full three-variable Maclaurin chain, axiom-free.**
    `M₁ ≥ M₂ ≥ M₃` for non-negative `x, y, z`. Together with `newton_n3_k1`,
    `newton_n3_k2` this discharges — for `n = 3` — the `newton_log_concavity`
    axiom and the Maclaurin chain assumed in the parent entry. -/
theorem maclaurin_n3_chain (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    M1 x y z ≥ M2 x y z ∧ M2 x y z ≥ M3 x y z :=
  ⟨maclaurin_n3_M1_ge_M2 x y z hx hy hz, maclaurin_n3_M2_ge_M3 x y z hx hy hz⟩

/-- **AM ≥ GM as the endpoints of the chain.** `M₁ ≥ M₃`, i.e.
    `(x+y+z)/3 ≥ (xyz)^(1/3)` for non-negative `x, y, z` — the classical AM–GM
    inequality recovered as the transitive closure of the Maclaurin chain. -/
theorem maclaurin_n3_am_ge_gm (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    M1 x y z ≥ M3 x y z :=
  le_trans (maclaurin_n3_M2_ge_M3 x y z hx hy hz) (maclaurin_n3_M1_ge_M2 x y z hx hy hz)

end AmgmOQ02OQ04
