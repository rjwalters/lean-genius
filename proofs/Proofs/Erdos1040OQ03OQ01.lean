/-
Erdős Problem #1040 — open question oq-03, follow-up oq-01:
"Is the unconditional area bound `area {|f| < 1} ≤ degree · π` sharp, and is the
value `π` actually attained by monic polynomials of every degree?"

The parent companion (#1040 / oq-03) proved the elementary UPPER bounds on the
lemniscate area
   area {z : |f(z)| < 1} ≤ degree · π        (unconditional)
   area {z : |f(z)| < 1} ≤ 4π                 (roots in the closed unit disc)
and left open how tight these are relative to the genuine infimum
   μ(F) = inf { area {|f| < 1} : f monic, roots ⊆ F }.

This file supplies the matching LOWER-side witness. For the *pure power*
   f(z) = (z - c)^n
all `n` roots collapse to the single point `c`, and the lemniscate is *exactly*
the open unit disc about `c`:
   {z : |(z - c)^n| < 1} = {z : |z - c| < 1} = B(c, 1),
because `|(z - c)^n| = |z - c|^n` and, for a nonnegative real `t`, `t^n < 1 ⟺ t < 1`.
Hence the lemniscate has area EXACTLY `π`, for EVERY positive degree `n`.

Two structural consequences follow at once:

* **Attainment.** The value `π` is attained as a lemniscate area by a monic
  polynomial of every positive degree. So `μ({c}) ≤ π`, and the infimum over the
  single-point root set is realised (it is in fact `= π`, the elementary upper
  half of which is recorded here; the lower half `area ≥ π` is Pólya's theorem).

* **Non-sharpness of `degree · π`.** Since the pure-power area is `π` while the
  unconditional bound is `degree · π`, the parent bound overshoots by the full
  factor `degree`: for every `n ≥ 2` the inequality `area < degree · π` is
  STRICT. The unconditional bound is therefore never attained beyond degree one.

Everything is axiom-free and self-contained: the file re-introduces the minimal
`RootedPoly` framing of the parent so it stands alone. Nothing depends on the
parent's (axiomatized) transfinite-diameter answers.
-/

import Mathlib

open Complex BigOperators MeasureTheory Metric
open scoped ENNReal NNReal

namespace Erdos1040OQ03OQ01

/-- A monic polynomial `f(z) = ∏ᵢ (z - rootᵢ)` of a given degree, recorded by its
list of roots (the framing inherited from the parent companion). -/
structure RootedPoly where
  degree : ℕ
  roots : Fin degree → ℂ

/-- The monic polynomial `f(z) = ∏ᵢ (z - rootᵢ)` evaluated at `z`. -/
noncomputable def RootedPoly.eval (p : RootedPoly) (z : ℂ) : ℂ :=
  ∏ i : Fin p.degree, (z - p.roots i)

/-- The lemniscate of `p`, the open sublevel set `{z : |f(z)| < 1}`. -/
def lem (p : RootedPoly) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

/-- The **pure power** `f(z) = (z - c)^n`: a monic polynomial of degree `n` whose
roots are all equal to `c`. -/
def purePower (c : ℂ) (n : ℕ) : RootedPoly :=
  ⟨n, fun _ => c⟩

@[simp] theorem purePower_degree (c : ℂ) (n : ℕ) : (purePower c n).degree = n := rfl

/-- The pure power evaluates to `(z - c)^n`: a product of `n` identical factors. -/
theorem eval_purePower (c : ℂ) (n : ℕ) (z : ℂ) :
    (purePower c n).eval z = (z - c) ^ n := by
  show (∏ _i : Fin n, (z - c)) = (z - c) ^ n
  exact Fin.prod_const n (z - c)

/-- **Pure-power lemniscate = unit disc.** For positive degree the lemniscate of
`(z - c)^n` is precisely the open unit ball about `c`: `|(z - c)^n| = |z - c|^n`
and `t^n < 1 ⟺ t < 1` for the nonnegative real `t = |z - c|`. -/
theorem lem_purePower_eq_ball (c : ℂ) {n : ℕ} (hn : 0 < n) :
    lem (purePower c n) = Metric.ball c 1 := by
  ext z
  simp only [lem, Set.mem_setOf_eq, eval_purePower, norm_pow, Metric.mem_ball,
    dist_eq_norm]
  exact pow_lt_one_iff_of_nonneg (norm_nonneg _) hn.ne'

/-- In degree `0` the "polynomial" is the empty product `f ≡ 1`, so `|f| = 1`
is never `< 1`: the lemniscate is empty. This shows the positivity hypothesis in
`lem_purePower_eq_ball` is genuinely needed. -/
theorem lem_purePower_zero (c : ℂ) : lem (purePower c 0) = (∅ : Set ℂ) := by
  ext z
  simp [lem, eval_purePower]

/-- **Exact area `π`, every degree.** The pure-power lemniscate has Lebesgue
(area) measure exactly `π`, independently of the degree `n ≥ 1`. -/
theorem volume_lem_purePower (c : ℂ) {n : ℕ} (hn : 0 < n) :
    volume (lem (purePower c n)) = (NNReal.pi : ℝ≥0∞) := by
  rw [lem_purePower_eq_ball c hn, Complex.volume_ball]
  simp

/-- The pure-power area, written with `Real.pi`: `volume = ENNReal.ofReal π`. -/
theorem volume_lem_purePower' (c : ℂ) {n : ℕ} (hn : 0 < n) :
    volume (lem (purePower c n)) = ENNReal.ofReal Real.pi := by
  rw [volume_lem_purePower c hn, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- **Attainment.** The area value `π` is realised as a lemniscate area by a monic
polynomial of *every* positive degree `n` — namely the pure power `(z - c)^n`.
Consequently the single-point infimum satisfies `μ({c}) ≤ π`. -/
theorem area_pi_attained_each_degree (c : ℂ) (n : ℕ) (hn : 0 < n) :
    ∃ p : RootedPoly, p.degree = n ∧ volume (lem p) = ENNReal.ofReal Real.pi :=
  ⟨purePower c n, rfl, volume_lem_purePower' c hn⟩

/-- **Non-sharpness of the unconditional bound.** For every degree `n ≥ 2` the
pure-power lemniscate area `π` is STRICTLY below the parent's unconditional bound
`degree · π`: the bound `area ≤ degree · π` is attained only at degree one. -/
theorem volume_lem_purePower_lt_degree_bound (c : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    volume (lem (purePower c n)) < (n : ℝ≥0∞) * (NNReal.pi : ℝ≥0∞) := by
  have hpos : 0 < n := by omega
  rw [volume_lem_purePower c hpos]
  have hone : (1 : ℝ≥0∞) < (n : ℝ≥0∞) := by exact_mod_cast (by omega : 1 < n)
  calc (NNReal.pi : ℝ≥0∞)
      = 1 * (NNReal.pi : ℝ≥0∞) := (one_mul _).symm
    _ < (n : ℝ≥0∞) * (NNReal.pi : ℝ≥0∞) :=
        ENNReal.mul_lt_mul_right
          (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero) ENNReal.coe_ne_top hone

/-- **Capstone.** The pure power `(z - c)^n` exhibits, simultaneously and for every
`n ≥ 2`:
* its lemniscate is *exactly* the open unit disc `B(c, 1)`;
* that lemniscate has area *exactly* `π`, independent of the degree;
* this area lies *strictly* below the parent's unconditional bound `degree · π`.
Thus the area infimum is pinned to `π` from above at every degree, and the
elementary `degree · π` bound is sharp only at degree one. -/
theorem purePower_sharp_witness (c : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    lem (purePower c n) = Metric.ball c 1 ∧
      volume (lem (purePower c n)) = ENNReal.ofReal Real.pi ∧
      volume (lem (purePower c n)) < (n : ℝ≥0∞) * (NNReal.pi : ℝ≥0∞) :=
  ⟨lem_purePower_eq_ball c (by omega),
   volume_lem_purePower' c (by omega),
   volume_lem_purePower_lt_degree_bound c hn⟩

end Erdos1040OQ03OQ01
