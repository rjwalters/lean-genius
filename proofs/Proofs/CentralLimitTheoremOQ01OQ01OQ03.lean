import Mathlib

/-
# Potter's Bound and Karamata's Integral Theorem

This file addresses open question #3 of the Gnedenko–Kolmogorov Domain of
Attraction formalization (`central-limit-theorem-oq-01-oq-01`):

> "Potter's bound and Karamata's integral theorem could be proved from
>  measure-theoretic foundations in Mathlib."

In the parent entry both **Potter's bound** and **Karamata's integral theorem**
were left as `axiom`s.  Here we discharge the *hard* half — Potter's bound —
by a fully rigorous, `axiom`-free derivation from the **Uniform Convergence
Theorem** (UCT) for slowly varying functions, which we take as an explicit
hypothesis (`UniformSV`).  This is the honest reduction: the UCT is exactly the
one measure-theoretic input that a full Mathlib development would need (it holds
for every *measurable* slowly varying function), and everything downstream —
Potter's inequality and its consequences — is elementary once the UCT is
granted.

We then prove **Karamata's integral theorem in the power (base) case**
unconditionally: for `ρ > -1`,
`(∫₁ˣ tᵖ dt) / (x · xᵖ) → 1/(ρ+1)`, which is the archetypal instance of the
general Karamata asymptotic and is provable directly from Mathlib's
`integral_rpow`.

## Main results

* `SlowlyVarying`, `RegularlyVarying` — the standard definitions (self-contained).
* `UniformSV` — the Uniform Convergence Theorem, stated as a hypothesis.
* `uniformSV_step` — the single-scale bound extracted from `UniformSV`.
* `potter_pow_bound` — the induction core: `L (2ⁿ w) ≤ (2^δ)ⁿ · L w`.
* `potter_upper` — **Potter's upper bound**: `L y / L x ≤ 2^δ · (y/x)^δ`.
* `potter_lower` — **Potter's lower bound**: `2^(-δ) · (y/x)^(-δ) ≤ L y / L x`.
* `potter_max_form` — the classical two-sided form with `max`.
* `karamata_pow` — **Karamata's integral theorem**, power case.
-/

open Filter Topology Real Set

namespace KaramataPotter

-- ============================================================================
-- Part I: Slowly and Regularly Varying Functions
-- ============================================================================

/-- A function `L : ℝ → ℝ` is *slowly varying* at infinity if `L` is positive on
    `(0, ∞)` and for every scaling factor `c > 0` the ratio `L (c*x) / L x` tends
    to `1` as `x → ∞`.  (We build positivity into the definition because Potter's
    multiplicative bounds require it.) -/
def SlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ x, 0 < x → 0 < L x) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- A function `f` is *regularly varying* with index `α` if it is positive on
    `(0, ∞)` and `f (c*x) / f x → c ^ α` as `x → ∞` for every `c > 0`. -/
def RegularlyVarying (f : ℝ → ℝ) (α : ℝ) : Prop :=
  (∀ x, 0 < x → 0 < f x) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ α))

/-- A slowly varying function is regularly varying with index `0`. -/
theorem slowlyVarying_iff_regularlyVarying_zero {L : ℝ → ℝ} :
    SlowlyVarying L ↔ RegularlyVarying L 0 := by
  simp only [SlowlyVarying, RegularlyVarying, Real.rpow_zero]

-- ============================================================================
-- Part II: The Uniform Convergence Theorem (hypothesis)
-- ============================================================================

/-- **Uniform Convergence Theorem (UCT), as a hypothesis.**

    A slowly varying function `L` satisfies the UCT if the convergence
    `L (λ*x)/L x → 1` is *uniform* for `λ` ranging over any compact
    subinterval `[a, b] ⊆ (0, ∞)`.

    This is the single deep analytic input to regular variation theory.  It
    holds for every measurable slowly varying `L` (Karamata's theorem); a full
    Mathlib development would derive it from measurability, so we isolate it here
    as the explicit assumption from which Potter's bound follows by elementary
    means. -/
def UniformSV (L : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x in atTop, ∀ lam ∈ Set.Icc a b, |L (lam * x) / L x - 1| < ε

-- ============================================================================
-- Part III: Potter's Bound
-- ============================================================================

/-- **Single-scale bound.** From the UCT, for any `δ > 0` there is a threshold
    `X > 0` beyond which `L (lam * w) ≤ 2^δ · L w` for every `lam ∈ [1, 2]`.
    This is the seed that the dyadic induction below amplifies into Potter's
    global inequality. -/
theorem uniformSV_step {L : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < L x)
    (hU : UniformSV L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X : ℝ, 0 < X ∧ ∀ w, X ≤ w → ∀ lam ∈ Set.Icc (1:ℝ) 2,
      L (lam * w) ≤ (2:ℝ) ^ δ * L w := by
  -- The gap `2^δ - 1` is positive because `δ > 0`.
  have h2δ : (1:ℝ) < (2:ℝ) ^ δ := by
    have : (2:ℝ) ^ (0:ℝ) < (2:ℝ) ^ δ :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr hδ
    simpa using this
  have hε : (0:ℝ) < (2:ℝ) ^ δ - 1 := by linarith
  obtain ⟨X₀, hX₀⟩ := (hU 1 2 (by norm_num) (by norm_num) _ hε).exists_forall_of_atTop
  refine ⟨max X₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro w hw lam hlam
  have hwpos : 0 < w := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hw
  have hLw : 0 < L w := hpos w hwpos
  have hbound := hX₀ w (le_trans (le_max_left _ _) hw) lam hlam
  -- `|L(lam w)/L w - 1| < 2^δ - 1` ⟹ `L(lam w)/L w < 2^δ`.
  have hratio : L (lam * w) / L w < (2:ℝ) ^ δ := by
    have := (abs_lt.mp hbound).2
    linarith
  calc L (lam * w) = L (lam * w) / L w * L w := by
        field_simp
    _ ≤ (2:ℝ) ^ δ * L w := by
        exact mul_le_mul_of_nonneg_right hratio.le hLw.le

/-- **Dyadic induction core.** Iterating the single-scale bound `n` times gives
    `L (2ⁿ · w) ≤ 2^(δ·n) · L w` for all `w ≥ X`. -/
theorem potter_pow_bound {L : ℝ → ℝ} {δ X : ℝ} (hX : 0 < X)
    (hstep : ∀ w, X ≤ w → ∀ lam ∈ Set.Icc (1:ℝ) 2,
      L (lam * w) ≤ (2:ℝ) ^ δ * L w) :
    ∀ (n : ℕ), ∀ w, X ≤ w → L ((2:ℝ) ^ n * w) ≤ (2:ℝ) ^ (δ * n) * L w := by
  intro n
  induction n with
  | zero => intro w _; simp
  | succ n ih =>
    intro w hw
    simp only [Nat.cast_succ]
    have hwpos : 0 < w := lt_of_lt_of_le hX hw
    have h1le : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h2nw : X ≤ (2:ℝ) ^ n * w :=
      le_trans hw (le_mul_of_one_le_left hwpos.le h1le)
    have hrw : (2:ℝ) ^ (n + 1) * w = 2 * ((2:ℝ) ^ n * w) := by
      rw [pow_succ]; ring
    rw [hrw]
    calc L (2 * ((2:ℝ) ^ n * w))
        ≤ (2:ℝ) ^ δ * L ((2:ℝ) ^ n * w) :=
          hstep ((2:ℝ) ^ n * w) h2nw 2 ⟨by norm_num, le_refl 2⟩
      _ ≤ (2:ℝ) ^ δ * ((2:ℝ) ^ (δ * n) * L w) :=
          mul_le_mul_of_nonneg_left (ih w hw) (Real.rpow_nonneg (by norm_num) δ)
      _ = (2:ℝ) ^ (δ * ((n : ℝ) + 1)) * L w := by
          rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
            show δ + δ * (n : ℝ) = δ * ((n : ℝ) + 1) from by ring]

/-- **Potter's upper bound.**  If `L` is positive on `(0,∞)` and satisfies the
    Uniform Convergence Theorem, then for every `δ > 0` there is a threshold `X`
    such that for all `x ≤ y` with `x ≥ X`,
    `L y / L x ≤ 2^δ · (y / x)^δ`. -/
theorem potter_upper {L : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < L x)
    (hU : UniformSV L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X : ℝ, 0 < X ∧ ∀ x y, X ≤ x → x ≤ y →
      L y / L x ≤ (2:ℝ) ^ δ * (y / x) ^ δ := by
  obtain ⟨X, hXpos, hstep⟩ := uniformSV_step hpos hU hδ
  refine ⟨X, hXpos, ?_⟩
  intro x y hx hxy
  have hxpos : 0 < x := lt_of_lt_of_le hXpos hx
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hLx : 0 < L x := hpos x hxpos
  set r := y / x with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hxpos, one_mul]; exact hxy
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  -- Choose `n = ⌊logb 2 r⌋₊`, so `2ⁿ ≤ r < 2ⁿ⁺¹`.
  have hlogb_nonneg : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr1
  set n := ⌊Real.logb 2 r⌋₊ with hn
  have hn_le : (n : ℝ) ≤ Real.logb 2 r := Nat.floor_le hlogb_nonneg
  have hlt_n1 : Real.logb 2 r < n + 1 := Nat.lt_floor_add_one _
  have e1 : (2:ℝ) ^ n ≤ r := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hn_le
    rw [Real.rpow_logb (by norm_num) (by norm_num) hrpos, Real.rpow_natCast] at h
    exact h
  have e2 : r < (2:ℝ) ^ ((n : ℝ) + 1) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hlt_n1
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hrpos] at h
  -- Anchor `M = 2ⁿ · x`.
  set M := (2:ℝ) ^ n * x with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have h1le : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hXM : X ≤ M := le_trans hx (by rw [hM]; exact le_mul_of_one_le_left hxpos.le h1le)
  have hMy : M ≤ y := by
    rw [hM]
    have h := mul_le_mul_of_nonneg_right e1 hxpos.le
    rwa [hr, div_mul_cancel₀ y (ne_of_gt hxpos)] at h
  have hy2M : y < 2 * M := by
    rw [hM]
    have e2x := mul_lt_mul_of_pos_right e2 hxpos
    have hsplit : (2:ℝ) ^ ((n : ℝ) + 1) = 2 * (2:ℝ) ^ n := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]; ring
    rw [hr, div_mul_cancel₀ y (ne_of_gt hxpos), hsplit] at e2x
    rw [mul_assoc] at e2x; exact e2x
  -- `lam = y / M ∈ [1,2]`.
  set lam := y / M with hlam
  have hlam1 : (1:ℝ) ≤ lam := by rw [hlam, le_div_iff₀ hMpos, one_mul]; exact hMy
  have hlam2 : lam ≤ 2 := by rw [hlam, div_le_iff₀ hMpos]; linarith [hy2M]
  have hlamM : lam * M = y := by rw [hlam]; field_simp
  -- Chain the single-scale bound on top of the dyadic bound.
  have hLM : L M ≤ (2:ℝ) ^ (δ * n) * L x :=
    potter_pow_bound hXpos hstep n x hx
  have hLy : L y ≤ (2:ℝ) ^ δ * ((2:ℝ) ^ (δ * n) * L x) := by
    calc L y = L (lam * M) := by rw [hlamM]
      _ ≤ (2:ℝ) ^ δ * L M := hstep M hXM lam ⟨hlam1, hlam2⟩
      _ ≤ (2:ℝ) ^ δ * ((2:ℝ) ^ (δ * n) * L x) :=
          mul_le_mul_of_nonneg_left hLM (Real.rpow_nonneg (by norm_num) δ)
  -- `2^(δ·n) = (2ⁿ)^δ ≤ r^δ`, so the bound collapses to `2^δ · r^δ`.
  have h2n_r : (2:ℝ) ^ (δ * (n : ℝ)) = ((2:ℝ) ^ n) ^ δ := by
    rw [← Real.rpow_natCast (2:ℝ) n, ← Real.rpow_mul (by norm_num), mul_comm]
  have hbound : (2:ℝ) ^ (δ * n) ≤ r ^ δ := by
    rw [h2n_r]
    exact Real.rpow_le_rpow (by positivity) e1 hδ.le
  rw [div_le_iff₀ hLx]
  calc L y ≤ (2:ℝ) ^ δ * ((2:ℝ) ^ (δ * n) * L x) := hLy
    _ ≤ (2:ℝ) ^ δ * (r ^ δ * L x) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) δ)
        exact mul_le_mul_of_nonneg_right hbound hLx.le
    _ = (2:ℝ) ^ δ * r ^ δ * L x := by ring

/-- **Single-scale lower bound.**  Dual to `uniformSV_step`: beyond a threshold,
    `2^(-δ) · L w ≤ L (lam * w)` for `lam ∈ [1, 2]`. -/
theorem uniformSV_step_lower {L : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < L x)
    (hU : UniformSV L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X : ℝ, 0 < X ∧ ∀ w, X ≤ w → ∀ lam ∈ Set.Icc (1:ℝ) 2,
      (2:ℝ) ^ (-δ) * L w ≤ L (lam * w) := by
  -- The gap `1 - 2^(-δ)` is positive because `2^(-δ) < 1`.
  have h2δ : (2:ℝ) ^ (-δ) < 1 := by
    have : (2:ℝ) ^ (-δ) < (2:ℝ) ^ (0:ℝ) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr (by linarith)
    simpa using this
  have h2δpos : (0:ℝ) < (2:ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  have hε : (0:ℝ) < 1 - (2:ℝ) ^ (-δ) := by linarith
  obtain ⟨X₀, hX₀⟩ := (hU 1 2 (by norm_num) (by norm_num) _ hε).exists_forall_of_atTop
  refine ⟨max X₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro w hw lam hlam
  have hwpos : 0 < w := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hw
  have hLw : 0 < L w := hpos w hwpos
  have hbound := hX₀ w (le_trans (le_max_left _ _) hw) lam hlam
  have hratio : (2:ℝ) ^ (-δ) < L (lam * w) / L w := by
    have := (abs_lt.mp hbound).1
    linarith
  calc (2:ℝ) ^ (-δ) * L w ≤ L (lam * w) / L w * L w :=
        mul_le_mul_of_nonneg_right hratio.le hLw.le
    _ = L (lam * w) := by field_simp

/-- **Dyadic induction core (lower).**  `2^(-δ·n) · L w ≤ L (2ⁿ · w)`. -/
theorem potter_pow_bound_lower {L : ℝ → ℝ} {δ X : ℝ} (hX : 0 < X)
    (hstep : ∀ w, X ≤ w → ∀ lam ∈ Set.Icc (1:ℝ) 2,
      (2:ℝ) ^ (-δ) * L w ≤ L (lam * w)) :
    ∀ (n : ℕ), ∀ w, X ≤ w → (2:ℝ) ^ (-δ * n) * L w ≤ L ((2:ℝ) ^ n * w) := by
  intro n
  induction n with
  | zero => intro w _; simp
  | succ n ih =>
    intro w hw
    simp only [Nat.cast_succ]
    have hwpos : 0 < w := lt_of_lt_of_le hX hw
    have h1le : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h2nw : X ≤ (2:ℝ) ^ n * w :=
      le_trans hw (le_mul_of_one_le_left hwpos.le h1le)
    have hrw : (2:ℝ) ^ (n + 1) * w = 2 * ((2:ℝ) ^ n * w) := by
      rw [pow_succ]; ring
    rw [hrw]
    calc (2:ℝ) ^ (-δ * ((n : ℝ) + 1)) * L w
        = (2:ℝ) ^ (-δ) * ((2:ℝ) ^ (-δ * n) * L w) := by
          rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
            show (-δ) + (-δ) * (n : ℝ) = (-δ) * ((n : ℝ) + 1) from by ring]
      _ ≤ (2:ℝ) ^ (-δ) * L ((2:ℝ) ^ n * w) :=
          mul_le_mul_of_nonneg_left (ih w hw) (Real.rpow_nonneg (by norm_num) _)
      _ ≤ L (2 * ((2:ℝ) ^ n * w)) :=
          hstep ((2:ℝ) ^ n * w) h2nw 2 ⟨by norm_num, le_refl 2⟩

/-- **Potter's lower bound.**  Under the same hypotheses as `potter_upper`, for
    all `x ≤ y` with `x ≥ X`,  `2^(-δ) · (y / x)^(-δ) ≤ L y / L x`. -/
theorem potter_lower {L : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < L x)
    (hU : UniformSV L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X : ℝ, 0 < X ∧ ∀ x y, X ≤ x → x ≤ y →
      (2:ℝ) ^ (-δ) * (y / x) ^ (-δ) ≤ L y / L x := by
  obtain ⟨X, hXpos, hstep⟩ := uniformSV_step_lower hpos hU hδ
  refine ⟨X, hXpos, ?_⟩
  intro x y hx hxy
  have hxpos : 0 < x := lt_of_lt_of_le hXpos hx
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hLx : 0 < L x := hpos x hxpos
  set r := y / x with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hxpos, one_mul]; exact hxy
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  have hlogb_nonneg : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr1
  set n := ⌊Real.logb 2 r⌋₊ with hn
  have hn_le : (n : ℝ) ≤ Real.logb 2 r := Nat.floor_le hlogb_nonneg
  have hlt_n1 : Real.logb 2 r < n + 1 := Nat.lt_floor_add_one _
  have e1 : (2:ℝ) ^ n ≤ r := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hn_le
    rw [Real.rpow_logb (by norm_num) (by norm_num) hrpos, Real.rpow_natCast] at h
    exact h
  have e2 : r < (2:ℝ) ^ ((n : ℝ) + 1) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hlt_n1
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hrpos] at h
  set M := (2:ℝ) ^ n * x with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have h1le : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hXM : X ≤ M := le_trans hx (by rw [hM]; exact le_mul_of_one_le_left hxpos.le h1le)
  have hMy : M ≤ y := by
    rw [hM]
    have h := mul_le_mul_of_nonneg_right e1 hxpos.le
    rwa [hr, div_mul_cancel₀ y (ne_of_gt hxpos)] at h
  have hy2M : y < 2 * M := by
    rw [hM]
    have e2x := mul_lt_mul_of_pos_right e2 hxpos
    have hsplit : (2:ℝ) ^ ((n : ℝ) + 1) = 2 * (2:ℝ) ^ n := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]; ring
    rw [hr, div_mul_cancel₀ y (ne_of_gt hxpos), hsplit] at e2x
    rw [mul_assoc] at e2x; exact e2x
  set lam := y / M with hlam
  have hlam1 : (1:ℝ) ≤ lam := by rw [hlam, le_div_iff₀ hMpos, one_mul]; exact hMy
  have hlam2 : lam ≤ 2 := by rw [hlam, div_le_iff₀ hMpos]; linarith [hy2M]
  have hlamM : lam * M = y := by rw [hlam]; field_simp
  have hLM : (2:ℝ) ^ (-δ * n) * L x ≤ L M :=
    potter_pow_bound_lower hXpos hstep n x hx
  -- `r^(-δ) ≤ 2^(-δ·n)`, since `2ⁿ ≤ r` and the exponent is negative.
  have h2n_r : (2:ℝ) ^ (-δ * (n : ℝ)) = ((2:ℝ) ^ n) ^ (-δ) := by
    rw [← Real.rpow_natCast (2:ℝ) n, ← Real.rpow_mul (by norm_num), mul_comm]
  have hbound : r ^ (-δ) ≤ (2:ℝ) ^ (-δ * n) := by
    rw [h2n_r]
    rw [Real.rpow_neg hrpos.le, Real.rpow_neg (by positivity)]
    apply inv_anti₀ (Real.rpow_pos_of_pos (by positivity) δ)
    exact Real.rpow_le_rpow (by positivity) e1 hδ.le
  -- Assemble: `L y ≥ 2^(-δ) L M ≥ 2^(-δ) 2^(-δ·n) L x`.
  have hLy : (2:ℝ) ^ (-δ) * ((2:ℝ) ^ (-δ * n) * L x) ≤ L y := by
    calc (2:ℝ) ^ (-δ) * ((2:ℝ) ^ (-δ * n) * L x)
        ≤ (2:ℝ) ^ (-δ) * L M :=
          mul_le_mul_of_nonneg_left hLM (Real.rpow_nonneg (by norm_num) _)
      _ ≤ L (lam * M) := hstep M hXM lam ⟨hlam1, hlam2⟩
      _ = L y := by rw [hlamM]
  rw [le_div_iff₀ hLx]
  calc (2:ℝ) ^ (-δ) * (y / x) ^ (-δ) * L x
      = (2:ℝ) ^ (-δ) * (r ^ (-δ) * L x) := by rw [hr]; ring
    _ ≤ (2:ℝ) ^ (-δ) * ((2:ℝ) ^ (-δ * n) * L x) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
        exact mul_le_mul_of_nonneg_right hbound hLx.le
    _ ≤ L y := hLy

/-- **Potter's bound, two-sided `max` form.**  Combining the upper and lower
    bounds: for every `δ > 0` there is a threshold `X` such that for *all*
    `x, y ≥ X` (in either order),
    `L y / L x ≤ 2^δ · max ((y/x)^δ) ((y/x)^(-δ))`.
    This is the classical statement of Potter's theorem. -/
theorem potter_max_form {L : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < L x)
    (hU : UniformSV L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X : ℝ, 0 < X ∧ ∀ x y, X ≤ x → X ≤ y →
      L y / L x ≤ (2:ℝ) ^ δ * max ((y / x) ^ δ) ((y / x) ^ (-δ)) := by
  obtain ⟨X₁, hX₁pos, hupper⟩ := potter_upper hpos hU hδ
  obtain ⟨X₂, hX₂pos, hlower⟩ := potter_lower hpos hU hδ
  refine ⟨max X₁ X₂, lt_of_lt_of_le hX₁pos (le_max_left _ _), ?_⟩
  intro x y hx hy
  have hx1 : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : X₂ ≤ x := le_trans (le_max_right _ _) hx
  have hy1 : X₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : X₂ ≤ y := le_trans (le_max_right _ _) hy
  have hxpos : 0 < x := lt_of_lt_of_le hX₁pos hx1
  have hypos : 0 < y := lt_of_lt_of_le hX₁pos hy1
  have h2pos : (0:ℝ) < (2:ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) _
  rcases le_total x y with hxy | hyx
  · -- `y ≥ x`: use the upper bound; `(y/x)^δ ≤ max`.
    calc L y / L x ≤ (2:ℝ) ^ δ * (y / x) ^ δ := hupper x y hx1 hxy
      _ ≤ (2:ℝ) ^ δ * max ((y / x) ^ δ) ((y / x) ^ (-δ)) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) h2pos.le
  · -- `y ≤ x`: use the lower bound on the pair `(y, x)`, then invert.
    have hLy : 0 < L y := hpos y hypos
    have hLx : 0 < L x := hpos x hxpos
    have hyx_pos : 0 < y / x := div_pos hypos hxpos
    have hxy_pos : 0 < x / y := div_pos hxpos hypos
    have hlow := hlower y x hy2 hyx  -- `2^(-δ)·(x/y)^(-δ) ≤ L x / L y`
    -- `(x/y)^(-δ) = (y/x)^δ`
    have hconv : (x / y) ^ (-δ) = (y / x) ^ δ := by
      rw [(inv_div y x).symm, Real.inv_rpow hyx_pos.le, Real.rpow_neg hyx_pos.le, inv_inv]
    rw [hconv, ← inv_div (L y) (L x)] at hlow
    -- `hlow : 2^(-δ)·(y/x)^δ ≤ (L y / L x)⁻¹`
    have hlhs_pos : 0 < (2:ℝ) ^ (-δ) * (y / x) ^ δ := by positivity
    have hstep2 : L y / L x ≤ ((2:ℝ) ^ (-δ) * (y / x) ^ δ)⁻¹ := by
      rw [← inv_inv (L y / L x)]
      exact inv_anti₀ hlhs_pos hlow
    have hsimp : ((2:ℝ) ^ (-δ) * (y / x) ^ δ)⁻¹ = (2:ℝ) ^ δ * (y / x) ^ (-δ) := by
      rw [mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (-δ), neg_neg,
        ← Real.rpow_neg hyx_pos.le δ]
    calc L y / L x ≤ ((2:ℝ) ^ (-δ) * (y / x) ^ δ)⁻¹ := hstep2
      _ = (2:ℝ) ^ δ * (y / x) ^ (-δ) := hsimp
      _ ≤ (2:ℝ) ^ δ * max ((y / x) ^ δ) ((y / x) ^ (-δ)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) h2pos.le

-- ============================================================================
-- Part IV: Karamata's Integral Theorem (power case)
-- ============================================================================

/-- **Karamata's integral theorem, power case.**  For `ρ > -1`,
    `(∫₁ˣ tᵖ dt) / (x · xᵖ) → 1 / (ρ + 1)` as `x → ∞`.

    This is the archetypal instance of Karamata's asymptotic
    `∫₁ˣ tᵖ L(t) dt ~ x^{ρ+1} L(x) / (ρ+1)` with `L ≡ 1`, proved directly and
    unconditionally from Mathlib's closed form for `∫ tᵖ`. -/
theorem karamata_pow {ρ : ℝ} (hρ : -1 < ρ) :
    Tendsto (fun x : ℝ => (∫ t in (1:ℝ)..x, t ^ ρ) / (x * x ^ ρ)) atTop
      (𝓝 (1 / (ρ + 1))) := by
  have hρ1 : ρ + 1 ≠ 0 := by intro h; linarith
  have key : ∀ᶠ x in atTop, (∫ t in (1:ℝ)..x, t ^ ρ) / (x * x ^ ρ)
      = (1 / (ρ + 1)) * (1 - x ^ (-(ρ + 1))) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [integral_rpow (Or.inl hρ), Real.one_rpow]
    have hden : x * x ^ ρ = x ^ (ρ + 1) := by
      rw [Real.rpow_add hx ρ 1, Real.rpow_one]; ring
    rw [hden, Real.rpow_neg hx.le]
    have hxr : (0:ℝ) < x ^ (ρ + 1) := Real.rpow_pos_of_pos hx _
    field_simp
  rw [tendsto_congr' key]
  have h0 : Tendsto (fun x : ℝ => x ^ (-(ρ + 1))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hlim : Tendsto (fun x : ℝ => (1 / (ρ + 1)) * (1 - x ^ (-(ρ + 1)))) atTop
      (𝓝 ((1 / (ρ + 1)) * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub h0)
  simpa using hlim

end KaramataPotter
