/-
  Yang-Mills 2D OQ-02: Does Casimir Scaling Persist Exactly or Approximately in 4D?

  In 2D Yang-Mills theory (Migdal formula), Casimir scaling is an EXACT result:
  the string tension ratio σ_R/σ_fund equals the Casimir ratio C₂(R)/C₂(fund) for all r.

  In 4D, Casimir scaling is observed approximately in lattice simulations at intermediate
  distances, but it CANNOT be exact:
  - Adjoint and other screened representations undergo string breaking at r = r_break
  - After breaking, V_R(r) saturates at 2·m_gluelump while V_fund(r) grows linearly
  - The potential ratio V_R(r)/V_fund(r) decreases after r_break, contradicting constancy

  This file proves:
  - Part I: In 2D, the potential ratio exactly equals the Casimir ratio for all r > 0
  - Part II: String breaking implies the potential ratio decreases after r_break
  - Part III: The 4D approximate Casimir scaling predicate (with a formalization caveat)

  Parts I, II, and III: 0 axioms, 0 sorries.
  Part III note: the free-existential predicate is a tautology of real analysis and is
  stated as a proved theorem, NOT an axiom. It does not capture the (still open) physical
  small-ε conjecture, which needs an explicit bound on ε (see the caveat before Part III).

  References:
  - Migdal, "Recursion equations in gauge theories" (1975)
  - Bali et al., "Casimir scaling of SU(3) static potentials" Phys. Rev. D 62 (2000)
  - Piccioni, "Casimir scaling and string breaking in G(2) gauge theory" (2006)
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

open Real

namespace YangMills2DOQ02

-- ============================================================
-- PART I: 2D Casimir Scaling is Exact
-- ============================================================

/-
In 2D Yang-Mills, the Migdal formula gives string tension σ_R = g²·C₂(R)/(2·dim R).
The static potential V_R(r) = σ_R · r for ALL r (no string breaking in 2D).
The potential ratio is therefore constant and equals the Casimir ratio.
-/

/-- The linear static potential: V(r) = σ · r. -/
def linearPotential (sigma r : ℝ) : ℝ := sigma * r

/-- The 2D Migdal string tension: σ_R = g² · C₂(R) / (2 · dim R). -/
def migdalTension (g_sq casimir_R : ℝ) (dim_R : ℕ) : ℝ :=
  g_sq * casimir_R / (2 * dim_R)

/-- The Migdal tension is positive when g² > 0, C₂(R) > 0, dim R ≥ 1. -/
theorem migdalTension_pos (g_sq casimir_R : ℝ) (dim_R : ℕ)
    (hg : g_sq > 0) (hC : casimir_R > 0) (hd : dim_R ≥ 1) :
    migdalTension g_sq casimir_R dim_R > 0 := by
  unfold migdalTension
  apply div_pos (mul_pos hg hC)
  have : (dim_R : ℝ) ≥ 1 := by exact_mod_cast hd
  linarith

/-- In 2D, the potential ratio exactly equals the tension ratio for all r > 0. -/
theorem twoD_potential_ratio_exact (sigma_R sigma_fund r : ℝ)
    (hR : sigma_R > 0) (hf : sigma_fund > 0) (hr : r > 0) :
    linearPotential sigma_R r / linearPotential sigma_fund r = sigma_R / sigma_fund := by
  unfold linearPotential
  field_simp [ne_of_gt hr, ne_of_gt hf]

/-- The Migdal tension ratio equals the Casimir ratio (same-dimension representations). -/
theorem migdalTension_ratio_eq_casimir_ratio (g_sq casimir_R casimir_fund : ℝ) (dim : ℕ)
    (hg : g_sq > 0) (hCR : casimir_R > 0) (hCf : casimir_fund > 0) (hd : dim ≥ 1) :
    migdalTension g_sq casimir_R dim / migdalTension g_sq casimir_fund dim =
    casimir_R / casimir_fund := by
  unfold migdalTension
  have hg_ne : g_sq ≠ 0 := ne_of_gt hg
  have hCf_ne : casimir_fund ≠ 0 := ne_of_gt hCf
  have hdim_pos : (0 : ℝ) < (dim : ℝ) := by exact_mod_cast (show 0 < dim from by omega)
  have hdim_ne : (dim : ℝ) ≠ 0 := ne_of_gt hdim_pos
  have h2dim_ne : (2 : ℝ) * (dim : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hdim_ne
  field_simp [hg_ne, h2dim_ne, hCf_ne]

/-- **2D Exact Casimir Scaling**: For any r > 0, the potential ratio equals the Casimir ratio.
    This is the central exact result in 2D Yang-Mills. -/
theorem twoD_exact_casimir_scaling (g_sq casimir_R casimir_fund : ℝ) (dim : ℕ)
    (hg : g_sq > 0) (hCR : casimir_R > 0) (hCf : casimir_fund > 0) (hd : dim ≥ 1) (r : ℝ)
    (hr : r > 0) :
    linearPotential (migdalTension g_sq casimir_R dim) r /
    linearPotential (migdalTension g_sq casimir_fund dim) r =
    casimir_R / casimir_fund := by
  rw [twoD_potential_ratio_exact _ _ r
    (migdalTension_pos g_sq casimir_R dim hg hCR hd)
    (migdalTension_pos g_sq casimir_fund dim hg hCf hd) hr]
  exact migdalTension_ratio_eq_casimir_ratio g_sq casimir_R casimir_fund dim hg hCR hCf hd

-- ============================================================
-- PART II: 4D Casimir Scaling Fails Exactly Due to String Breaking
-- ============================================================

/-
In 4D Yang-Mills, representations with N-ality 0 (e.g., adjoint) undergo string
breaking at r = r_break = 2·m_gluelump/σ_R. After breaking:
  V_R(r) = 2·m_gluelump  (constant, all r > r_break)
  V_fund(r) = σ_fund · r  (still linear; N-ality ≠ 0 representations don't break)

The potential ratio V_R/V_fund = 2·m/(σ_fund·r) → 0 as r → ∞.
This is strictly less than the pre-break ratio σ_R/σ_fund.
Therefore the ratio is NOT constant, and exact Casimir scaling fails.
-/

/-- The saturation potential after string breaking: V_R(r) = 2·m_gluelump. -/
def saturationPotential (m_gluelump : ℝ) : ℝ := 2 * m_gluelump

/-- Breaking distance r_break = 2·m_gluelump/σ_R. -/
def breakDistance (sigma_R m_gluelump : ℝ) : ℝ := 2 * m_gluelump / sigma_R

/-- The breaking distance is positive. -/
theorem breakDistance_pos (sigma_R m_gluelump : ℝ)
    (hsig : sigma_R > 0) (hm : m_gluelump > 0) :
    breakDistance sigma_R m_gluelump > 0 :=
  div_pos (by linarith) hsig

/-- At r_break, the linear potential equals the saturation energy:
    σ_R · r_break = 2·m_gluelump. -/
theorem potential_at_break (sigma_R m_gluelump : ℝ) (hsig : sigma_R > 0) :
    linearPotential sigma_R (breakDistance sigma_R m_gluelump) =
    saturationPotential m_gluelump := by
  unfold linearPotential breakDistance saturationPotential
  field_simp [ne_of_gt hsig]

/-- For r > r_break, the saturation energy is strictly less than the linear potential
    σ_R · r. This is the key inequality underlying the failure of exact scaling. -/
private lemma saturation_lt_linear_post_break (sigma_R m_gluelump r : ℝ)
    (hsig : sigma_R > 0) (hm : m_gluelump > 0)
    (hr : r > breakDistance sigma_R m_gluelump) :
    2 * m_gluelump < sigma_R * r := by
  have hbreak : sigma_R * breakDistance sigma_R m_gluelump = 2 * m_gluelump := by
    unfold breakDistance
    field_simp [ne_of_gt hsig]
  calc 2 * m_gluelump
      = sigma_R * breakDistance sigma_R m_gluelump := hbreak.symm
    _ < sigma_R * r := by exact mul_lt_mul_of_pos_left hr hsig

/-- **Theorem**: After string breaking (r > r_break), the saturation potential ratio
    is strictly less than the pre-break string tension ratio.
    Exact Casimir scaling would require the ratio to be constant = σ_R/σ_fund,
    but after breaking it is 2·m/(σ_fund·r) < σ_R/σ_fund. -/
theorem post_break_ratio_lt_tension_ratio (sigma_R sigma_fund m_gluelump r : ℝ)
    (hsig_R : sigma_R > 0) (hsig_f : sigma_fund > 0) (hm : m_gluelump > 0)
    (hr : r > breakDistance sigma_R m_gluelump) :
    saturationPotential m_gluelump / linearPotential sigma_fund r <
    sigma_R / sigma_fund := by
  have hr_break_pos : breakDistance sigma_R m_gluelump > 0 :=
    breakDistance_pos sigma_R m_gluelump hsig_R hm
  have hr_pos : r > 0 := lt_trans hr_break_pos hr
  unfold saturationPotential linearPotential
  rw [div_lt_div_iff₀ (mul_pos hsig_f hr_pos) hsig_f]
  -- Goal: 2 * m_gluelump * sigma_fund < sigma_R * (sigma_fund * r)
  have key : 2 * m_gluelump < sigma_R * r :=
    saturation_lt_linear_post_break sigma_R m_gluelump r hsig_R hm hr
  nlinarith [mul_lt_mul_of_pos_right key hsig_f]

/-- **Main theorem**: Exact Casimir scaling fails in 4D when string breaking occurs.
    - Before breaking (any r₁ > 0): ratio = σ_R/σ_fund (Casimir-consistent)
    - After breaking (r₂ > r_break): ratio < σ_R/σ_fund (Casimir scaling violated)
    The ratio is not constant, disproving exactness. -/
theorem exact_casimir_scaling_fails_4d
    (sigma_R sigma_fund m_gluelump r₁ r₂ : ℝ)
    (hsig_R : sigma_R > 0) (hsig_f : sigma_fund > 0) (hm : m_gluelump > 0)
    (hr₁ : r₁ > 0) (hr₂ : r₂ > breakDistance sigma_R m_gluelump) :
    linearPotential sigma_R r₁ / linearPotential sigma_fund r₁ = sigma_R / sigma_fund ∧
    saturationPotential m_gluelump / linearPotential sigma_fund r₂ < sigma_R / sigma_fund ∧
    saturationPotential m_gluelump / linearPotential sigma_fund r₂ <
    linearPotential sigma_R r₁ / linearPotential sigma_fund r₁ := by
  have h_ratio : linearPotential sigma_R r₁ / linearPotential sigma_fund r₁ = sigma_R / sigma_fund :=
    twoD_potential_ratio_exact sigma_R sigma_fund r₁ hsig_R hsig_f hr₁
  have h_post : saturationPotential m_gluelump / linearPotential sigma_fund r₂ < sigma_R / sigma_fund :=
    post_break_ratio_lt_tension_ratio sigma_R sigma_fund m_gluelump r₂ hsig_R hsig_f hm hr₂
  exact ⟨h_ratio, h_post, h_post.trans_eq h_ratio.symm⟩

-- ============================================================
-- PART III: 4D Approximate Casimir Scaling (a formalization caveat)
-- ============================================================

/-
While exact Casimir scaling fails in 4D (proved above), lattice simulations show
approximate Casimir scaling at intermediate distances (r < r_break):

  |σ_R/σ_fund - C₂(R)/C₂(fund)| < ε  for small ε > 0

The genuine physics conjecture asserts this holds for a SMALL, physically-motivated
ε tied to measured lattice deviations. That statement is genuinely open and would
require constructive QFT methods beyond current Mathlib.

Key lattice measurements (Bali et al. 2000):
  SU(2): σ_adj/σ_fund = C₂(adj)/C₂(fund) = 8/3 ≈ 2.67, measured ≈ 2.5 ± 0.2
  SU(3): σ_adj/σ_fund = C₂(adj)/C₂(fund) = 9/4 = 2.25, measured ≈ 2.2 ± 0.1

CAVEAT (formalization honesty): the predicate below, with ε a *free, unbounded*
existential, does NOT capture that physics. Any two reals are within |x - y| + 1
of each other, so `∃ ε, ApproximateCasimirScaling4D ...` is a tautology of real
analysis — it holds unconditionally, needs no positivity hypotheses, and encodes
zero physical content. We therefore state it as an ordinary `theorem` (proved
trivially), NOT an axiom, so the entry makes no false "open conjecture" claim.
Formalizing the real conjecture requires an explicit, physically-grounded bound
on ε (e.g. ε ≤ 0.2 for SU(2)); that remains future work.
-/

/-- Approximate Casimir scaling: the string tension ratio is within ε of the Casimir ratio. -/
def ApproximateCasimirScaling4D (sigma_R sigma_fund casimir_R casimir_fund ε : ℝ) : Prop :=
  ε > 0 ∧ |sigma_R / sigma_fund - casimir_R / casimir_fund| < ε

/-- The free-existential form of approximate Casimir scaling is a **tautology**, not an
    open conjecture: for any reals it holds with `ε := |σ_R/σ_fund - C₂(R)/C₂(fund)| + 1`,
    without any positivity hypotheses. This makes explicit that the predicate as written
    does not encode the physical (small-ε) conjecture — see the caveat above. -/
theorem casimir_scaling_4d_approximate :
    ∀ (sigma_R sigma_fund casimir_R casimir_fund : ℝ),
    sigma_R > 0 → sigma_fund > 0 → casimir_R > 0 → casimir_fund > 0 →
    ∃ ε : ℝ, ApproximateCasimirScaling4D sigma_R sigma_fund casimir_R casimir_fund ε := by
  intro sR sf cR cf _ _ _ _
  refine ⟨|sR / sf - cR / cf| + 1, ?_, ?_⟩
  · positivity
  · linarith [abs_nonneg (sR / sf - cR / cf)]

-- ============================================================
-- SUMMARY
-- ============================================================

/-- **Summary**: 2D vs 4D Casimir scaling.

    2D (EXACT, proved): For all r > 0, V_R/V_fund = C₂(R)/C₂(fund) exactly.
    4D (APPROXIMATE, open): The ratio is approximately C₂(R)/C₂(fund) at intermediate r,
    but fails exactly at large r due to string breaking (proved above).

    Answer to OQ-02: Casimir scaling persists only APPROXIMATELY in 4D, not exactly.
    The failure is a provable consequence of string breaking. -/
theorem casimir_scaling_2d_exact_4d_approximate :
    -- 2D: exact for all r > 0
    (∀ (g_sq casimir_R casimir_fund : ℝ) (dim : ℕ) (r : ℝ),
     g_sq > 0 → casimir_R > 0 → casimir_fund > 0 → dim ≥ 1 → r > 0 →
     linearPotential (migdalTension g_sq casimir_R dim) r /
     linearPotential (migdalTension g_sq casimir_fund dim) r = casimir_R / casimir_fund) ∧
    -- 4D: ratio decreases after string breaking (not constant → not exactly Casimir)
    (∀ (sigma_R sigma_fund m_gluelump r : ℝ),
     sigma_R > 0 → sigma_fund > 0 → m_gluelump > 0 →
     r > breakDistance sigma_R m_gluelump →
     saturationPotential m_gluelump / linearPotential sigma_fund r < sigma_R / sigma_fund) :=
  ⟨fun g_sq casimir_R casimir_fund dim r hg hCR hCf hd hr =>
    twoD_exact_casimir_scaling g_sq casimir_R casimir_fund dim hg hCR hCf hd r hr,
   fun sigma_R sigma_fund m_gluelump r hsig_R hsig_f hm hr =>
    post_break_ratio_lt_tension_ratio sigma_R sigma_fund m_gluelump r hsig_R hsig_f hm hr⟩

end YangMills2DOQ02
