/-
  The Regular-Variation Index is a Well-Defined Asymptotic Invariant
  Open Question: central-limit-theorem-oq-01-oq-01-oq-01

  This file is a follow-up to the Gnedenko-Kolmogorov domain-of-attraction
  formalization (central-limit-theorem-oq-01-oq-01). There, the tail of a
  distribution in the domain of attraction of an α-stable law is described by a
  regularly varying function with index -α, and the stability parameter α is the
  central invariant of the whole theory.

  Here we prove that this index is *intrinsic*: it is a uniquely determined,
  additive, and rigid asymptotic invariant of the function.

  Main results:
  * `regularlyVarying_index_unique`   — a function is regularly varying with at
                                        most one index (the index is well-defined).
  * `slowlyVarying_iff_regularlyVarying_zero`
                                      — slowly varying = regularly varying of index 0.
  * `slowlyVarying_regularlyVarying_index`
                                      — the only possible index of a slowly
                                        varying function is 0.
  * `rpow_regularlyVarying`           — `x ↦ x^α` is regularly varying with
                                        index α (the model example).
  * `rpow_slowlyVarying_iff`          — `x ↦ x^α` is slowly varying ⇔ α = 0
                                        (sharp non-example).
  * `not_slowlyVarying_id`            — the identity `x ↦ x` is not slowly varying.
  * `regularlyVarying_mul_index`      — the index is *additive* under pointwise
                                        products: index(f·g) = index f + index g,
                                        i.e. the index is a homomorphism into (ℝ,+).
  * `regularlyVarying_of_asymp_equiv` — regular variation (with its index) is
                                        preserved under asymptotic equivalence.
  * `regularlyVarying_asymp_equiv_same_index`
                                      — asymptotically equivalent regularly
                                        varying functions share the same index.

  Together these say: the stability/tail index of a domain-of-attraction
  distribution is a genuine invariant — unique, additive, and unchanged by
  asymptotically negligible perturbations.

  The file is self-contained (imports only Mathlib) and axiom-free.

  References:
  - Gnedenko & Kolmogorov, "Limit Distributions for Sums of Independent
    Random Variables" (1954)
  - Bingham, Goldie & Teugels, "Regular Variation" (1987), Ch. 1
  - Feller, "An Introduction to Probability Theory", Vol. 2, Ch. VIII, XVII
-/

import Mathlib

open Filter Topology Real

set_option maxHeartbeats 400000

noncomputable section

namespace DomainOfAttractionIndex

-- ============================================================================
-- Definitions (mirroring central-limit-theorem-oq-01-oq-01, kept local so the
-- file is self-contained and axiom-free)
-- ============================================================================

/-- A function `L : ℝ → ℝ` is slowly varying at infinity if for every positive
    scaling factor `c`, the ratio `L(cx)/L(x) → 1` as `x → +∞`. -/
def SlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ x, 0 < x → L x ≠ 0) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- A function is regularly varying with index `α` if the ratio
    `f(cx)/f(x) → c^α` as `x → +∞` for every `c > 0`. -/
def RegularlyVarying (f : ℝ → ℝ) (α : ℝ) : Prop :=
  (∀ x, 0 < x → f x ≠ 0) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ α))

/-- A positive constant function is slowly varying. -/
theorem slowlyVarying_const {a : ℝ} (ha : 0 < a) :
    SlowlyVarying (fun _ => a) := by
  refine ⟨fun _ _ => ne_of_gt ha, ?_⟩
  intro c _
  simp only [div_self (ne_of_gt ha)]
  exact tendsto_const_nhds

-- ============================================================================
-- Part I: The index is well-defined (uniqueness)
-- ============================================================================

/-- **Uniqueness of the regular-variation index.** A function can be regularly
    varying with at most one index. This is what makes "the index of `f`" a
    well-defined notion.

    Proof: evaluate the defining limit at `c = 2`. The ratio `f(2x)/f(x)`
    converges to both `2^α` and `2^β`, so `2^α = 2^β` by uniqueness of limits;
    taking logarithms and cancelling `log 2 ≠ 0` gives `α = β`. -/
theorem regularlyVarying_index_unique {f : ℝ → ℝ} {α β : ℝ}
    (hα : RegularlyVarying f α) (hβ : RegularlyVarying f β) : α = β := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have ha := hα.2 2 h2
  have hb := hβ.2 2 h2
  have hpow : (2 : ℝ) ^ α = (2 : ℝ) ^ β := tendsto_nhds_unique ha hb
  have hlog := congrArg Real.log hpow
  rw [Real.log_rpow h2, Real.log_rpow h2] at hlog
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact mul_right_cancel₀ hlog2 hlog

-- ============================================================================
-- Part II: Slowly varying = index 0
-- ============================================================================

/-- Slowly varying functions are exactly the regularly varying functions of
    index `0` (`c^0 = 1`). -/
theorem slowlyVarying_iff_regularlyVarying_zero {L : ℝ → ℝ} :
    SlowlyVarying L ↔ RegularlyVarying L 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc => ?_⟩
    simpa [Real.rpow_zero] using h2 c hc
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc => ?_⟩
    simpa [Real.rpow_zero] using h2 c hc

/-- The only index a slowly varying function can have is `0`. -/
theorem slowlyVarying_regularlyVarying_index {L : ℝ → ℝ} {α : ℝ}
    (hSV : SlowlyVarying L) (hRV : RegularlyVarying L α) : α = 0 :=
  regularlyVarying_index_unique hRV (slowlyVarying_iff_regularlyVarying_zero.mp hSV)

-- ============================================================================
-- Part III: The model example `x ↦ x^α` and sharpness
-- ============================================================================

/-- The power function `x ↦ x^α` is regularly varying with index `α`.
    This is the canonical example and shows every real number occurs as an index. -/
theorem rpow_regularlyVarying (α : ℝ) :
    RegularlyVarying (fun x => x ^ α) α := by
  refine ⟨fun x hx => ne_of_gt (Real.rpow_pos_of_pos hx α), ?_⟩
  intro c hc
  have heq : (fun x : ℝ => (c * x) ^ α / x ^ α) =ᶠ[atTop] (fun _ => c ^ α) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.mul_rpow (le_of_lt hc) (le_of_lt hx), mul_div_assoc,
        div_self (ne_of_gt (Real.rpow_pos_of_pos hx α)), mul_one]
  exact Tendsto.congr' heq.symm tendsto_const_nhds

/-- **Sharp non-example.** The power function `x ↦ x^α` is slowly varying if and
    only if `α = 0`. Any nonzero exponent breaks slow variation. -/
theorem rpow_slowlyVarying_iff {α : ℝ} :
    SlowlyVarying (fun x => x ^ α) ↔ α = 0 := by
  constructor
  · intro h
    exact regularlyVarying_index_unique (rpow_regularlyVarying α)
      (slowlyVarying_iff_regularlyVarying_zero.mp h)
  · intro hα
    subst hα
    have hfun : (fun x : ℝ => x ^ (0 : ℝ)) = (fun _ => (1 : ℝ)) := by
      ext x; exact Real.rpow_zero x
    rw [hfun]
    exact slowlyVarying_const (by norm_num)

/-- The identity function `x ↦ x` (index `1`) is not slowly varying: the ratio
    `(2x)/x → 2 ≠ 1`. -/
theorem not_slowlyVarying_id : ¬ SlowlyVarying (fun x => x) := by
  intro h
  have h2 := h.2 2 (by norm_num)
  have heq : (fun x : ℝ => 2 * x / x) =ᶠ[atTop] (fun _ => (2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mul_div_assoc, div_self (ne_of_gt hx), mul_one]
  have hconst : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 1) := h2.congr' heq
  have : (1 : ℝ) = 2 := tendsto_nhds_unique hconst tendsto_const_nhds
  norm_num at this

-- ============================================================================
-- Part IV: The index is additive (a homomorphism into (ℝ, +))
-- ============================================================================

/-- **Additivity of the index.** The index of a pointwise product is the sum of
    the indices: `index (f·g) = index f + index g`. Combined with uniqueness this
    exhibits the index as a homomorphism from (regularly varying functions under
    pointwise multiplication) into `(ℝ, +)`. -/
theorem regularlyVarying_mul_index {f g : ℝ → ℝ} {α β : ℝ}
    (hf : RegularlyVarying f α) (hg : RegularlyVarying g β) :
    RegularlyVarying (fun x => f x * g x) (α + β) := by
  refine ⟨fun x hx => mul_ne_zero (hf.1 x hx) (hg.1 x hx), ?_⟩
  intro c hc
  have key : (fun x => f (c * x) * g (c * x) / (f x * g x)) =ᶠ[atTop]
      (fun x => f (c * x) / f x * (g (c * x) / g x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hfx := hf.1 x hx
    have hgx := hg.1 x hx
    field_simp
  rw [Real.rpow_add hc]
  exact Tendsto.congr' key.symm ((hf.2 c hc).mul (hg.2 c hc))

-- ============================================================================
-- Part V: Rigidity — regular variation is preserved by asymptotic equivalence
-- ============================================================================

/-- **Rigidity under asymptotic equivalence.** If `f` is regularly varying with
    index `α` and `g` is asymptotically equivalent to `f` (i.e. `f/g → 1`, with
    `g` nonvanishing on the positives), then `g` is also regularly varying with
    the *same* index `α`.

    Proof: decompose `g(cx)/g(x) = (f(cx)/f(x))·(f(x)/g(x))·(g(cx)/f(cx))`. The
    first factor tends to `c^α`; the second is `f/g → 1`; the third is the
    reciprocal of `f/g` precomposed with the scaling `x ↦ cx` (which tends to
    infinity), hence also `→ 1`. -/
theorem regularlyVarying_of_asymp_equiv {f g : ℝ → ℝ} {α : ℝ}
    (hf : RegularlyVarying f α)
    (hg_pos : ∀ x, 0 < x → g x ≠ 0)
    (hfg : Tendsto (fun x => f x / g x) atTop (𝓝 1)) :
    RegularlyVarying g α := by
  refine ⟨hg_pos, ?_⟩
  intro c hc
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have p1 : Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ α)) := hf.2 c hc
  have p2 : Tendsto (fun x => f x / g x) atTop (𝓝 1) := hfg
  have p3 : Tendsto (fun x => g (c * x) / f (c * x)) atTop (𝓝 1) := by
    have hfg2 : Tendsto (fun x => f (c * x) / g (c * x)) atTop (𝓝 1) := hfg.comp hcx
    have hinv := hfg2.inv₀ (one_ne_zero)
    rw [inv_one] at hinv
    exact hinv.congr (fun x => inv_div _ _)
  have hprod : Tendsto
      (fun x => f (c * x) / f x * (f x / g x) * (g (c * x) / f (c * x)))
      atTop (𝓝 (c ^ α * 1 * 1)) := (p1.mul p2).mul p3
  simp only [mul_one] at hprod
  refine Tendsto.congr' ?_ hprod
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hfx := hf.1 x hx
  have hgx := hg_pos x hx
  have hfcx := hf.1 (c * x) (mul_pos hc hx)
  field_simp

/-- Asymptotically equivalent regularly varying functions have equal indices. -/
theorem regularlyVarying_asymp_equiv_same_index {f g : ℝ → ℝ} {α β : ℝ}
    (hf : RegularlyVarying f α) (hg : RegularlyVarying g β)
    (hfg : Tendsto (fun x => f x / g x) atTop (𝓝 1)) : α = β :=
  regularlyVarying_index_unique
    (regularlyVarying_of_asymp_equiv hf hg.1 hfg) hg

-- ============================================================================
-- Part VI: Corollaries tying the invariant back to the domain-of-attraction
-- picture
-- ============================================================================

/-- The reciprocal of a regularly varying function negates the index:
    `index (1/f) = -index f`. A special case of additivity, since
    `f · (1/f) = 1` has index `0`. -/
theorem regularlyVarying_inv_index {f : ℝ → ℝ} {α : ℝ}
    (hf : RegularlyVarying f α) :
    RegularlyVarying (fun x => (f x)⁻¹) (-α) := by
  refine ⟨fun x hx => inv_ne_zero (hf.1 x hx), ?_⟩
  intro c hc
  have key : (fun x => (f (c * x))⁻¹ / (f x)⁻¹) =ᶠ[atTop]
      (fun x => (f (c * x) / f x)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with _ _
    rw [inv_div_inv, inv_div]
  rw [Real.rpow_neg (le_of_lt hc)]
  refine Tendsto.congr' key.symm ?_
  exact (hf.2 c hc).inv₀ (by positivity)

/-- A slowly varying correction factor does not change the index: multiplying a
    regularly varying function of index `α` by a slowly varying function keeps
    the index at `α`. This is the precise sense in which the index "sees only the
    power-law part" of a domain-of-attraction tail. -/
theorem regularlyVarying_mul_slowlyVarying {f L : ℝ → ℝ} {α : ℝ}
    (hf : RegularlyVarying f α) (hL : SlowlyVarying L) :
    RegularlyVarying (fun x => f x * L x) α := by
  have hL0 : RegularlyVarying L 0 := slowlyVarying_iff_regularlyVarying_zero.mp hL
  have := regularlyVarying_mul_index hf hL0
  simpa using this

end DomainOfAttractionIndex
