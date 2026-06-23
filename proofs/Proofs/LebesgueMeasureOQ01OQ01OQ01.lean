import Mathlib

/-
# Thomae's Function and Lebesgue's Criterion for Riemann Integrability

## Open Question (lebesgue-measure-oq-01-oq-01-oq-01)
Can we formalize the Riemann integrability of Thomae's function via **Lebesgue's
criterion** — the principle that a bounded function on `[a,b]` is Riemann
integrable iff its set of discontinuities has Lebesgue measure zero?

## Answer: YES — the discontinuity set is null
This entry supplies the **measure-theoretic content of Lebesgue's criterion**,
the part the prior Riemann entry (`…-oq-01-oq-01-oq-02-oq-01`) deliberately
sidestepped (it went through `thomae =ᵐ 0` instead, noting Mathlib exposes no
first-class Lebesgue-criterion lemma). Concretely:

1. Thomae's function is **continuous at every irrational** (rebuilt here in a
   self-contained way: only finitely many rationals of bounded denominator lie
   near an irrational, and they sit a positive distance away).
2. Hence the discontinuity set `{x | ¬ ContinuousAt thomae x}` is contained in
   the rationals `range ((↑) : ℚ → ℝ)`.
3. The rationals are countable, hence **Lebesgue-null** for the atomless measure
   `volume` (`Set.Countable.measure_zero`).
4. Therefore the discontinuity set is null, so Thomae's function is **continuous
   almost everywhere** — exactly the hypothesis of Lebesgue's criterion.

By Lebesgue's theorem this is what makes Thomae's function Riemann integrable; we
package the criterion (null discontinuity set + a.e.-continuity) with the value:
the function is integrable with `∫ = 0`, on the line and on `[0,1]`.

## Note on "Riemann integrable"
Mathlib's `intervalIntegral` is the Bochner/Lebesgue integral and carries no
separate `RiemannIntegrable` predicate. The classical assertion "Thomae's
function is Riemann integrable on `[0,1]`" is the consequence of Lebesgue's
criterion *because* its discontinuity set is null — the content of
`thomae_discontinuitySet_null` and `thomae_ae_continuousAt`. The value `0`
agrees with the Lebesgue integral.

## Self-containment
The continuity-at-irrationals argument is reproved here rather than imported: the
existing gallery file carrying it has bit-rotted against the current Mathlib
(`div_lt_iff`, `Set.Finite.ofFinset` signature, induction-pattern drift). The
proof below uses the current API (`div_lt_iff₀`, `Set.Finite.subset`,
`one_div_le_one_div_of_le`).
-/

namespace LebesgueMeasureOQ01OQ01OQ01

open MeasureTheory

open Classical in
/-- Thomae's function (popcorn function): `1/q.den` if `x` is rational, `0` if
irrational. -/
noncomputable def thomae : ℝ → ℝ := fun x =>
  if h : ∃ q : ℚ, (q : ℝ) = x then 1 / (h.choose.den : ℝ) else 0

/-- `thomae = 0` at irrationals. -/
theorem thomae_irrational {x : ℝ} (hx : Irrational x) : thomae x = 0 := by
  have hne : ¬ ∃ q : ℚ, (q : ℝ) = x := by
    rintro ⟨q, rfl⟩; exact hx ⟨q, rfl⟩
  simp only [thomae, dif_neg hne]

/-- `thomae` at a rational `q` equals `1/q.den`. -/
theorem thomae_rat (q : ℚ) : thomae (q : ℝ) = 1 / (q.den : ℝ) := by
  have hq : ∃ r : ℚ, (r : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  have heq : hq.choose = q := Rat.cast_inj.mp hq.choose_spec
  simp only [thomae, dif_pos hq, heq]

-- ============================================================
-- PART 1: Continuity at the irrationals (self-contained)
-- ============================================================

/-- `q.num = q * q.den` over `ℝ`. -/
private lemma rat_num_eq_mul_den (q : ℚ) : (q.num : ℝ) = (q : ℝ) * q.den := by
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have hq_eq : (q.num : ℚ) = q * q.den := (div_eq_iff hd).mp (Rat.num_div_den q)
  exact_mod_cast hq_eq

/-- Rationals with bounded denominator in `[x-1, x+1]` form a finite set. -/
private lemma finite_rat_bounded (x : ℝ) (N : ℕ) :
    Set.Finite {q : ℚ | |(q : ℝ) - x| ≤ 1 ∧ q.den ≤ N} := by
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (N + 1)).biUnion fun d =>
      (Finset.Icc ⌊(x - 1) * (d : ℝ)⌋ ⌈(x + 1) * (d : ℝ)⌉).image
        fun n : ℤ => (n : ℚ) / (d : ℚ)))
  intro q hq
  obtain ⟨habs, hden⟩ := hq
  rw [Finset.mem_coe]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
  have habs' := abs_le.mp habs
  have hq_lower : x - 1 ≤ (q : ℝ) := by linarith [habs'.1]
  have hq_upper : (q : ℝ) ≤ x + 1 := by linarith [habs'.2]
  have hden_pos : (0 : ℝ) < (q.den : ℝ) := Nat.cast_pos.mpr q.pos
  have hq_num := rat_num_eq_mul_den q
  refine ⟨q.den, Nat.lt_succ_of_le hden, q.num, ⟨?_, ?_⟩, ?_⟩
  · have hle : (x - 1) * (q.den : ℝ) ≤ (q.num : ℝ) := by
      rw [hq_num]; nlinarith [hq_lower, hden_pos]
    have := (Int.floor_le ((x - 1) * (q.den : ℝ))).trans hle
    exact_mod_cast this
  · have hge : (q.num : ℝ) ≤ (x + 1) * (q.den : ℝ) := by
      rw [hq_num]; nlinarith [hq_upper, hden_pos]
    have := hge.trans (Int.le_ceil ((x + 1) * (q.den : ℝ)))
    exact_mod_cast this
  · exact Rat.num_div_den q

/-- From an irrational `x` and a finite set of rationals, there is a positive
minimum distance from `x` to the set. -/
private lemma pos_min_dist {x : ℝ} (hx : Irrational x) (S : Finset ℚ) :
    ∃ δ > 0, ∀ q ∈ S, δ ≤ |x - (q : ℝ)| := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨δ₀, hδ₀, hq₀⟩ := ih
    refine ⟨min δ₀ |x - (a : ℝ)|, lt_min hδ₀ ?_, fun q hq' => ?_⟩
    · rw [abs_pos, sub_ne_zero]
      exact fun h => hx ⟨a, h.symm⟩
    · rcases Finset.mem_insert.mp hq' with rfl | hq''
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hq₀ q hq'')

/-- **Thomae's function is continuous at every irrational.** -/
theorem thomae_continuous_at_irrational {x : ℝ} (hx : Irrational x) :
    ContinuousAt thomae x := by
  rw [Metric.continuousAt_iff]
  simp only [thomae_irrational hx, Real.dist_eq, sub_zero]
  intro ε hε
  obtain ⟨N, hN_raw⟩ : ∃ N : ℕ, (1 : ℝ) / ε < N := exists_nat_gt (1 / ε)
  have hNpos : (0 : ℝ) < N := by linarith [div_pos one_pos hε]
  have hN : (1 : ℝ) / (↑N + 1) < ε := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < ↑N + 1)]
    have h1 : (1 : ℝ) < N * ε := (div_lt_iff₀ hε).mp hN_raw
    nlinarith [h1, hε]
  have hS := finite_rat_bounded x N
  obtain ⟨δ, hδ, hbnd⟩ := pos_min_dist hx hS.toFinset
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy => ?_⟩
  have hy1 : |y - x| ≤ 1 := le_of_lt (hy.trans_le (min_le_right _ _))
  by_cases hirr : Irrational y
  · rw [thomae_irrational hirr, abs_zero]; exact hε
  · simp only [Irrational, not_not] at hirr
    obtain ⟨q, hq⟩ := hirr
    rw [← hq, thomae_rat, abs_of_nonneg (by positivity)]
    rcases le_or_gt q.den N with hle | hlt
    · have hmem : q ∈ hS.toFinset := by
        rw [Set.Finite.mem_toFinset]
        refine ⟨?_, hle⟩
        rw [hq]; exact hy1
      have hdist : δ ≤ |x - (q : ℝ)| := hbnd q hmem
      have hclose : |y - x| < δ := hy.trans_le (min_le_left _ _)
      rw [← hq] at hclose
      linarith [abs_sub_comm (q : ℝ) x]
    · calc (1 : ℝ) / (q.den : ℝ)
          ≤ 1 / (↑N + 1) :=
            one_div_le_one_div_of_le (by linarith)
              (by exact_mod_cast Nat.succ_le_of_lt hlt)
        _ < ε := hN

-- ============================================================
-- PART 2: Lebesgue's criterion — the discontinuity set is null
-- ============================================================

/-- Every discontinuity point of Thomae's function is rational. -/
theorem thomae_discontinuitySet_subset :
    {x : ℝ | ¬ ContinuousAt thomae x} ⊆ Set.range ((↑) : ℚ → ℝ) := by
  intro x hx
  by_contra hxr
  -- `hxr : x ∉ Set.range ((↑) : ℚ → ℝ)` is definitionally `Irrational x`
  exact hx (thomae_continuous_at_irrational hxr)

/-- The image of `ℚ` in `ℝ` has Lebesgue measure zero (countable, atomless `volume`). -/
theorem rat_range_null : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
  (Set.countable_range _).measure_zero volume

/-- **Lebesgue's criterion (measure side).** The discontinuity set of Thomae's
function has Lebesgue measure zero. -/
theorem thomae_discontinuitySet_null :
    volume {x : ℝ | ¬ ContinuousAt thomae x} = 0 :=
  measure_mono_null thomae_discontinuitySet_subset rat_range_null

/-- Thomae's function is **continuous almost everywhere** — the hypothesis of
Lebesgue's criterion, from which classical Riemann integrability follows. -/
theorem thomae_ae_continuousAt : ∀ᵐ x ∂volume, ContinuousAt thomae x := by
  rw [ae_iff]
  exact thomae_discontinuitySet_null

-- ============================================================
-- PART 3: Integrability and the value
-- ============================================================

/-- Thomae's function vanishes almost everywhere. -/
theorem thomae_ae_zero : ∀ᵐ x ∂volume, thomae x = 0 := by
  have hsub : {x : ℝ | thomae x ≠ 0} ⊆ Set.range ((↑) : ℚ → ℝ) := by
    intro x hx
    by_contra hxr
    exact hx (thomae_irrational hxr)
  rw [ae_iff]
  exact measure_mono_null hsub rat_range_null

/-- Thomae's function is Lebesgue integrable (a.e. equal to `0`). -/
theorem thomae_integrable : Integrable thomae volume := by
  refine (integrable_zero ℝ ℝ volume).congr ?_
  filter_upwards [thomae_ae_zero] with x hx
  exact hx.symm

/-- The integral of Thomae's function over the line is `0`. -/
theorem thomae_integral_zero : ∫ x, thomae x ∂volume = 0 :=
  integral_eq_zero_of_ae thomae_ae_zero

/-- Thomae's function is integrable on `[0,1]`. -/
theorem thomae_integrableOn_Icc : IntegrableOn thomae (Set.Icc 0 1) volume :=
  thomae_integrable.integrableOn

/-- The interval integral of Thomae's function over `[0,1]` is `0`. -/
theorem thomae_intervalIntegral_zero : ∫ x in (0 : ℝ)..1, thomae x = 0 := by
  have h0 : ∫ x in (0 : ℝ)..1, thomae x = ∫ _ in (0 : ℝ)..1, (0 : ℝ) :=
    intervalIntegral.integral_congr_ae
      (by filter_upwards [thomae_ae_zero] with x hx _; exact hx)
  rw [h0, intervalIntegral.integral_zero]

/-- **Lebesgue's criterion for Thomae's function.** Its discontinuity set is
Lebesgue-null (so it is continuous a.e.), and it is integrable with interval
integral `0` over `[0,1]`. Classically this is exactly the statement that
Thomae's function is Riemann integrable on `[0,1]` with value `0`, now obtained
through the criterion rather than around it. -/
theorem thomae_riemann_via_lebesgue_criterion :
    volume {x : ℝ | ¬ ContinuousAt thomae x} = 0 ∧
      Integrable thomae volume ∧ ∫ x in (0 : ℝ)..1, thomae x = 0 :=
  ⟨thomae_discontinuitySet_null, thomae_integrable, thomae_intervalIntegral_zero⟩

end LebesgueMeasureOQ01OQ01OQ01
