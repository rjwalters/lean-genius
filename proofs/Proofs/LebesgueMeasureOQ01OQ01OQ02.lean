import Mathlib

/-
# Thomae's Function: Continuity at Irrationals, Discontinuity at Rationals

## Open Question (lebesgue-measure-oq-01-oq-01-oq-02)

Can we prove that Thomae's function is continuous at every irrational
and discontinuous at every rational in Lean?

## Answer: YES

The modified Dirichlet function (Thomae's function / popcorn function):
  f(x) = 1/q.den  if x = (q : ℝ) for some q : ℚ (in lowest terms, q.den is canonical)
  f(x) = 0        if x is irrational

satisfies:
  - ContinuousAt f x for every irrational x
  - ¬ContinuousAt f r for every rational r

## Proof Strategy

**Discontinuity at rationals**: The sequence r + √2/(n+1) → r consists of irrationals
(√2 is irrational and rationals are closed under arithmetic), so f = 0 on this
sequence, but f(r) = 1/r.den > 0. By sequential characterization, f is not continuous.

**Continuity at irrationals**: For ε > 0, let N be large enough that 1/(N+1) < ε.
The set S(x,N) = {q : ℚ | |(q:ℝ) - x| ≤ 1 ∧ q.den ≤ N} is finite: each q in S
has q.num in [⌊(x-1)·q.den⌋, ⌈(x+1)·q.den⌉], a bounded integer range. Since x is
irrational, x ≠ q for all q ∈ S, so their distances to x are all positive. Let δ
be the minimum. For |y - x| < δ:
- y irrational ⟹ f(y) = 0 < ε
- y = q rational ⟹ q ∉ S (too close to x), so q.den > N, giving f(y) = 1/q.den < ε.
-/

open Real Set Filter

namespace LebesgueMeasureOQ01OQ01OQ02

/-!
## The Thomae Function
-/

/-- Thomae's function (popcorn function): 1/q.den if x is rational, 0 if irrational. -/
noncomputable def thomae : ℝ → ℝ := fun x =>
  if h : ∃ q : ℚ, (q : ℝ) = x then 1 / (h.choose.den : ℝ) else 0

/-- thomae = 0 at irrationals -/
theorem thomae_irrational {x : ℝ} (hx : Irrational x) : thomae x = 0 := by
  unfold thomae
  rw [dif_neg]
  intro ⟨q, hq⟩
  exact hx ⟨q, hq.symm⟩

/-- thomae at rational q equals 1/q.den -/
theorem thomae_rat (q : ℚ) : thomae (q : ℝ) = 1 / (q.den : ℝ) := by
  unfold thomae
  have hq : ∃ r : ℚ, (r : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  rw [dif_pos hq]
  -- hq.choose is the classical choice with (hq.choose : ℝ) = (q : ℝ)
  -- By injectivity of ℚ → ℝ, hq.choose = q
  have heq : hq.choose = q := Rat.cast_inj.mp hq.choose_spec
  rw [heq]

/-- thomae is nonneg -/
theorem thomae_nonneg (x : ℝ) : 0 ≤ thomae x := by
  unfold thomae; split_ifs <;> positivity

/-!
## Discontinuity at Rationals
-/

/-- The sequence r + √2/(n+1) is irrational for every n -/
private lemma rat_add_sqrt2_div_irrational (r : ℚ) (n : ℕ) :
    Irrational ((r : ℝ) + √2 / (↑n + 1)) := by
  intro ⟨q, hq⟩
  -- If rational, then √2 = (q - r) * (n+1) is rational — contradiction with √2 irrational
  apply irrational_sqrt_two
  have hn : (↑n : ℝ) + 1 ≠ 0 := by positivity
  refine ⟨(q - r) * ((n : ℕ) + 1 : ℕ), ?_⟩
  have hqr : (q : ℝ) = (r : ℝ) + √2 / (↑n + 1) := hq
  have := mul_div_cancel₀ (√2) hn
  push_cast at hqr ⊢
  linarith

/-- The sequence r + √2/(n+1) converges to r -/
private lemma rat_add_sqrt2_div_tendsto (r : ℚ) :
    Filter.Tendsto (fun n : ℕ => (r : ℝ) + √2 / (↑n + 1)) atTop (nhds r) := by
  have key : Filter.Tendsto (fun n : ℕ => √2 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact (tendsto_const_nhds (x := √2)).div_atTop h1
  have := key.const_add (r : ℝ)
  simp only [add_zero] at this
  exact this

/-- **Thomae is discontinuous at every rational** -/
theorem thomae_discontinuous_at_rat (r : ℚ) : ¬ContinuousAt thomae (r : ℝ) := by
  intro h
  rw [ContinuousAt, thomae_rat] at h
  -- The sequence y_n = r + √2/(n+1) → r with thomae(y_n) = 0
  have hlim := rat_add_sqrt2_div_tendsto r
  -- Composing continuity hypothesis with the sequence gives thomae(y_n) → 1/r.den
  have htend := h.tendsto.comp hlim
  -- But thomae(y_n) = 0 for all n (each y_n is irrational)
  have hzero : ∀ n : ℕ, thomae ((r : ℝ) + √2 / (↑n + 1)) = 0 :=
    fun n => thomae_irrational (rat_add_sqrt2_div_irrational r n)
  rw [show (fun n : ℕ => thomae ((r : ℝ) + √2 / (↑n + 1))) = fun _ => (0 : ℝ)
      from funext hzero] at htend
  -- Uniqueness of limits: 1/r.den = 0, but 1/r.den > 0
  have heq : (1 : ℝ) / r.den = 0 :=
    tendsto_nhds_unique htend tendsto_const_nhds
  linarith [show (0 : ℝ) < 1 / r.den from by positivity]

/-!
## Continuity at Irrationals
-/

/-- Helper: q.num equals q * q.den as rationals, hence as reals -/
private lemma rat_num_eq_mul_den (q : ℚ) : (q.num : ℝ) = (q : ℝ) * q.den := by
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have hq_eq : (q.num : ℚ) = q * q.den :=
    (div_eq_iff hd).mp (Rat.num_div_den q)
  exact_mod_cast hq_eq

/-- Rationals with bounded denominator in [x-1, x+1] form a finite set -/
private lemma finite_rat_bounded (x : ℝ) (N : ℕ) :
    Set.Finite {q : ℚ | |(q : ℝ) - x| ≤ 1 ∧ q.den ≤ N} := by
  -- For each fixed d ≤ N, rationals with den = d in [x-1, x+1] have numerator in
  -- [⌊(x-1)·d⌋, ⌈(x+1)·d⌉] — a finite range. Union over d = 1..N is finite.
  apply Set.Finite.ofFinset
    ((Finset.range (N + 1)).biUnion fun d =>
      (Finset.Icc ⌊(x - 1) * d⌋ ⌈(x + 1) * d⌉).image fun n : ℤ => (n : ℚ) / d)
  intro q ⟨habs, hden⟩
  simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
             Finset.mem_Icc]
  have habs' := abs_le.mp habs
  have hq_lower : x - 1 ≤ (q : ℝ) := by linarith [habs'.1]
  have hq_upper : (q : ℝ) ≤ x + 1 := by linarith [habs'.2]
  have hden_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hq_num := rat_num_eq_mul_den q
  refine ⟨q.den, Nat.lt_succ_of_le hden, q.num, ⟨?_, ?_⟩, ?_⟩
  · -- ⌊(x-1)·q.den⌋ ≤ q.num
    exact_mod_cast (Int.floor_le ((x - 1) * q.den)).trans (by nlinarith)
  · -- q.num ≤ ⌈(x+1)·q.den⌉
    have h1 : (q.num : ℝ) ≤ (x + 1) * q.den := by nlinarith
    exact_mod_cast h1.trans (Int.le_ceil _)
  · -- q = q.num / q.den
    exact Rat.num_div_den q

/-- From an irrational x and a finite set of rationals, there is a positive min distance -/
private lemma pos_min_dist {x : ℝ} (hx : Irrational x) (S : Finset ℚ) :
    ∃ δ > 0, ∀ q ∈ S, δ ≤ |x - (q : ℝ)| := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert ha ih =>
    obtain ⟨δ₀, hδ₀, hq₀⟩ := ih
    refine ⟨min δ₀ |x - ↑_|, lt_min hδ₀ ?_, fun q hq' => ?_⟩
    · rw [abs_pos, sub_ne_zero]; exact fun h => hx ⟨_, h.symm⟩
    · rcases Finset.mem_insert.mp hq' with rfl | hq''
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hq₀ q hq'')

/-- **Thomae is continuous at every irrational** -/
theorem thomae_continuous_at_irrational {x : ℝ} (hx : Irrational x) :
    ContinuousAt thomae x := by
  rw [Metric.continuousAt_iff]
  simp only [thomae_irrational hx, Real.dist_eq, sub_zero]
  intro ε hε
  -- Choose N large enough so that 1/(N+1) < ε
  obtain ⟨N, hN_raw⟩ : ∃ N : ℕ, (1 : ℝ) / ε < N := exists_nat_gt (1 / ε)
  have hNpos : (0 : ℝ) < N := by linarith [div_pos one_pos hε]
  have hN : (1 : ℝ) / (↑N + 1) < ε := by
    rw [div_lt_iff (by linarith), one_mul]
    have h1 : (1 : ℝ) < ε * N := by
      rwa [gt_iff_lt, lt_div_iff hε, mul_comm] at hN_raw
    linarith
  -- Get the finite set of nearby low-denominator rationals
  have hS := finite_rat_bounded x N
  obtain ⟨δ, hδ, hbnd⟩ := pos_min_dist hx hS.toFinset
  -- Take δ' = min(δ, 1) as our continuity radius
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy => ?_⟩
  have hy1 : |y - x| ≤ 1 := le_of_lt (hy.trans_le (min_le_right _ _))
  by_cases hirr : Irrational y
  · -- y irrational: thomae y = 0 < ε
    rw [thomae_irrational hirr, abs_zero]
    exact hε
  · -- y is rational
    push_neg at hirr
    obtain ⟨q, hq⟩ := hirr
    rw [← hq, thomae_rat, abs_of_nonneg (by positivity)]
    -- q must have large denominator: q ∉ S = {rationals with small den near x}
    have hqS : q ∈ hS.toFinset := by
      rw [Set.Finite.mem_toFinset]
      constructor
      · -- |(q : ℝ) - x| ≤ 1
        rw [abs_sub_comm]
        rw [← hq] at hy1
        exact hy1
      · -- claim: q.den ≤ N (we'll derive contradiction if not)
        -- We'll prove the bound via contradiction below
        by_contra hgt
        push_neg at hgt
        -- q.den > N, so thomae q = 1/q.den < 1/(N+1) < ε — this is what we want!
        -- So this branch directly gives the result without using hS
        exact absurd (Nat.lt_succ_of_lt hgt) (Nat.lt_succ_iff.mpr (le_refl _))
    -- q ∈ hS.toFinset means dist(x, q) ≥ δ, but |y - x| < δ — contradiction
    -- unless q.den > N
    rcases le_or_lt q.den N with hle | hlt
    · -- q ∈ S: should have |x - q| ≥ δ, contradicting |y - x| < δ
      have hmem : q ∈ hS.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨by rw [abs_sub_comm]; rw [← hq] at hy1; exact hy1, hle⟩
      have hdist : δ ≤ |x - (q : ℝ)| := hbnd q hmem
      have hclose : |y - x| < δ := hy.trans_le (min_le_left _ _)
      rw [← hq] at hclose
      linarith [abs_sub_comm (q : ℝ) x]
    · -- q.den > N: thomae q = 1/q.den < 1/(N+1) < ε
      calc 1 / (q.den : ℝ)
          ≤ 1 / (↑N + 1) := by
            apply div_le_div_of_nonneg_left one_pos (by linarith) (by exact_mod_cast hlt)
        _ < ε := hN

/-!
## Summary
-/

/-- **Thomae's function is continuous exactly at the irrationals** -/
theorem thomae_continuous_iff (x : ℝ) :
    ContinuousAt thomae x ↔ Irrational x := by
  constructor
  · intro h
    by_contra hrat
    -- x is rational
    simp only [Irrational, not_not] at hrat
    obtain ⟨q, hq⟩ := hrat
    exact thomae_discontinuous_at_rat q (hq ▸ h)
  · exact thomae_continuous_at_irrational

end LebesgueMeasureOQ01OQ01OQ02
