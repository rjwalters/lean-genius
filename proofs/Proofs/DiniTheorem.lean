import Mathlib

/-!
# Dini's Theorem and the Sharpness of Its Hypotheses

**Dini's theorem.** If `F n` is a monotone sequence of continuous real-valued functions
on a compact space, converging *pointwise* to a continuous limit `f`, then the convergence
is in fact *uniform*.

Mathlib proves Dini's theorem in full generality (codomain a normed lattice additive
commutative group) in `Mathlib/Topology/UniformSpace/Dini.lean`. We re-export the four
real-valued faces of the theorem (monotone / antitone, compact space / compact subset).

The genuinely new content of this entry is a **sharpness witness**: the standard sequence
`Fₙ(x) = xⁿ` on the compact interval `[0,1]`. It is continuous in `x`, antitone in `n`, and
converges pointwise — but its pointwise limit (`0` on `[0,1)`, `1` at `x = 1`) is
discontinuous, so the convergence is *not* uniform. This shows the continuity-of-the-limit
hypothesis in Dini's theorem cannot be dropped.

We also record the companion witness that *compactness of the domain* is necessary: the
same `xⁿ`, restricted to the non-compact set `[0,1)`, is monotone, continuous, and converges
pointwise to the continuous function `0`, yet the convergence is not uniform.

The non-uniformity in the first witness is obtained "for free" from the Mathlib fact that a
uniform limit of continuous functions is continuous (`TendstoUniformlyOn.continuousOn`):
no `ε`-`N` bookkeeping is required.
-/

open Filter Topology Set

namespace DiniTheorem

/-! ## Dini's theorem (re-exported from Mathlib) -/

/-- **Dini's theorem (monotone, compact space).** A monotone increasing sequence of
continuous real-valued functions on a compact space converging pointwise to a continuous
function converges uniformly. -/
theorem dini_monotone {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {F : ℕ → α → ℝ} {f : α → ℝ}
    (hF_cont : ∀ n, Continuous (F n)) (hF_mono : Monotone F) (hf : Continuous f)
    (h : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  Monotone.tendstoUniformly_of_forall_tendsto hF_cont hF_mono hf h

/-- **Dini's theorem (antitone, compact space).** The decreasing version. -/
theorem dini_antitone {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {F : ℕ → α → ℝ} {f : α → ℝ}
    (hF_cont : ∀ n, Continuous (F n)) (hF_anti : Antitone F) (hf : Continuous f)
    (h : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    TendstoUniformly F f atTop :=
  Antitone.tendstoUniformly_of_forall_tendsto hF_cont hF_anti hf h

/-- **Dini's theorem (monotone, compact subset).** The version localized to a compact set
`s`, requiring only continuity / monotonicity / pointwise convergence on `s`. -/
theorem dini_monotone_on {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {f : α → ℝ} {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ n, ContinuousOn (F n) s) (hF_mono : ∀ x ∈ s, Monotone (fun n => F n x))
    (hf : ContinuousOn f s) (h : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto hs hF_cont hF_mono hf h

/-- **Dini's theorem (antitone, compact subset).** -/
theorem dini_antitone_on {α : Type*} [TopologicalSpace α]
    {F : ℕ → α → ℝ} {f : α → ℝ} {s : Set α} (hs : IsCompact s)
    (hF_cont : ∀ n, ContinuousOn (F n) s) (hF_anti : ∀ x ∈ s, Antitone (fun n => F n x))
    (hf : ContinuousOn f s) (h : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto hs hF_cont hF_anti hf h

/-! ## Sharpness witness: `xⁿ` on `[0,1]` (continuity of the limit is necessary) -/

/-- The pointwise limit of `xⁿ` on `[0,1]`: it equals `0` on `[0,1)` and jumps to `1` at
`x = 1`. This function is discontinuous, which is exactly what obstructs uniform convergence. -/
noncomputable def limitPow (x : ℝ) : ℝ := if x = 1 then 1 else 0

/-- Each `x ↦ xⁿ` is continuous. -/
theorem pow_continuous (n : ℕ) : Continuous (fun x : ℝ => x ^ n) := by fun_prop

/-- On `[0,1]`, the sequence `n ↦ xⁿ` is antitone (decreasing). -/
theorem pow_antitone_on {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Antitone (fun n : ℕ => x ^ n) :=
  pow_right_anti₀ hx.1 hx.2

/-- `xⁿ` converges pointwise on `[0,1]` to the discontinuous function `limitPow`. -/
theorem pow_tendsto_limitPow {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 (limitPow x)) := by
  by_cases hx1 : x = 1
  · subst hx1
    simpa [limitPow] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · have hlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    simpa [limitPow, hx1] using tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hlt

/-- The pointwise limit is discontinuous on `[0,1]`: it is not even continuous at the
endpoint `x = 1`, where it jumps from `0` to `1`. -/
theorem limitPow_not_continuousOn : ¬ ContinuousOn limitPow (Icc (0 : ℝ) 1) := by
  intro hcont
  -- approach `1` from the left along `aₖ = 1 - 1/(k+1)`, all of which avoid `1`
  have hpos : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hle : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := by
    intro k; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have ha_mem : ∀ k : ℕ, (1 - 1 / ((k : ℝ) + 1)) ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨by linarith [hle k], by linarith [(hpos k).le]⟩
  have ha_ne : ∀ k : ℕ, (1 - 1 / ((k : ℝ) + 1)) ≠ 1 := by
    intro k h
    have hp := hpos k
    have : 1 / ((k : ℝ) + 1) = 0 := by linarith
    rw [this] at hp; exact lt_irrefl 0 hp
  have ha_tendsto : Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have ha_within :
      Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 1)) atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨ha_tendsto, eventually_of_forall ha_mem⟩
  -- continuity would force `limitPow (aₖ) → limitPow 1 = 1`
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := mem_Icc.2 ⟨zero_le_one, le_refl 1⟩
  have hcomp :
      Tendsto (fun k : ℕ => limitPow (1 - 1 / ((k : ℝ) + 1))) atTop (𝓝 (limitPow 1)) :=
    ((hcont 1 h1mem).tendsto).comp ha_within
  -- but `limitPow (aₖ) = 0`, so the limit is `0`, not `limitPow 1 = 1`
  have hconst :
      Tendsto (fun k : ℕ => limitPow (1 - 1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have heq : (fun k : ℕ => limitPow (1 - 1 / ((k : ℝ) + 1))) = fun _ : ℕ => (0 : ℝ) := by
      funext k; simp only [limitPow, if_neg (ha_ne k)]
    rw [heq]; exact tendsto_const_nhds
  have hbad : limitPow 1 = 0 := tendsto_nhds_unique hcomp hconst
  simp [limitPow] at hbad

/-- **Sharpness witness (continuity of the limit is necessary).** On the compact interval
`[0,1]`, the sequence `xⁿ` is continuous in `x`, antitone in `n`, and converges pointwise —
yet it does **not** converge uniformly, because a uniform limit of continuous functions
would have to be continuous, whereas the pointwise limit jumps at `x = 1`. -/
theorem pow_not_tendstoUniformlyOn :
    ¬ TendstoUniformlyOn (fun n (x : ℝ) => x ^ n) limitPow atTop (Icc (0 : ℝ) 1) := by
  intro h
  exact limitPow_not_continuousOn <|
    h.continuousOn <| Eventually.frequently <|
      eventually_of_forall fun n => (pow_continuous n).continuousOn

/-! ## Companion witness: `xⁿ` on `[0,1)` (compactness of the domain is necessary) -/

/-- `xⁿ → 0` pointwise on the non-compact interval `[0,1)` (here the pointwise limit *is*
continuous). -/
theorem pow_tendsto_zero_on_Ico {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 hx.2

/-- **Sharpness witness (compactness of the domain is necessary).** On the non-compact set
`[0,1)`, the sequence `xⁿ` is continuous, monotone (antitone) in `n`, and converges
pointwise to the continuous function `0` — but the convergence is not uniform: for every `n`
there is a point of `[0,1)` where `xⁿ ≥ 1/2`, so `sup` of the error stays `≥ 1/2`. -/
theorem pow_not_tendstoUniformlyOn_Ico :
    ¬ TendstoUniformlyOn (fun n (x : ℝ) => x ^ n) (fun _ => (0 : ℝ)) atTop (Ico (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  push_neg
  refine ⟨1 / 2, by norm_num, ?_⟩
  -- for every threshold `N`, find `n ≥ N` and a point `x ∈ [0,1)` with `1/2 ≤ xⁿ`
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨N + 1, le_self_add, ?_⟩
  -- by the intermediate value theorem `xⁿ` attains the value `1/2` somewhere in `[0,1]`
  have hcont : ContinuousOn (fun x : ℝ => x ^ (N + 1)) (Icc (0 : ℝ) 1) :=
    (pow_continuous (N + 1)).continuousOn
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hsub := intermediate_value_Icc h01 hcont
  have hmem : (1 / 2 : ℝ) ∈ Icc ((0 : ℝ) ^ (N + 1)) ((1 : ℝ) ^ (N + 1)) := by
    simp only [zero_pow (Nat.succ_ne_zero N), one_pow, mem_Icc]; norm_num
  obtain ⟨x, hxIcc, hxval⟩ := hsub hmem
  have hv : x ^ (N + 1) = 1 / 2 := by simpa using hxval
  have hxlt : x < 1 := by
    refine lt_of_le_of_ne hxIcc.2 ?_
    rintro rfl
    rw [one_pow] at hv; norm_num at hv
  refine ⟨x, ⟨hxIcc.1, hxlt⟩, ?_⟩
  have hx0 : (0 : ℝ) ≤ x ^ (N + 1) := pow_nonneg hxIcc.1 _
  show (1 : ℝ) / 2 ≤ dist (0 : ℝ) (x ^ (N + 1))
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hx0]
  linarith [hv]

end DiniTheorem
