/-
  Capacity of parallel Gaussian channels via water-filling

  Open question (shannon-channel-coding-awgn-oq-03-oq-01):
  "Capacity of parallel Gaussian channels via water-filling."

  ## The problem

  Given `n` independent AWGN sub-channels with noise powers `N₁,…,Nₙ > 0` and a
  total transmit-power budget `P ≥ 0` to share among them, the total achievable
  rate is

        R(P₁,…,Pₙ) = ∑ᵢ ½ log(1 + Pᵢ/Nᵢ) = ∑ᵢ perUseCapacity Pᵢ Nᵢ

  where `perUseCapacity P N = ½ log(1 + P/N)` is definitionally identical to the
  gallery's per-use AWGN capacity `ShannonAWGN.awgnCapacity` (inlined below to
  keep this file self-contained).  The **water-filling theorem** (Shannon 1949;
  Cover & Thomas, *Elements of Information Theory*, Thm 9.9.1) states that the
  budget-constrained maximum

        max_{Pᵢ ≥ 0, ∑ Pᵢ ≤ P} R(P₁,…,Pₙ)

  is attained by the *water-filling allocation*

        Pᵢ⋆ = (μ − Nᵢ)₊ = max (μ − Nᵢ) 0,

  where the common **water level** `μ ≥ 0` is the unique solution of
  `∑ᵢ (μ − Nᵢ)₊ = P`:  pour power into a landscape whose floor heights are the
  noise levels `Nᵢ` until the water surface reaches height `μ`; each channel
  receives depth `(μ − Nᵢ)₊`, and channels too noisy to reach the surface
  (`Nᵢ ≥ μ`) are switched off.

  ## What this file proves (all axiom-free, sorry-free)

  1. `add_waterAlloc`       — the key algebraic identity `Nᵢ + Pᵢ⋆ = max μ Nᵢ`.
  2. `waterfilling_optimal` — **KKT optimality**: for the water level `μ` of a
     budget `P`, the allocation `Pᵢ⋆` maximises the total rate over every
     feasible allocation.  The proof is *elementary* — it uses only the tangent
     bound `log u ≤ u − 1` (`Real.log_le_sub_one_of_pos`) as a stand-in for the
     first-order optimality condition, avoiding all differentiability / Lagrange
     machinery.
  3. `waterAlloc_rate_closedForm` — the closed-form optimum
     `R(P⋆) = ∑ᵢ ½ log(max μ Nᵢ / Nᵢ)`.
  4. `exists_waterLevel` — **existence** of a water level `μ ∈ [0, M]` solving
     `∑ᵢ (μ − Nᵢ)₊ = P` (intermediate value theorem on a continuous, monotone,
     unbounded budget function).
  5. `waterLevel_unique` — **uniqueness** of the water level for a positive
     budget `P > 0` (strict monotonicity of the budget function once any channel
     is active).

  Together (2)+(4)+(5) are exactly the three open items recorded for this
  problem: optimality of `Pᵢ⋆`, existence/uniqueness of `μ`, and the closed
  form.  The mathematical heart — that `(μ − Nᵢ)₊` is *optimal* — is proved by a
  one-line-per-channel concavity (tangent) inequality summed across channels.
-/

import Mathlib

open Real
open scoped BigOperators

namespace ShannonWaterFilling

variable {ι : Type*} [Fintype ι]

/-- **Per-use AWGN capacity** `½ log(1 + P/N)` (nats per channel use).  This is
    *definitionally identical* to the gallery's `ShannonAWGN.awgnCapacity`; it is
    inlined here so this file depends only on Mathlib and is verifiable
    independently of the Shannon-entropy import chain. -/
noncomputable def perUseCapacity (P N : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + P / N)

/-- The **water-filling allocation** at water level `μ` for noise powers `N`:
    channel `i` receives depth `(μ − Nᵢ)₊ = max (μ − Nᵢ) 0`. -/
noncomputable def waterAlloc (μ : ℝ) (N : ι → ℝ) (i : ι) : ℝ :=
  max (μ - N i) 0

/-- The **total rate** of a parallel Gaussian channel with noise powers `N` and
    power allocation `P`:
    `R(P) = ∑ᵢ perUseCapacity Pᵢ Nᵢ = ∑ᵢ ½ log(1 + Pᵢ/Nᵢ)`. -/
noncomputable def parallelRate (N P : ι → ℝ) : ℝ :=
  ∑ i, perUseCapacity (P i) (N i)

/-- The **budget function** `g(μ) = ∑ᵢ (μ − Nᵢ)₊` — the total power poured in at
    water level `μ`.  The water level for a budget `P` is a solution of
    `g(μ) = P`. -/
noncomputable def waterBudget (N : ι → ℝ) (μ : ℝ) : ℝ :=
  ∑ i, waterAlloc μ N i

/-! ## The key algebraic identity -/

/-- **Water-level identity.**  Adding the noise floor back to the water-filling
    depth recovers the water surface, clipped up to the noise floor:
    `Nᵢ + (μ − Nᵢ)₊ = max μ Nᵢ`. -/
theorem add_waterAlloc (μ : ℝ) (N : ι → ℝ) (i : ι) :
    N i + waterAlloc μ N i = max μ (N i) := by
  unfold waterAlloc
  rcases le_total (N i) μ with h | h
  · rw [max_eq_left (by linarith), max_eq_left h]; ring
  · rw [max_eq_right (by linarith), max_eq_right h]; ring

/-- The water-filling depth is non-negative. -/
theorem waterAlloc_nonneg (μ : ℝ) (N : ι → ℝ) (i : ι) :
    0 ≤ waterAlloc μ N i := le_max_right _ _

/-! ## Optimality of the water-filling allocation -/

/-- **Per-channel tangent bound** (the first-order optimality condition, in
    elementary form).  For positive noise, positive water level, a feasible power
    `0 ≤ xᵢ` and the water-filling depth `Pᵢ⋆`,

        perUseCapacity xᵢ Nᵢ − perUseCapacity Pᵢ⋆ Nᵢ ≤ (xᵢ − Pᵢ⋆) / (2μ).

    Concavity of `t ↦ log(1 + t/Nᵢ)` is captured by `log u ≤ u − 1`; the
    denominator drops from `max μ Nᵢ` to `μ` because inactive channels
    (`Nᵢ ≥ μ`) carry `Pᵢ⋆ = 0` and non-negative `xᵢ`. -/
theorem perUseCapacity_sub_le
    (N : ι → ℝ) {μ : ℝ} (hμ : 0 < μ) (i : ι) (hNi : 0 < N i)
    {xi : ℝ} (hxi : 0 ≤ xi) :
    perUseCapacity xi (N i) - perUseCapacity (waterAlloc μ N i) (N i)
      ≤ (xi - waterAlloc μ N i) / (2 * μ) := by
  set Ps := waterAlloc μ N i with hPs
  have hPs_nonneg : 0 ≤ Ps := waterAlloc_nonneg μ N i
  have hNne : N i ≠ 0 := ne_of_gt hNi
  have hb : 0 < N i + xi := by linarith
  have ha : 0 < N i + Ps := by linarith
  -- rewrite each capacity as ½·(log(Nᵢ + ·) − log Nᵢ)
  have hrw : ∀ t : ℝ, 0 ≤ t →
      perUseCapacity t (N i) = (1 / 2) * (Real.log (N i + t) - Real.log (N i)) := by
    intro t ht
    have hNt : (0 : ℝ) < N i + t := by linarith
    unfold perUseCapacity
    have hdiv : 1 + t / N i = (N i + t) / N i := by
      rw [add_div, div_self hNne]
    rw [hdiv, Real.log_div hNt.ne' hNne]
  rw [hrw xi hxi, hrw Ps hPs_nonneg]
  -- the capacity difference is ½·log((Nᵢ+xᵢ)/(Nᵢ+Pᵢ⋆))
  have hlog : (1 / 2) * (Real.log (N i + xi) - Real.log (N i))
      - (1 / 2) * (Real.log (N i + Ps) - Real.log (N i))
      = (1 / 2) * Real.log ((N i + xi) / (N i + Ps)) := by
    rw [Real.log_div hb.ne' ha.ne']; ring
  rw [hlog]
  -- tangent bound: log u ≤ u − 1, with u = (Nᵢ+xᵢ)/(Nᵢ+Pᵢ⋆)
  have htan : Real.log ((N i + xi) / (N i + Ps)) ≤ (xi - Ps) / (N i + Ps) := by
    have h := Real.log_le_sub_one_of_pos (x := (N i + xi) / (N i + Ps)) (by positivity)
    have hstep : (N i + xi) / (N i + Ps) - 1 = (xi - Ps) / (N i + Ps) := by
      field_simp; ring
    linarith [hstep ▸ h]
  -- coefficient bound: (xᵢ − Pᵢ⋆)/(Nᵢ+Pᵢ⋆) ≤ (xᵢ − Pᵢ⋆)/μ
  have hden : N i + Ps = max μ (N i) := by rw [hPs]; exact add_waterAlloc μ N i
  have hcoef : (xi - Ps) / (N i + Ps) ≤ (xi - Ps) / μ := by
    rcases le_total (N i) μ with h | h
    · have hEq : N i + Ps = μ := by rw [hden, max_eq_left h]
      exact le_of_eq (by rw [hEq])
    · have hPs0 : Ps = 0 := by
        rw [hPs]; unfold waterAlloc; exact max_eq_right (by linarith)
      rw [hPs0]; simp only [sub_zero, add_zero]
      exact div_le_div_of_nonneg_left hxi hμ h
  calc (1 / 2) * Real.log ((N i + xi) / (N i + Ps))
      ≤ (1 / 2) * ((xi - Ps) / (N i + Ps)) := by linarith [htan]
    _ ≤ (1 / 2) * ((xi - Ps) / μ) := by
          exact mul_le_mul_of_nonneg_left hcoef (by norm_num)
    _ = (xi - Ps) / (2 * μ) := by ring

/-- **Water-filling is optimal (KKT optimality).**  Let `μ > 0` be the water
    level realising a budget `P` (i.e. `∑ᵢ (μ − Nᵢ)₊ = P`).  Then for every
    feasible allocation `x` (non-negative, total power `≤ P`),

        parallelRate N x ≤ parallelRate N (waterAlloc μ N).

    The water-filling allocation attains the constrained capacity of the vector
    Gaussian channel.  Proof: sum the per-channel tangent bound
    `perUseCapacity_sub_le`, then collapse the linear part using
    `∑(xᵢ − Pᵢ⋆) = ∑xᵢ − P ≤ 0`. -/
theorem waterfilling_optimal
    (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    {μ : ℝ} (hμ : 0 < μ) {P : ℝ}
    (hbudget : waterBudget N μ = P)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxsum : ∑ i, x i ≤ P) :
    parallelRate N x ≤ parallelRate N (waterAlloc μ N) := by
  rw [← sub_nonpos]
  have hdiff : parallelRate N x - parallelRate N (waterAlloc μ N)
      = ∑ i, (perUseCapacity (x i) (N i)
                - perUseCapacity (waterAlloc μ N i) (N i)) := by
    unfold parallelRate
    rw [← Finset.sum_sub_distrib]
  rw [hdiff]
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      perUseCapacity (x i) (N i) - perUseCapacity (waterAlloc μ N i) (N i)
        ≤ (x i - waterAlloc μ N i) / (2 * μ) := by
    intro i _
    exact perUseCapacity_sub_le N hμ i (hN i) (hx i)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsum : ∑ i, (x i - waterAlloc μ N i) / (2 * μ)
      = (∑ i, x i - ∑ i, waterAlloc μ N i) / (2 * μ) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hsum]
  have hPsum : ∑ i, waterAlloc μ N i = P := hbudget
  rw [hPsum]
  apply div_nonpos_iff.mpr
  right
  exact ⟨by linarith, by positivity⟩

/-! ## Closed form of the optimum -/

/-- **Closed-form optimum.**  The water-filling rate collapses to
    `∑ᵢ ½ log(max μ Nᵢ / Nᵢ)`:  active channels contribute `½ log(μ/Nᵢ)` and
    switched-off channels contribute `0`. -/
theorem waterAlloc_rate_closedForm
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) (μ : ℝ) :
    parallelRate N (waterAlloc μ N)
      = ∑ i, (1 / 2) * Real.log (max μ (N i) / N i) := by
  unfold parallelRate perUseCapacity
  apply Finset.sum_congr rfl
  intro i _
  have hNne : N i ≠ 0 := ne_of_gt (hN i)
  have hdiv : 1 + waterAlloc μ N i / N i = max μ (N i) / N i := by
    rw [← add_waterAlloc μ N i, add_div, div_self hNne]
  rw [hdiv]

/-! ## Existence and uniqueness of the water level -/

/-- The budget function `g(μ) = ∑ᵢ (μ − Nᵢ)₊` is continuous in `μ`. -/
theorem continuous_waterBudget (N : ι → ℝ) :
    Continuous (waterBudget N) := by
  unfold waterBudget waterAlloc
  exact continuous_finset_sum _ fun i _ =>
    (continuous_id.sub continuous_const).max continuous_const

/-- The budget function is monotone in the water level. -/
theorem monotone_waterBudget (N : ι → ℝ) :
    Monotone (waterBudget N) := by
  intro a b hab
  unfold waterBudget waterAlloc
  exact Finset.sum_le_sum fun i _ => max_le_max (by linarith) le_rfl

/-- At water level `0` the budget is `0` (all channels are switched off, since
    every noise power is positive). -/
theorem waterBudget_zero (N : ι → ℝ) (hN : ∀ i, 0 < N i) :
    waterBudget N 0 = 0 := by
  unfold waterBudget waterAlloc
  apply Finset.sum_eq_zero
  intro i _
  rw [max_eq_right (by linarith [hN i])]

/-- **Existence of the water level.**  For any non-negative budget `P`, there is
    a water level `μ ∈ [0, M]` with `∑ᵢ (μ − Nᵢ)₊ = P`, obtained by the
    intermediate value theorem applied to the continuous, monotone budget
    function between `μ = 0` (budget `0`) and a large `μ = M` (budget `≥ P`). -/
theorem exists_waterLevel [Nonempty ι]
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) {P : ℝ} (hP : 0 ≤ P) :
    ∃ μ, 0 ≤ μ ∧ waterBudget N μ = P := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  set M := N i₀ + P with hM
  have hM0 : (0 : ℝ) ≤ M := by have := (hN i₀).le; linarith
  -- budget at M dominates P (the single channel i₀ already contributes P)
  have hMbig : P ≤ waterBudget N M := by
    have hterm : waterAlloc M N i₀ = P := by
      unfold waterAlloc
      have hle : (0 : ℝ) ≤ M - N i₀ := by rw [hM]; linarith
      rw [max_eq_left hle, hM]; ring
    calc P = waterAlloc M N i₀ := hterm.symm
      _ ≤ waterBudget N M := by
            unfold waterBudget
            exact Finset.single_le_sum
              (f := fun i => waterAlloc M N i)
              (fun i _ => waterAlloc_nonneg M N i) (Finset.mem_univ i₀)
  have hcont : ContinuousOn (waterBudget N) (Set.Icc 0 M) :=
    (continuous_waterBudget N).continuousOn
  have hmem : P ∈ Set.Icc (waterBudget N 0) (waterBudget N M) :=
    ⟨by rw [waterBudget_zero N hN]; exact hP, hMbig⟩
  obtain ⟨μ, hμmem, hμval⟩ := intermediate_value_Icc hM0 hcont hmem
  exact ⟨μ, hμmem.1, hμval⟩

/-- **Strict monotonicity where the budget is positive.**  If some channel is
    already active at level `a` (`g(a) > 0`) then raising the water level
    strictly increases the budget.  This is the uniqueness engine. -/
theorem waterBudget_strictMono_of_pos (N : ι → ℝ) {a b : ℝ}
    (hab : a < b) (hpos : 0 < waterBudget N a) :
    waterBudget N a < waterBudget N b := by
  -- some channel is active at level a
  have hact : ∃ i, 0 < waterAlloc a N i := by
    by_contra hcon
    push_neg at hcon
    have hle : waterBudget N a ≤ 0 := by
      unfold waterBudget
      exact Finset.sum_nonpos fun i _ => hcon i
    linarith
  obtain ⟨i₀, hi₀⟩ := hact
  have hpos0 : 0 ≤ a - N i₀ := by
    unfold waterAlloc at hi₀
    rcases le_or_gt 0 (a - N i₀) with h | h
    · exact h
    · rw [max_eq_right (le_of_lt h)] at hi₀; exact absurd hi₀ (lt_irrefl 0)
  unfold waterBudget
  apply Finset.sum_lt_sum
  · intro i _
    exact max_le_max (by linarith) le_rfl
  · refine ⟨i₀, Finset.mem_univ i₀, ?_⟩
    have haa : waterAlloc a N i₀ = a - N i₀ := by
      unfold waterAlloc; exact max_eq_left hpos0
    have hbb : b - N i₀ ≤ waterAlloc b N i₀ := le_max_left _ _
    rw [haa]; linarith

/-- **Uniqueness of the water level for a positive budget.**  Any two water
    levels solving `g(μ) = P` with `P > 0` coincide. -/
theorem waterLevel_unique (N : ι → ℝ) {P : ℝ} (hP : 0 < P)
    {μ₁ μ₂ : ℝ} (h1 : waterBudget N μ₁ = P) (h2 : waterBudget N μ₂ = P) :
    μ₁ = μ₂ := by
  rcases lt_trichotomy μ₁ μ₂ with h | h | h
  · have hp1 : 0 < waterBudget N μ₁ := by rw [h1]; exact hP
    have hlt := waterBudget_strictMono_of_pos N h hp1
    rw [h1, h2] at hlt
    exact absurd hlt (lt_irrefl P)
  · exact h
  · have hp2 : 0 < waterBudget N μ₂ := by rw [h2]; exact hP
    have hlt := waterBudget_strictMono_of_pos N h hp2
    rw [h1, h2] at hlt
    exact absurd hlt (lt_irrefl P)

/-- **A positive budget forces a positive water level.**  If the water level `μ`
    realises a strictly positive budget `P > 0`, then `μ > 0`.  Otherwise
    (`μ ≤ 0`) monotonicity would push the budget below its value `0` at level `0`
    (all channels off, since every noise power is positive), contradicting
    `g(μ) = P > 0`.  This is the bridge that upgrades the *existence* level
    `0 ≤ μ` to the *strictly positive* level required by optimality. -/
theorem waterLevel_pos (N : ι → ℝ) (hN : ∀ i, 0 < N i) {P : ℝ} (hP : 0 < P)
    {μ : ℝ} (hμ : waterBudget N μ = P) : 0 < μ := by
  by_contra hcon
  push_neg at hcon
  have hmono := monotone_waterBudget N hcon
  rw [waterBudget_zero N hN, hμ] at hmono
  linarith

/-! ## Capacity of the parallel Gaussian channel (capstone) -/

/-- **Capacity of the parallel Gaussian channel via water-filling.**  This is the
    full statement of the open question.  For any strictly positive power budget
    `P > 0` there is a water level `μ > 0` whose water-filling allocation
    `Pᵢ⋆ = (μ − Nᵢ)₊`

      * **is feasible** — every `Pᵢ⋆ ≥ 0` and it uses exactly the budget,
        `∑ᵢ Pᵢ⋆ = P`;
      * **is optimal** — it maximises the total rate `∑ᵢ ½ log(1 + Pᵢ/Nᵢ)` over
        every feasible allocation `x` (`xᵢ ≥ 0`, `∑ xᵢ ≤ P`);
      * **attains the closed-form capacity** `∑ᵢ ½ log(max μ Nᵢ / Nᵢ)`.

    It assembles the file's separate results — `exists_waterLevel`,
    `waterLevel_pos`, `waterfilling_optimal`, `waterAlloc_rate_closedForm` — into
    the single "the constrained capacity of a bank of parallel AWGN sub-channels
    is achieved by water-filling" statement.  The *value* of the water level `μ`
    is the only remaining implicit datum; by `waterLevel_unique` it is uniquely
    determined by `P`. -/
theorem parallel_gaussian_capacity [Nonempty ι]
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) {P : ℝ} (hP : 0 < P) :
    ∃ μ : ℝ, 0 < μ ∧
      (∀ i, 0 ≤ waterAlloc μ N i) ∧
      (∑ i, waterAlloc μ N i = P) ∧
      (∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i ≤ P) →
        parallelRate N x ≤ parallelRate N (waterAlloc μ N)) ∧
      parallelRate N (waterAlloc μ N)
        = ∑ i, (1 / 2) * Real.log (max μ (N i) / N i) := by
  obtain ⟨μ, hμ0, hbudget⟩ := exists_waterLevel N hN hP.le
  have hμpos : 0 < μ := waterLevel_pos N hN hP hbudget
  refine ⟨μ, hμpos, fun i => waterAlloc_nonneg μ N i, hbudget, ?_,
          waterAlloc_rate_closedForm N hN μ⟩
  intro x hx hxsum
  exact waterfilling_optimal N hN hμpos hbudget x hx hxsum

end ShannonWaterFilling
