import Mathlib.Tactic

/-
  Property B — the convex tradeoff that powers the Radhakrishnan–Srinivasan flip rate.

  Open question (property-b-first-moment-oq-03): sharpen Erdős's 1963 bound
  `m(k) ≥ 2^(k-1)` to the Radhakrishnan–Srinivasan `m(k) = Ω(2^k·√(k/log k))` (RS 2000)
  via the asymmetric / recoloring refinement of the first moment argument.

  Three sibling entries settled the *negative* half of the program — the easy shortcuts
  do NOT move Erdős's threshold:

    • `property-b-first-moment-oq-03-oq-01` (`PropertyBFirstMomentAsymmetric.lean`):
      biasing the random coloring is worthless (`monoProb k p = p^k+(1-p)^k` is minimised
      at `p = 1/2`, value `2^(1-k)`).
    • `property-b-first-moment-oq-03-oq-03` (`PropertyBFirstMomentIndepRecoloring.lean`):
      *independent / product-space* recoloring is worthless — XOR-ing a uniform colour with
      an independent flip stays uniform, leaving `monoIndep k p = 2^(1-k)` for every `p`.

  and the *positive* deterministic core was formalised in
    • `property-b-first-moment-oq-03-oq-02` (`PropertyBFirstMomentRecoloring.lean`):
      flipping one private vertex of each monochromatic edge repairs the colouring.

  What the three negatives pin down is that the RS gain lives entirely in the
  *conditional, order-dependent* recoloring step: recolour ONLY the vertices of *dangerous*
  (already monochromatic) edges, each independently with a small probability `p`. This file
  formalises the two quantitative facts that the prior negatives could not reach — the
  **gain** of conditional recoloring and the **convex tradeoff** whose optimum selects the
  RS flip rate. It is the analytic "engine" left open as decomposition step (3) in the
  knowledge base.

  Model. After the uniform first round, a monochromatic ("dangerous") `k`-edge is recoloured
  by flipping each of its `k` vertices independently with probability `p`. It *survives* in
  its original colour iff no vertex flips:

      survivesOrig p k = (1 - p)^k.

  Unlike the product model (factor identically `1`, oq-03-oq-03), this is **strictly < 1**
  for every flip rate `p ∈ (0,1]` and `k ≥ 1`: conditional recoloring genuinely reduces a
  dangerous edge's survival. But one cannot push `p` to the unconstrained optimum `1/2`,
  because flipping vertices *creates* new monochromatic edges elsewhere — a *loss* term that
  grows with `p`. Bounding the gain by `(1-p)^k ≤ e^{-kp}` and modelling the loss linearly,
  `c·k·p`, the per-edge failure proxy is

      G(p) = e^{-k p} + c·k·p,

  a strictly convex function of `p`. Its minimum over all `p` is the closed form

      min_p G(p) = c·(1 - log c),   attained at   p* = -(log c)/k,

  i.e. a *small* flip rate `p* ≈ log(1/c)/k`. This `log(1/c)/k` scaling of the optimiser is
  exactly the mechanism behind the RS `√(k/log k)` improvement.

  Results (all over the real first-moment model, 0 sorries / 0 axioms):

    • `survivesOrig_le_one`            : `(1-p)^k ≤ 1`.
    • `survivesOrig_lt_one`            : `0 < p ≤ 1`, `k ≠ 0` ⟹ `(1-p)^k < 1` (strict gain).
    • `expSurvivors_cond_lt_baseline` : conditional recoloring strictly lowers the expected
                                        number of surviving dangerous edges below the Erdős
                                        baseline `m·2^(1-k)`.
    • `survivesOrig_le_exp`            : `(1-p)^k ≤ e^{-k p}` — linearises the gain term.
    • `tradeoff_ge_optimum`           : `G(p) ≥ c·(1 - log c)` for every `p` — the convex
                                        lower envelope = the optimum value.
    • `tradeoff_eq_at_optimum`        : `G(p*) = c·(1 - log c)` at `p* = -(log c)`, so the
                                        bound is tight (optimum attained).

  Honest scope. This supplies the analytic engine (gain bound + convex optimisation), NOT a
  derivation of `m(k) = Ω(2^k·√(k/log k))`. Assembling RS still needs (1) the rational
  two-stage single-edge expectation with the genuine loss coefficient `c`, (2) the union
  bound over `m` edges, and (3) the substitution of `p*` into a real `√(k/log k)` asymptotic
  — all in a conditional (non-product) probability model. The optimisation lemma here is the
  reusable centrepiece of that final step.

  Companion to `PropertyBFirstMoment.lean` (Erdős 1963) and the three oq-03 siblings.
-/

namespace ProbMethod.PropertyB.ConditionalOpt

open Real

/-- Survival probability (in its original colour) of a *dangerous* monochromatic `k`-edge
under conditional recoloring: each of the `k` vertices is flipped independently with
probability `p`, and the edge stays monochromatic in its original colour iff none flips. -/
noncomputable def survivesOrig (p : ℝ) (k : ℕ) : ℝ := (1 - p) ^ k

/-- The Erdős first-round monochromatic probability of a `k`-edge, `2·(1/2)^k = 2^(1-k)`. -/
noncomputable def monoOneStage (k : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ k

/-- The RS per-edge failure proxy: the gain term (a dangerous edge survives, bounded by
`e^{-kp}`) plus a linear loss term `c·k·p` (recoloring creates new dangers). -/
noncomputable def tradeoff (c : ℝ) (k : ℕ) (p : ℝ) : ℝ := Real.exp (-(k * p)) + c * (k * p)

/-- A dangerous edge's survival probability is at most `1`. -/
theorem survivesOrig_le_one (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    survivesOrig p k ≤ 1 := by
  unfold survivesOrig
  apply pow_le_one₀ (by linarith) (by linarith)

/-- **Conditional recoloring strictly helps.** For every flip rate `p ∈ (0,1]` and edge size
`k ≥ 1`, the survival probability of a dangerous edge is *strictly* below the no-recoloring
baseline `1`. This is the quantitative POSITIVE counterpart to the product-model result
(`property-b-first-moment-oq-03-oq-03`), where the analogous factor is identically `1`. -/
theorem survivesOrig_lt_one (k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hk : k ≠ 0) :
    survivesOrig p k < 1 := by
  unfold survivesOrig
  exact pow_lt_one₀ (by linarith) (by linarith) hk

/-- At flip rate `p = 0` the edge surely survives — recoloring degenerates to the Erdős
baseline. -/
@[simp]
theorem survivesOrig_zero (k : ℕ) : survivesOrig 0 k = 1 := by
  unfold survivesOrig; simp

/-- **Strict first-moment improvement.** The expected number of surviving dangerous edges of
an `m`-edge `k`-uniform hypergraph under conditional recoloring, `m · monoOneStage k ·
survivesOrig p k`, is *strictly less* than the Erdős baseline `m · monoOneStage k`, for any
positive flip rate. So conditional recoloring beats the first moment — the loss term aside. -/
theorem expSurvivors_cond_lt_baseline (m k : ℕ) (p : ℝ)
    (hm : 0 < m) (hp0 : 0 < p) (hp1 : p ≤ 1) (hk : k ≠ 0) :
    (m : ℝ) * monoOneStage k * survivesOrig p k < (m : ℝ) * monoOneStage k := by
  have hbase : 0 < (m : ℝ) * monoOneStage k := by
    have : 0 < monoOneStage k := by unfold monoOneStage; positivity
    have : (0:ℝ) < m := by exact_mod_cast hm
    positivity
  have hlt := survivesOrig_lt_one k p hp0 hp1 hk
  calc (m : ℝ) * monoOneStage k * survivesOrig p k
      < (m : ℝ) * monoOneStage k * 1 := by
        exact mul_lt_mul_of_pos_left hlt hbase
    _ = (m : ℝ) * monoOneStage k := by ring

/-- **Linearising the gain.** The gain term `(1-p)^k` is bounded by `e^{-k p}`, via
`1 - p ≤ e^{-p}` raised to the `k`-th power. This converts the per-edge survival into the
exponential form used in the convex tradeoff below. -/
theorem survivesOrig_le_exp (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    survivesOrig p k ≤ Real.exp (-(k * p)) := by
  unfold survivesOrig
  have h1 : (1 - p) ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p); linarith
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  calc (1 - p) ^ k ≤ Real.exp (-p) ^ k := pow_le_pow_left₀ h0 h1 k
    _ = Real.exp ((k : ℝ) * (-p)) := (Real.exp_nat_mul (-p) k).symm
    _ = Real.exp (-((k : ℝ) * p)) := by rw [mul_neg]

/-- **The convex optimum (lower envelope).** For every flip rate `p`, the RS tradeoff proxy
`G(p) = e^{-kp} + c·k·p` is bounded below by the closed-form optimum value `c·(1 - log c)`.

This is the heart of the RS optimisation: minimising the gain/loss tradeoff over the flip
rate yields exactly `c·(1 - log c)`. The slick proof reduces, after the substitution
`s = kp + log c`, to the tangent-line inequality `1 - s ≤ e^{-s}` (`Real.add_one_le_exp`). -/
theorem tradeoff_ge_optimum (c : ℝ) (hc : 0 < c) (k : ℕ) (p : ℝ) :
    c - c * Real.log c ≤ tradeoff c k p := by
  unfold tradeoff
  set x : ℝ := (k : ℝ) * p with hx
  have hle := Real.add_one_le_exp (-(x + Real.log c))
  have hexp : Real.exp (-(x + Real.log c)) = Real.exp (-x) / c := by
    rw [show -(x + Real.log c) = -x - Real.log c by ring, Real.exp_sub, Real.exp_log hc]
  rw [hexp, le_div_iff₀ hc] at hle
  nlinarith [hle]

/-- **Tightness: the optimum is attained.** At the optimiser `p` for which `k·p = -log c`
(i.e. the RS flip rate `p* = -(log c)/k`), the tradeoff proxy *equals* its lower bound
`c·(1 - log c)`. Combined with `tradeoff_ge_optimum`, this shows `c·(1 - log c)` is exactly
`min_p G(p)`. -/
theorem tradeoff_eq_at_optimum (c : ℝ) (hc : 0 < c) (k : ℕ) (p : ℝ)
    (hopt : (k : ℝ) * p = -Real.log c) :
    tradeoff c k p = c - c * Real.log c := by
  unfold tradeoff
  rw [hopt, neg_neg, Real.exp_log hc]
  ring

/-- The optimiser is a *small* flip rate: `p* = -(log c)/k`. For `0 < c ≤ 1` and `k ≥ 1` it
satisfies `k·p* = -log c = log(1/c) ≥ 0`, the `log(1/c)/k` scaling behind the RS
`√(k/log k)` gain. Stated as the defining identity of the optimiser used above. -/
theorem optimum_flip_rate (c : ℝ) (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * (-Real.log c / k) = -Real.log c := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp

end ProbMethod.PropertyB.ConditionalOpt
