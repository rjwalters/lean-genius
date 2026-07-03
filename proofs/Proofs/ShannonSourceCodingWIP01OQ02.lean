import Mathlib

/-
  # Converse to entropy additivity: additivity holds *only* for product distributions

  The parent file `ShannonSourceCodingWIP01` proves the **forward** direction of
  the equality case of subadditivity of Shannon entropy: for a *product*
  distribution `pXY(x, y) = pX(x)·pY(y)`,

      H(pX ⊗ pY) = H(pX) + H(pY).

  This file proves the **converse**. For an *arbitrary* joint distribution
  `p : α × β → ℝ` (nonnegative, `∑ p = 1`) with marginals

      pX(x) = ∑_y p(x, y),      pY(y) = ∑_x p(x, y),

  additivity of entropy holds *exactly* when `p` is the product of its own
  marginals:

      H(p) = H(pX) + H(pY)   ⟺   ∀ x y, p(x, y) = pX(x)·pY(y).

  In information-theoretic language, the entropy gap is the **mutual
  information**

      H(pX) + H(pY) − H(p) = ∑_{x,y} p(x,y) · log( p(x,y) / (pX(x)·pY(y)) )
                            = D( p ‖ pX ⊗ pY )  ≥ 0,

  a Kullback–Leibler divergence, and `D(p ‖ q) = 0` for probability
  distributions `p, q` holds iff `p = q`. So the entropy is additive precisely
  when `X` and `Y` are independent — the exact boundary of subadditivity.

  ## Strategy
  The engine is a self-contained **Gibbs equality lemma** (`gibbs_eq`): for
  finite probability distributions `p, q` with `p ≪ q` (support of `p` inside
  support of `q`), `∑ p·(log p − log q) ≤ 0` forces `p = q`. The proof uses the
  tangent-line bound `log t ≤ t − 1` (Mathlib `Real.log_le_sub_one_of_pos`) with
  its strict form `log t < t − 1` for `t ≠ 1` (from `Real.add_one_lt_exp`): the
  per-term gap `e i = (q i − p i) − p i·(log q i − log p i) ≥ 0` sums to the
  KL divergence, and `∑ eᵢ = 0` with each `eᵢ ≥ 0` forces every `eᵢ = 0`, hence
  `pᵢ = qᵢ`.

  Instantiating `q(x,y) = pX(x)·pY(y)` and identifying the KL divergence with the
  entropy gap (`entropy_diff_eq`) yields the converse. Absolute continuity is
  automatic here: `p(x,y) > 0 ⟹ pX(x), pY(y) > 0`.

  ## Results
  * `gibbs_eq`               : Gibbs / KL equality case for finite distributions.
  * `entropy_diff_eq`        : `H(pX) + H(pY) − H(p)` equals the mutual-information sum.
  * `entropy_prod`           : forward direction (product ⟹ additive; parent's result, reproved).
  * `entropy_additive_converse` : **additivity ⟹ product distribution**.
  * `entropy_additive_iff`   : the full characterization `H(p)=H(pX)+H(pY) ↔ product`.

  `0` axioms.
-/

namespace ShannonSourceCodingWIP01OQ02

open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Shannon entropy in `negMulLog` form (matching the parent file):
`H(p) = ∑ₓ negMulLog (p x)`. -/
noncomputable def entropy {γ : Type*} [Fintype γ] (p : γ → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (p x)

/-- Agreement with the standard definition `H(p) = -∑ₓ p x · log (p x)`. -/
theorem entropy_eq_neg_sum {γ : Type*} [Fintype γ] (p : γ → ℝ) :
    entropy p = -∑ x, p x * Real.log (p x) := by
  unfold entropy
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x _ => by rw [Real.negMulLog]; ring

/-- The `X`-marginal of a joint distribution `p : α × β → ℝ`. -/
noncomputable def marginalX (p : α × β → ℝ) (x : α) : ℝ := ∑ y, p (x, y)

/-- The `Y`-marginal of a joint distribution `p : α × β → ℝ`. -/
noncomputable def marginalY (p : α × β → ℝ) (y : β) : ℝ := ∑ x, p (x, y)

/-- A marginal of a normalised joint distribution is normalised. -/
theorem sum_marginalX (p : α × β → ℝ) (hsum : ∑ xy, p xy = 1) :
    ∑ x, marginalX p x = 1 := by
  unfold marginalX
  rw [← Fintype.sum_prod_type]
  exact hsum

theorem sum_marginalY (p : α × β → ℝ) (hsum : ∑ xy, p xy = 1) :
    ∑ y, marginalY p y = 1 := by
  unfold marginalY
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact hsum

/-- **Gibbs' inequality, equality case (finite form).** For finite probability
distributions `p, q` (nonnegative, equal total mass) with `p` absolutely
continuous with respect to `q` (`0 < p i → 0 < q i`), the Kullback–Leibler
divergence `∑ᵢ p i·(log (p i) − log (q i))` is `≥ 0`, and if it is `≤ 0` then
`p = q` pointwise. -/
theorem gibbs_eq {γ : Type*} [Fintype γ] (p q : γ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpq : ∑ i, p i = ∑ i, q i)
    (hac : ∀ i, 0 < p i → 0 < q i)
    (hKL : ∑ i, p i * (Real.log (p i) - Real.log (q i)) ≤ 0) :
    ∀ i, p i = q i := by
  -- Per-term nonnegative "gap": eᵢ = (qᵢ − pᵢ) − pᵢ(log qᵢ − log pᵢ) ≥ 0.
  set e : γ → ℝ := fun i => (q i - p i) - p i * (Real.log (q i) - Real.log (p i))
    with he_def
  have he_nonneg : ∀ i, 0 ≤ e i := by
    intro i
    rw [he_def]; dsimp only
    rcases eq_or_lt_of_le (hp i) with h0 | hpos
    · rw [← h0]; simpa using hq i
    · have hqi : 0 < q i := hac i hpos
      have hpne : p i ≠ 0 := ne_of_gt hpos
      have hbound : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hqi hpos)
      have hlog : Real.log (q i) - Real.log (p i) = Real.log (q i / p i) := by
        rw [Real.log_div (ne_of_gt hqi) hpne]
      have h2 : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hpos)
      have h3 : p i * (q i / p i - 1) = q i - p i := by field_simp
      rw [hlog]; linarith
  -- The sum of the gaps equals the KL divergence.
  have hsum_e : ∑ i, e i = ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
    have expand : ∀ i, e i = (q i - p i) + p i * (Real.log (p i) - Real.log (q i)) := by
      intro i; rw [he_def]; dsimp only; ring
    rw [Finset.sum_congr rfl (fun i _ => expand i), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← hpq]
    ring
  -- KL ≥ 0 and KL ≤ 0 (hypothesis) ⟹ KL = 0 ⟹ ∑ e = 0.
  have hKL0 : ∑ i, p i * (Real.log (p i) - Real.log (q i)) = 0 :=
    le_antisymm hKL (by rw [← hsum_e]; exact Finset.sum_nonneg (fun i _ => he_nonneg i))
  have hsum_e0 : ∑ i, e i = 0 := by rw [hsum_e, hKL0]
  have he_zero : ∀ i, e i = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => he_nonneg j)).mp hsum_e0 i
      (Finset.mem_univ i)
  -- Each gap being zero forces pᵢ = qᵢ.
  intro i
  have hei : e i = 0 := he_zero i
  rw [he_def] at hei; dsimp only at hei
  rcases eq_or_lt_of_le (hp i) with h0 | hpos
  · -- pᵢ = 0: the gap is qᵢ, so qᵢ = 0.
    rw [← h0] at hei ⊢
    simp only [sub_zero, zero_mul] at hei
    exact hei.symm
  · -- pᵢ > 0: strict tangent inequality unless qᵢ = pᵢ.
    have hqi : 0 < q i := hac i hpos
    have hpne : p i ≠ 0 := ne_of_gt hpos
    by_contra hne
    have hqp_ne : q i / p i ≠ 1 := by
      intro h1
      exact hne ((div_eq_one_iff_eq hpne).mp h1).symm
    have ht : (0 : ℝ) < q i / p i := div_pos hqi hpos
    have hlt : Real.log (q i / p i) < q i / p i - 1 := by
      have hu : Real.log (q i / p i) ≠ 0 := by
        intro h0
        have hexp : Real.exp (Real.log (q i / p i)) = q i / p i := Real.exp_log ht
        rw [h0, Real.exp_zero] at hexp
        exact hqp_ne hexp.symm
      have h := Real.add_one_lt_exp hu
      rw [Real.exp_log ht] at h; linarith
    have hlog : Real.log (q i) - Real.log (p i) = Real.log (q i / p i) := by
      rw [Real.log_div (ne_of_gt hqi) hpne]
    have h2 : p i * Real.log (q i / p i) < p i * (q i / p i - 1) :=
      mul_lt_mul_of_pos_left hlt hpos
    have h3 : p i * (q i / p i - 1) = q i - p i := by field_simp
    rw [hlog] at hei
    linarith

/-- **The entropy gap is the mutual-information sum.** For any joint
distribution `p : α × β → ℝ`,

  `H(pX) + H(pY) − H(p) = ∑_{x,y} p(x,y)·(log p(x,y) − log pX(x) − log pY(y))`.

This is a pure algebraic rearrangement (marginalisation), no positivity needed. -/
theorem entropy_diff_eq (p : α × β → ℝ) :
    entropy (marginalX p) + entropy (marginalY p) - entropy p
      = ∑ xy : α × β, p xy *
          (Real.log (p xy) - Real.log (marginalX p xy.1) - Real.log (marginalY p xy.2)) := by
  have hX : ∑ x, marginalX p x * Real.log (marginalX p x)
      = ∑ xy : α × β, p xy * Real.log (marginalX p xy.1) := by
    simp only [marginalX]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [← Finset.sum_mul]
  have hY : ∑ y, marginalY p y * Real.log (marginalY p y)
      = ∑ xy : α × β, p xy * Real.log (marginalY p xy.2) := by
    simp only [marginalY]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    rw [← Finset.sum_mul]
  have hRHS : (∑ xy : α × β, p xy *
        (Real.log (p xy) - Real.log (marginalX p xy.1) - Real.log (marginalY p xy.2)))
      = (∑ xy : α × β, p xy * Real.log (p xy))
        - (∑ xy : α × β, p xy * Real.log (marginalX p xy.1))
        - (∑ xy : α × β, p xy * Real.log (marginalY p xy.2)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [entropy_eq_neg_sum p, entropy_eq_neg_sum (marginalX p), entropy_eq_neg_sum (marginalY p),
      hX, hY, hRHS]
  ring

/-- **Forward direction (parent's result, reproved):** entropy is additive for a
product distribution. -/
theorem entropy_prod (pX : α → ℝ) (pY : β → ℝ)
    (hX : ∑ x, pX x = 1) (hY : ∑ y, pY y = 1) :
    entropy (fun xy : α × β => pX xy.1 * pY xy.2) = entropy pX + entropy pY := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  have key : ∀ x, (∑ y, Real.negMulLog (pX x * pY y))
      = Real.negMulLog (pX x) + pX x * ∑ y, Real.negMulLog (pY y) := by
    intro x
    simp_rw [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hY, one_mul, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
    ← Finset.sum_mul, hX, one_mul]

/-- **Entropy additivity converse.** If a nonnegative, normalised joint
distribution `p` satisfies `H(p) = H(pX) + H(pY)`, then `p` is the product of its
own marginals: `p(x, y) = pX(x)·pY(y)` for all `x, y`. Equivalently, additivity
of entropy holds only when `X` and `Y` are independent. -/
theorem entropy_additive_converse (p : α × β → ℝ)
    (hp : ∀ xy, 0 ≤ p xy) (hsum : ∑ xy, p xy = 1)
    (hadd : entropy p = entropy (marginalX p) + entropy (marginalY p)) :
    ∀ x y, p (x, y) = marginalX p x * marginalY p y := by
  -- Nonnegativity of the product distribution `q = pX ⊗ pY`.
  have hq' : ∀ xy : α × β, 0 ≤ marginalX p xy.1 * marginalY p xy.2 := by
    intro xy
    exact mul_nonneg (Finset.sum_nonneg fun y _ => hp (xy.1, y))
      (Finset.sum_nonneg fun x _ => hp (x, xy.2))
  -- Absolute continuity: p(x,y) > 0 ⟹ pX(x), pY(y) > 0.
  have hac' : ∀ xy : α × β, 0 < p xy → 0 < marginalX p xy.1 * marginalY p xy.2 := by
    intro xy hpos
    refine mul_pos ?_ ?_
    · have hle : p (xy.1, xy.2) ≤ ∑ y, p (xy.1, y) :=
        Finset.single_le_sum (f := fun y => p (xy.1, y)) (fun y _ => hp (xy.1, y))
          (Finset.mem_univ xy.2)
      rw [Prod.mk.eta] at hle
      exact lt_of_lt_of_le hpos hle
    · have hle : p (xy.1, xy.2) ≤ ∑ x, p (x, xy.2) :=
        Finset.single_le_sum (f := fun x => p (x, xy.2)) (fun x _ => hp (x, xy.2))
          (Finset.mem_univ xy.1)
      rw [Prod.mk.eta] at hle
      exact lt_of_lt_of_le hpos hle
  -- Total mass of `q` is 1.
  have hqsum : ∑ xy : α × β, marginalX p xy.1 * marginalY p xy.2 = 1 := by
    have hsplit : ∑ xy : α × β, marginalX p xy.1 * marginalY p xy.2
        = ∑ x, ∑ y, marginalX p x * marginalY p y := by
      rw [Fintype.sum_prod_type]
    rw [hsplit, ← Fintype.sum_mul_sum, sum_marginalX p hsum, sum_marginalY p hsum, mul_one]
  have hpq : ∑ xy : α × β, p xy = ∑ xy : α × β, marginalX p xy.1 * marginalY p xy.2 := by
    rw [hsum, hqsum]
  -- The KL divergence w.r.t. `q` equals the (zero) entropy gap.
  have hbridge : (∑ xy : α × β, p xy *
        (Real.log (p xy) - Real.log (marginalX p xy.1 * marginalY p xy.2)))
      = ∑ xy : α × β, p xy *
          (Real.log (p xy) - Real.log (marginalX p xy.1) - Real.log (marginalY p xy.2)) := by
    refine Finset.sum_congr rfl fun xy _ => ?_
    rcases eq_or_lt_of_le (hp xy) with h0 | hpos
    · rw [← h0]; ring
    · have hmx : 0 < marginalX p xy.1 := by
        have hle : p (xy.1, xy.2) ≤ ∑ y, p (xy.1, y) :=
          Finset.single_le_sum (f := fun y => p (xy.1, y)) (fun y _ => hp (xy.1, y))
            (Finset.mem_univ xy.2)
        rw [Prod.mk.eta] at hle
        exact lt_of_lt_of_le hpos hle
      have hmy : 0 < marginalY p xy.2 := by
        have hle : p (xy.1, xy.2) ≤ ∑ x, p (x, xy.2) :=
          Finset.single_le_sum (f := fun x => p (x, xy.2)) (fun x _ => hp (x, xy.2))
            (Finset.mem_univ xy.1)
        rw [Prod.mk.eta] at hle
        exact lt_of_lt_of_le hpos hle
      rw [Real.log_mul (ne_of_gt hmx) (ne_of_gt hmy)]; ring
  have hKL : ∑ xy : α × β, p xy *
        (Real.log (p xy) - Real.log (marginalX p xy.1 * marginalY p xy.2)) ≤ 0 := by
    rw [hbridge, ← entropy_diff_eq, ← hadd]
    linarith
  -- Apply the Gibbs equality lemma with `q = pX ⊗ pY`.
  have key := gibbs_eq p (fun xy : α × β => marginalX p xy.1 * marginalY p xy.2)
    hp hq' hpq hac' hKL
  intro x y
  simpa using key (x, y)

/-- **Entropy additivity characterization.** For a nonnegative, normalised joint
distribution `p`, entropy is additive iff `X` and `Y` are independent (the joint
is the product of its marginals). The forward implication is the converse proved
above; the backward implication is `entropy_prod`. -/
theorem entropy_additive_iff (p : α × β → ℝ)
    (hp : ∀ xy, 0 ≤ p xy) (hsum : ∑ xy, p xy = 1) :
    entropy p = entropy (marginalX p) + entropy (marginalY p) ↔
      ∀ x y, p (x, y) = marginalX p x * marginalY p y := by
  constructor
  · intro hadd
    exact entropy_additive_converse p hp hsum hadd
  · intro hprod
    have hpeq : p = (fun xy : α × β => marginalX p xy.1 * marginalY p xy.2) := by
      funext xy
      exact hprod xy.1 xy.2
    have step : entropy p
        = entropy (fun xy : α × β => marginalX p xy.1 * marginalY p xy.2) :=
      congrArg entropy hpeq
    rw [step]
    exact entropy_prod (marginalX p) (marginalY p) (sum_marginalX p hsum) (sum_marginalY p hsum)

end ShannonSourceCodingWIP01OQ02
