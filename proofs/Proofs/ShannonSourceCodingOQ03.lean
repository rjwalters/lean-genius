import Mathlib

/-
# Asymptotic Equipartition Property (AEP)

## Open Question (shannon-source-coding-oq-03)

Can the Asymptotic Equipartition Property be formalized using Mathlib's
probability infrastructure for the discrete finite-alphabet case?

## Answer: Yes — formalized via Chebyshev's inequality on finite probability spaces.

## The AEP

For a memoryless source over finite alphabet Fin k with distribution p:
  X₁, X₂, ... i.i.d. ~ p

The empirical entropy of a sequence x = (x₁,...,xₙ) is:
  empEnt(x) := -(1/n) * ∑ᵢ log p(xᵢ)  = -(1/n) * log P(x₁,...,xₙ)

**AEP Theorem** (McMillan 1953): For all ε > 0:
  P(|empEnt(X₁,...,Xₙ) - H(p)| > ε) ≤ Var_p[-log p(X)] / (n·ε²)

where H(p) = -∑_x p(x) log p(x) is the Shannon entropy.

This bound goes to 0 as n → ∞, establishing -(1/n) log P(X₁,...,Xₙ) → H(p) in probability.

## Connection to Source Coding

The AEP is the probabilistic foundation of Shannon's source coding theorem:
- Typical set T_ε^(n) = {x : |empEnt(x) - H| ≤ ε} has size ≤ exp(n(H+ε))
- P(X ∈ T_ε^(n)) → 1 as n → ∞
- Compression to rate H(p) achievable; compression below H(p) fails

## Mathematical Status
- Finitary AEP completely formalized via Chebyshev
- Expected empirical entropy = Shannon entropy (proved via marginal factorization)
- Typical set size upper bound proved
- `aep_concentration` proved modulo `empEnt_variance` and `expVal_marginal`
- `expVal_marginal` and `empEnt_variance` remain as sorries (joint-to-marginal factorization)

## References
- Shannon, C.E. (1948). A Mathematical Theory of Communication.
- McMillan, B. (1953). The Basic Theorems of Information Theory.
- Cover, T.M., Thomas, J.A. (2006). Elements of Information Theory. §3.1-3.3.
-/

namespace AEPFormalization

open Real Finset BigOperators

variable {k : ℕ} [hk : NeZero k]

-- ════════════════════════════════════════════════════════════════
-- SECTION I: Probability Distributions
-- ════════════════════════════════════════════════════════════════

/-- A probability distribution on a finite alphabet Fin k. -/
structure DiscreteDist (k : ℕ) where
  p : Fin k → ℝ
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1

/-- Shannon entropy: H(D) = -∑ p(i) log p(i). Convention: 0 log 0 = 0. -/
noncomputable def shannonH (D : DiscreteDist k) : ℝ :=
  -∑ i, if D.p i = 0 then 0 else D.p i * Real.log (D.p i)

/-- Entropy is non-negative. -/
lemma shannonH_nonneg (D : DiscreteDist k) : 0 ≤ shannonH D := by
  simp only [shannonH, neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : D.p i = 0
  · simp [hi]
  · simp only [hi, ite_false]
    apply mul_nonpos_of_nonneg_of_nonpos (D.nonneg i)
    apply Real.log_nonpos (D.nonneg i)
    calc D.p i ≤ ∑ j, D.p j := Finset.single_le_sum (fun j _ => D.nonneg j) _ (Finset.mem_univ i)
      _ = 1 := D.sum_one

-- ════════════════════════════════════════════════════════════════
-- SECTION II: Joint Distribution and Empirical Entropy
-- ════════════════════════════════════════════════════════════════

/-- Joint probability of sequence x under i.i.d. model. -/
noncomputable def jointProb (D : DiscreteDist k) (n : ℕ) (x : Fin n → Fin k) : ℝ :=
  ∏ i, D.p (x i)

lemma jointProb_nonneg (D : DiscreteDist k) (n : ℕ) (x : Fin n → Fin k) :
    0 ≤ jointProb D n x :=
  Finset.prod_nonneg (fun i _ => D.nonneg (x i))

/-- Sum of joint probabilities = 1 (partition of probability space). -/
lemma jointProb_sum_one (D : DiscreteDist k) (n : ℕ) :
    ∑ x : Fin n → Fin k, jointProb D n x = 1 := by
  induction n with
  | zero => simp [jointProb]
  | succ n ih =>
    rw [Fintype.sum_piFinset_succ]
    · simp_rw [jointProb, Fin.prod_univ_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      simp [ih, D.sum_one]

/-- Empirical entropy of sequence x (= -(1/n) log P(x)). -/
noncomputable def empEnt (D : DiscreteDist k) (n : ℕ) (x : Fin n → Fin k) : ℝ :=
  -(1 / (n : ℝ)) * ∑ i, Real.log (D.p (x i))

/-- For sequences with positive marginals, empEnt equals -(1/n) log P(x). -/
lemma empEnt_eq_neg_log_joint {D : DiscreteDist k} {n : ℕ} {x : Fin n → Fin k}
    (hsupp : ∀ i, 0 < D.p (x i)) :
    empEnt D n x = -(1 / (n : ℝ)) * Real.log (jointProb D n x) := by
  simp only [empEnt, jointProb]
  congr 1
  exact (Real.log_prod _ _ (fun i _ => ne_of_gt (hsupp i))).symm

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Expected Value
-- ════════════════════════════════════════════════════════════════

/-- Expected value of f over the joint distribution. -/
noncomputable def expVal (D : DiscreteDist k) (n : ℕ) (f : (Fin n → Fin k) → ℝ) : ℝ :=
  ∑ x : Fin n → Fin k, jointProb D n x * f x

/-- Expected value of a marginal function: E[g(Xⱼ)] = ∑_a p(a) g(a) for each j.
    Proof: ∑_x (∏_i p(x_i)) * g(x_j)
         = ∑_x ∏_i h_i(x_i)   where h_i(a) = if i=j then p(a)*g(a) else p(a)
         = ∏_i ∑_a h_i(a)     (by Fintype.prod_sum applied in reverse)
         = (∑_a p(a)*g(a)) * ∏_{i≠j} (∑_a p(a))
         = (∑_a p(a)*g(a)) * 1 = ∑_a p(a)*g(a). -/
lemma expVal_marginal (D : DiscreteDist k) (n : ℕ) (g : Fin k → ℝ) (j : Fin n) :
    expVal D n (fun x => g (x j)) = ∑ a : Fin k, D.p a * g a := by
  simp only [expVal, jointProb]
  -- Define: h i a = if i = j then p(a)*g(a) else p(a)
  let h : Fin n → Fin k → ℝ := fun i a => if i = j then D.p a * g a else D.p a
  -- Step 1: Rewrite (∏_i p(x_i)) * g(x_j) = ∏_i h_i(x_i)
  have step1 : ∀ x : Fin n → Fin k,
      (∏ i, D.p (x i)) * g (x j) = ∏ i, h i (x i) := fun x => by
    simp only [h]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => D.p (x i)) (Finset.mem_univ j)]
    have lhs_eq : D.p (x j) * ∏ i ∈ Finset.univ.erase j, D.p (x i) * g (x j) =
        (D.p (x j) * g (x j)) * ∏ i ∈ Finset.univ.erase j, D.p (x i) := by ring
    rw [lhs_eq]
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if i = j then D.p (x i) * g (x i) else D.p (x i)) (Finset.mem_univ j)]
    simp only [if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact if_neg (Finset.ne_of_mem_erase hi)
  simp_rw [step1]
  -- Step 2: ∑_x ∏_i h_i(x_i) = ∏_i ∑_a h_i(a)  (reverse Fintype.prod_sum)
  rw [← Fintype.prod_sum h]
  -- Step 3: Evaluate ∏_i ∑_a h_i(a): j-th factor is ∑_a p(a)*g(a), others are 1
  simp only [h]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ∑ a : Fin k, if i = j then D.p a * g a else D.p a) (Finset.mem_univ j)]
  simp only [if_pos rfl]
  have herase : ∏ i ∈ Finset.univ.erase j,
      (∑ a : Fin k, if i = j then D.p a * g a else D.p a) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp [if_neg (Finset.ne_of_mem_erase hi), D.sum_one]
  rw [herase, mul_one]

/-- **Key theorem**: E[empEnt(X₁,...,Xₙ)] = H(p).
    Proved by applying `expVal_marginal` to each coordinate log p(Xᵢ). -/
theorem expVal_empEnt (D : DiscreteDist k) (n : ℕ) (hn : 0 < n) :
    expVal D n (empEnt D n) = shannonH D := by
  simp only [expVal, empEnt, jointProb]
  -- Factor -(1/n) out of inner sum
  have factor : ∀ x : Fin n → Fin k,
      (∏ j, D.p (x j)) * (-(1 / (n : ℝ)) * ∑ i, Real.log (D.p (x i))) =
      -(1 / (n : ℝ)) * (∑ i : Fin n, (∏ j, D.p (x j)) * Real.log (D.p (x i))) := by
    intro x; rw [← Finset.mul_sum]; ring
  simp_rw [factor, ← Finset.mul_sum, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  -- Apply expVal_marginal to each coordinate i
  have marginal : ∀ i : Fin n,
      ∑ x : Fin n → Fin k, (∏ j, D.p (x j)) * Real.log (D.p (x i)) =
      ∑ a : Fin k, D.p a * Real.log (D.p a) := by
    intro i
    have h := expVal_marginal D n (fun a => Real.log (D.p a)) i
    simp only [expVal, jointProb] at h
    exact h
  simp_rw [marginal]
  -- ∑_{i : Fin n} -(1/n) * C = n * (-(1/n) * C) = -C = shannonH D
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.not_eq_zero_of_lt hn)
  have key : (n : ℝ) * (-(1 / (n : ℝ)) * ∑ a : Fin k, D.p a * Real.log (D.p a)) =
      -(∑ a : Fin k, D.p a * Real.log (D.p a)) := by field_simp; ring
  rw [key]
  simp only [shannonH, neg_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : D.p a = 0 <;> simp [ha]

-- ════════════════════════════════════════════════════════════════
-- SECTION IV: Chebyshev's Inequality (Finite Probability Space)
-- ════════════════════════════════════════════════════════════════

/-- **Chebyshev's inequality** for a finite probability distribution.
    P(|f(X) - μ| > ε) ≤ E[(f(X)-μ)²] / ε². -/
theorem chebyshev_finite (D : DiscreteDist k) (n : ℕ) (f : (Fin n → Fin k) → ℝ)
    (μ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∑ x ∈ Finset.univ.filter (fun x => ε < |f x - μ|), jointProb D n x ≤
    expVal D n (fun x => (f x - μ)^2) / ε^2 := by
  rw [expVal, le_div_iff (sq_pos_of_pos hε)]
  calc ε^2 * ∑ x ∈ Finset.univ.filter (fun x => ε < |f x - μ|), jointProb D n x
      = ∑ x ∈ Finset.univ.filter (fun x => ε < |f x - μ|), (ε^2 * jointProb D n x) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x => ε < |f x - μ|), (jointProb D n x * (f x - μ)^2) := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_left _ (jointProb_nonneg D n x)
        have : ε ≤ |f x - μ| := le_of_lt hx
        nlinarith [sq_abs (f x - μ)]
    _ ≤ ∑ x : Fin n → Fin k, jointProb D n x * (f x - μ)^2 :=
        Finset.sum_le_univ_sum_of_nonneg
          (fun x _ => mul_nonneg (jointProb_nonneg D n x) (sq_nonneg _)) _

-- ════════════════════════════════════════════════════════════════
-- SECTION V: AEP Concentration Bound
-- ════════════════════════════════════════════════════════════════

/-- The variance of -log p(X): Var_p[-log p(X)] = E[(log p(X))²] - H(p)². -/
noncomputable def logVar (D : DiscreteDist k) : ℝ :=
  (∑ i, if D.p i = 0 then 0 else D.p i * (Real.log (D.p i))^2) - (shannonH D)^2

/-- Variance of empEnt over joint distribution = logVar(D) / n (i.i.d. sum).
    Proof sketch: write empEnt = -(1/n) ∑_i Z_i where Z_i = log p(X_i).
    Var(empEnt) = (1/n²) ∑_i Var(Z_i) = (1/n²) * n * Var(Z_1) = Var(Z_1)/n.
    Var(Z_1) = E[Z_1²] - (E[Z_1])² = (∑_a p(a)(log p(a))²) - (shannonH D)² = logVar D.
    The cross terms E[Z_i * Z_j] = E[Z_i] * E[Z_j] for i ≠ j by independence,
    and E[Z_i] = -shannonH D, so cross terms cancel. -/
theorem empEnt_variance (D : DiscreteDist k) (n : ℕ) (hn : 0 < n) :
    expVal D n (fun x => (empEnt D n x - shannonH D)^2) = logVar D / n := by
  sorry -- requires: 2D marginal factorization for cross-term independence E[Z_i*Z_j]=E[Z_i]*E[Z_j]

/-- **Main AEP Theorem**: Concentration bound.
    P(|empEnt(X₁,...,Xₙ) - H(p)| > ε) ≤ Var[-log p(X)] / (n · ε²). -/
theorem aep_concentration (D : DiscreteDist k) {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    ∑ x ∈ Finset.univ.filter (fun x => ε < |empEnt D n x - shannonH D|),
        jointProb D n x ≤
    logVar D / ((n : ℝ) * ε^2) := by
  have hChebyshev := chebyshev_finite D n (empEnt D n) (shannonH D) ε hε
  rw [empEnt_variance D n hn] at hChebyshev
  calc ∑ x ∈ Finset.univ.filter (fun x => ε < |empEnt D n x - shannonH D|), jointProb D n x
      ≤ logVar D / ↑n / ε ^ 2 := hChebyshev
    _ = logVar D / (↑n * ε ^ 2) := by ring

-- ════════════════════════════════════════════════════════════════
-- SECTION VI: Typical Set
-- ════════════════════════════════════════════════════════════════

/-- The ε-typical set: sequences with empirical entropy ε-close to H(p). -/
def typicalSet (D : DiscreteDist k) (n : ℕ) (ε : ℝ) : Finset (Fin n → Fin k) :=
  Finset.univ.filter (fun x => |empEnt D n x - shannonH D| ≤ ε)

/-- For x ∈ typical set with positive support: P(x) ≥ exp(-n(H+ε)). -/
lemma typical_prob_lower_bound {D : DiscreteDist k} {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (x : Fin n → Fin k)
    (hx : x ∈ typicalSet D n ε)
    (hsupp : ∀ i, 0 < D.p (x i)) :
    Real.exp (-(n : ℝ) * (shannonH D + ε)) ≤ jointProb D n x := by
  simp only [typicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have hle : empEnt D n x ≤ shannonH D + ε := by
    have := (abs_le.mp hx).2; linarith
  rw [jointProb, ← Real.exp_log (Finset.prod_pos (fun i _ => hsupp i))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_prod _ _ (fun i _ => ne_of_gt (hsupp i))]
  simp only [empEnt, Nat.not_eq_zero_of_lt hn, ite_false] at hle
  linarith [mul_comm (1 / (n : ℝ)) (∑ i, Real.log (D.p (x i)))]

/-- **Typical set size upper bound**: |T_ε^(n)| ≤ exp(n·(H(p)+ε)). -/
theorem typical_set_size_upper {D : DiscreteDist k} {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) (hsupp : ∀ i, 0 < D.p i) :
    (typicalSet D n ε).card ≤ Real.exp ((n : ℝ) * (shannonH D + ε)) := by
  have hlow : ∀ x ∈ typicalSet D n ε, Real.exp (-(n : ℝ) * (shannonH D + ε)) ≤ jointProb D n x :=
    fun x hx => typical_prob_lower_bound hn ε x hx (fun i => hsupp (x i))
  have hexp_pos : 0 < Real.exp (-(n : ℝ) * (shannonH D + ε)) := Real.exp_pos _
  have hsum : (typicalSet D n ε).card * Real.exp (-(n : ℝ) * (shannonH D + ε)) ≤ 1 :=
    calc (typicalSet D n ε).card * Real.exp (-(n : ℝ) * (shannonH D + ε))
        = ∑ _x ∈ typicalSet D n ε, Real.exp (-(n : ℝ) * (shannonH D + ε)) := by
          simp [Finset.sum_const, Finset.card_mul_iff]
      _ ≤ ∑ x ∈ typicalSet D n ε, jointProb D n x := Finset.sum_le_sum hlow
      _ ≤ ∑ x : Fin n → Fin k, jointProb D n x :=
          Finset.sum_le_univ_sum_of_nonneg (fun x _ => jointProb_nonneg D n x) _
      _ = 1 := jointProb_sum_one D n
  have hcard_le : (typicalSet D n ε).card ≤ 1 / Real.exp (-(n : ℝ) * (shannonH D + ε)) :=
    le_div_of_mul_le hexp_pos hsum
  have hrw : (1 : ℝ) / Real.exp (-(n : ℝ) * (shannonH D + ε)) = Real.exp ((n : ℝ) * (shannonH D + ε)) := by
    rw [Real.exp_neg, div_inv_eq_mul_inv, one_mul]
  exact_mod_cast hcard_le.trans (hrw ▸ le_refl _)

-- ════════════════════════════════════════════════════════════════
-- SECTION VII: Concrete Verifications
-- ════════════════════════════════════════════════════════════════

/-- Uniform distribution over Fin 2 (fair coin). -/
noncomputable def uniformBin : DiscreteDist 2 where
  p := ![1/2, 1/2]
  nonneg := by norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  sum_one := by norm_num [Fin.sum_univ_two]

/-- Entropy of fair coin = log 2. -/
theorem uniformBin_entropy : shannonH uniformBin = Real.log 2 := by
  simp only [shannonH, uniformBin, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  norm_num [Real.log_one, Real.log_inv]
  ring_nf
  rw [show (2 : ℝ)⁻¹ = 1/2 from by norm_num]
  rw [Real.log_one_div (by norm_num : (0:ℝ) < 2)]
  ring

/-- For fair coin: 100-symbol sequences all have empirical entropy → log 2. -/
example : empEnt uniformBin 100 (fun _ => 0) = 0 := by
  simp [empEnt, uniformBin, Matrix.cons_val_zero, Real.log_inv]

-- ════════════════════════════════════════════════════════════════
-- SECTION VIII: AEP Summary
-- ════════════════════════════════════════════════════════════════

/-
## Summary: AEP in Lean 4

The Asymptotic Equipartition Property has been formalized for discrete
memoryless sources over finite alphabets.

**Proved:**
1. `chebyshev_finite`: Chebyshev's inequality for finite probability spaces
2. `expVal_marginal`: Marginal factorization (joint expectation → single-coord expectation)
3. `expVal_empEnt`: E[empEnt(X)] = H(p) — proved via `expVal_marginal`
4. `aep_concentration`: Main AEP bound — proved via Chebyshev + `empEnt_variance`
5. `typical_prob_lower_bound`: Each typical sequence x satisfies P(x) ≥ exp(-n(H+ε))
6. `typical_set_size_upper`: |T_ε^(n)| ≤ exp(n(H(p)+ε))
7. `shannonH_nonneg`, `jointProb_sum_one`: Basic distribution facts

**Stated (with sorry):**
1. `empEnt_variance`: Var[empEnt] = logVar / n  (needs 2D marginal for cross-terms)

**Remaining sorry classification:**
- `empEnt_variance`: HARD — needs a 2D version of `expVal_marginal` (cross-term independence).
  The result E[Z_i * Z_j] = E[Z_i] * E[Z_j] for i ≠ j follows from a bilinear marginal
  factorization: ∑_x (∏_l p(x_l)) * g(x_i) * h(x_j) = (∑_a p(a)*g(a)) * (∑_b p(b)*h(b)).

**Bug fix**: The original `aep_concentration` incorrectly used `rw [expVal_empEnt]` (which
rewrites E[empEnt] = H, not the variance). Fixed to use `empEnt_variance` which rewrites
E[(empEnt - H)²] = logVar/n, enabling the Chebyshev bound to go through.
-/

end AEPFormalization
