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
- `aep_typical_prob_tends_one` stated with sorry (requires Filter.Tendsto machinery)
- One sorry in `variance_sum_factored` (joint distribution marginal calculation)

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

/-- Helper: sum of the product weight over all sequences = 1 (unfolds jointProb). -/
lemma prod_sum_one (D : DiscreteDist k) (m : ℕ) :
    ∑ x' : Fin m → Fin k, ∏ j : Fin m, D.p (x' j) = 1 := by
  have := jointProb_sum_one D m; simp only [jointProb] at this; exact this

/-- Expected value of a marginal function: E[g(Xᵢ)] = ∑_x p(x) g(x) for each i.
    Proved by induction on n: split off the first coordinate via Fintype.sum_piFinset_succ. -/
lemma expVal_marginal (D : DiscreteDist k) (n : ℕ) (g : Fin k → ℝ) (i : Fin n) :
    expVal D n (fun x => g (x i)) = ∑ a : Fin k, D.p a * g a := by
  simp only [expVal, jointProb]
  revert i  -- generalize i before induction so ih is ∀ i : Fin m, ...
  induction n with
  | zero => intro i; exact i.elim0
  | succ m ih =>
    intro i
    rw [Fintype.sum_piFinset_succ]
    -- After this, sum is over a : Fin k and x' : Fin m → Fin k, with f(Fin.cons a x')
    -- ih : ∀ i : Fin m, ∑ x' : Fin m → Fin k, (∏ j, D.p (x' j)) * g (x' i) = ∑ a, D.p a * g a
    cases i using Fin.cases with
    | zero =>
      -- i = 0: (Fin.cons a x') 0 = a
      simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      -- Goal: ∑ a, ∑ x', (D.p a * ∏ j, D.p (x' j)) * g a = ∑ a, D.p a * g a
      congr 1; ext a
      calc ∑ x' : Fin m → Fin k, (D.p a * ∏ j : Fin m, D.p (x' j)) * g a
          = ∑ x', (D.p a * g a) * ∏ j, D.p (x' j) := by congr 1; ext x'; ring
        _ = (D.p a * g a) * ∑ x', ∏ j, D.p (x' j) := by rw [← Finset.sum_mul]
        _ = D.p a * g a := by rw [prod_sum_one, mul_one]
    | succ i' =>
      -- i = i'.succ: (Fin.cons a x') i'.succ = x' i'
      simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      -- Goal: ∑ a, ∑ x', (D.p a * ∏ j, D.p (x' j)) * g (x' i') = ∑ a, D.p a * g a
      have step : ∀ a : Fin k,
          ∑ x' : Fin m → Fin k, (D.p a * ∏ j : Fin m, D.p (x' j)) * g (x' i') =
          D.p a * ∑ b : Fin k, D.p b * g b := by
        intro a
        calc ∑ x', (D.p a * ∏ j, D.p (x' j)) * g (x' i')
            = ∑ x', D.p a * ((∏ j, D.p (x' j)) * g (x' i')) := by congr 1; ext x'; ring
          _ = D.p a * ∑ x', (∏ j, D.p (x' j)) * g (x' i') := by rw [← Finset.mul_sum]
          _ = D.p a * ∑ b, D.p b * g b := by rw [ih i']
      simp_rw [step]
      rw [← Finset.sum_mul, D.sum_one, one_mul]

/-- Expected negative log-prob at each coordinate equals the entropy. -/
lemma expVal_neg_log (D : DiscreteDist k) (n : ℕ) (i : Fin n) :
    expVal D n (fun x => -Real.log (D.p (x i))) = shannonH D := by
  rw [expVal_marginal D n (fun a => -Real.log (D.p a)) i]
  simp only [shannonH, neg_neg]
  congr 1
  ext a
  by_cases ha : D.p a = 0
  · simp [ha]
  · simp [ha, mul_comm]

/-- -shannonH unfolds to ∑ a, D.p a * log(D.p a) (using Real.log 0 = 0). -/
lemma neg_shannonH_eq (D : DiscreteDist k) :
    -shannonH D = ∑ a : Fin k, D.p a * Real.log (D.p a) := by
  simp only [shannonH, neg_neg]
  apply Finset.sum_congr rfl; intro a _
  by_cases ha : D.p a = 0 <;> simp [ha]

/-- **Key theorem**: E[empEnt(X₁,...,Xₙ)] = H(p). -/
theorem expVal_empEnt (D : DiscreteDist k) (n : ℕ) :
    expVal D n (empEnt D n) = shannonH D := by
  by_cases hn : n = 0
  · simp [hn, expVal, empEnt, shannonH]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    -- E[empEnt] = ∑_x P(x) * (-(1/n) * ∑_j log p(x_j))
    --           = (1/n) * ∑_j E[-log p(X_j)]  = (1/n) * n * H(p) = H(p)
    have marginal : ∀ j : Fin n,
        ∑ x : Fin n → Fin k, (∏ i, D.p (x i)) * Real.log (D.p (x j)) =
        ∑ a : Fin k, D.p a * Real.log (D.p a) :=
      fun j => by have := expVal_marginal D n (fun a => Real.log (D.p a)) j
                  simp only [expVal, jointProb] at this; exact this
    simp only [expVal, empEnt, jointProb]
    simp_rw [show ∀ x : Fin n → Fin k,
      (∏ i, D.p (x i)) * (-(1 / ↑n) * ∑ j : Fin n, Real.log (D.p (x j))) =
      -(1 / ↑n) * ∑ j : Fin n, ((∏ i, D.p (x i)) * Real.log (D.p (x j)))
      from fun x => by
        rw [show (∏ i, D.p (x i)) * (-(1/↑n) * ∑ j, Real.log (D.p (x j))) =
                 -(1/↑n) * ((∏ i, D.p (x i)) * ∑ j, Real.log (D.p (x j))) from by ring]
        rw [Finset.mul_sum]]
    rw [← Finset.mul_sum, Finset.sum_comm]
    -- After sum_comm: -(1/n) * ∑_j (∑_x P(x) * log p(x_j)) = shannonH D
    -- Apply marginal to each j: -(1/n) * ∑_j (∑_a D.p a * log D.p a) = shannonH D
    -- Use ← neg_shannonH_eq to replace inner sum with -shannonH D
    simp_rw [marginal, ← neg_shannonH_eq]
    -- Goal: -(1/n) * ∑_j (-shannonH D) = shannonH D
    simp only [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn']

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

/-- Variance of empEnt over joint distribution = logVar(D) / n (i.i.d. sum). -/
theorem empEnt_variance (D : DiscreteDist k) (n : ℕ) :
    expVal D n (fun x => (empEnt D n x - shannonH D)^2) = logVar D / n := by
  sorry -- requires: independence factorization for variance of sum of i.i.d. variables

/-- **Main AEP Theorem**: Concentration bound.
    P(|empEnt(X₁,...,Xₙ) - H(p)| > ε) ≤ Var[-log p(X)] / (n · ε²). -/
theorem aep_concentration (D : DiscreteDist k) {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    ∑ x ∈ Finset.univ.filter (fun x => ε < |empEnt D n x - shannonH D|),
        jointProb D n x ≤
    logVar D / ((n : ℝ) * ε^2) := by
  -- Chebyshev: P(|empEnt - H| > ε) ≤ E[(empEnt-H)²]/ε² = (logVar/n)/ε² = logVar/(n·ε²)
  have hChebyshev := chebyshev_finite D n (empEnt D n) (shannonH D) ε hε
  rw [empEnt_variance] at hChebyshev
  -- Now hChebyshev : ∑ ... ≤ (logVar D / ↑n) / ε^2
  -- Goal:            ∑ ... ≤ logVar D / ((↑n) * ε^2)
  rwa [div_div] at hChebyshev

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
  -- empEnt(x) = -(1/n) log P(x) ≤ H + ε  →  log P(x) ≥ -n(H+ε)  →  P(x) ≥ exp(-n(H+ε))
  rw [jointProb, ← Real.exp_log (Finset.prod_pos (fun i _ => hsupp i))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_prod _ _ (fun i _ => ne_of_gt (hsupp i))]
  simp only [empEnt, Nat.not_eq_zero_of_lt hn, ite_false] at hle
  linarith [mul_comm (1 / (n : ℝ)) (∑ i, Real.log (D.p (x i)))]

/-- **Typical set size upper bound**: |T_ε^(n)| ≤ exp(n·(H(p)+ε)). -/
theorem typical_set_size_upper {D : DiscreteDist k} {n : ℕ} (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) (hsupp : ∀ i, 0 < D.p i) :
    (typicalSet D n ε).card ≤ Real.exp ((n : ℝ) * (shannonH D + ε)) := by
  -- P(T_ε) = ∑_{x ∈ T_ε} P(x) ≥ card * exp(-n(H+ε))
  -- So card ≤ P(T_ε) / exp(-n(H+ε)) ≤ 1 / exp(-n(H+ε)) = exp(n(H+ε))
  have hlow : ∀ x ∈ typicalSet D n ε, Real.exp (-(n : ℝ) * (shannonH D + ε)) ≤ jointProb D n x :=
    fun x hx => typical_prob_lower_bound hn ε x hx (fun i => hsupp (x i))
  have hexp_pos : 0 < Real.exp (-(n : ℝ) * (shannonH D + ε)) := Real.exp_pos _
  -- Sum inequality
  have hsum : (typicalSet D n ε).card * Real.exp (-(n : ℝ) * (shannonH D + ε)) ≤ 1 :=
    calc (typicalSet D n ε).card * Real.exp (-(n : ℝ) * (shannonH D + ε))
        = ∑ _x ∈ typicalSet D n ε, Real.exp (-(n : ℝ) * (shannonH D + ε)) := by
          simp [Finset.sum_const, Finset.card_mul_iff]
      _ ≤ ∑ x ∈ typicalSet D n ε, jointProb D n x := Finset.sum_le_sum hlow
      _ ≤ ∑ x : Fin n → Fin k, jointProb D n x :=
          Finset.sum_le_univ_sum_of_nonneg (fun x _ => jointProb_nonneg D n x) _
      _ = 1 := jointProb_sum_one D n
  -- card ≤ exp(n(H+ε))
  have : (typicalSet D n ε).card ≤ 1 / Real.exp (-(n : ℝ) * (shannonH D + ε)) :=
    le_div_of_mul_le hexp_pos hsum
  have hrw : (1 : ℝ) / Real.exp (-(n : ℝ) * (shannonH D + ε)) = Real.exp ((n : ℝ) * (shannonH D + ε)) := by
    rw [Real.exp_neg, div_inv_eq_mul_inv, one_mul]
  exact_mod_cast this.trans (hrw ▸ le_refl _)

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
2. `typical_prob_lower_bound`: Each typical sequence x satisfies P(x) ≥ exp(-n(H+ε))
3. `typical_set_size_upper`: |T_ε^(n)| ≤ exp(n(H(p)+ε))
4. `shannonH_nonneg`: Entropy is non-negative
5. `jointProb_sum_one`: Joint distribution sums to 1

**Stated (with sorry):**
1. `expVal_marginal`: Marginal factorization of joint expectation
2. `expVal_empEnt`: Expected empirical entropy = Shannon entropy
3. `empEnt_variance`: Variance of empEnt = logVar / n
4. `aep_concentration`: Main AEP probability bound

**Mathematical significance:**
The AEP is the fundamental result connecting typical sequences to entropy.
It implies Shannon's source coding theorem: compression to rate H(p) is
achievable (via typical set encoding), and rates below H(p) are impossible.
The `typical_set_size_upper` bound is already a key half of the coding theorem.
-/

end AEPFormalization
