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
    calc D.p i ≤ ∑ j, D.p j := Finset.single_le_sum (fun j _ => D.nonneg j) (Finset.mem_univ i)
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
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin k))
      (fun x => jointProb D (n + 1) x), Fintype.sum_prod_type]
    show ∑ a : Fin k, ∑ x : Fin n → Fin k, jointProb D (n + 1) (Fin.cons a x) = 1
    simp_rw [jointProb, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    simp only [D.sum_one, one_mul]
    exact ih

/-- Empirical entropy of sequence x (= -(1/n) log P(x)). -/
noncomputable def empEnt (D : DiscreteDist k) (n : ℕ) (x : Fin n → Fin k) : ℝ :=
  -(1 / (n : ℝ)) * ∑ i, Real.log (D.p (x i))

/-- For sequences with positive marginals, empEnt equals -(1/n) log P(x). -/
lemma empEnt_eq_neg_log_joint {D : DiscreteDist k} {n : ℕ} {x : Fin n → Fin k}
    (hsupp : ∀ i, 0 < D.p (x i)) :
    empEnt D n x = -(1 / (n : ℝ)) * Real.log (jointProb D n x) := by
  simp only [empEnt, jointProb]
  congr 1
  exact (Real.log_prod (fun i _ => ne_of_gt (hsupp i))).symm

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Expected Value
-- ════════════════════════════════════════════════════════════════

/-- Expected value of f over the joint distribution. -/
noncomputable def expVal (D : DiscreteDist k) (n : ℕ) (f : (Fin n → Fin k) → ℝ) : ℝ :=
  ∑ x : Fin n → Fin k, jointProb D n x * f x

/-- Expected value of a marginal function: E[g(Xⱼ)] = ∑_a p(a) g(a) for each j.
    Proof: ∑_x (∏_i p(x_i)) * g(x_j)
         = ∑_x ∏_i h_i(x_i)   where h_i(a) = if i=j then p(a)*g(a) else p(a)
         = ∏_i ∑_a h_i(a)     (by Fintype.prod_sum applied ∈ reverse)
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
    have lhs_eq : D.p (x j) * (∏ i ∈ Finset.univ.erase j, D.p (x i)) * g (x j) =
        (D.p (x j) * g (x j)) * ∏ i ∈ Finset.univ.erase j, D.p (x i) := by ring
    rw [lhs_eq]
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if i = j then D.p (x i) * g (x i) else D.p (x i)) (Finset.mem_univ j)]
    simp only [if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact (if_neg (Finset.ne_of_mem_erase hi)).symm
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
  simp

/-- **Key theorem**: E[empEnt(X₁,...,Xₙ)] = H(p).
    Proved by applying `expVal_marginal` to each coordinate log p(Xᵢ). -/
theorem expVal_empEnt (D : DiscreteDist k) (n : ℕ) (hn : 0 < n) :
    expVal D n (empEnt D n) = shannonH D := by
  simp only [expVal, empEnt, jointProb]
  -- Factor -(1/n) out of inner sum
  have factor : ∀ x : Fin n → Fin k,
      (∏ j, D.p (x j)) * (-(1 / (n : ℝ)) * ∑ i, Real.log (D.p (x i))) =
      -(1 / (n : ℝ)) * ∑ i : Fin n, (∏ j, D.p (x j)) * Real.log (D.p (x i)) := by
    intro x; rw [← Finset.mul_sum]; ring
  simp_rw [factor]
  rw [← Finset.mul_sum, Finset.sum_comm]
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
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have key : -(1 / (n : ℝ)) * ((n : ℝ) * ∑ a : Fin k, D.p a * Real.log (D.p a)) =
      -(∑ a : Fin k, D.p a * Real.log (D.p a)) := by field_simp
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
  rw [expVal, le_div_iff₀ (sq_pos_of_pos hε)]
  calc (∑ x ∈ Finset.univ.filter (fun x => ε < |f x - μ|), jointProb D n x) * ε^2
      = ∑ x ∈ Finset.univ.filter (fun x => ε < |f x - μ|), (jointProb D n x * ε^2) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x => ε < |f x - μ|), (jointProb D n x * (f x - μ)^2) := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        apply mul_le_mul_of_nonneg_left _ (jointProb_nonneg D n x)
        have : ε ≤ |f x - μ| := le_of_lt hx
        nlinarith [sq_abs (f x - μ)]
    _ ≤ ∑ x : Fin n → Fin k, jointProb D n x * (f x - μ)^2 :=
        Finset.sum_le_univ_sum_of_nonneg
          (fun x => mul_nonneg (jointProb_nonneg D n x) (sq_nonneg _))

-- ════════════════════════════════════════════════════════════════
-- SECTION V: AEP Concentration Bound
-- ════════════════════════════════════════════════════════════════

/-- The variance of -log p(X): Var_p[-log p(X)] = E[(log p(X))²] - H(p)². -/
noncomputable def logVar (D : DiscreteDist k) : ℝ :=
  (∑ i, if D.p i = 0 then 0 else D.p i * (Real.log (D.p i))^2) - (shannonH D)^2

/-- 2D independence: for distinct coordinates j₁ ≠ j₂,
    E[g₁(X_{j₁}) · g₂(X_{j₂})] = E[g₁(X)] · E[g₂(X)]. -/
private lemma expVal_marginal_product (D : DiscreteDist k) (n : ℕ)
    (g₁ g₂ : Fin k → ℝ) (j₁ j₂ : Fin n) (hj : j₁ ≠ j₂) :
    expVal D n (fun x => g₁ (x j₁) * g₂ (x j₂)) =
    (∑ a, D.p a * g₁ a) * (∑ b, D.p b * g₂ b) := by
  simp only [expVal, jointProb]
  let h : Fin n → Fin k → ℝ := fun i a =>
    if i = j₁ then D.p a * g₁ a else if i = j₂ then D.p a * g₂ a else D.p a
  -- Rewrite (∏_i p(x_i)) * (g₁(x_{j₁}) * g₂(x_{j₂})) = ∏_i h_i(x_i)
  have step1 : ∀ x : Fin n → Fin k,
      (∏ i, D.p (x i)) * (g₁ (x j₁) * g₂ (x j₂)) = ∏ i, h i (x i) := fun x => by
    simp only [h]
    -- Factor the h product by extracting j₁ and j₂
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => if i = j₁ then D.p (x i) * g₁ (x i) else if i = j₂ then D.p (x i) * g₂ (x i) else D.p (x i))
        (Finset.mem_univ j₁)]
    rw [if_pos rfl]
    have hcongr1 : ∏ i ∈ Finset.univ.erase j₁,
        (if i = j₁ then D.p (x i) * g₁ (x i) else if i = j₂ then D.p (x i) * g₂ (x i) else D.p (x i)) =
        ∏ i ∈ Finset.univ.erase j₁,
          (if i = j₂ then D.p (x i) * g₂ (x i) else D.p (x i)) :=
      Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))
    rw [hcongr1]
    rw [← Finset.mul_prod_erase (Finset.univ.erase j₁)
        (fun i => if i = j₂ then D.p (x i) * g₂ (x i) else D.p (x i))
        (Finset.mem_erase.mpr ⟨hj.symm, Finset.mem_univ _⟩)]
    rw [if_pos rfl]
    have hcongr2 : ∏ i ∈ (Finset.univ.erase j₁).erase j₂,
        (if i = j₂ then D.p (x i) * g₂ (x i) else D.p (x i)) =
        ∏ i ∈ (Finset.univ.erase j₁).erase j₂, D.p (x i) :=
      Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))
    rw [hcongr2]
    -- Factor ∏_i D.p(x_i) the same way and ring
    rw [← Finset.mul_prod_erase Finset.univ (fun i => D.p (x i)) (Finset.mem_univ j₁),
        ← Finset.mul_prod_erase (Finset.univ.erase j₁) (fun i => D.p (x i))
          (Finset.mem_erase.mpr ⟨hj.symm, Finset.mem_univ _⟩)]
    ring
  simp_rw [step1, ← Fintype.prod_sum h]
  -- Evaluate ∏_i (∑_a h_i(a)) by extracting j₁ and j₂
  simp only [h]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ∑ a : Fin k, if i = j₁ then D.p a * g₁ a else if i = j₂ then D.p a * g₂ a else D.p a)
      (Finset.mem_univ j₁)]
  have hj1 : (∑ a : Fin k, if j₁ = j₁ then D.p a * g₁ a else if j₁ = j₂ then D.p a * g₂ a else D.p a) =
      ∑ a : Fin k, D.p a * g₁ a :=
    Finset.sum_congr rfl (fun a _ => if_pos rfl)
  rw [hj1]
  have hcongr3 : ∏ i ∈ Finset.univ.erase j₁,
      (∑ a : Fin k, if i = j₁ then D.p a * g₁ a else if i = j₂ then D.p a * g₂ a else D.p a) =
      ∏ i ∈ Finset.univ.erase j₁, (∑ a : Fin k, if i = j₂ then D.p a * g₂ a else D.p a) :=
    Finset.prod_congr rfl (fun i hi =>
      Finset.sum_congr rfl (fun a _ => if_neg (Finset.ne_of_mem_erase hi)))
  rw [hcongr3]
  rw [← Finset.mul_prod_erase (Finset.univ.erase j₁)
      (fun i => ∑ a : Fin k, if i = j₂ then D.p a * g₂ a else D.p a)
      (Finset.mem_erase.mpr ⟨hj.symm, Finset.mem_univ _⟩)]
  have hj2 : (∑ a : Fin k, if j₂ = j₂ then D.p a * g₂ a else D.p a) =
      ∑ a : Fin k, D.p a * g₂ a :=
    Finset.sum_congr rfl (fun a _ => if_pos rfl)
  rw [hj2]
  -- Remaining factors are all ∑_a D.p a = 1
  have hcongr4 : ∏ i ∈ (Finset.univ.erase j₁).erase j₂,
      (∑ a : Fin k, if i = j₂ then D.p a * g₂ a else D.p a) =
      ∏ _i ∈ (Finset.univ.erase j₁).erase j₂, (1 : ℝ) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (Finset.sum_congr rfl (fun a _ => if_neg (Finset.ne_of_mem_erase hi))).trans D.sum_one
  rw [hcongr4, Finset.prod_const_one, mul_one]

/-- Variance of empEnt over joint distribution = logVar(D) / n (i.i.d. sum).
    Proved by expanding the square: diagonal terms contribute logVar D each (via
    expVal_marginal), cross terms are zero (via expVal_marginal_product + mean-zero). -/
theorem empEnt_variance (D : DiscreteDist k) (n : ℕ) (hn : 0 < n) :
    expVal D n (fun x => (empEnt D n x - shannonH D)^2) = logVar D / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Z a = -log p(a) - H  is the centered log-probability
  let Z : Fin k → ℝ := fun a => -Real.log (D.p a) - shannonH D
  -- empEnt D n x - H = (1/n) * ∑_j Z(x j)
  have hw : ∀ x : Fin n → Fin k, empEnt D n x - shannonH D = (1 / ↑n) * ∑ j, Z (x j) :=
    fun x => by
      simp only [empEnt, Z]
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      field_simp
  -- E[Z] = 0  (centered)
  have hZ_mean : ∑ a : Fin k, D.p a * Z a = 0 := by
    have step : ∀ a : Fin k, D.p a * Z a = -(D.p a * Real.log (D.p a)) - D.p a * shannonH D := by
      intro a; simp only [Z]; ring
    simp_rw [step]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, D.sum_one, one_mul]
    have heq : ∑ a : Fin k, D.p a * Real.log (D.p a) =
        ∑ a, if D.p a = 0 then 0 else D.p a * Real.log (D.p a) :=
      Finset.sum_congr rfl (fun a _ => by by_cases h : D.p a = 0 <;> simp [h])
    rw [heq]
    simp only [shannonH]
    ring
  -- E[Z²] = logVar D  (variance computation)
  have hZ_var : ∑ a : Fin k, D.p a * Z a ^ 2 = logVar D := by
    simp only [Z, logVar]
    have hlog : ∑ a : Fin k, D.p a * Real.log (D.p a) = -shannonH D := by
      simp only [shannonH, neg_neg]
      exact Finset.sum_congr rfl (fun a _ => by by_cases h : D.p a = 0 <;> simp [h])
    have : ∑ a : Fin k, D.p a * (-Real.log (D.p a) - shannonH D) ^ 2 =
        (∑ a, D.p a * (Real.log (D.p a))^2) - (shannonH D)^2 := by
      have expand := calc
          ∑ a : Fin k, D.p a * (-Real.log (D.p a) - shannonH D)^2
          = ∑ a, (D.p a * (Real.log (D.p a))^2
              + 2 * shannonH D * (D.p a * Real.log (D.p a))
              + (shannonH D)^2 * D.p a) :=
            Finset.sum_congr rfl (fun a _ => by ring)
        _ = ∑ a, D.p a * (Real.log (D.p a))^2
              + 2 * shannonH D * ∑ a, D.p a * Real.log (D.p a)
              + (shannonH D)^2 * ∑ a, D.p a := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← Finset.mul_sum, ← Finset.mul_sum]
        _ = _ := by rw [hlog, D.sum_one]
      rw [expand]; ring
    rw [this]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by by_cases h : D.p a = 0 <;> simp [h])
  -- Main calculation: expand the square and use marginals
  simp_rw [hw]
  -- Factor out (1/n)²
  have factor : ∀ x : Fin n → Fin k,
      ((1 / ↑n) * ∑ j, Z (x j))^2 =
      (1 / ↑n)^2 * ∑ i : Fin n, ∑ j : Fin n, Z (x i) * Z (x j) := fun x => by
    rw [mul_pow, sq (∑ j, Z (x j)), Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  simp_rw [factor]
  simp only [expVal, jointProb]
  -- Goal: ∑ x, (∏ l, D.p (x l)) * ((1/n)^2 * ∑ i, ∑ j, Z (x i) * Z (x j)) = logVar D / n
  have step2 : ∀ x : Fin n → Fin k,
      (∏ l, D.p (x l)) * ((1 / (n:ℝ))^2 * ∑ i : Fin n, ∑ j : Fin n, Z (x i) * Z (x j)) =
      (1 / (n:ℝ))^2 * ∑ i : Fin n, ∑ j : Fin n, (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) := fun x => by
    rw [← mul_assoc, mul_comm (∏ l, D.p (x l)) ((1 / (n:ℝ))^2), mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  simp_rw [step2]
  rw [← Finset.mul_sum]
  -- Goal: (1/n)^2 * ∑ x, ∑ i, ∑ j, (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) = logVar D / n
  have swap1 : ∑ x : Fin n → Fin k, ∑ i : Fin n, ∑ j : Fin n,
      (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) =
      ∑ i : Fin n, ∑ x : Fin n → Fin k, ∑ j : Fin n,
        (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) :=
    Finset.sum_comm
  rw [swap1]
  have swap2 : ∀ i : Fin n, ∑ x : Fin n → Fin k, ∑ j : Fin n,
      (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) =
      ∑ j : Fin n, ∑ x : Fin n → Fin k,
        (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) :=
    fun i => Finset.sum_comm
  simp_rw [swap2]
  -- Goal: (1/n)^2 * ∑ i, ∑ j, ∑ x, (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) = logVar D / n
  suffices h : ∑ i : Fin n, ∑ j : Fin n,
      ∑ x : Fin n → Fin k, (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) = n * logVar D by
    rw [h]; field_simp
  -- Each term: diagonal = logVar D, off-diagonal = 0
  have diag : ∀ i : Fin n, expVal D n (fun x => Z (x i) * Z (x i)) = logVar D := fun i => by
    have heq : (fun x : Fin n → Fin k => Z (x i) * Z (x i)) = fun x => Z (x i) ^ 2 := by
      funext x; ring
    rw [heq, expVal_marginal D n (fun a => Z a ^ 2) i, hZ_var]
  have offdiag : ∀ i j : Fin n, i ≠ j →
      expVal D n (fun x => Z (x i) * Z (x j)) = 0 := fun i j hij => by
    rw [expVal_marginal_product D n Z Z i j hij, hZ_mean, mul_zero]
  have hval : ∀ i j : Fin n, ∑ x : Fin n → Fin k, (∏ l, D.p (x l)) * (Z (x i) * Z (x j)) =
      expVal D n (fun x => Z (x i) * Z (x j)) := fun i j => by
    simp only [expVal, jointProb]
  simp_rw [hval]
  -- Sum: diagonal contributes n * logVar D, off-diagonal contributes 0
  rw [show ∑ i : Fin n, ∑ j : Fin n, expVal D n (fun x => Z (x i) * Z (x j)) =
      ∑ i : Fin n, (expVal D n (fun x => Z (x i) * Z (x i)) +
        ∑ j ∈ Finset.univ.erase i, expVal D n (fun x => Z (x i) * Z (x j))) from by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]]
  have hoff2 : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i,
      expVal D n (fun x => Z (x i) * Z (x j)) = 0 := fun i => by
    apply Finset.sum_eq_zero
    intro j hj
    exact offdiag i j (Finset.ne_of_mem_erase hj).symm
  simp_rw [diag, hoff2, add_zero]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

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
noncomputable def typicalSet (D : DiscreteDist k) (n : ℕ) (ε : ℝ) : Finset (Fin n → Fin k) :=
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
  rw [Real.log_prod (fun i _ => ne_of_gt (hsupp i))]
  simp only [empEnt] at hle
  have hn'' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have key : (n:ℝ) * (-(1 / (n:ℝ)) * ∑ i, Real.log (D.p (x i))) ≤ (n:ℝ) * (shannonH D + ε) :=
    mul_le_mul_of_nonneg_left hle hn''.le
  have hn3 : (n:ℝ) * (-(1 / (n:ℝ)) * ∑ i, Real.log (D.p (x i))) = -(∑ i, Real.log (D.p (x i))) := by
    field_simp
  linarith [key, hn3]

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
          Finset.sum_le_univ_sum_of_nonneg (fun x => jointProb_nonneg D n x)
      _ = 1 := jointProb_sum_one D n
  have hcard_le : (typicalSet D n ε).card ≤ 1 / Real.exp (-(n : ℝ) * (shannonH D + ε)) :=
    (le_div_iff₀ hexp_pos).mpr hsum
  have hrw : (1 : ℝ) / Real.exp (-(n : ℝ) * (shannonH D + ε)) = Real.exp ((n : ℝ) * (shannonH D + ε)) := by
    rw [neg_mul, Real.exp_neg, one_div, inv_inv]
  exact_mod_cast hrw ▸ hcard_le

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
  have h : (1:ℝ)/2 ≠ 0 := by norm_num
  rw [if_neg h]
  have hlog : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2 : ℝ) = 2⁻¹ from by norm_num, Real.log_inv]
  rw [hlog]
  ring

/-- For fair coin: the constant-0 100-symbol sequence has empirical entropy log 2
    (matching the fair-coin entropy exactly, since every symbol has probability 1/2). -/
example : empEnt uniformBin 100 (fun _ => 0) = Real.log 2 := by
  simp only [empEnt, uniformBin, Matrix.cons_val_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlog : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2 : ℝ) = 2⁻¹ from by norm_num, Real.log_inv]
  rw [hlog]
  ring

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

**No remaining sorries.** All theorems are fully proved.

- `empEnt_variance` was proved via:
  - `expVal_marginal_product`: 2D marginal factorization (bilinear: E[g(X_i)*h(X_j)] = E[g]*E[h] for i≠j)
  - Centering Z = -log p - H, mean-zero property, diagonal vs off-diagonal splitting

**Bug fix**: The original `aep_concentration` incorrectly used `rw [expVal_empEnt]` (which
rewrites E[empEnt] = H, not the variance). Fixed to use `empEnt_variance` which rewrites
E[(empEnt - H)²] = logVar/n, enabling the Chebyshev bound to go through.
-/

end AEPFormalization
