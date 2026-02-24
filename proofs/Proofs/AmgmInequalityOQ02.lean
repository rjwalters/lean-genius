/-
  Maclaurin Inequalities via Elementary Symmetric Polynomials
  Open Question: amgm-inequality-oq-02

  Related: AMGMInequality.lean, AmgmInequalityOQ03.lean (power means)
  Status: Known classical result (Maclaurin 1729, Newton 1687)

  Statement:
  For non-negative reals x₁, ..., xₙ, define the k-th elementary symmetric polynomial
    eₖ(x) = ∑_{|S|=k} ∏_{i∈S} xᵢ
  and the normalized Maclaurin means:
    Mₖ = (eₖ / C(n,k))^(1/k)

  Maclaurin's Theorem: M₁ ≥ M₂ ≥ ⋯ ≥ Mₙ ≥ 0
  In particular: AM = M₁ ≥ Mₙ = GM  (the AM-GM inequality as special case).

  Key Proof Engine:
  Newton's inequalities (log-concavity): (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1))·(eₖ₊₁/C(n,k+1))
  This implies the Maclaurin chain step-by-step.

  What This File Proves:
  1. Elementary symmetric polynomial setup
  2. M₁ ≥ M₂ for n=2 (classical AM-GM, proved)
  3. M₁² ≥ M₂ for n=3 via (a-b)²+(b-c)²+(c-a)² ≥ 0 (proved)
  4. General e_k non-negativity for non-negative inputs (proved)
  5. Newton log-concavity (axiom - deep inductive result)
  6. General Maclaurin step Mₖ ≥ Mₖ₊₁ (axiom)
  7. AM ≥ GM (proved from Mathlib)

  References:
  - Maclaurin, C. (1729): A Second Letter to Martin Folkes, Esq.
  - Hardy-Littlewood-Pólya "Inequalities" (1934) §2.22
  - Mathlib: Real.geom_mean_le_arith_mean_weighted
-/

import Mathlib

open Finset Real

/-
## Part I: Elementary Symmetric Polynomials
-/

/-- The k-th elementary symmetric polynomial of x₁, ..., xₙ:
    eₖ(x) = ∑_{S ⊆ {0,...,n-1}, |S|=k} ∏_{i ∈ S} xᵢ -/
noncomputable def elemSymm {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, x i

/-- e₀ = 1 (empty product, empty set) -/
theorem elemSymm_zero {n : ℕ} (x : Fin n → ℝ) : elemSymm 0 x = 1 := by
  simp [elemSymm, powersetCard_zero]

/-- e₁ = ∑ xᵢ (sum of all variables) -/
theorem elemSymm_one {n : ℕ} (x : Fin n → ℝ) : elemSymm 1 x = ∑ i, x i := by
  simp [elemSymm, powersetCard_one, sum_map, prod_singleton]

/-- For non-negative variables, eₖ ≥ 0 -/
theorem elemSymm_nonneg {n : ℕ} (k : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ elemSymm k x :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun i _ => hx i

/-
## Part II: The M₁ ≥ M₂ Inequality (Key Special Cases)
-/

/-- For two variables a, b ≥ 0: (a+b)/2 ≥ √(ab).
    This is M₁ ≥ M₂ for n=2 (classical AM-GM).
    Proof: (√a - √b)² ≥ 0 gives a + b ≥ 2√(ab). -/
theorem maclaurin_m1_ge_m2_n2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ Real.sqrt (a * b) := by
  have h_sq : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have h_expand : (Real.sqrt a - Real.sqrt b) ^ 2 =
      Real.sqrt a ^ 2 - 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2 := by ring
  rw [h_expand, Real.sq_sqrt ha, Real.sq_sqrt hb] at h_sq
  have h_sqrt_mul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) :=
    (Real.sqrt_mul ha b).symm
  linarith

/-- For three non-negative variables: (e₁/3)² ≥ e₂/C(3,2) = (ab+bc+ca)/3.
    Equivalently: (a+b+c)² ≥ 3(ab+bc+ca).
    Proof: This is (a-b)² + (b-c)² + (c-a)² ≥ 0. -/
theorem maclaurin_m1sq_ge_m2_n3 (a b c : ℝ) :
    ((a + b + c) / 3) ^ 2 ≥ (a * b + b * c + c * a) / 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

/-- For four non-negative variables: (e₁/4)² ≥ e₂/C(4,2).
    Equivalently: (a+b+c+d)² ≥ 4(ab+ac+ad+bc+bd+cd)/3.
    Same sum-of-squares argument. -/
theorem maclaurin_m1sq_ge_m2_n4 (a b c d : ℝ) :
    ((a + b + c + d) / 4) ^ 2 ≥ (a*b + a*c + a*d + b*c + b*d + c*d) / 6 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
             sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- The Cauchy-Schwarz inequality for finite sums: n·∑xᵢ² ≥ (∑xᵢ)².
    Proof via ∑ᵢ∑ⱼ(xᵢ-xⱼ)² = 2·(n·∑xᵢ² - (∑xᵢ)²) ≥ 0. -/
private lemma cauchy_schwarz_sum {n : ℕ} (x : Fin n → ℝ) :
    (n : ℝ) * ∑ i : Fin n, (x i) ^ 2 ≥ (∑ i : Fin n, x i) ^ 2 := by
  have h_nn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h_expand : ∑ i : Fin n, ∑ j : Fin n, (x i - x j) ^ 2 =
      2 * ((n : ℝ) * ∑ i, (x i) ^ 2 - (∑ i, x i) ^ 2) := by
    simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib]
    have h1 : ∑ i : Fin n, ∑ _j : Fin n, (x i) ^ 2 = (n : ℝ) * ∑ i, (x i) ^ 2 := by
      simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    have h2 : ∑ _i : Fin n, ∑ j : Fin n, (x j) ^ 2 = (n : ℝ) * ∑ j, (x j) ^ 2 := by
      simp [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    have h3 : ∑ i : Fin n, ∑ j : Fin n, 2 * x i * x j = 2 * (∑ i, x i) ^ 2 := by
      rw [sq, sum_mul]; simp_rw [mul_sum]; congr 1; ext i; ring
    rw [h1, h2, h3]; ring
  linarith

/-- General squared M₁ ≥ M₂ via sum-of-squares identity.
    Key reduction: C(n,2)·(∑xᵢ)² - n²·e₂ = n/2·(n·∑xᵢ² - (∑xᵢ)²) ≥ 0
    by Cauchy-Schwarz.
    The algebraic chain uses the binomial identity (∑xᵢ)² = ∑xᵢ² + 2·e₂. -/
theorem maclaurin_sq_m1_ge_m2_general {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    (Nat.choose n 2 : ℝ) * (∑ i, x i) ^ 2 ≥ (n : ℝ) ^ 2 * elemSymm 2 x := by
  -- Cauchy-Schwarz (proved above)
  have h_cs : (n : ℝ) * ∑ i : Fin n, (x i) ^ 2 ≥ (∑ i : Fin n, x i) ^ 2 :=
    cauchy_schwarz_sum x
  -- Binomial identity: (∑xᵢ)² = ∑xᵢ² + 2·e₂
  -- This follows from expanding (∑xᵢ)² = ∑ᵢ∑ⱼ xᵢxⱼ and separating diagonal/off-diagonal.
  -- The off-diagonal sum ∑_{i≠j} xᵢxⱼ = 2·e₂ by symmetry of powersetCard 2.
  have h_binom : (∑ i : Fin n, x i) ^ 2 =
      ∑ i : Fin n, (x i) ^ 2 + 2 * elemSymm 2 x := by
    sorry -- binomial expansion: provable by induction on n using elemSymm recurrence
  -- The formula 2·C(n,2) = n·(n-1) in ℕ, proved by induction
  have h_2cn2 : 2 * (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    -- Prove by induction on n (works for all n ≥ 0)
    suffices ∀ m : ℕ, 2 * (Nat.choose m 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) from this n
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      -- C(k+1, 2) = k + C(k, 2) by Pascal's rule
      have hstep : Nat.choose (k + 1) 2 = k + Nat.choose k 2 := by
        have h := Nat.choose_succ_succ k 1
        simp only [Nat.choose_one_right] at h
        omega
      rw [hstep]
      push_cast
      nlinarith
  -- Key nonnegativity: n·(n·∑xᵢ² - (∑xᵢ)²) ≥ 0
  have h_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have h_nonneg_diff : 0 ≤ (n : ℝ) * ∑ i, (x i) ^ 2 - (∑ i, x i) ^ 2 := by linarith
  have h_key : 0 ≤ (n : ℝ) * ((n : ℝ) * ∑ i, (x i) ^ 2 - (∑ i, x i) ^ 2) :=
    mul_nonneg (le_of_lt h_pos) h_nonneg_diff
  -- Algebraic combination:
  -- C(n,2)·S₁² - n²·e₂ = n/2·(n·S₂ - S₁²) ≥ 0
  -- where S₁ = ∑xᵢ, S₂ = ∑xᵢ²
  set S₁ := ∑ i : Fin n, x i
  set S₂ := ∑ i : Fin n, (x i) ^ 2
  set e₂ := elemSymm 2 x
  -- From h_binom: S₁² = S₂ + 2·e₂, so 2·n²·e₂ = n²·(S₁² - S₂)
  -- From h_2cn2: 2·C = n·(n-1) = n² - n
  -- Therefore: 2·(C·S₁² - n²·e₂) = (n²-n)·S₁² - n²·(S₁²-S₂) = n·(n·S₂ - S₁²) ≥ 0
  nlinarith [sq_nonneg S₁, h_key, h_binom, h_2cn2, sq_nonneg (n : ℝ),
             mul_self_nonneg (n : ℝ)]

/-
## Part III: Newton's Log-Concavity and the Maclaurin Chain
-/

/-- Newton's inequality: the normalized elementary symmetric polynomials are log-concave.
    For 1 ≤ k < n: (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1)) · (eₖ₊₁/C(n,k+1))
    This is the fundamental engine of the Maclaurin chain.

    Proof strategy: Polarization + induction on n.
    The one-dimensional case is trivial. The inductive step uses the recurrence
    eₖ(x₁,...,xₙ) = eₖ(x₁,...,xₙ₋₁) + xₙ·eₖ₋₁(x₁,...,xₙ₋₁) and Cauchy-Schwarz.
    See Hardy-Littlewood-Pólya §2.22 or Maclaurin's original argument. -/
axiom newton_log_concavity {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (elemSymm k x / (Nat.choose n k : ℝ)) ^ 2 ≥
    (elemSymm (k - 1) x / (Nat.choose n (k - 1) : ℝ)) *
    (elemSymm (k + 1) x / (Nat.choose n (k + 1) : ℝ))

/-- The Maclaurin means, defined as Mₖ = (eₖ/C(n,k))^(1/k). -/
noncomputable def maclaurinMean {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  (elemSymm k x / (Nat.choose n k : ℝ)) ^ ((1 : ℝ) / k)

/-- Maclaurin's step inequality: Mₖ ≥ Mₖ₊₁.
    Follows from Newton's log-concavity + monotonicity of t^(1/k) vs t^(1/(k+1))
    for t ≥ 0. The derivation requires careful manipulation of real power functions.
    See Hardy-Littlewood-Pólya (1934) or Maclaurin (1729). -/
axiom maclaurin_step {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean k x ≥ maclaurinMean (k + 1) x

/-- Maclaurin means are non-negative for non-negative inputs. -/
theorem maclaurinMean_nonneg {n : ℕ} (k : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ maclaurinMean k x := by
  apply Real.rpow_nonneg
  apply div_nonneg
  · exact elemSymm_nonneg k x hx
  · exact Nat.cast_nonneg _

/-
## Part IV: AM ≥ GM as Corollary
-/

/-- The AM-GM inequality: ∏ xᵢ^(1/n) ≤ (∑ xᵢ)/n.
    This is a special case of the Maclaurin chain (M₁ ≥ Mₙ).
    We prove it here using Mathlib's weighted AM-GM inequality. -/
theorem amgm_from_maclaurin {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ∏ i ∈ (univ : Finset (Fin n)), x i ^ ((1 : ℝ) / n) ≤ (∑ i, x i) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hw : ∀ i ∈ (univ : Finset (Fin n)), (0 : ℝ) ≤ (1 : ℝ) / n := fun _ _ => by positivity
  have hw' : ∑ _i ∈ (univ : Finset (Fin n)), (1 : ℝ) / n = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hn'
  have key := Real.geom_mean_le_arith_mean_weighted univ (fun _ => (1 : ℝ) / n) x
    hw hw' (fun i _ => hx i)
  calc ∏ i ∈ univ, x i ^ ((1:ℝ)/n)
      ≤ ∑ i ∈ univ, ((1:ℝ)/n) * x i := key
    _ = (∑ i, x i) / n := by rw [← Finset.mul_sum]; ring

/-
## Summary

### The Main Answer:
Maclaurin's inequalities M₁ ≥ M₂ ≥ ⋯ ≥ Mₙ hold for non-negative reals,
where Mₖ = (eₖ/C(n,k))^(1/k) and eₖ is the k-th elementary symmetric polynomial.
The chain follows from Newton's log-concavity inequalities for the sequence eₖ/C(n,k).

### Proved (no sorry or axiom):
1. `elemSymm_zero` — e₀ = 1
2. `elemSymm_one` — e₁ = ∑ xᵢ
3. `elemSymm_nonneg` — non-negative inputs give non-negative eₖ
4. `maclaurin_m1_ge_m2_n2` — AM ≥ GM for n=2 (classical, via (√a-√b)² ≥ 0)
5. `maclaurin_m1sq_ge_m2_n3` — (M₁)² ≥ M₂ for n=3 (via nlinarith + sq_nonneg)
6. `maclaurin_m1sq_ge_m2_n4` — (M₁)² ≥ M₂ for n=4 (via nlinarith + sq_nonneg)
7. `maclaurinMean_nonneg` — Maclaurin means are non-negative
8. `amgm_from_maclaurin` — AM-GM from Mathlib weighted AM-GM

### Has sorry (1):
1. `maclaurin_sq_m1_ge_m2_general` — general (∑xᵢ)²·C(n,2) ≥ n²·e₂
   (identity: C(n,2)·e₁² - n²·e₂ = n/2·∑_{i<j}(xᵢ-xⱼ)², needs Finset algebra)

### Axiomatized (deep results):
1. `newton_log_concavity` — log-concavity of eₖ/C(n,k)
2. `maclaurin_step` — Mₖ ≥ Mₖ₊₁ (general Maclaurin step)
-/
