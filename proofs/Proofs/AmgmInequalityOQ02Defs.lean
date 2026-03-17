/-
  Maclaurin Inequalities: Core Definitions and Standalone Theorems
  Open Question: amgm-inequality-oq-02

  This file contains the core definitions for elementary symmetric polynomials
  and Maclaurin means, along with theorems that do NOT depend on Newton's
  log-concavity. The Newton/Maclaurin proofs are in AmgmInequalityOQ02OQ02.lean.

  Definitions:
  - elemSymm: k-th elementary symmetric polynomial
  - maclaurinMean: k-th Maclaurin mean Mₖ = (eₖ/C(n,k))^(1/k)

  Standalone Theorems:
  - elemSymm_zero, elemSymm_one, elemSymm_nonneg
  - elemSymm_succ (recurrence), elemSymm_gt_eq_zero, elemSymm_n_eq_prod
  - maclaurin_sq_m1_ge_m2_general (M₁² ≥ M₂ via Cauchy-Schwarz)
  - Special cases for n=2,3,4
  - amgm_from_maclaurin (AM-GM from Mathlib)

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

/-
## Binomial Identity Helpers: (∑xᵢ)² = ∑xᵢ² + 2·e₂
These private lemmas prove the binomial identity by induction using
the recurrence e₂(x₀,...,xₙ) = e₂(x₀,...,xₙ₋₁) + xₙ·e₁(x₀,...,xₙ₋₁).
-/

-- Explicit castSucc embedding (avoids API naming issues in Docker Lean 4.26.0)
private def csEmb (n : ℕ) : Fin n ↪ Fin (n + 1) :=
  ⟨Fin.castSucc, fun _ _ h => Fin.castSucc_inj.mp h⟩

@[simp] private lemma csEmb_apply (n : ℕ) (i : Fin n) : csEmb n i = Fin.castSucc i := rfl

-- mapEmbedding via toEmbedding = map (Finset.sum_map uses .toEmbedding coercion)
private lemma mapEmb_eq {n : ℕ} (s : Finset (Fin n)) :
    (Finset.mapEmbedding (csEmb n)).toEmbedding s = s.map (csEmb n) := rfl

private lemma fin_univ_insert_last (n : ℕ) :
    (univ : Finset (Fin (n + 1))) = insert (Fin.last n) (univ.map (csEmb n)) := by
  ext i
  simp only [mem_univ, mem_insert, mem_map, true_and, csEmb_apply]
  constructor
  · intro _; exact Fin.lastCases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
  · intro _; trivial

private lemma fin_last_not_mem_map (n : ℕ) :
    Fin.last n ∉ (univ : Finset (Fin n)).map (csEmb n) := by
  simp only [mem_map, mem_univ, true_and, csEmb_apply, not_exists]
  intro i; exact (Fin.castSucc_lt_last i).ne

private lemma pc_disj (n : ℕ) :
    Disjoint
      (powersetCard 2 ((univ : Finset (Fin n)).map (csEmb n)))
      ((powersetCard 1 ((univ : Finset (Fin n)).map (csEmb n))).image
        (insert (Fin.last n))) := by
  apply Finset.disjoint_left.mpr
  intro t ht1 ht2
  simp only [mem_image, Finset.mem_powersetCard] at ht1 ht2
  obtain ⟨s, hs, rfl⟩ := ht2
  obtain ⟨ht1_sub, _⟩ := ht1
  have hmem := ht1_sub (Finset.mem_insert_self (Fin.last n) _)
  simp only [mem_map, mem_univ, true_and, csEmb_apply] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact (Fin.castSucc_lt_last i).ne hi

private lemma prod_map_csEmb {n : ℕ} (s : Finset (Fin n)) (x : Fin (n + 1) → ℝ) :
    ∏ i ∈ s.map (csEmb n), x i = ∏ j ∈ s, x (Fin.castSucc j) := by
  rw [Finset.prod_map]; simp only [csEmb_apply]

-- Key recurrence: e₂(x₀,...,xₙ) = e₂(x₀,...,xₙ₋₁) + xₙ·e₁(x₀,...,xₙ₋₁)
private lemma elemSymm_two_succ {n : ℕ} (x : Fin (n + 1) → ℝ) :
    elemSymm 2 x =
    elemSymm 2 (x ∘ Fin.castSucc) +
    x (Fin.last n) * elemSymm 1 (x ∘ Fin.castSucc) := by
  simp only [elemSymm]
  rw [fin_univ_insert_last, Finset.powersetCard_succ_insert (fin_last_not_mem_map n)]
  rw [Finset.sum_union (pc_disj n)]
  congr 1
  · rw [Finset.powersetCard_map, Finset.sum_map]
    congr 1; ext s
    simp only [mapEmb_eq]
    rw [prod_map_csEmb]
    simp only [Function.comp_apply]
  · have insert_inj : Set.InjOn (insert (Fin.last n))
        (powersetCard 1 ((univ : Finset (Fin n)).map (csEmb n))).toSet := by
      intro s hs t ht hst
      rw [Finset.mem_coe] at hs ht
      rw [Finset.mem_powersetCard] at hs ht
      have hs' : Fin.last n ∉ s := by
        intro hmem
        have h := hs.1 hmem
        simp only [mem_map, mem_univ, true_and, csEmb_apply] at h
        obtain ⟨i, hi⟩ := h
        exact (Fin.castSucc_lt_last i).ne hi
      have ht' : Fin.last n ∉ t := by
        intro hmem
        have h := ht.1 hmem
        simp only [mem_map, mem_univ, true_and, csEmb_apply] at h
        obtain ⟨i, hi⟩ := h
        exact (Fin.castSucc_lt_last i).ne hi
      rw [show s = (insert (Fin.last n) s).erase (Fin.last n) from
          (Finset.erase_insert hs').symm, hst, Finset.erase_insert ht']
    rw [Finset.sum_image insert_inj, Finset.powersetCard_map, Finset.sum_map]
    have h_prod : ∀ s ∈ (powersetCard 1 (univ : Finset (Fin n))),
        ∏ i ∈ insert (Fin.last n) ((Finset.mapEmbedding (csEmb n)).toEmbedding s), x i =
        x (Fin.last n) * ∏ j ∈ s, (x ∘ Fin.castSucc) j := by
      intro s _
      rw [mapEmb_eq, Finset.prod_insert]
      · simp only [Function.comp_apply]; rw [prod_map_csEmb]
      · simp only [mem_map, csEmb_apply, not_exists, not_and]
        intro j _; exact (Fin.castSucc_lt_last j).ne
    rw [Finset.sum_congr rfl h_prod, ← Finset.mul_sum]

-- Binomial identity by induction: (∑xᵢ)² = ∑xᵢ² + 2·e₂
private theorem sq_sum_eq_sum_sq_add_two_elemSymm {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, x i) ^ 2 = ∑ i : Fin n, (x i) ^ 2 + 2 * elemSymm 2 x := by
  induction n with
  | zero =>
    have hzero : elemSymm 2 (x : Fin 0 → ℝ) = 0 := by
      apply Finset.sum_eq_zero; intro s hs
      exfalso
      have h2 := (Finset.mem_powersetCard.mp hs).2
      have h3 : s.card ≤ (univ : Finset (Fin 0)).card := Finset.card_le_card
        (Finset.mem_powersetCard.mp hs).1
      have h4 : (univ : Finset (Fin 0)).card = 0 := by simp
      omega
    simp [hzero]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
        elemSymm_two_succ, elemSymm_one (x ∘ Fin.castSucc)]
    simp only [Function.comp_apply]
    have hih := ih (x ∘ Fin.castSucc)
    simp only [Function.comp_apply] at hih
    nlinarith [sq_nonneg (∑ i : Fin k, x i.castSucc), sq_nonneg (x (Fin.last k))]

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
  -- Proved by induction on n using the recurrence e₂(x₀,...,xₙ) = e₂(x₀,...,xₙ₋₁) + xₙ·e₁
  have h_binom : (∑ i : Fin n, x i) ^ 2 =
      ∑ i : Fin n, (x i) ^ 2 + 2 * elemSymm 2 x :=
    sq_sum_eq_sum_sq_add_two_elemSymm x
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
## Part III: Maclaurin Means
-/

/-- The Maclaurin means, defined as Mₖ = (eₖ/C(n,k))^(1/k). -/
noncomputable def maclaurinMean {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  (elemSymm k x / (Nat.choose n k : ℝ)) ^ ((1 : ℝ) / k)

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
## Part V: General Recurrence and Structural Theorems
These theorems provide the infrastructure for inductive proofs on n
and establish boundary behavior of elementary symmetric polynomials.
-/

-- Generalized disjointness for powersetCard (k+1) vs image of insert on powersetCard k.
-- Same proof as pc_disj: any subset of mapped range cannot contain Fin.last.
private lemma pc_disj_general (n k : ℕ) :
    Disjoint
      (powersetCard (k + 1) ((univ : Finset (Fin n)).map (csEmb n)))
      ((powersetCard k ((univ : Finset (Fin n)).map (csEmb n))).image
        (insert (Fin.last n))) := by
  apply Finset.disjoint_left.mpr
  intro t ht1 ht2
  simp only [mem_image, Finset.mem_powersetCard] at ht1 ht2
  obtain ⟨s, _, rfl⟩ := ht2
  obtain ⟨ht1_sub, _⟩ := ht1
  have hmem := ht1_sub (Finset.mem_insert_self (Fin.last n) _)
  simp only [mem_map, mem_univ, true_and, csEmb_apply] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact (Fin.castSucc_lt_last i).ne hi

/-- General recurrence for elementary symmetric polynomials:
    eₖ₊₁(x₀,...,xₙ) = eₖ₊₁(x₀,...,xₙ₋₁) + xₙ · eₖ(x₀,...,xₙ₋₁)
    Generalizes elemSymm_two_succ from k=1 to arbitrary k.
    This is the essential tool for inductive proofs on n. -/
theorem elemSymm_succ {n : ℕ} (k : ℕ) (x : Fin (n + 1) → ℝ) :
    elemSymm (k + 1) x =
    elemSymm (k + 1) (x ∘ Fin.castSucc) +
    x (Fin.last n) * elemSymm k (x ∘ Fin.castSucc) := by
  simp only [elemSymm]
  rw [fin_univ_insert_last, Finset.powersetCard_succ_insert (fin_last_not_mem_map n)]
  rw [Finset.sum_union (pc_disj_general n k)]
  congr 1
  · rw [Finset.powersetCard_map, Finset.sum_map]
    congr 1; ext s
    simp only [mapEmb_eq]
    rw [prod_map_csEmb]
    simp only [Function.comp_apply]
  · have insert_inj : Set.InjOn (insert (Fin.last n))
        (powersetCard k ((univ : Finset (Fin n)).map (csEmb n))).toSet := by
      intro s hs t ht hst
      rw [Finset.mem_coe] at hs ht
      rw [Finset.mem_powersetCard] at hs ht
      have hs' : Fin.last n ∉ s := by
        intro hmem
        have h := hs.1 hmem
        simp only [mem_map, mem_univ, true_and, csEmb_apply] at h
        obtain ⟨i, hi⟩ := h
        exact (Fin.castSucc_lt_last i).ne hi
      have ht' : Fin.last n ∉ t := by
        intro hmem
        have h := ht.1 hmem
        simp only [mem_map, mem_univ, true_and, csEmb_apply] at h
        obtain ⟨i, hi⟩ := h
        exact (Fin.castSucc_lt_last i).ne hi
      rw [show s = (insert (Fin.last n) s).erase (Fin.last n) from
          (Finset.erase_insert hs').symm, hst, Finset.erase_insert ht']
    rw [Finset.sum_image insert_inj, Finset.powersetCard_map, Finset.sum_map]
    have h_prod : ∀ s ∈ (powersetCard k (univ : Finset (Fin n))),
        ∏ i ∈ insert (Fin.last n) ((Finset.mapEmbedding (csEmb n)).toEmbedding s), x i =
        x (Fin.last n) * ∏ j ∈ s, (x ∘ Fin.castSucc) j := by
      intro s _
      rw [mapEmb_eq, Finset.prod_insert]
      · simp only [Function.comp_apply]; rw [prod_map_csEmb]
      · simp only [mem_map, csEmb_apply, not_exists, not_and]
        intro j _; exact (Fin.castSucc_lt_last j).ne
    rw [Finset.sum_congr rfl h_prod, ← Finset.mul_sum]

/-- eₖ = 0 when k > n (no k-element subsets of an n-element set). -/
theorem elemSymm_gt_eq_zero {n : ℕ} (k : ℕ) (hk : n < k) (x : Fin n → ℝ) :
    elemSymm k x = 0 := by
  simp only [elemSymm]
  apply Finset.sum_eq_zero
  intro s hs
  exfalso
  have h1 := (Finset.mem_powersetCard.mp hs).2
  have h2 : s.card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.mem_powersetCard.mp hs).1
  simp only [card_univ, Fintype.card_fin] at h2
  omega

/-- eₙ(x₀,...,xₙ₋₁) = ∏ᵢ xᵢ (the only n-element subset of Fin n is the full set). -/
theorem elemSymm_n_eq_prod {n : ℕ} (x : Fin n → ℝ) :
    elemSymm n x = ∏ i : Fin n, x i := by
  simp only [elemSymm]
  have h_uniq : (univ : Finset (Fin n)).powersetCard n = {univ} := by
    ext s
    simp only [mem_powersetCard, mem_singleton, subset_univ, true_and]
    constructor
    · intro h; exact Finset.eq_univ_of_card s (by rwa [Fintype.card_fin])
    · intro h; rw [h, Finset.card_univ, Fintype.card_fin]
  rw [h_uniq, Finset.sum_singleton]
