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

/-! ### Deriving the Maclaurin step from Newton's log-concavity

`maclaurin_step` below is no longer an axiom: it is a theorem derived from
`newton_log_concavity` alone, via the logarithm-free, product-free multiplicative
core `p_{k+1}^k ≤ p_k^{k+1}` (`maclaurin_core_of_pos`) and a crossed root extraction
(`rpow_cross`). The general non-negative case is handled by a "zeros form a suffix"
argument (`elemSymm_pos_of_top_pos`). See `Hardy–Littlewood–Pólya §2.22`. -/

/-- For strictly positive inputs and `k ≤ n`, the k-th symmetric polynomial is
    strictly positive (the index set of size-k subsets is nonempty). -/
theorem elemSymm_pos {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) : 0 < elemSymm k x := by
  unfold elemSymm
  apply Finset.sum_pos
  · intro s _
    exact Finset.prod_pos (fun i _ => hx i)
  · rw [← Finset.card_pos, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin]
    exact Nat.choose_pos hk

/-- **Zeros form a suffix (single step).** For non-negative inputs, if the
    `(j+1)`-st elementary symmetric polynomial is positive, then so is the `j`-th.
    A positive `e_{j+1}` means some `(j+1)`-subset `S` has all-positive product, hence
    all its entries are positive; any `j`-subset `T ⊆ S` then has positive product and
    is one of the (non-negative) summands of `e_j`, forcing `e_j > 0`. -/
theorem elemSymm_pred_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    {j : ℕ} (hjn : j + 1 ≤ n) (h : 0 < elemSymm (j + 1) x) : 0 < elemSymm j x := by
  rw [elemSymm] at h
  obtain ⟨S, hS, hSne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  have hSpos : 0 < ∏ i ∈ S, x i :=
    lt_of_le_of_ne (Finset.prod_nonneg (fun i _ => hx i)) (Ne.symm hSne)
  have hSx : ∀ i ∈ S, 0 < x i := by
    intro i hi
    rcases (hx i).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (Finset.prod_eq_zero hi h'.symm) hSpos.ne'
  have hScard : S.card = j + 1 := (Finset.mem_powersetCard.1 hS).2
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show j ≤ S.card by omega)
  have hTmem : T ∈ (univ : Finset (Fin n)).powersetCard j :=
    Finset.mem_powersetCard.2 ⟨Finset.subset_univ T, hTcard⟩
  have hTpos : 0 < ∏ i ∈ T, x i := Finset.prod_pos (fun i hi => hSx i (hTS hi))
  calc 0 < ∏ i ∈ T, x i := hTpos
    _ ≤ elemSymm j x := by
        rw [elemSymm]
        exact Finset.single_le_sum (f := fun s => ∏ i ∈ s, x i)
          (fun s _ => Finset.prod_nonneg (fun i _ => hx i)) hTmem

/-- **Zeros form a suffix (prefix form).** For non-negative inputs, if `e_K > 0` then
    `e_j > 0` for every `j ≤ K`. Iterates `elemSymm_pred_pos` down from `K`. -/
theorem elemSymm_pos_of_top_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ K, K ≤ n → 0 < elemSymm K x → ∀ j, j ≤ K → 0 < elemSymm j x := by
  intro K
  induction K with
  | zero =>
    intro _ _ j hj
    rw [Nat.le_zero.1 hj, elemSymm_zero]; exact one_pos
  | succ m ih =>
    intro hK hpos j hj
    have hmpos : 0 < elemSymm m x := elemSymm_pred_pos x hx hK hpos
    rcases Nat.eq_or_lt_of_le hj with h | h
    · rw [h]; exact hpos
    · exact ih (by omega) hmpos j (by omega)

/-- The normalized symmetric mean pₖ = eₖ / C(n,k). -/
noncomputable def normElemSymm {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  elemSymm k x / (n.choose k : ℝ)

/-- p₀ = 1. -/
theorem normElemSymm_zero {n : ℕ} (x : Fin n → ℝ) : normElemSymm 0 x = 1 := by
  simp [normElemSymm, elemSymm_zero, Nat.choose_zero_right]

/-- pₖ > 0 for strictly positive inputs and `k ≤ n`. -/
theorem normElemSymm_pos {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) : 0 < normElemSymm k x := by
  apply div_pos (elemSymm_pos k hk x hx)
  exact_mod_cast Nat.choose_pos hk

/-- The multiplicative Maclaurin core, **from positivity of the normalized means**:
    `p_{k+1}^k ≤ p_k^{k+1}`, proved from Newton's log-concavity by induction on `k`,
    using ONLY `ℕ`-powers. The positivity hypothesis is on the `pⱼ` (not on the inputs
    `xᵢ`), so this version applies to the non-negative case once the prefix lemma
    `elemSymm_pos_of_top_pos` supplies `0 < pⱼ` for `j ≤ k+1` from `e_{k+1} > 0`. -/
theorem maclaurin_core_of_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ k : ℕ, k + 1 ≤ n → (∀ j, j ≤ k + 1 → 0 < normElemSymm j x) →
      normElemSymm (k + 1) x ^ k ≤ normElemSymm k x ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _ _
    simp [normElemSymm_zero]
  | succ m ih =>
    intro hk hpos
    have hm : m + 1 ≤ n := by omega
    have IH := ih hm (fun j hj => hpos j (by omega))
    have hA : 0 < normElemSymm m x := hpos m (by omega)
    have hB : 0 < normElemSymm (m + 1) x := hpos (m + 1) (by omega)
    have hC : 0 < normElemSymm (m + 2) x := hpos (m + 2) (by omega)
    have hNewton : normElemSymm m x * normElemSymm (m + 2) x
        ≤ normElemSymm (m + 1) x ^ 2 := by
      have h := newton_log_concavity (m + 1) (by omega) (by omega) x hx
      simp only [Nat.add_sub_cancel] at h
      exact h
    have hAC : (normElemSymm m x * normElemSymm (m + 2) x) ^ (m + 1)
        ≤ (normElemSymm (m + 1) x ^ 2) ^ (m + 1) :=
      pow_le_pow_left₀ (mul_nonneg hA.le hC.le) hNewton (m + 1)
    rw [mul_pow, ← pow_mul] at hAC
    have hsplit : normElemSymm (m + 1) x ^ (2 * (m + 1))
        = normElemSymm (m + 1) x ^ m * normElemSymm (m + 1) x ^ (m + 2) := by
      rw [← pow_add]; congr 1; omega
    have hIH2 : normElemSymm (m + 1) x ^ m * normElemSymm (m + 1) x ^ (m + 2)
        ≤ normElemSymm m x ^ (m + 1) * normElemSymm (m + 1) x ^ (m + 2) :=
      mul_le_mul_of_nonneg_right IH (pow_nonneg hB.le _)
    have hcomb : normElemSymm m x ^ (m + 1) * normElemSymm (m + 2) x ^ (m + 1)
        ≤ normElemSymm m x ^ (m + 1) * normElemSymm (m + 1) x ^ (m + 2) := by
      calc normElemSymm m x ^ (m + 1) * normElemSymm (m + 2) x ^ (m + 1)
            ≤ normElemSymm (m + 1) x ^ (2 * (m + 1)) := hAC
        _ = normElemSymm (m + 1) x ^ m * normElemSymm (m + 1) x ^ (m + 2) := hsplit
        _ ≤ normElemSymm m x ^ (m + 1) * normElemSymm (m + 1) x ^ (m + 2) := hIH2
    exact le_of_mul_le_mul_left hcomb (pow_pos hA _)

/-- If `b^s ≤ a^t` for positive reals and positive naturals, then taking the
    appropriate crossed roots gives `b^(1/t) ≤ a^(1/s)`. -/
theorem rpow_cross {a b : ℝ} {s t : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (ht : 0 < t) (h : b ^ s ≤ a ^ t) :
    b ^ ((1 : ℝ) / t) ≤ a ^ ((1 : ℝ) / s) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have key : (b ^ s) ^ ((1 : ℝ) / (s * t)) ≤ (a ^ t) ^ ((1 : ℝ) / (s * t)) :=
    Real.rpow_le_rpow (pow_nonneg hb.le s) h (by positivity)
  have lhs : (b ^ s) ^ ((1 : ℝ) / (s * t)) = b ^ ((1 : ℝ) / t) := by
    rw [← Real.rpow_natCast b s, ← Real.rpow_mul hb.le]
    congr 1
    field_simp
  have rhs : (a ^ t) ^ ((1 : ℝ) / (s * t)) = a ^ ((1 : ℝ) / s) := by
    rw [← Real.rpow_natCast a t, ← Real.rpow_mul ha.le]
    congr 1
    field_simp
  rwa [lhs, rhs] at key

/-- **Maclaurin's step inequality**, now a THEOREM derived from
    `newton_log_concavity` alone (formerly an axiom): `Mₖ ≥ Mₖ₊₁` for all
    non-negative inputs. Case split on `e_{k+1}`: if `e_{k+1} = 0` then
    `Mₖ₊₁ = 0 ≤ Mₖ`; if `e_{k+1} > 0` then every `pⱼ` (`j ≤ k+1`) is positive
    (`elemSymm_pos_of_top_pos`), so the multiplicative core `maclaurin_core_of_pos`
    plus the crossed root extraction `rpow_cross` give the step. -/
theorem maclaurin_step {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean k x ≥ maclaurinMean (k + 1) x := by
  by_cases hek1 : 0 < elemSymm (k + 1) x
  · have hpos : ∀ j, j ≤ k + 1 → 0 < normElemSymm j x := by
      intro j hj
      have hej : 0 < elemSymm j x :=
        elemSymm_pos_of_top_pos x hx (k + 1) hkn hek1 j hj
      exact div_pos hej (by exact_mod_cast Nat.choose_pos (le_trans hj hkn))
    have hcore := maclaurin_core_of_pos x hx k hkn hpos
    have hp : 0 < normElemSymm k x := hpos k (by omega)
    have hq : 0 < normElemSymm (k + 1) x := hpos (k + 1) (le_refl _)
    have hstep := rpow_cross hp hq hk (Nat.succ_pos k) hcore
    simpa only [maclaurinMean, normElemSymm] using hstep
  · have hzero : elemSymm (k + 1) x = 0 :=
      le_antisymm (not_lt.1 hek1) (elemSymm_nonneg (k + 1) x hx)
    have hMk1 : maclaurinMean (k + 1) x = 0 := by
      rw [maclaurinMean, hzero, zero_div, Real.zero_rpow (by positivity)]
    rw [ge_iff_le, hMk1, maclaurinMean]
    exact Real.rpow_nonneg (div_nonneg (elemSymm_nonneg k x hx) (by positivity)) _

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
## Part V: Non-Negative Maclaurin Chain Theorems
-/

/-- M₁² ≥ M₂ for non-negative inputs, via Newton's log-concavity at k=1.
    Newton gives: ((∑xᵢ)/n)² ≥ e₂/C(n,2), which is C(n,2)·(∑xᵢ)² ≥ n²·e₂. -/
theorem maclaurin_sq_m1_ge_m2_from_newton {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    (Nat.choose n 2 : ℝ) * (∑ i, x i) ^ 2 ≥ (n : ℝ) ^ 2 * elemSymm 2 x := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hC2_pos : (0 : ℝ) < (Nat.choose n 2 : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega : 2 ≤ n))
  have h_newton := newton_log_concavity 1 le_rfl (by omega : 1 + 1 ≤ n) x hx
  simp only [show (1 - 1 : ℕ) = 0 from rfl, show (1 + 1 : ℕ) = 2 from rfl,
             elemSymm_zero, elemSymm_one, Nat.choose_zero_right, Nat.choose_one_right,
             Nat.cast_one, div_one, one_mul] at h_newton
  -- h_newton : ((∑ i, x i) / ↑n) ^ 2 ≥ elemSymm 2 x / ↑(Nat.choose n 2)
  have hnn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hn_pos 2
  have key : elemSymm 2 x * (n : ℝ) ^ 2 ≤ (∑ i : Fin n, x i) ^ 2 * (Nat.choose n 2 : ℝ) := by
    -- Cross-multiply: e₂/C ≤ S²/n² implies e₂·n² ≤ S²·C (for C, n² > 0)
    have h1 : 0 ≤ ((∑ i : Fin n, x i) / (n : ℝ)) ^ 2 - elemSymm 2 x / (Nat.choose n 2 : ℝ) :=
      sub_nonneg.mpr h_newton
    have h2 : 0 < (n : ℝ) ^ 2 * (Nat.choose n 2 : ℝ) := mul_pos hnn2_pos hC2_pos
    have h3 : 0 ≤ (((∑ i : Fin n, x i) / (n : ℝ)) ^ 2 -
                   elemSymm 2 x / (Nat.choose n 2 : ℝ)) *
                  ((n : ℝ) ^ 2 * (Nat.choose n 2 : ℝ)) := mul_nonneg h1 h2.le
    have h4 : (((∑ i : Fin n, x i) / (n : ℝ)) ^ 2 -
               elemSymm 2 x / (Nat.choose n 2 : ℝ)) *
              ((n : ℝ) ^ 2 * (Nat.choose n 2 : ℝ)) =
              (∑ i : Fin n, x i) ^ 2 * (Nat.choose n 2 : ℝ) - elemSymm 2 x * (n : ℝ) ^ 2 := by
      field_simp [hn_pos.ne', hC2_pos.ne']
    linarith [h4 ▸ h3]
  linarith

/-- The Maclaurin chain: Mⱼ ≥ Mₖ for 0 < j ≤ k ≤ n.
    Proved by induction on k - j using the maclaurin_step axiom. -/
theorem maclaurin_chain {n : ℕ} (j k : ℕ) (hj : 0 < j) (hjk : j ≤ k) (hkn : k ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean j x ≥ maclaurinMean k x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  revert hkn
  induction d with
  | zero => intro; simp
  | succ e ih =>
    intro hkn
    have hstep : maclaurinMean (j + e) x ≥ maclaurinMean (j + e + 1) x :=
      maclaurin_step (j + e) (by omega) (by omega) x hx
    have h_eq : j + (e + 1) = j + e + 1 := by omega
    rw [h_eq]
    have h_e_le : j + e ≤ n := by omega
    have hih := ih (Nat.le_add_right j e) h_e_le
    calc maclaurinMean j x
        ≥ maclaurinMean (j + e) x := hih
      _ ≥ maclaurinMean (j + e + 1) x := hstep

/-- The first Maclaurin mean dominates the last: M₁ ≥ Mₙ (AM ≥ GM in disguise). -/
theorem maclaurin_m1_ge_mn {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean 1 x ≥ maclaurinMean n x :=
  maclaurin_chain 1 n (by omega) (by omega) le_rfl x hx

/-
## Part VI: General Recurrence and Structural Theorems
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

/-- Newton's inequality for k=1, proved WITHOUT the newton_log_concavity axiom.
    (e₁/C(n,1))² ≥ (e₀/C(n,0)) · (e₂/C(n,2))
    Equivalently: C(n,2)·(∑xᵢ)² ≥ n²·e₂, which follows from the binomial
    identity and Cauchy-Schwarz. Works for ALL reals, not just non-negative. -/
theorem newton_k1 {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    (elemSymm 1 x / (Nat.choose n 1 : ℝ)) ^ 2 ≥
    (elemSymm 0 x / (Nat.choose n 0 : ℝ)) *
    (elemSymm 2 x / (Nat.choose n 2 : ℝ)) := by
  simp only [elemSymm_zero, elemSymm_one, Nat.choose_zero_right, Nat.choose_one_right,
             Nat.cast_one, div_one, one_mul]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hC_pos : (0 : ℝ) < (↑(Nat.choose n 2) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hN_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hC_ne : (↑(Nat.choose n 2) : ℝ) ≠ 0 := ne_of_gt hC_pos
  have h := maclaurin_sq_m1_ge_m2_general hn x
  rw [ge_iff_le, ← sub_nonneg, div_pow]
  have hdiff : (∑ i : Fin n, x i) ^ 2 / (n : ℝ) ^ 2 -
      elemSymm 2 x / (↑(Nat.choose n 2) : ℝ) =
      ((↑(Nat.choose n 2) : ℝ) * (∑ i : Fin n, x i) ^ 2 -
       (n : ℝ) ^ 2 * elemSymm 2 x) / ((n : ℝ) ^ 2 * (↑(Nat.choose n 2) : ℝ)) := by
    field_simp
  rw [hdiff]
  exact div_nonneg (by linarith) (le_of_lt (mul_pos (pow_pos hn_pos 2) hC_pos))

/-
## Part VII: The chain endpoints ARE the arithmetic and geometric means

`maclaurin_m1_ge_mn` (`M₁ ≥ Mₙ`) is repeatedly described as "AM ≥ GM in disguise",
but until now the file never machine-checked that the two endpoints of the chain
literally *are* the arithmetic and geometric means. These identities close that gap:
`M₁ = (∑ xᵢ)/n` (arithmetic mean) and `Mₙ = (∏ xᵢ)^(1/n)` (geometric mean), so the
top-to-bottom Maclaurin chain collapses to the AM–GM inequality itself. Unlike
`amgm_from_maclaurin` (which invokes Mathlib's weighted AM–GM as a black box), the
capstone `maclaurin_chain_amgm` obtains AM–GM *through the Maclaurin chain*, i.e. from
`newton_log_concavity` alone. No new axioms.
-/

/-- **The first Maclaurin mean is the arithmetic mean.** `M₁ = (∑ xᵢ)/n`, since
`e₁ = ∑ xᵢ`, `C(n,1) = n`, and the exponent `1/1 = 1`. -/
theorem maclaurinMean_one {n : ℕ} (x : Fin n → ℝ) :
    maclaurinMean 1 x = (∑ i, x i) / n := by
  simp only [maclaurinMean, elemSymm_one, Nat.choose_one_right, Nat.cast_one, div_one,
    Real.rpow_one]

/-- **The last Maclaurin mean is the geometric mean.** `Mₙ = (∏ xᵢ)^(1/n)`, since
`eₙ = ∏ xᵢ` (`elemSymm_n_eq_prod`) and `C(n,n) = 1`. -/
theorem maclaurinMean_top_eq_geom {n : ℕ} (x : Fin n → ℝ) :
    maclaurinMean n x = (∏ i, x i) ^ ((1 : ℝ) / n) := by
  rw [maclaurinMean, elemSymm_n_eq_prod, Nat.choose_self, Nat.cast_one, div_one]

/-- **AM–GM through the Maclaurin chain.** `(∏ xᵢ)^(1/n) ≤ (∑ xᵢ)/n` for non-negative
inputs, obtained by identifying the endpoints of `maclaurin_m1_ge_mn` (`M₁ ≥ Mₙ`) with
the arithmetic and geometric means via `maclaurinMean_one` / `maclaurinMean_top_eq_geom`.
This is the AM–GM inequality derived *through* the Maclaurin chain — hence from
`newton_log_concavity` alone — rather than from Mathlib's weighted AM–GM
(`amgm_from_maclaurin`). No new axioms. -/
theorem maclaurin_chain_amgm {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    (∏ i, x i) ^ ((1 : ℝ) / n) ≤ (∑ i, x i) / n := by
  have h := maclaurin_m1_ge_mn hn x hx
  rw [maclaurinMean_one, maclaurinMean_top_eq_geom] at h
  exact h

/-
## Summary

### The Main Answer:
Maclaurin's inequalities M₁ ≥ M₂ ≥ ⋯ ≥ Mₙ hold for non-negative reals,
where Mₖ = (eₖ/C(n,k))^(1/k) and eₖ is the k-th elementary symmetric polynomial.
The chain follows from Newton's log-concavity inequalities for the sequence eₖ/C(n,k).

### Proved (no sorry):
1. `elemSymm_zero` — e₀ = 1
2. `elemSymm_one` — e₁ = ∑ xᵢ
3. `elemSymm_nonneg` — non-negative inputs give non-negative eₖ
4. `maclaurin_m1_ge_m2_n2` — AM ≥ GM for n=2 (classical, via (√a-√b)² ≥ 0)
5. `maclaurin_m1sq_ge_m2_n3` — (M₁)² ≥ M₂ for n=3 (via nlinarith + sq_nonneg)
6. `maclaurin_m1sq_ge_m2_n4` — (M₁)² ≥ M₂ for n=4 (via nlinarith + sq_nonneg)
7. `maclaurinMean_nonneg` — Maclaurin means are non-negative
8. `amgm_from_maclaurin` — AM-GM from Mathlib weighted AM-GM
9. `sq_sum_eq_sum_sq_add_two_elemSymm` — (∑xᵢ)² = ∑xᵢ² + 2·e₂ (binomial identity, by induction)
10. `maclaurin_sq_m1_ge_m2_general` — general (∑xᵢ)²·C(n,2) ≥ n²·e₂ (all reals, via binomial id)
11. `maclaurin_sq_m1_ge_m2_from_newton` — C(n,2)·(∑xᵢ)² ≥ n²·e₂ (non-negative, Newton)
12. `maclaurin_chain` — Mⱼ ≥ Mₖ for j ≤ k ≤ n (induction on k-j via maclaurin_step)
13. `maclaurin_m1_ge_mn` — M₁ ≥ Mₙ, i.e., AM ≥ GM (corollary of chain)
14. `elemSymm_succ` — general recurrence eₖ₊₁(x₁,...,xₙ₊₁) = eₖ₊₁(x₁,...,xₙ) + xₙ₊₁·eₖ(x₁,...,xₙ)
15. `elemSymm_gt_eq_zero` — eₖ = 0 for k > n
16. `elemSymm_n_eq_prod` — eₙ = ∏ xᵢ
17. `newton_k1` — Newton's inequality at k=1, proved from scratch (no axiom)
18. `maclaurinMean_one` — M₁ = (∑ xᵢ)/n (first Maclaurin mean is the arithmetic mean)
19. `maclaurinMean_top_eq_geom` — Mₙ = (∏ xᵢ)^(1/n) (last is the geometric mean)
20. `maclaurin_chain_amgm` — (∏ xᵢ)^(1/n) ≤ (∑ xᵢ)/n, AM-GM through the chain (from Newton alone)

### Axiomatized (deep results):
1. `newton_log_concavity` — log-concavity of eₖ/C(n,k) for non-negative inputs
2. `maclaurin_step` — Mₖ ≥ Mₖ₊₁ for consecutive Maclaurin means
-/
