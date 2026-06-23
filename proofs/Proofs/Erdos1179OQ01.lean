/-
Erdős Problem #1179 - Open Question 01:
What is the precise second-order term in g_ε(N)?

Source: https://erdosproblems.com/1179

The main asymptotic g_ε(N) ~ log₂ N is known. The open question asks:
what is the precise form of the correction term?

Known bounds:
- Lower: g_ε(N) ≥ log₂ N (trivial)
- Upper: g_ε(N) ≤ log₂ N · (1 + O_ε(log log log N / log log N)) (Erdős-Hall)

The gap leaves the second-order term unknown. We formalize the question
and prove foundational results about representation counts in ℤ/Nℤ.

References:
- [ErRe65] Erdős, Rényi (1965)
- [ErHa76] Erdős, Hall (1976)
-/

import Mathlib

namespace Erdos1179OQ01

open Finset Real

/-
## Part I: Representation counts in ℤ/Nℤ

We work concretely in ℤ/Nℤ to make proofs more tractable.
-/

/-- The representation count: number of subsets of A that sum to g. -/
noncomputable def reprCount {N : ℕ} (A : Finset (ZMod N)) (g : ZMod N) : ℕ :=
  (A.powerset.filter (fun S => S.sum id = g)).card

/-- Total representations partition: ∑_g F_A(g) = 2^|A|. -/
theorem total_reprCount {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (∑ g : ZMod N, reprCount A g) = 2 ^ A.card := by
  simp only [reprCount]
  rw [← card_powerset A]
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro S _
  exact Finset.mem_univ (S.sum id)

/-- The empty set has exactly one representation of 0. -/
theorem reprCount_empty_zero {N : ℕ} [NeZero N] :
    reprCount (∅ : Finset (ZMod N)) (0 : ZMod N) = 1 := by
  simp [reprCount, powerset_empty, filter_singleton, sum_empty]

/-- The empty set has no representations of nonzero elements. -/
theorem reprCount_empty_nonzero {N : ℕ} [NeZero N]
    (g : ZMod N) (hg : g ≠ 0) :
    reprCount (∅ : Finset (ZMod N)) g = 0 := by
  simp [reprCount, powerset_empty, filter_singleton, sum_empty, hg.symm]

/-
## Part II: Monotonicity under set growth
-/

/-- Adding an element to A doesn't decrease reprCount for any g.
    Proof: every subset of A is also a subset of A ∪ {b}. -/
theorem reprCount_insert_ge {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (b : ZMod N) (g : ZMod N) (hb : b ∉ A) :
    reprCount A g ≤ reprCount (insert b A) g := by
  simp only [reprCount]
  apply Finset.card_le_card
  intro S hS
  rw [mem_filter] at hS ⊢
  exact ⟨mem_powerset.mpr ((mem_powerset.mp hS.1).trans (subset_insert b A)), hS.2⟩

/-- Representation counts are nonneg (trivially, as they're natural numbers). -/
theorem reprCount_nonneg {N : ℕ} (A : Finset (ZMod N)) (g : ZMod N) :
    0 ≤ reprCount A g := Nat.zero_le _

/-
## Part III: Representation count of a singleton
-/

/-- For a singleton {a}, the only subsets are ∅ and {a}.
    ∅ sums to 0, {a} sums to a.
    So reprCount {a} g = (if g = 0 then 1 else 0) + (if g = a then 1 else 0). -/
theorem reprCount_singleton_le_two {N : ℕ} [NeZero N]
    (a : ZMod N) (g : ZMod N) :
    reprCount {a} g ≤ 2 := by
  simp only [reprCount]
  calc (({a} : Finset (ZMod N)).powerset.filter (fun S => S.sum id = g)).card
      ≤ ({a} : Finset (ZMod N)).powerset.card := card_filter_le _ _
    _ = 2 ^ ({a} : Finset (ZMod N)).card := card_powerset _
    _ = 2 := by simp

/-
## Part IV: Total coverage grows with set size
-/

/-- The number of elements with nonzero representation is monotone in A. -/
theorem coverage_mono {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (b : ZMod N) (hb : b ∉ A) :
    (Finset.univ.filter (fun g : ZMod N => 0 < reprCount A g)).card ≤
    (Finset.univ.filter (fun g : ZMod N => 0 < reprCount (insert b A) g)).card := by
  apply Finset.card_le_card
  intro g hg
  rw [mem_filter] at hg ⊢
  exact ⟨mem_univ g, lt_of_lt_of_le hg.2 (reprCount_insert_ge A b g hb)⟩

/-
## Part V: The second-order term question
-/

/-- The correction term: g_ε(N) - log₂ N. -/
noncomputable def correctionTerm (gEps : ℝ → ℕ → ℕ) (ε : ℝ) (N : ℕ) : ℝ :=
  (gEps ε N : ℝ) - Real.logb 2 ↑N

/-- The correction is o(log₂ N) — follows from the main asymptotic. -/
def CorrectionIsSublinearInLog (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    |correctionTerm gEps ε N| < δ * Real.logb 2 ↑N

/-- The correction is O(1) — strongest possible (open). -/
def CorrectionIsBounded (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    |correctionTerm gEps ε N| ≤ C

/-- The correction is Θ(log log N) — conjectured by analogy with Problem #543. -/
def CorrectionIsLogLog (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    c₁ * Real.log (Real.log ↑N) ≤ correctionTerm gEps ε N ∧
    correctionTerm gEps ε N ≤ c₂ * Real.log (Real.log ↑N)

/-- O(1) implies o(log N) — the hierarchy is well-ordered.
    Proof: if |correction| ≤ C for all N, then for N large enough,
    logb 2 N > C/δ, so C < δ · logb 2 N. -/
theorem bounded_implies_sublinear (gEps : ℝ → ℕ → ℕ) (ε : ℝ)
    (h : CorrectionIsBounded gEps ε) : CorrectionIsSublinearInLog gEps ε := by
  intro δ hδ
  obtain ⟨C, hC, hbound⟩ := h
  set m := Nat.ceil (C / δ) + 2
  use 2 ^ m
  intro N hN
  have hN2 : N ≥ 2 := by
    have : 2 ≤ 2 ^ m := le_trans (show 2 ≤ 2 ^ 1 from le_refl _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hm_bound : (m : ℝ) > C / δ + 1 := by
    show (↑(Nat.ceil (C / δ) + 2) : ℝ) > C / δ + 1
    push_cast; linarith [Nat.le_ceil (C / δ)]
  -- logb 2 N ≥ m (since N ≥ 2^m and logb 2 (2^m) = m)
  have hNlog : Real.logb 2 (N : ℝ) ≥ ↑m := by
    have hN_le : (2 : ℝ) ^ (m : ℕ) ≤ (N : ℝ) := by exact_mod_cast hN
    have key : Real.logb 2 ((2 : ℝ) ^ (m : ℕ)) = ↑m := by
      rw [show ((2 : ℝ) ^ (m : ℕ)) = ((2 : ℝ) ^ ((m : ℕ) : ℝ)) from
        (rpow_natCast 2 m).symm]
      exact Real.logb_rpow (by norm_num) (by norm_num)
    have mono : Real.logb 2 ((2 : ℝ) ^ (m : ℕ)) ≤ Real.logb 2 (N : ℝ) := by
      simp only [Real.logb]
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) hN_le)
        (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2)))
    linarith
  calc |correctionTerm gEps ε N| ≤ C := hbound N (by omega)
    _ < δ * (C / δ + 1) := by
        have : δ * (C / δ + 1) = C + δ := by field_simp
        linarith
    _ < δ * ↑m := by nlinarith
    _ ≤ δ * Real.logb 2 ↑N := by nlinarith

/-
## Part V-A: Fourier infrastructure for ℤ/pℤ

We develop the minimal discrete Fourier analysis on ℤ/pℤ needed for the
error bound. The key identity: for A ⊆ ℤ/pℤ of size k,

  F_A(g) = (1/p) ∑_{j=0}^{p-1} ω^{-jg} · ∏_{a∈A} (1 + ω^{ja})

where ω = exp(2πi/p). The j=0 term gives 2^k/p; bounding the j≠0 terms
gives the error bound.

Infrastructure adapted from RothTheorem.lean's Fourier analysis section.
-/

/-- Primitive p-th root of unity ω = exp(2πi/p). -/
private noncomputable def ωp (p : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I / ↑p)

/-- ω^p = 1: the root of unity has order dividing p. -/
private lemma ωp_pow_eq_one (p : ℕ) [NeZero p] : ωp p ^ p = 1 := by
  simp only [ωp, ← Complex.exp_nat_mul]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [show (↑p : ℂ) * (2 * ↑Real.pi * Complex.I / ↑p) =
      2 * ↑Real.pi * Complex.I from by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- |ω^n| = 1: every power of ω lies on the unit circle. -/
private lemma ωp_pow_norm (p n : ℕ) [NeZero p] : ‖ωp p ^ n‖ = 1 := by
  rw [norm_pow]
  suffices h : ‖ωp p‖ = 1 by rw [h, one_pow]
  simp only [ωp, Complex.norm_exp]
  have : (2 * ↑Real.pi * Complex.I / (↑p : ℂ)).re = 0 := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I / ↑p =
        ↑(2 * Real.pi / (p : ℝ)) * Complex.I from by push_cast; ring]
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [this, Real.exp_zero]

/-- ω ≠ 0 (it lies on the unit circle). -/
private lemma ωp_ne_zero (p : ℕ) [NeZero p] : ωp p ≠ 0 := by
  intro h; have := ωp_pow_norm p 1; simp [h] at this

/-- The additive character ψ_p(x) = ω^{val(x)} on ℤ/pℤ. -/
private noncomputable def ψp {p : ℕ} (x : ZMod p) : ℂ :=
  ωp p ^ ZMod.val x

/-- ψ has norm 1. -/
private lemma ψp_norm {p : ℕ} [NeZero p] (x : ZMod p) : ‖ψp x‖ = 1 :=
  ωp_pow_norm p (ZMod.val x)

/-- ψ(0) = 1. -/
private lemma ψp_zero {p : ℕ} [NeZero p] : ψp (0 : ZMod p) = 1 := by
  simp [ψp, ZMod.val_zero]

/-- ω^{a % p} = ω^a, since ω^p = 1. -/
private lemma ωp_pow_mod (p a : ℕ) [NeZero p] : ωp p ^ (a % p) = ωp p ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a p]
  rw [pow_add, pow_mul, ωp_pow_eq_one, one_pow, one_mul]

/-- ψ is an additive character: ψ(x + y) = ψ(x) · ψ(y). -/
private lemma ψp_add {p : ℕ} [NeZero p] (x y : ZMod p) :
    ψp (x + y) = ψp x * ψp y := by
  simp only [ψp, ← pow_add]
  rw [ZMod.val_add x y]
  exact ωp_pow_mod p (ZMod.val x + ZMod.val y)

/-- ψ distributes over negation: ψ(-x) · ψ(x) = 1. -/
private lemma ψp_neg_mul {p : ℕ} [NeZero p] (x : ZMod p) :
    ψp (-x) * ψp x = 1 := by
  rw [← ψp_add, neg_add_cancel, ψp_zero]

/-- ψ distributes over Finset.sum: ψ(∑ f) = ∏ ψ(f i). -/
private lemma ψp_sum {p : ℕ} [NeZero p] {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    ψp (s.sum f) = ∏ i ∈ s, ψp (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [ψp_zero]
  | cons a s ha ih => rw [Finset.sum_cons, ψp_add, ih, Finset.prod_cons]

/-- Character orthogonality on ℤ/pℤ:
    ∑_j ψ(j·c) = p if c = 0, and 0 if c ≠ 0.
    The c≠0 case uses the geometric sum formula with ψ(c)^p = 1. -/
private lemma character_orthogonality {p : ℕ} (hp : Nat.Prime p) (c : ZMod p) :
    ∑ j : ZMod p, ψp (j * c) = if c = 0 then ↑p else 0 := by
  split
  · -- c = 0: each term is ψ(0) = 1, sum = p
    rename_i hc; subst hc
    simp only [mul_zero, ψp_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_one]
  · -- c ≠ 0: shift argument. S = ψ(c) · S and ψ(c) ≠ 1, so S = 0.
    rename_i hc
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    -- Step 1: ψp(c) ≠ 1 when c ≠ 0
    have hψp_ne : ψp c ≠ 1 := by
      simp only [ψp, ωp, ← Complex.exp_nat_mul]
      have hval_pos : 0 < ZMod.val c :=
        Nat.pos_of_ne_zero (fun h => hc (ZMod.val_eq_zero.mp h))
      have hval_lt : ZMod.val c < p := ZMod.val_lt c
      intro h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      -- hn : val(c) * (2πI/p) = n * (2πI)
      have hpi_ne : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero
      have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      -- From hn: val(c)/p = n
      have heq : (↑(ZMod.val c) : ℂ) / ↑p = ↑n :=
        mul_left_cancel₀ hpi_ne (by rw [hn]; ring)
      -- So val(c) = n * p as integers
      have heq_int : (ZMod.val c : ℤ) = n * ↑p := by
        have h := heq; rw [div_eq_iff hp_ne] at h; exact_mod_cast h
      -- But 0 < val(c) < p, contradiction
      have hp_pos : (0 : ℤ) < ↑p := Int.natCast_pos.mpr hp.pos
      have hvc_pos : (0 : ℤ) < ↑(ZMod.val c) := Int.natCast_pos.mpr hval_pos
      have hvc_lt : (↑(ZMod.val c) : ℤ) < ↑p := Int.natCast_lt.mpr hval_lt
      rcases le_or_gt n 0 with hn_le | hn_gt
      · linarith [mul_nonpos_of_nonpos_of_nonneg hn_le hp_pos.le]
      · linarith [mul_le_mul_of_nonneg_right (show 1 ≤ n by omega) hp_pos.le]
    -- Step 2: ψp(c) · S = S via shift j ↦ j + 1
    set S := ∑ j : ZMod p, ψp (j * c) with hS_def
    have hshift : ψp c * S = S := by
      rw [hS_def, Finset.mul_sum]
      -- ψ(c) · ψ(j·c) = ψ(c + j·c) = ψ((j+1)·c)
      have hstep : ∀ j : ZMod p, ψp c * ψp (j * c) = ψp ((j + 1) * c) := by
        intro j; rw [← ψp_add, show c + j * c = (j + 1) * c from by ring]
      simp_rw [hstep]
      -- Reindex: sum over j of f(j+1) = sum over j of f(j)
      apply Finset.sum_equiv (Equiv.addRight (1 : ZMod p))
      · intro r; simp
      · intro r _; ring_nf
    -- Step 3: (ψp(c) - 1) · S = 0, and ψp(c) - 1 ≠ 0, so S = 0
    have h0 : (ψp c - 1) * S = 0 := by rw [sub_mul, one_mul, hshift, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hψp_ne)

/-- Fourier expansion of reprCount.
    reprCount A g = (1/p) ∑_j ω^{val(-j·g)} · ∏_{a∈A} (1 + ω^{val(j·a)})

    Proof uses three key ingredients:
    1. ψ additivity (ψp_add, ψp_sum): character property of ω^{val(·)}
    2. Character orthogonality: ∑_j ψ(j·c) = p·[c=0] via geometric sum
    3. Subset product identity: ∏(1+f(a)) = ∑_{S⊆A} ∏_{a∈S} f(a)

    Infrastructure (ωp_pow_mod, ψp_add, ψp_sum) is proved above;
    the remaining steps need character orthogonality on ZMod p
    and the subset product identity (Finset.prod_add or by induction). -/
private lemma reprCount_fourier_expansion {p : ℕ} (hp : Nat.Prime p)
    (A : Finset (ZMod p)) (g : ZMod p) :
    (reprCount A g : ℂ) =
      (1 / (p : ℂ)) * ∑ j : ZMod p,
        (ωp p) ^ ZMod.val (-j * g) *
          ∏ a ∈ A, (1 + (ωp p) ^ ZMod.val (j * a)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  -- Rewrite ωp in terms of ψp
  have hψp_eq : ∀ x : ZMod p, (ωp p) ^ ZMod.val x = ψp x := fun _ => rfl
  -- Product expansion: ∏(1 + f(a)) = ∑_{S⊆A} ∏_{a∈S} f(a)
  have hprod_expand : ∀ j : ZMod p,
      ∏ a ∈ A, ((1 : ℂ) + ψp (j * a)) =
      ∑ S ∈ A.powerset, ∏ a ∈ S, ψp (j * a) := by
    intro j
    have h := Finset.prod_add A (fun _ => (1 : ℂ)) (fun a => ψp (j * a))
    simp only [Finset.prod_const_one, one_mul] at h
    exact h
  -- Simplify RHS
  -- Step 1: Replace ω^{val(...)} with ψp
  conv_rhs => arg 2; ext j; rw [hψp_eq (-j * g)]
  conv_rhs => arg 2; ext j; arg 2; arg 2; ext a; rw [hψp_eq (j * a)]
  -- Step 2: Expand product
  simp_rw [hprod_expand]
  -- RHS = (1/p) * ∑_j ψp(-j*g) * ∑_{S⊆A} ∏_{a∈S} ψp(j*a)
  -- Step 3: Distribute ψp(-j*g) into the sum
  simp_rw [Finset.mul_sum]
  -- RHS = (1/p) * ∑_j ∑_{S⊆A} ψp(-j*g) * ∏_{a∈S} ψp(j*a)
  -- Step 4: Use ψp_sum to simplify: ∏_{a∈S} ψp(j*a) = ψp(j * S.sum id)
  conv_rhs =>
    arg 2; ext j; arg 2; ext S
    rw [show ∏ a ∈ S, ψp (j * a) = ψp (S.sum (fun a => j * a)) from
      (ψp_sum S (fun a => j * a)).symm]
    rw [show S.sum (fun a => j * a) = j * S.sum id from Finset.mul_sum.symm]
  -- RHS = (1/p) * ∑_j ∑_{S⊆A} ψp(-j*g) * ψp(j * S.sum id)
  -- Step 5: Combine ψp terms: ψp(-j*g) * ψp(j * S.sum id) = ψp(j * (S.sum id - g))
  conv_rhs =>
    arg 2; ext j; arg 2; ext S
    rw [← ψp_add, show -j * g + j * S.sum id = j * (S.sum id - g) from by ring]
  -- RHS = (1/p) * ∑_j ∑_{S⊆A} ψp(j * (S.sum id - g))
  -- Step 6: Swap sums
  rw [show (1 / (p : ℂ)) * ∑ j : ZMod p, ∑ S ∈ A.powerset, ψp (j * (S.sum id - g)) =
      (1 / (p : ℂ)) * ∑ S ∈ A.powerset, ∑ j : ZMod p, ψp (j * (S.sum id - g)) from by
    congr 1; rw [Finset.sum_comm]]
  -- RHS = (1/p) * ∑_{S⊆A} ∑_j ψp(j * (S.sum id - g))
  -- Step 7: Apply character_orthogonality
  simp_rw [character_orthogonality hp]
  -- RHS = (1/p) * ∑_{S⊆A} (if S.sum id - g = 0 then ↑p else 0)
  -- Step 8: Simplify
  simp_rw [sub_eq_zero]
  rw [Finset.mul_sum]
  simp_rw [show ∀ S : Finset (ZMod p),
      (1 / (p : ℂ)) * (if S.sum id = g then (↑p : ℂ) else 0) =
      if S.sum id = g then 1 else 0 from by
    intro S; split_ifs <;> simp [hp_ne]]
  -- RHS = ∑_{S⊆A} (if S.sum id = g then 1 else 0) = reprCount A g
  simp only [reprCount, Finset.card_filter]
  push_cast; rfl

/-- For j = 0 in ℤ/pℤ, the Fourier term equals 2^|A|. -/
private lemma fourier_j_zero_term {p : ℕ} [NeZero p]
    (A : Finset (ZMod p)) (g : ZMod p) :
    (ωp p) ^ ZMod.val (-(0 : ZMod p) * g) *
      ∏ a ∈ A, (1 + (ωp p) ^ ZMod.val ((0 : ZMod p) * a)) =
    ↑(2 ^ A.card) := by
  simp only [zero_mul, neg_zero, ZMod.val_zero, pow_zero, one_mul]
  rw [show (1 : ℂ) + 1 = 2 from by norm_num]
  rw [Finset.prod_const, ← Nat.cast_ofNat, ← Nat.cast_pow]
  simp [nsmul_eq_mul]

/-- For nonzero j and nonzero a in ℤ/pℤ (p prime), val(j*a) ∈ {1,...,p-1}.
    This means ω^{val(j*a)} is a nontrivial root of unity. -/
private lemma val_mul_nonzero {p : ℕ} (hp : Nat.Prime p)
    (j a : ZMod p) (hj : j ≠ 0) (ha : a ≠ 0) :
    ZMod.val (j * a) ≠ 0 := by
  intro h
  rw [ZMod.val_eq_zero] at h
  have := mul_eq_zero.mp h
  rcases this with rfl | rfl <;> contradiction

/-- |1 + ω^m| = 2|cos(πm/p)| for any m.
    Uses the identity |1 + e^{iθ}| = 2|cos(θ/2)|. -/
private lemma norm_one_add_ωp_pow (p m : ℕ) [NeZero p] :
    ‖(1 : ℂ) + ωp p ^ m‖ = 2 * |Real.cos (↑m * Real.pi / ↑p)| := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  set α := (↑m : ℝ) * π / ↑p with hα_def
  -- ωp p ^ m = exp(2αi)
  have hωm : ωp p ^ m = Complex.exp (↑(2 * α) * Complex.I) := by
    simp only [ωp, ← Complex.exp_nat_mul, α]
    congr 1; push_cast; ring
  rw [hωm]
  set w := Complex.exp (↑(2 * α) * Complex.I) with hw_def
  have hw_re : w.re = Real.cos (2 * α) := Complex.exp_ofReal_mul_I_re (2 * α)
  have hw_im : w.im = Real.sin (2 * α) := Complex.exp_ofReal_mul_I_im (2 * α)
  -- Both sides nonneg
  have h_nn₁ : 0 ≤ ‖(1 : ℂ) + w‖ := norm_nonneg _
  have h_nn₂ : 0 ≤ 2 * |Real.cos α| := by positivity
  -- Suffices: squares are equal (then take sqrt)
  suffices key : ‖(1 : ℂ) + w‖ ^ 2 = (2 * |Real.cos α|) ^ 2 by
    have := congr_arg Real.sqrt key
    rwa [Real.sqrt_sq h_nn₁, Real.sqrt_sq h_nn₂] at this
  -- LHS² = normSq(1+w) = (1+cos 2α)² + sin²(2α)
  have h_lhs : ‖(1 : ℂ) + w‖ ^ 2 =
      (1 + Real.cos (2 * α)) ^ 2 + Real.sin (2 * α) ^ 2 := by
    rw [Complex.norm_eq_abs, Complex.sq_abs]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, hw_re, hw_im]
    ring
  -- RHS² = 4cos²α
  rw [h_lhs, mul_pow, sq_abs]
  -- Goal: (1+cos 2α)² + sin²(2α) = 2² * cos²α
  -- From Pythagoras: sin²(2α) + cos²(2α) = 1
  -- From double angle: cos(2α) = 2cos²α - 1
  nlinarith [Real.sin_sq_add_cos_sq (2 * α), Real.cos_two_mul α]

/-- For m ∈ {1,...,p-1}: |cos(πm/p)| ≤ cos(π/p).
    This follows from cos being strictly decreasing on [0,π] and the
    symmetry |cos(π-x)| = |cos(x)|. -/
private lemma abs_cos_mul_pi_div_le {p : ℕ} (hp : Nat.Prime p)
    (m : ℕ) (hm_pos : 0 < m) (hm_lt : m < p) :
    |Real.cos (↑m * Real.pi / ↑p)| ≤ Real.cos (Real.pi / ↑p) := by
  have hp_pos : (0 : ℝ) < ↑p := Nat.cast_pos.mpr hp.pos
  set x := (↑m : ℝ) * π / ↑p with hx_def
  set x₁ := π / ↑p with hx₁_def
  -- x₁ ∈ (0, π]
  have hx₁_pos : 0 < x₁ := div_pos Real.pi_pos hp_pos
  have hx₁_le_pi : x₁ ≤ π := div_le_self Real.pi_pos.le (by exact_mod_cast hp.one_le)
  -- x = m · x₁, so x₁ ≤ x
  have hx_eq : x = ↑m * x₁ := by simp only [hx_def, hx₁_def]; ring
  have hx_ge : x₁ ≤ x := by
    rw [hx_eq]; nlinarith [show (1 : ℝ) ≤ ↑m from by exact_mod_cast hm_pos]
  -- x ≤ π - x₁ (since m ≤ p - 1)
  have hx_le : x ≤ π - x₁ := by
    rw [hx_eq]
    have hm_le : (↑m : ℝ) ≤ ↑p - 1 := by
      have := Nat.lt_iff_le_pred hp.pos |>.mp hm_lt; exact_mod_cast this
    have h_rw : π - x₁ = (↑p - 1) * x₁ := by simp only [hx₁_def]; field_simp
    rw [h_rw]; nlinarith [hx₁_pos]
  -- x ∈ [0, π]
  have hx_nn : 0 ≤ x := by linarith
  have hx_le_pi : x ≤ π := by linarith
  -- cos x ≤ cos x₁ (cos is antitone on [0, π] and x₁ ≤ x)
  have h_upper : Real.cos x ≤ Real.cos x₁ :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨hx₁_pos.le, hx₁_le_pi⟩ ⟨hx_nn, hx_le_pi⟩ hx_ge
  -- -cos x₁ ≤ cos x (from cos(π - x₁) = -cos x₁ ≤ cos x since x ≤ π - x₁)
  have h_lower : -Real.cos x₁ ≤ Real.cos x := by
    rw [← Real.cos_pi_sub]
    exact Real.strictAntiOn_cos.antitoneOn
      ⟨hx_nn, hx_le_pi⟩ ⟨by linarith, by linarith⟩ hx_le
  exact abs_le.mpr ⟨h_lower, h_upper⟩

/-- Product bound: for j ≠ 0, ∏_{a∈A} |1 + ω^{val(ja)}| ≤ 2^k · cos(π/p)^{k-1}.
    At most one element a ∈ A can be zero (giving factor 2);
    all nonzero elements give factor ≤ 2cos(π/p). -/
private lemma fourier_product_bound {p : ℕ} (hp : Nat.Prime p)
    (A : Finset (ZMod p)) (k : ℕ) (hAk : A.card = k) (hk : 1 ≤ k)
    (j : ZMod p) (hj : j ≠ 0) :
    ∏ a ∈ A, ‖(1 : ℂ) + ωp p ^ ZMod.val (j * a)‖ ≤
      (2 : ℝ) ^ k * |Real.cos (Real.pi / ↑p)| ^ (k - 1) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- Rewrite each factor: ‖1+ω^{val(ja)}‖ = 2|cos(π·val(ja)/p)|
  have h_eq : ∀ a ∈ A,
      ‖(1 : ℂ) + ωp p ^ ZMod.val (j * a)‖ =
        2 * |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)| :=
    fun a _ => norm_one_add_ωp_pow p (ZMod.val (j * a))
  rw [Finset.prod_congr rfl h_eq]
  -- Split: ∏(2 * |cos|) = 2^k * ∏|cos|
  have h_split : ∏ a ∈ A, ((2 : ℝ) * |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)|) =
      (2 : ℝ) ^ k * ∏ a ∈ A, |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)| := by
    rw [← Finset.prod_mul_distrib, Finset.prod_const, hAk]
  rw [h_split]
  -- Suffices: ∏|cos(π·val(ja)/p)| ≤ |cos(π/p)|^{k-1}
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
  -- Helper: each |cos| factor is ≤ 1
  have hcos_le_one : ∀ a ∈ A,
      |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)| ≤ 1 := fun a _ => abs_cos_le_one _
  -- Helper: for a ≠ 0, the factor is ≤ |cos(π/p)|
  have hcos_bound : ∀ a ∈ A, a ≠ 0 →
      |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)| ≤ |Real.cos (π / ↑p)| := by
    intro a _ ha_ne
    have hv_pos : 0 < ZMod.val (j * a) :=
      Nat.pos_of_ne_zero (val_mul_nonzero hp j a hj ha_ne)
    calc |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)|
        ≤ Real.cos (π / ↑p) := abs_cos_mul_pi_div_le hp _ hv_pos (ZMod.val_lt _)
      _ ≤ |Real.cos (π / ↑p)| := le_abs_self _
  have hcos_nn : 0 ≤ |Real.cos (π / ↑p)| := abs_nonneg _
  have hcos_abs_le : |Real.cos (π / ↑p)| ≤ 1 := abs_cos_le_one _
  by_cases h0 : (0 : ZMod p) ∈ A
  · -- Case: 0 ∈ A. Split product at a = 0.
    rw [← Finset.mul_prod_erase A _ h0]
    -- Factor at a = 0: val(j·0) = 0, cos(0) = 1, |1| = 1
    simp only [mul_zero, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_div, Real.cos_zero,
      abs_one, one_mul]
    -- Remaining k-1 factors, each ≤ |cos(π/p)|
    have hcard : (A.erase 0).card = k - 1 := by
      rw [Finset.card_erase_of_mem h0, hAk]
    calc ∏ a ∈ A.erase 0, |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)|
        ≤ ∏ _a ∈ A.erase 0, |Real.cos (π / ↑p)| := by
          apply Finset.prod_le_prod (fun a _ => abs_nonneg _)
          intro a ha
          exact hcos_bound a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)
      _ = |Real.cos (π / ↑p)| ^ (A.erase 0).card := Finset.prod_const _
      _ = |Real.cos (π / ↑p)| ^ (k - 1) := by rw [hcard]
  · -- Case: 0 ∉ A. All factors have a ≠ 0.
    calc ∏ a ∈ A, |Real.cos (↑(ZMod.val (j * a)) * π / ↑p)|
        ≤ ∏ _a ∈ A, |Real.cos (π / ↑p)| := by
          apply Finset.prod_le_prod (fun a _ => abs_nonneg _)
          intro a ha
          exact hcos_bound a ha (fun h => h0 (h ▸ ha))
      _ = |Real.cos (π / ↑p)| ^ A.card := Finset.prod_const _
      _ = |Real.cos (π / ↑p)| ^ k := by rw [hAk]
      _ ≤ |Real.cos (π / ↑p)| ^ (k - 1) :=
          pow_le_pow_of_le_one hcos_nn hcos_abs_le (by omega)

/-
## Part VI: Fourier analysis connection
-/

/-- |cos(π/p)| < 1 for any prime p ≥ 2.
    For p = 2: cos(π/2) = 0. For p ≥ 3: 0 < π/p < π so -1 < cos(π/p) < 1. -/
private lemma abs_cos_pi_div_prime_lt_one (p : ℕ) (hp : Nat.Prime p) :
    |Real.cos (Real.pi / ↑p)| < 1 := by
  have hp_pos : (0 : ℝ) < ↑p := Nat.cast_pos.mpr hp.pos
  have hp_one_lt : (1 : ℝ) < ↑p := by exact_mod_cast hp.one_lt
  have hx_pos : (0 : ℝ) < π / ↑p := div_pos Real.pi_pos hp_pos
  have hx_lt_pi : π / ↑p < π := div_lt_self Real.pi_pos hp_one_lt
  rw [abs_lt]
  constructor
  · -- cos(π/p) > cos(π) = -1 since π/p < π and cos strictly decreasing on [0,π]
    have h1 : π / ↑p ∈ Set.Icc (0 : ℝ) π := ⟨hx_pos.le, hx_lt_pi.le⟩
    have h2 : π ∈ Set.Icc (0 : ℝ) π := ⟨Real.pi_pos.le, le_refl _⟩
    have := Real.strictAntiOn_cos h1 h2 hx_lt_pi
    rw [Real.cos_pi] at this
    linarith
  · -- cos(π/p) < cos(0) = 1 since 0 < π/p and cos strictly decreasing on [0,π]
    have h1 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) π := ⟨le_refl _, Real.pi_pos.le⟩
    have h2 : π / ↑p ∈ Set.Icc (0 : ℝ) π := ⟨hx_pos.le, hx_lt_pi.le⟩
    have := Real.strictAntiOn_cos h1 h2 hx_pos
    rwa [Real.cos_zero] at this

/-- Fourier-analytic error bound for representation counts in ℤ/pℤ.

    For A ⊆ ℤ/pℤ of size k, Fourier inversion gives:
      F_A(g) = (1/p) ∑_χ χ(-g) ∏_{a ∈ A} (1 + χ(a))
    The trivial character contributes 2^k/p (the "uniform" term).
    For χ ≠ 1: |1 + χ(a)| = 2|cos(πja/p)|, and for nonzero a mod p,
    |cos(πja/p)| ≤ cos(π/p) < 1. The exponent k-1 (not k) accounts for
    the possibility that 0 ∈ A, where |cos(0)| = 1.

    **Note**: The original axiom (without 2^k/p factor) was mathematically
    false. Counterexample: A = {1,2} in ℤ/3ℤ gives error 2/3 but the old
    bound was (3-1)·cos(π/3)² = 1/2 < 2/3.

    Proof: From the Fourier expansion (reprCount_fourier_expansion),
    extract the j=0 term (= 2^k/p), bound the remaining p-1 terms
    using triangle inequality and the product bound
    (fourier_product_bound). -/
theorem fourier_error_bound (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 1 ≤ k) :
  ∀ A : Finset (ZMod p), A.card = k →
    ∀ g : ZMod p, |(reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p| ≤
      (↑p - 1 : ℝ) * |Real.cos (Real.pi / ↑p)| ^ (k - 1) * ((2 : ℝ) ^ k / ↑p) := by
  intro A hAk g
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp_pos : (0 : ℝ) < ↑p := Nat.cast_pos.mpr hp.pos
  have hp_ne_c : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  -- Fourier expansion and product bound
  have hfourier := reprCount_fourier_expansion hp A g
  have h_prod_bound := fun j (hj : j ≠ (0 : ZMod p)) =>
    fourier_product_bound hp A k hAk hk j hj
  -- Per-character Fourier term
  set f : ZMod p → ℂ := fun j =>
    (ωp p) ^ ZMod.val (-j * g) * ∏ a ∈ A, (1 + (ωp p) ^ ZMod.val (j * a)) with hf_def
  -- Nonzero characters
  set S := Finset.univ.erase (0 : ZMod p) with hS_def
  -- f(0) = 2^k
  have hf0 : f 0 = ↑(2 ^ A.card) := fourier_j_zero_term A g
  -- Split sum: ∑ f = f(0) + ∑_{j≠0} f(j)
  have hsplit : ∑ j : ZMod p, f j = f 0 + ∑ j ∈ S, f j :=
    (Finset.add_sum_erase Finset.univ f (Finset.mem_univ 0)).symm
  -- Error in ℂ: reprCount - 2^k/p = (1/p) ∑_{j≠0} f(j)
  have herror : (reprCount A g : ℂ) - ↑(2 ^ k : ℕ) / (p : ℂ) =
      (1 / (p : ℂ)) * ∑ j ∈ S, f j := by
    rw [hfourier, hsplit, mul_add, hf0, hAk]
    field_simp [hp_ne_c]
  -- |S| = p - 1
  have hS_card : S.card = p - 1 := by
    rw [hS_def, Finset.card_erase_of_mem (Finset.mem_univ _), ZMod.card]
  -- Helper: ‖∏ h(a)‖ = ∏ ‖h(a)‖ (norm is multiplicative in normed fields)
  have norm_finset_prod : ∀ (T : Finset (ZMod p)) (h : ZMod p → ℂ),
      ‖∏ a ∈ T, h a‖ = ∏ a ∈ T, ‖h a‖ := by
    intro T h
    induction T using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, norm_mul, ih]
  -- ‖f(j)‖ ≤ 2^k * |cos(π/p)|^{k-1} for j ≠ 0
  have hf_bound : ∀ j ∈ S, ‖f j‖ ≤ (2 : ℝ) ^ k * |Real.cos (π / ↑p)| ^ (k - 1) := by
    intro j hj
    have hj_ne : j ≠ 0 := Finset.ne_of_mem_erase hj
    simp only [hf_def]
    rw [norm_mul, ωp_pow_norm, one_mul, norm_finset_prod]
    exact h_prod_bound j hj_ne
  -- ‖1/p‖ = 1/p
  have h1p : ‖(1 / (p : ℂ))‖ = 1 / (↑p : ℝ) := by
    rw [norm_div, Complex.norm_one, Complex.norm_natCast]
  -- Bridge ℂ → ℝ: real absolute value equals complex norm (both sides are real)
  have hbridge : |(reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p| =
      ‖(↑((reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hcast : (↑((reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p) : ℂ) =
      (reprCount A g : ℂ) - ↑(2 ^ k : ℕ) / (p : ℂ) := by
    push_cast
    rw [Nat.cast_pow, Nat.cast_ofNat]
  -- Main calculation
  rw [hbridge, hcast, herror]
  calc ‖(1 / (p : ℂ)) * ∑ j ∈ S, f j‖
      = ‖(1 / (p : ℂ))‖ * ‖∑ j ∈ S, f j‖ := norm_mul _ _
    _ ≤ (1 / ↑p) * ∑ j ∈ S, ‖f j‖ := by
        rw [h1p]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
          (div_nonneg zero_le_one (Nat.cast_nonneg p))
    _ ≤ (1 / ↑p) * ∑ j ∈ S, ((2 : ℝ) ^ k * |Real.cos (π / ↑p)| ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hf_bound)
          (div_nonneg zero_le_one (Nat.cast_nonneg p))
    _ = (↑p - 1) * |Real.cos (π / ↑p)| ^ (k - 1) * ((2 : ℝ) ^ k / ↑p) := by
        rw [Finset.sum_const, hS_card, nsmul_eq_mul]
        field_simp
        ring

/-- For k ≥ clog₂ p + C, the Fourier error decays to at most ε · 2^k/p.
    This is the core of the Erdős-Rényi (1965) approach.

    Proof: from fourier_error_bound, the relative error is bounded by
    (p-1) · |cos(π/p)|^(k-1). Since |cos(π/p)| < 1 for all primes,
    this decays geometrically and falls below ε for large enough k. -/
theorem erdos_renyi_decay (p : ℕ) (hp : Nat.Prime p) :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℕ, ∀ k : ℕ, k ≥ Nat.clog 2 p + C →
      ∀ A : Finset (ZMod p), A.card = k →
        ∀ g : ZMod p, |(reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p| ≤
          ε * ((2 : ℝ) ^ k / ↑p) := by
  intro ε hε
  -- |cos(π/p)| < 1 for primes
  have hcos_lt := abs_cos_pi_div_prime_lt_one p hp
  have hcos_nn := abs_nonneg (Real.cos (π / ↑p))
  -- (p : ℝ) - 1 > 0 for primes
  have hp_sub : (0 : ℝ) < ↑p - 1 := by
    have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  -- Find K₀ with |cos(π/p)|^K₀ < ε/(p-1)
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one (div_pos hε hp_sub) hcos_lt
  -- C = K₀ + 1 ensures k-1 ≥ K₀ and k ≥ 1
  use K₀ + 1
  intro k hk A hA g
  have hk1 : 1 ≤ k := by omega
  -- From fourier_error_bound (corrected):
  -- |error| ≤ (p-1) · |cos(π/p)|^(k-1) · (2^k/p)
  have hfourier := fourier_error_bound p hp k hk1 A hA g
  -- Suffices: (p-1) · |cos(π/p)|^(k-1) ≤ ε
  suffices hsuff : (↑p - 1 : ℝ) * |Real.cos (π / ↑p)| ^ (k - 1) ≤ ε by
    calc |(reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p|
        ≤ (↑p - 1) * |Real.cos (π / ↑p)| ^ (k - 1) * ((2 : ℝ) ^ k / ↑p) := hfourier
      _ ≤ ε * ((2 : ℝ) ^ k / ↑p) := by
          apply mul_le_mul_of_nonneg_right hsuff
          exact div_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k) (Nat.cast_nonneg p)
  -- k - 1 ≥ K₀ since k ≥ clog 2 p + K₀ + 1 ≥ K₀ + 1
  have hk_ge : K₀ ≤ k - 1 := by omega
  -- |cos(π/p)|^(k-1) ≤ |cos(π/p)|^K₀ (decreasing for base ≤ 1)
  -- Then (p-1) · |cos(π/p)|^(k-1) ≤ (p-1) · ε/(p-1) = ε
  calc (↑p - 1 : ℝ) * |Real.cos (π / ↑p)| ^ (k - 1)
      ≤ (↑p - 1) * |Real.cos (π / ↑p)| ^ K₀ := by
        apply mul_le_mul_of_nonneg_left _ hp_sub.le
        exact pow_le_pow_of_le_one hcos_nn hcos_lt.le hk_ge
    _ ≤ (↑p - 1) * (ε / (↑p - 1)) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hK₀) hp_sub.le
    _ = ε := by field_simp

/-
## Part VII: Summary and open question
-/

/-- The central open question: what is the precise rate at which
    g_ε(N) - log₂ N grows?

    Three candidate answers, in order of strength:
    1. O(1) — strongest, would mean g_ε(N) = log₂ N + O_ε(1)
    2. Θ(log log N) — by analogy with Problem #543
    3. o(log₂ N) — weakest, already known from Erdős-Hall

    We proved: O(1) ⟹ o(log₂ N), establishing the hierarchy.
    We proved: erdos_renyi_decay from fourier_error_bound (geometric decay). -/
theorem second_order_hierarchy (gEps : ℝ → ℕ → ℕ) (ε : ℝ) :
    CorrectionIsBounded gEps ε → CorrectionIsSublinearInLog gEps ε :=
  bounded_implies_sublinear gEps ε

end Erdos1179OQ01
