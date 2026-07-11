/-
  Aristotle companion for Erdős Problem #125 (positive_lower_density variant).

  Single remaining target: `scale_step` — the multi-scale counting core of
  DeepMind's AlphaProof Nexus proof (2026-05-21, arXiv:2605.22763v1) that the
  sumset A + B (A = base-3 digits in {0,1}, B = base-4 digits in {0,1}) has
  lower density zero. This is a KNOWN result with a published Lean proof in
  https://github.com/google-deepmind/alphaproof-nexus-results
  (APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean),
  so it is a legitimate HARD-tier proof-search target, not an open conjecture.

  The AlphaProof original proves scale_step by:
  1. Choosing eps = 1/(24*N) and (k, m) from dirichlet_approx (proved below)
     with 3^k <= 4^m <= 3^k(1+eps) and 3^k * eps >= 3.
  2. Setting N' = N * 3^k. Every x in (A+B) with x < N*3^k decomposes as
     x = y*3^k + z with y in A+B, y < N, and
     z = a0 + b0 + b1*(4^m - 3^k) <= 3^k*(5/6 + eps*N + eps/3)
     via A_decomp/B_decomp/A_max_k/B_max_m/hz_eq_lemma (all proved below).
  3. Counting: card <= card([0,N) filter A+B) * M with M <= 3^k*(5/6 + 2*eps*N),
     and (5/6 + 2*eps*N) <= 11/12 by the choice of eps.

  All supporting lemmas AND scale_step are now fully proved below (#20842);
  this file is `sorry`-free. It is self-contained (mirrors
  Erdos125PositiveLowerDensity.lean with the namespace renamed). Block comments
  only — no module docstrings.
-/


import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Nat Pointwise Filter
open scoped Topology Classical

namespace Erdos125Aristotle

/- ## Density definitions (inlined from FormalConjecturesForMathlib) -/

/-- Set of naturals `< b` that lie in `S`. -/
noncomputable def interIio (S : Set ℕ) (b : ℕ) : Finset ℕ :=
  (Finset.range b).filter (· ∈ S)

/--
Partial density of `S` at `b`: proportion of `{x : ℕ | x < b}` lying in `S`.
This is the natural-numbers specialisation of
`FormalConjecturesForMathlib.Data.Set.Density.partialDensity`.
-/
noncomputable def partialDensity (S : Set ℕ) (b : ℕ) : ℝ :=
  ((interIio S b).card : ℝ) / (b : ℝ)

/-- Lower density of `S ⊆ ℕ`: `liminf` of partial densities. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  atTop.liminf (fun b : ℕ => partialDensity S b)

/- ## The digit-restricted sets A and B -/

/-- `A` = naturals whose base-3 digits are all `0` or `1`. -/
def A : Set ℕ := { x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} }

/-- `B` = naturals whose base-4 digits are all `0` or `1`. -/
def B : Set ℕ := { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }

/- ## Supporting lemmas

The lemmas below mirror exactly the structure of the AlphaProof Nexus proof
(see https://github.com/google-deepmind/alphaproof-nexus-results, file
`APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`).
The AlphaProof one-line `bound`/`valid` tactic proofs were re-derived in pure
Mathlib v4.26.0 (#20842), including the multi-scale counting core `scale_step`.
This file is `sorry`-free. -/

lemma zero_in_A : 0 ∈ A := by
  -- AlphaProof: `norm_num`
  simp [A]

lemma zero_in_B : 0 ∈ B := by
  -- AlphaProof: `bound`
  simp [B]

lemma zero_in_A_plus_B : 0 ∈ A + B := by
  refine ⟨0, zero_in_A, 0, zero_in_B, ?_⟩
  simp

/- ### Digit helper lemmas for `A` (base 3)

Membership in `A` is stable under taking the low digit (`% 3`) and the tail
(`/ 3`), which lets us reason about `A` by peeling one base-3 digit at a time.
These replace the AlphaProof `bound`/`valid` golf with explicit `Nat.digits`
manipulation. -/

/-- The lowest base-3 digit of an element of `A` is `0` or `1`. -/
lemma A_head3 (x : ℕ) (hx : x ∈ A) : x % 3 ≤ 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · omega
  · have hsub : (Nat.digits 3 x).toFinset ⊆ {0, 1} := hx
    have hd : Nat.digits 3 x = x % 3 :: Nat.digits 3 (x / 3) :=
      Nat.digits_def' (by norm_num) hpos
    have hmem : x % 3 ∈ (Nat.digits 3 x).toFinset := by rw [hd]; simp
    have hcase := hsub hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcase
    omega

/-- Dropping the lowest base-3 digit (`/ 3`) keeps an element inside `A`. -/
lemma A_tail3 (x : ℕ) (hx : x ∈ A) : x / 3 ∈ A := by
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · rw [Nat.zero_div]; exact zero_in_A
  · have hsub : (Nat.digits 3 x).toFinset ⊆ {0, 1} := hx
    have hd : Nat.digits 3 x = x % 3 :: Nat.digits 3 (x / 3) :=
      Nat.digits_def' (by norm_num) hpos
    show (Nat.digits 3 (x / 3)).toFinset ⊆ {0, 1}
    intro d hd2
    apply hsub
    rw [hd]
    simp only [List.toFinset_cons, Finset.mem_insert]
    exact Or.inr hd2

/-- Reassemble membership in `A` from the lowest digit and the tail. -/
lemma mem_A_of_head_tail (x : ℕ) (h1 : x % 3 ≤ 1) (h2 : x / 3 ∈ A) : x ∈ A := by
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · exact zero_in_A
  · have hsub2 : (Nat.digits 3 (x / 3)).toFinset ⊆ {0, 1} := h2
    have hd : Nat.digits 3 x = x % 3 :: Nat.digits 3 (x / 3) :=
      Nat.digits_def' (by norm_num) hpos
    show (Nat.digits 3 x).toFinset ⊆ {0, 1}
    rw [hd, List.toFinset_cons, Finset.insert_subset_iff]
    refine ⟨?_, hsub2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- Dividing by `3 ^ k` (dropping the low `k` base-3 digits) keeps `A`. -/
lemma A_div_pow (k a : ℕ) (ha : a ∈ A) : a / 3 ^ k ∈ A := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    have h : a / 3 ^ (k + 1) = a / 3 ^ k / 3 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [h]
    exact A_tail3 _ ih

/-- Reducing mod `3 ^ k` (keeping the low `k` base-3 digits) keeps `A`. -/
lemma A_mod_pow : ∀ (k a : ℕ), a ∈ A → a % 3 ^ k ∈ A := by
  intro k
  induction k with
  | zero => intro a _; rw [pow_zero, Nat.mod_one]; exact zero_in_A
  | succ k ih =>
    intro a ha
    have htail : a / 3 ∈ A := A_tail3 a ha
    have hs : (a / 3) % 3 ^ k ∈ A := ih (a / 3) htail
    have hhead : a % 3 ≤ 1 := A_head3 a ha
    have hmod : a % 3 ^ (k + 1) = a % 3 + 3 * (a / 3 % 3 ^ k) := by
      rw [pow_succ']; exact Nat.mod_mul
    rw [hmod]
    set T := a / 3 % 3 ^ k with hT
    apply mem_A_of_head_tail
    · have h3 : (a % 3 + 3 * T) % 3 = a % 3 := by omega
      rw [h3]; exact hhead
    · have h4 : (a % 3 + 3 * T) / 3 = T := by omega
      rw [h4]; exact hs

/- ### Digit helper lemmas for `B` (base 4) -/

/-- The lowest base-4 digit of an element of `B` is `0` or `1`. -/
lemma B_head4 (y : ℕ) (hy : y ∈ B) : y % 4 ≤ 1 := by
  rcases Nat.eq_zero_or_pos y with rfl | hpos
  · omega
  · have hsub : (Nat.digits 4 y).toFinset ⊆ {0, 1} := hy
    have hd : Nat.digits 4 y = y % 4 :: Nat.digits 4 (y / 4) :=
      Nat.digits_def' (by norm_num) hpos
    have hmem : y % 4 ∈ (Nat.digits 4 y).toFinset := by rw [hd]; simp
    have hcase := hsub hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcase
    omega

/-- Dropping the lowest base-4 digit (`/ 4`) keeps an element inside `B`. -/
lemma B_tail4 (y : ℕ) (hy : y ∈ B) : y / 4 ∈ B := by
  rcases Nat.eq_zero_or_pos y with rfl | hpos
  · rw [Nat.zero_div]; exact zero_in_B
  · have hsub : (Nat.digits 4 y).toFinset ⊆ {0, 1} := hy
    have hd : Nat.digits 4 y = y % 4 :: Nat.digits 4 (y / 4) :=
      Nat.digits_def' (by norm_num) hpos
    show (Nat.digits 4 (y / 4)).toFinset ⊆ {0, 1}
    intro d hd2
    apply hsub
    rw [hd]
    simp only [List.toFinset_cons, Finset.mem_insert]
    exact Or.inr hd2

/-- Reassemble membership in `B` from the lowest digit and the tail. -/
lemma mem_B_of_head_tail (y : ℕ) (h1 : y % 4 ≤ 1) (h2 : y / 4 ∈ B) : y ∈ B := by
  rcases Nat.eq_zero_or_pos y with rfl | hpos
  · exact zero_in_B
  · have hsub2 : (Nat.digits 4 (y / 4)).toFinset ⊆ {0, 1} := h2
    have hd : Nat.digits 4 y = y % 4 :: Nat.digits 4 (y / 4) :=
      Nat.digits_def' (by norm_num) hpos
    show (Nat.digits 4 y).toFinset ⊆ {0, 1}
    rw [hd, List.toFinset_cons, Finset.insert_subset_iff]
    refine ⟨?_, hsub2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- Dividing by `4 ^ m` (dropping the low `m` base-4 digits) keeps `B`. -/
lemma B_div_pow (m b : ℕ) (hb : b ∈ B) : b / 4 ^ m ∈ B := by
  induction m with
  | zero => simpa using hb
  | succ m ih =>
    have h : b / 4 ^ (m + 1) = b / 4 ^ m / 4 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [h]
    exact B_tail4 _ ih

/-- Reducing mod `4 ^ m` (keeping the low `m` base-4 digits) keeps `B`. -/
lemma B_mod_pow : ∀ (m b : ℕ), b ∈ B → b % 4 ^ m ∈ B := by
  intro m
  induction m with
  | zero => intro b _; rw [pow_zero, Nat.mod_one]; exact zero_in_B
  | succ m ih =>
    intro b hb
    have htail : b / 4 ∈ B := B_tail4 b hb
    have hs : (b / 4) % 4 ^ m ∈ B := ih (b / 4) htail
    have hhead : b % 4 ≤ 1 := B_head4 b hb
    have hmod : b % 4 ^ (m + 1) = b % 4 + 4 * (b / 4 % 4 ^ m) := by
      rw [pow_succ']; exact Nat.mod_mul
    rw [hmod]
    set T := b / 4 % 4 ^ m with hT
    apply mem_B_of_head_tail
    · have h3 : (b % 4 + 4 * T) % 4 = b % 4 := by omega
      rw [h3]; exact hhead
    · have h4 : (b % 4 + 4 * T) / 4 = T := by omega
      rw [h4]; exact hs

/-- If `x < 3^k` and `x ∈ A` then `x ≤ (3^k - 1) / 2`. -/
lemma A_max_k (k x : ℕ) (hx : x < 3 ^ k) (hA : x ∈ A) : x ≤ (3 ^ k - 1) / 2 := by
  induction k generalizing x with
  | zero => simp only [pow_zero] at hx ⊢; omega
  | succ k ih =>
    have hh : x % 3 ≤ 1 := A_head3 x hA
    have ht : x / 3 ∈ A := A_tail3 x hA
    have hlt : x / 3 < 3 ^ k := by
      have hx' : x < 3 ^ k * 3 := by rw [← pow_succ]; exact hx
      exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hx'
    have hih := ih (x / 3) hlt ht
    have hP : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hodd : 3 ^ k % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    have hdm : 3 * (x / 3) + x % 3 = x := Nat.div_add_mod x 3
    have hpow : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ']
    omega

/-- If `y < 4^m` and `y ∈ B` then `y ≤ (4^m - 1) / 3`. -/
lemma B_max_m (m y : ℕ) (hy : y < 4 ^ m) (hB : y ∈ B) : y ≤ (4 ^ m - 1) / 3 := by
  induction m generalizing y with
  | zero => simp only [pow_zero] at hy ⊢; omega
  | succ m ih =>
    have hh : y % 4 ≤ 1 := B_head4 y hB
    have ht : y / 4 ∈ B := B_tail4 y hB
    have hlt : y / 4 < 4 ^ m := by
      have hy' : y < 4 ^ m * 4 := by rw [← pow_succ]; exact hy
      exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hy'
    have hih := ih (y / 4) hlt ht
    have hP : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hmod3 : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have hdm : 4 * (y / 4) + y % 4 = y := Nat.div_add_mod y 4
    have hpow : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [pow_succ']
    omega

/--
**Gap lemma.** If `(3^k - 1)/2 + (4^m - 1)/3 < x`, `x < 3^k`, and `x < 4^m`,
then `x ∉ A + B`. (No `(a,b)` decomposition can reach the upper part of the
interval below `min(3^k, 4^m)`.)
-/
lemma A_B_gap (k m x : ℕ)
    (hx_gt : (3 ^ k - 1) / 2 + (4 ^ m - 1) / 3 < x)
    (hx_lt_A : x < 3 ^ k) (hx_lt_B : x < 4 ^ m) : x ∉ A + B := by
  intro h
  rcases Set.mem_add.mp h with ⟨a, ha, b, hb, hab⟩
  have hak : a < 3 ^ k ∨ 3 ^ k ≤ a := by omega
  have hbm : b < 4 ^ m ∨ 4 ^ m ≤ b := by omega
  rcases hak with hak1 | hak2
  · rcases hbm with hbm1 | hbm2
    · have h1 := A_max_k k a hak1 ha
      have h2 := B_max_m m b hbm1 hb
      omega
    · omega
  · omega

/-- Decomposition: every `a ∈ A` factors as `a = a₁ · 3^k + a₀` with both pieces in `A`. -/
lemma A_decomp (k a : ℕ) (ha : a ∈ A) :
    ∃ a1 a0 : ℕ, a1 ∈ A ∧ a0 ∈ A ∧ a0 < 3 ^ k ∧ a = a1 * 3 ^ k + a0 := by
  refine ⟨a / 3 ^ k, a % 3 ^ k, A_div_pow k a ha, A_mod_pow k a ha,
    Nat.mod_lt a (by positivity), ?_⟩
  exact (Nat.div_add_mod' a (3 ^ k)).symm

/-- Decomposition: every `b ∈ B` factors as `b = b₁ · 4^m + b₀` with both pieces in `B`. -/
lemma B_decomp (m b : ℕ) (hb : b ∈ B) :
    ∃ b1 b0 : ℕ, b1 ∈ B ∧ b0 ∈ B ∧ b0 < 4 ^ m ∧ b = b1 * 4 ^ m + b0 := by
  refine ⟨b / 4 ^ m, b % 4 ^ m, B_div_pow m b hb, B_mod_pow m b hb,
    Nat.mod_lt b (by positivity), ?_⟩
  exact (Nat.div_add_mod' b (4 ^ m)).symm

/-- `log 4 / log 3` is irrational. -/
lemma log_ratio_irrational : Irrational (Real.log 4 / Real.log 3) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog3ne : Real.log 3 ≠ 0 := hlog3.ne'
  intro h
  obtain ⟨q, hq⟩ := h
  have hdenpos : 0 < q.den := q.den_pos
  have hden_posR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hdenpos
  have hden0 : (q.den : ℝ) ≠ 0 := hden_posR.ne'
  -- From `↑q = log 4 / log 3` and `↑q = q.num / q.den`, cross-multiply.
  have hcast : (q.num : ℝ) / (q.den : ℝ) = Real.log 4 / Real.log 3 := by
    rw [← Rat.cast_def]; exact hq
  have h2 : (q.num : ℝ) * Real.log 3 = (q.den : ℝ) * Real.log 4 := by
    field_simp [hlog3ne, hden0] at hcast
    linear_combination hcast
  have hprod : 0 < (q.num : ℝ) * Real.log 3 := by rw [h2]; exact mul_pos hden_posR hlog4
  have hnumpos : 0 < q.num := by
    have hR : 0 < (q.num : ℝ) := by nlinarith [hprod, hlog3]
    exact_mod_cast hR
  set n := q.num.toNat with hn
  have hnum_cast : (q.num : ℝ) = (n : ℝ) := by
    rw [hn]; exact_mod_cast (Int.toNat_of_nonneg hnumpos.le).symm
  rw [hnum_cast] at h2
  -- `n * log 3 = q.den * log 4` forces `3 ^ n = 4 ^ q.den`.
  have hlogeq : Real.log ((3 : ℝ) ^ n) = Real.log ((4 : ℝ) ^ q.den) := by
    rw [Real.log_pow, Real.log_pow]; linarith [h2]
  have hpoweq : (3 : ℝ) ^ n = (4 : ℝ) ^ q.den :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) hlogeq
  have hnateq : (3 : ℕ) ^ n = (4 : ℕ) ^ q.den := by exact_mod_cast hpoweq
  -- But `3 ^ n` is odd and `4 ^ q.den` is even (`q.den ≥ 1`).
  have hodd : (3 : ℕ) ^ n % 2 = 1 := by rw [Nat.pow_mod]; norm_num
  have hdvd : 2 ∣ (4 : ℕ) ^ q.den := dvd_pow (by norm_num) hdenpos.ne'
  omega

/--
**Dirichlet helper.** For any irrational `α > 0` and any `δ > 0`, there exist
positive integers `m, k` with `0 < m·α - k < δ`.
-/
lemma exists_small_pos_lin_comb_help (α : ℝ) (hα : Irrational α) (hα_pos : 0 < α)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
      0 < (m : ℝ) * α - (k : ℝ) ∧ (m : ℝ) * α - (k : ℝ) < δ := by
  -- Strategy: the additive subgroup `ℤ·1 + ℤ·α ≤ ℝ` is dense (were it cyclic,
  -- `α` would be rational).  Pick `x = p + q·α ∈ (0, δ')` in the subgroup with
  -- `δ' = min δ (min α 1)`.  If `q ≥ 1` then `p ≤ -1` (since `x < α`) and
  -- `(q, -p)` works directly.  If `q ≤ -1` then `p ≥ 1` and the descent step
  -- `y = α - ⌊α/x⌋·x ∈ (0, x)` has the form `(1 - jq)·α - jp` with positive
  -- coefficients.  `q = 0` is impossible since `(0, δ') ⊆ (0, 1)` contains no
  -- integer.
  set δ' : ℝ := min δ (min α 1) with hδ'def
  have hδ'_pos : 0 < δ' := lt_min hδ (lt_min hα_pos one_pos)
  have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
  have hδ'_le_α : δ' ≤ α := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'_le_one : δ' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  -- The subgroup `⟨1, α⟩` is dense in `ℝ`.
  have hdense : Dense ((AddSubgroup.closure {1, α} : AddSubgroup ℝ) : Set ℝ) := by
    rcases AddSubgroup.dense_or_cyclic (AddSubgroup.closure {1, α}) with h | ⟨a, ha⟩
    · exact h
    · exfalso
      have h1 : (1 : ℝ) ∈ AddSubgroup.closure ({1, α} : Set ℝ) :=
        AddSubgroup.subset_closure (by simp)
      have h2 : α ∈ AddSubgroup.closure ({1, α} : Set ℝ) :=
        AddSubgroup.subset_closure (by simp)
      rw [ha, AddSubgroup.mem_closure_singleton] at h1 h2
      obtain ⟨n, hn⟩ := h1
      obtain ⟨m, hm⟩ := h2
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hn
      have hcomm : (n : ℝ) * α = (m : ℝ) := by
        have hn' : (n : ℝ) * a = 1 := by rw [← zsmul_eq_mul]; exact hn
        have hm' : (m : ℝ) * a = α := by rw [← zsmul_eq_mul]; exact hm
        calc (n : ℝ) * α = (n : ℝ) * ((m : ℝ) * a) := by rw [hm']
          _ = (m : ℝ) * ((n : ℝ) * a) := by ring
          _ = (m : ℝ) := by rw [hn', mul_one]
      exact (hα.intCast_mul hn0).ne_int m hcomm
  -- Pick a subgroup element `x ∈ (0, δ')`.
  obtain ⟨x, hx_Ioo, hxG⟩ :=
    dense_iff_inter_open.mp hdense (Set.Ioo 0 δ') isOpen_Ioo
      ⟨δ' / 2, Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
  rw [Set.mem_Ioo] at hx_Ioo
  obtain ⟨hx_pos, hx_lt⟩ := hx_Ioo
  rw [SetLike.mem_coe] at hxG
  obtain ⟨p, q, hpq⟩ := AddSubgroup.mem_closure_pair.mp hxG
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hpq
  -- `hpq : (p : ℝ) + (q : ℝ) * α = x`
  rcases lt_trichotomy q 0 with hq_neg | rfl | hq_pos
  · -- `q ≤ -1`: descent step `y = α - ⌊α/x⌋·x`.
    have hq1 : (q : ℝ) ≤ -1 := by exact_mod_cast (by omega : q ≤ (-1 : ℤ))
    have hqα : (q : ℝ) * α ≤ -1 * α := mul_le_mul_of_nonneg_right hq1 hα_pos.le
    have hpR : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : 1 ≤ p := by
      have : (0 : ℤ) < p := by exact_mod_cast hpR
      omega
    set j : ℤ := ⌊α / x⌋ with hjdef
    have hj1 : 1 ≤ j := by
      rw [hjdef, Int.le_floor, Int.cast_one, le_div_iff₀ hx_pos, one_mul]
      linarith
    have hfl := Int.floor_le (α / x)
    rw [← hjdef] at hfl
    have hjx_le : (j : ℝ) * x ≤ α := by
      have h' := mul_le_mul_of_nonneg_right hfl hx_pos.le
      rwa [div_mul_cancel₀ α hx_pos.ne'] at h'
    have hfl2 := Int.lt_floor_add_one (α / x)
    rw [← hjdef] at hfl2
    have hjx_gt : α < ((j : ℝ) + 1) * x := by
      have h' := mul_lt_mul_of_pos_right hfl2 hx_pos
      rwa [div_mul_cancel₀ α hx_pos.ne'] at h'
    -- Integer coefficients of the descent element.
    have hjq : j * q ≤ j * (-1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hM1 : 1 ≤ 1 - j * q := by linarith
    have hK1 : 1 ≤ j * p := by
      have h' := mul_le_mul hj1 hp1 zero_le_one (by omega : (0 : ℤ) ≤ j)
      linarith
    have hMcast : (((1 - j * q).toNat : ℤ)) = 1 - j * q := Int.toNat_of_nonneg (by linarith)
    have hKcast : (((j * p).toNat : ℤ)) = j * p := Int.toNat_of_nonneg (by linarith)
    have hMR : (((1 - j * q).toNat : ℕ) : ℝ) = 1 - (j : ℝ) * (q : ℝ) := by
      rw [← Int.cast_natCast, hMcast]; push_cast; ring
    have hKR : (((j * p).toNat : ℕ) : ℝ) = (j : ℝ) * (p : ℝ) := by
      rw [← Int.cast_natCast, hKcast]; push_cast; ring
    have hyx : (1 - (j : ℝ) * (q : ℝ)) * α - (j : ℝ) * (p : ℝ) = α - (j : ℝ) * x := by
      rw [← hpq]; ring
    have hMne : 1 - j * q ≠ 0 := by
      intro hh
      rw [hh] at hM1
      exact absurd hM1 (by norm_num)
    have hy_ne : α - (j : ℝ) * x ≠ 0 := by
      intro h0
      have heq : ((1 - j * q : ℤ) : ℝ) * α = ((j * p : ℤ) : ℝ) := by
        push_cast
        linarith [hyx]
      exact (hα.intCast_mul hMne).ne_int (j * p) heq
    have hy_pos : 0 < α - (j : ℝ) * x :=
      lt_of_le_of_ne (by linarith) (Ne.symm hy_ne)
    have hy_lt : α - (j : ℝ) * x < x := by linarith
    refine ⟨(1 - j * q).toNat, (j * p).toNat, ?_, ?_, ?_, ?_⟩
    · have h' : (0 : ℤ) < ((1 - j * q).toNat : ℤ) := by rw [hMcast]; linarith
      exact_mod_cast h'
    · have h' : (0 : ℤ) < ((j * p).toNat : ℤ) := by rw [hKcast]; linarith
      exact_mod_cast h'
    · calc (0 : ℝ) < α - (j : ℝ) * x := hy_pos
        _ = (1 - (j : ℝ) * (q : ℝ)) * α - (j : ℝ) * (p : ℝ) := hyx.symm
        _ = (((1 - j * q).toNat : ℕ) : ℝ) * α - (((j * p).toNat : ℕ) : ℝ) := by
            rw [hMR, hKR]
    · calc (((1 - j * q).toNat : ℕ) : ℝ) * α - (((j * p).toNat : ℕ) : ℝ)
          = (1 - (j : ℝ) * (q : ℝ)) * α - (j : ℝ) * (p : ℝ) := by rw [hMR, hKR]
        _ = α - (j : ℝ) * x := hyx
        _ < x := hy_lt
        _ < δ' := hx_lt
        _ ≤ δ := hδ'_le_δ
  · -- `q = 0`: impossible, `(0, δ') ⊆ (0, 1)` contains no integer.
    exfalso
    rw [Int.cast_zero, zero_mul, add_zero] at hpq
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hpq ▸ hx_pos
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp0
    linarith [hpq ▸ hx_lt]
  · -- `q ≥ 1`: `(q, -p)` works directly since `p ≤ -1`.
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pos
    have hqα : α ≤ (q : ℝ) * α := le_mul_of_one_le_left hα_pos.le hq1
    have hp_neg : (p : ℝ) < 0 := by linarith
    have hp1 : p ≤ -1 := by
      have : p < 0 := by exact_mod_cast hp_neg
      omega
    have hqcast : ((q.toNat : ℤ)) = q := Int.toNat_of_nonneg (by omega)
    have hpcast : (((-p).toNat : ℤ)) = -p := Int.toNat_of_nonneg (by omega)
    have hqR : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by rw [← Int.cast_natCast, hqcast]
    have hpR : (((-p).toNat : ℕ) : ℝ) = -(p : ℝ) := by
      rw [← Int.cast_natCast, hpcast]; push_cast; ring
    refine ⟨q.toNat, (-p).toNat, ?_, ?_, ?_, ?_⟩
    · have h' : (0 : ℤ) < (q.toNat : ℤ) := by rw [hqcast]; omega
      exact_mod_cast h'
    · have h' : (0 : ℤ) < ((-p).toNat : ℤ) := by rw [hpcast]; omega
      exact_mod_cast h'
    · calc (0 : ℝ) < x := hx_pos
        _ = (q : ℝ) * α - -(p : ℝ) := by rw [← hpq]; ring
        _ = ((q.toNat : ℕ) : ℝ) * α - (((-p).toNat : ℕ) : ℝ) := by rw [hqR, hpR]
    · calc ((q.toNat : ℕ) : ℝ) * α - (((-p).toNat : ℕ) : ℝ)
          = (q : ℝ) * α - -(p : ℝ) := by rw [hqR, hpR]
        _ = x := by rw [← hpq]; ring
        _ < δ' := hx_lt
        _ ≤ δ := hδ'_le_δ

/-- Specialisation to `α = log 4 / log 3`. -/
lemma exists_small_pos_lin_comb (δ : ℝ) (hδ : 0 < δ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
      0 < (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 ∧
      (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 < δ := by
  have h_irr : Irrational (Real.log 4 / Real.log 3) := log_ratio_irrational
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3ne : Real.log 3 ≠ 0 := hlog3.ne'
  have h_pos : 0 < Real.log 4 / Real.log 3 :=
    div_pos (Real.log_pos (by norm_num)) hlog3
  have hdd : 0 < δ / Real.log 3 := div_pos hδ hlog3
  obtain ⟨m, k, hm, hk, hlo, hhi⟩ :=
    exists_small_pos_lin_comb_help (Real.log 4 / Real.log 3) h_irr h_pos
      (δ / Real.log 3) hdd
  -- Rescale by `log 3`: `(m·(log4/log3) − k)·log3 = m·log4 − k·log3`.
  have heq : (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3
      = ((m : ℝ) * (Real.log 4 / Real.log 3) - (k : ℝ)) * Real.log 3 := by
    field_simp
  refine ⟨m, k, hm, hk, ?_, ?_⟩
  · rw [heq]; exact mul_pos hlo hlog3
  · rw [heq]
    have hcancel : δ / Real.log 3 * Real.log 3 = δ := by field_simp
    have hmul := mul_lt_mul_of_pos_right hhi hlog3
    rwa [hcancel] at hmul

/-- Refinement: also `K ≤ 3^k`. -/
lemma exists_small_pos_lin_comb_large_k (δ : ℝ) (hδ : 0 < δ) (K : ℝ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ K ≤ (3 ^ k : ℝ) ∧
      0 < (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 ∧
      (m : ℝ) * Real.log 4 - (k : ℝ) * Real.log 3 < δ := by
  -- Archimedean: choose `N ≥ 1` with `K ≤ 3 ^ N`.
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt K (by norm_num : (1 : ℝ) < 3)
  set N := N0 + 1 with hNdef
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hKN : K ≤ (3 : ℝ) ^ N := by
    have hmono : (3 : ℝ) ^ N0 ≤ (3 : ℝ) ^ N :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [hN0]
  have hdivN : 0 < δ / (N : ℝ) := div_pos hδ hNR
  obtain ⟨m0, k0, hm0, hk0, hlo, hhi⟩ := exists_small_pos_lin_comb (δ / (N : ℝ)) hdivN
  have hexp : ((N * m0 : ℕ) : ℝ) * Real.log 4 - ((N * k0 : ℕ) : ℝ) * Real.log 3
      = (N : ℝ) * ((m0 : ℝ) * Real.log 4 - (k0 : ℝ) * Real.log 3) := by
    push_cast; ring
  refine ⟨N * m0, N * k0, Nat.mul_pos hNpos hm0, Nat.mul_pos hNpos hk0, ?_, ?_, ?_⟩
  · -- `K ≤ 3 ^ (N * k0)`.
    have hNk : N ≤ N * k0 := Nat.le_mul_of_pos_right N hk0
    have hle : (3 : ℝ) ^ N ≤ (3 : ℝ) ^ (N * k0) :=
      pow_le_pow_right₀ (by norm_num) hNk
    calc K ≤ (3 : ℝ) ^ N := hKN
      _ ≤ (3 : ℝ) ^ (N * k0) := hle
  · rw [hexp]; exact mul_pos hNR hlo
  · rw [hexp]
    have hmul := mul_lt_mul_of_pos_left hhi hNR
    have hcancel : (N : ℝ) * (δ / (N : ℝ)) = δ := by field_simp
    rwa [hcancel] at hmul

/--
**Dirichlet approximation.** For any `ε > 0`, there exist `k, m > 0` with
`3^k ≤ 4^m ≤ 3^k · (1+ε)` and `3^k · ε ≥ 3`.
-/
lemma dirichlet_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ (3 ^ k : ℝ) ≤ 4 ^ m ∧
      (4 ^ m : ℝ) ≤ (3 ^ k : ℝ) * (1 + ε) ∧ (3 ^ k : ℝ) * ε ≥ 3 := by
  have h_log_eps : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  obtain ⟨m, k, hm, hk, hk_large, h_diff_pos, h_diff_lt⟩ :=
    exists_small_pos_lin_comb_large_k (Real.log (1 + ε)) h_log_eps (3 / ε)
  refine ⟨k, m, hk, hm, ?_, ?_, ?_⟩
  · -- `3 ^ k ≤ 4 ^ m`, via monotonicity of `log`.
    have hkpos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    have hmpos : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
    rw [← Real.log_le_log_iff hkpos hmpos, Real.log_pow, Real.log_pow]
    linarith [h_diff_pos]
  · -- `4 ^ m ≤ 3 ^ k · (1 + ε)`.
    have hmpos : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
    have hrhs : (0 : ℝ) < (3 : ℝ) ^ k * (1 + ε) := by positivity
    rw [← Real.log_le_log_iff hmpos hrhs, Real.log_pow,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
    linarith [h_diff_lt]
  · -- `3 ^ k · ε ≥ 3`, from `3 / ε ≤ 3 ^ k`.
    rw [ge_iff_le, ← div_le_iff₀ hε]
    exact hk_large

/-- Algebraic identity used in the scale-step. -/
lemma hz_eq_lemma (x a b a1 a0 b1 b0 k m : ℕ)
    (h1 : 3 ^ k ≤ 4 ^ m) (h3 : x = a + b)
    (h4 : a = a1 * 3 ^ k + a0) (h5 : b = b1 * 4 ^ m + b0) :
    x = (a1 + b1) * 3 ^ k + (a0 + b0 + b1 * (4 ^ m - 3 ^ k)) := by
  have h2 : 4 ^ m = 3 ^ k + (4 ^ m - 3 ^ k) := by omega
  have h6 : b1 * 4 ^ m = b1 * 3 ^ k + b1 * (4 ^ m - 3 ^ k) := by
    calc
      b1 * 4 ^ m = b1 * (3 ^ k + (4 ^ m - 3 ^ k)) := congrArg (b1 * ·) h2
      _ = b1 * 3 ^ k + b1 * (4 ^ m - 3 ^ k) := Nat.mul_add b1 _ _
  have h7 : (a1 + b1) * 3 ^ k = a1 * 3 ^ k + b1 * 3 ^ k := Nat.add_mul a1 b1 _
  omega

/--
**Scale step.** Given a density bound `C` valid on `[0,N)`, we obtain an
improved density bound `(11/12)·C` valid on some larger window `[0,N')`.
-/
lemma scale_step (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) ≤ C * (N : ℝ)) :
    ∃ N' > 0, (((Finset.Ico 0 N').filter (· ∈ A + B)).card : ℝ) ≤
      (11 / 12 : ℝ) * C * (N' : ℝ) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set ε : ℝ := 1 / (24 * (N : ℝ)) with hεdef
  have hε_pos : 0 < ε := by rw [hεdef]; positivity
  have hεN : 2 * ε * (N : ℝ) = 1 / 12 := by rw [hεdef]; field_simp; ring
  obtain ⟨k, m, hk, hm, hkm_le, hkm_ge, hk_large⟩ := dirichlet_approx ε hε_pos
  have h3kR : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have h3k_natR : ((3 ^ k : ℕ) : ℝ) = (3 : ℝ) ^ k := by push_cast; ring
  have h4m_natR : ((4 ^ m : ℕ) : ℝ) = (4 : ℝ) ^ m := by push_cast; ring
  have h3k_le_4m : 3 ^ k ≤ 4 ^ m := by
    have : ((3 ^ k : ℕ) : ℝ) ≤ ((4 ^ m : ℕ) : ℝ) := by rw [h3k_natR, h4m_natR]; exact hkm_le
    exact_mod_cast this
  set zBound : ℝ := (3 : ℝ) ^ k * (5 / 6 + ε * (N : ℝ) + ε / 3) with hzBdef
  have hzBound_nonneg : 0 ≤ zBound := by rw [hzBdef]; positivity
  set M : ℕ := ⌊zBound⌋₊ + 1 with hMdef
  have hMR_ge : zBound < (M : ℝ) := by rw [hMdef]; push_cast; exact Nat.lt_floor_add_one zBound
  have hMR_le : (M : ℝ) ≤ (3 : ℝ) ^ k * (5 / 6 + 2 * ε * (N : ℝ)) := by
    have hstep : (M : ℝ) ≤ zBound + 1 := by
      rw [hMdef]; push_cast; linarith [Nat.floor_le hzBound_nonneg]
    calc (M : ℝ) ≤ zBound + 1 := hstep
      _ ≤ (3 : ℝ) ^ k * (5 / 6 + 2 * ε * (N : ℝ)) := by
          rw [hzBdef]
          have hεN_ge : (N : ℝ) * ((3 : ℝ) ^ k * ε) ≥ (3 : ℝ) ^ k * ε :=
            le_mul_of_one_le_left (by positivity) h1N
          have hgap1 : (1 : ℝ) ≤ (3 : ℝ) ^ k * ε * (2 / 3) := by nlinarith [hk_large]
          have hexpand : (3 : ℝ) ^ k * (5 / 6 + 2 * ε * (N : ℝ))
              = ((3 : ℝ) ^ k * (5 / 6 + ε * (N : ℝ) + ε / 3))
                + ((N : ℝ) * ((3 : ℝ) ^ k * ε) - (3 : ℝ) ^ k * ε / 3) := by ring
          rw [hexpand]
          have hkey : (1 : ℝ) ≤ (N : ℝ) * ((3 : ℝ) ^ k * ε) - (3 : ℝ) ^ k * ε / 3 := by
            nlinarith [hεN_ge, hgap1, hk_large]
          linarith
  refine ⟨N * 3 ^ k, by positivity, ?_⟩
  set S := (Finset.Ico 0 (N * 3 ^ k)).filter (· ∈ A + B) with hSdef
  set T := (Finset.Ico 0 N).filter (· ∈ A + B) with hTdef
  have h_decomp : ∀ x : ℕ, x ∈ S →
      ∃ y z : ℕ, y ∈ T ∧ z ∈ Finset.range M ∧ x = y * 3 ^ k + z := by
    intro x hx
    rw [hSdef, Finset.mem_filter, Finset.mem_Ico] at hx
    obtain ⟨⟨_, hx_lt⟩, hx_mem⟩ := hx
    rcases Set.mem_add.mp hx_mem with ⟨a, ha, b, hb, hab⟩
    rcases A_decomp k a ha with ⟨a1, a0, ha1, ha0, ha0_lt, ha_eq⟩
    rcases B_decomp m b hb with ⟨b1, b0, hb1, hb0, hb0_lt, hb_eq⟩
    have hz_eq : x = (a1 + b1) * 3 ^ k + (a0 + b0 + b1 * (4 ^ m - 3 ^ k)) :=
      hz_eq_lemma x a b a1 a0 b1 b0 k m h3k_le_4m hab.symm ha_eq hb_eq
    have hy_lt : a1 + b1 < N := by
      by_contra hle
      push_neg at hle
      have hmul : N * 3 ^ k ≤ (a1 + b1) * 3 ^ k := Nat.mul_le_mul_right _ hle
      have : N * 3 ^ k ≤ x := by rw [hz_eq]; omega
      omega
    refine ⟨a1 + b1, a0 + b0 + b1 * (4 ^ m - 3 ^ k), ?_, ?_, hz_eq⟩
    · rw [hTdef, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨Nat.zero_le _, hy_lt⟩, Set.add_mem_add ha1 hb1⟩
    · rw [Finset.mem_range]
      have hb1_lt : b1 < N := lt_of_le_of_lt (Nat.le_add_left b1 a1) hy_lt
      have ha0_le : a0 ≤ (3 ^ k - 1) / 2 := A_max_k k a0 ha0_lt ha0
      have hb0_le : b0 ≤ (4 ^ m - 1) / 3 := B_max_m m b0 hb0_lt hb0
      have h2a0 : (2 : ℝ) * (a0 : ℝ) + 1 ≤ (3 : ℝ) ^ k := by
        have h2a0N : 2 * a0 + 1 ≤ 3 ^ k := by
          have hP : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num); omega
        have : ((2 * a0 + 1 : ℕ) : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by exact_mod_cast h2a0N
        rw [h3k_natR] at this; push_cast at this; linarith
      have h3b0 : (3 : ℝ) * (b0 : ℝ) + 1 ≤ (4 : ℝ) ^ m := by
        have h3b0N : 3 * b0 + 1 ≤ 4 ^ m := by
          have hP : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num); omega
        have : ((3 * b0 + 1 : ℕ) : ℝ) ≤ ((4 ^ m : ℕ) : ℝ) := by exact_mod_cast h3b0N
        rw [h4m_natR] at this; push_cast at this; linarith
      have hgap_natR : (((4 ^ m - 3 ^ k : ℕ)) : ℝ) = (4 : ℝ) ^ m - (3 : ℝ) ^ k := by
        rw [Nat.cast_sub h3k_le_4m, h4m_natR, h3k_natR]
      have hgapR : (4 : ℝ) ^ m - (3 : ℝ) ^ k ≤ (3 : ℝ) ^ k * ε := by nlinarith [hkm_ge]
      have hb1R : (b1 : ℝ) < (N : ℝ) := by exact_mod_cast hb1_lt
      have hzcastR : ((a0 + b0 + b1 * (4 ^ m - 3 ^ k) : ℕ) : ℝ)
          = (a0 : ℝ) + (b0 : ℝ) + (b1 : ℝ) * ((4 : ℝ) ^ m - (3 : ℝ) ^ k) := by
        push_cast [hgap_natR]; ring
      have hz_le_bound : ((a0 + b0 + b1 * (4 ^ m - 3 ^ k) : ℕ) : ℝ) ≤ zBound := by
        rw [hzcastR, hzBdef]
        have hb1gap : (b1 : ℝ) * ((4 : ℝ) ^ m - (3 : ℝ) ^ k)
            ≤ (N : ℝ) * ((3 : ℝ) ^ k * ε) := by
          have hh1 : (b1 : ℝ) * ((4 : ℝ) ^ m - (3 : ℝ) ^ k)
              ≤ (b1 : ℝ) * ((3 : ℝ) ^ k * ε) :=
            mul_le_mul_of_nonneg_left hgapR (by positivity)
          have hh2 : (b1 : ℝ) * ((3 : ℝ) ^ k * ε) ≤ (N : ℝ) * ((3 : ℝ) ^ k * ε) :=
            mul_le_mul_of_nonneg_right hb1R.le (by positivity)
          linarith
        have ha0R : (a0 : ℝ) ≤ (3 : ℝ) ^ k / 2 := by linarith [h2a0]
        have hb0R : (b0 : ℝ) ≤ (3 : ℝ) ^ k / 3 + (3 : ℝ) ^ k * ε / 3 := by
          have h4m_le : (4 : ℝ) ^ m ≤ (3 : ℝ) ^ k * (1 + ε) := hkm_ge
          linarith [h3b0, h4m_le]
        have hexpand : (3 : ℝ) ^ k * (5 / 6 + ε * (N : ℝ) + ε / 3)
            = (3 : ℝ) ^ k / 2 + ((3 : ℝ) ^ k / 3 + (3 : ℝ) ^ k * ε / 3)
              + (N : ℝ) * ((3 : ℝ) ^ k * ε) := by ring
        rw [hexpand]
        linarith [ha0R, hb0R, hb1gap]
      have hzlt : ((a0 + b0 + b1 * (4 ^ m - 3 ^ k) : ℕ) : ℝ) < (M : ℝ) :=
        lt_of_le_of_lt hz_le_bound hMR_ge
      exact_mod_cast hzlt
  choose! yOf zOf hy_mem hz_mem hxeq using h_decomp
  have h_card_le : S.card ≤ T.card * M := by
    have hmap : S.card ≤ (T ×ˢ Finset.range M).card := by
      apply Finset.card_le_card_of_injOn (fun x => (yOf x, zOf x))
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_product]
        exact ⟨hy_mem x hx, hz_mem x hx⟩
      · intro x hx x' hx' heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hy, hz⟩ := heq
        rw [hxeq x hx, hxeq x' hx', hy, hz]
    calc S.card ≤ (T ×ˢ Finset.range M).card := hmap
      _ = T.card * M := by rw [Finset.card_product, Finset.card_range]
  have hScast : (S.card : ℝ) ≤ (T.card : ℝ) * (M : ℝ) := by exact_mod_cast h_card_le
  have hC_nonneg : 0 ≤ C := by
    by_contra hCneg
    push_neg at hCneg
    have hlt : C * (N : ℝ) < 0 := mul_neg_of_neg_of_pos hCneg hNR
    have hTle : (T.card : ℝ) ≤ C * (N : ℝ) := hC
    have hTnn := Nat.cast_nonneg (α := ℝ) T.card
    linarith
  have hstep1 : (S.card : ℝ)
      ≤ (C * (N : ℝ)) * ((3 : ℝ) ^ k * (5 / 6 + 2 * ε * (N : ℝ))) := by
    calc (S.card : ℝ) ≤ (T.card : ℝ) * (M : ℝ) := hScast
      _ ≤ (C * (N : ℝ)) * ((3 : ℝ) ^ k * (5 / 6 + 2 * ε * (N : ℝ))) :=
          mul_le_mul hC hMR_le (Nat.cast_nonneg _) (mul_nonneg hC_nonneg hNR.le)
  have hfinal : (C * (N : ℝ)) * ((3 : ℝ) ^ k * (5 / 6 + 2 * ε * (N : ℝ)))
      = (11 / 12 : ℝ) * C * ((N * 3 ^ k : ℕ) : ℝ) := by
    rw [hεN]; push_cast; ring
  rw [← hfinal]; exact hstep1

/-- Iterated scale step: `(11/12)^d · N` bound. -/
lemma density_multi_scale (d : ℕ) :
    ∃ N > 0, (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) ≤
      ((11 / 12 : ℝ) ^ d) * (N : ℝ) := by
  induction d with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    simp only [pow_zero, one_mul]
    have h1 : (((Finset.Ico 0 1).filter (· ∈ A + B)).card : ℝ) ≤
        ((Finset.Ico 0 1).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    have h2 : (Finset.Ico 0 1).card = 1 := rfl
    rw [h2] at h1
    push_cast at h1 ⊢
    exact h1
  | succ d ih =>
    rcases ih with ⟨N, hN, h_bound⟩
    obtain ⟨N', hN', h_bound'⟩ := scale_step N hN ((11 / 12 : ℝ) ^ d) h_bound
    refine ⟨N', hN', ?_⟩
    have h_mul : (11 / 12 : ℝ) ^ (d + 1) = (11 / 12 : ℝ) * (11 / 12 : ℝ) ^ d := by
      rw [pow_add, pow_one]; ring
    rw [h_mul]
    linarith

/-- For any `ε > 0`, there exists `d` with `(11/12)^d ≤ ε`. -/
lemma limit_11_12 (ε : ℝ) (hε : ε > 0) : ∃ d : ℕ, (11 / 12 : ℝ) ^ d ≤ ε :=
  (exists_pow_lt_of_lt_one hε (by norm_num)).imp (fun _ => le_of_lt)

/--
**Density-tends-to-zero lemma.** For every `ε > 0`, some window `[0,N)` has
`|A + B ∩ [0,N)| ≤ ε · N`. This is the key consequence of multi-scale
iteration.
-/
lemma density_tends_to_zero (ε : ℝ) (hε : ε > 0) :
    ∃ N > 0, (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) ≤ ε * (N : ℝ) := by
  obtain ⟨d, hd2⟩ := limit_11_12 ε hε
  obtain ⟨N, hN, h_bound⟩ := density_multi_scale d
  refine ⟨N, hN, ?_⟩
  have hN' : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le _
  calc (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ)
      ≤ ((11 / 12 : ℝ) ^ d) * (N : ℝ) := h_bound
    _ ≤ ε * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hd2 hN'

/- ## Main theorem -/

/--
**AlphaProof Nexus result (2026-05-21):** the sumset `A + B` has
**lower density equal to zero**.

In particular, the `positive_lower_density` variant of Erdős Problem #125
is **resolved in the negative**: $\liminf_{x \to \infty} |C \cap [1,x]|/x = 0$.

Source: `APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`
in https://github.com/google-deepmind/alphaproof-nexus-results.
-/
theorem AB_lowerDensity_eq_zero : lowerDensity (A + B) = 0 := by
  -- `lowerDensity` is the `liminf` of the partial densities; we show the
  -- partial densities are nonnegative, bounded by `1`, and frequently `≤ ε`
  -- for every `ε > 0`.  The last point uses `density_tends_to_zero` together
  -- with the observation that a window `[0,N)` of density `≤ ε'` must satisfy
  -- `N ≥ 1/ε'` (because `0 ∈ A + B` forces at least one element), so the
  -- small-density windows go to infinity.
  have h_nonneg : ∀ b : ℕ, 0 ≤ partialDensity (A + B) b := fun b =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h_le_one : ∀ b : ℕ, partialDensity (A + B) b ≤ 1 := by
    intro b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [partialDensity]
    · have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hcard : (interIio (A + B) b).card ≤ b := by
        calc (interIio (A + B) b).card
            ≤ (Finset.range b).card := Finset.card_filter_le _ _
          _ = b := Finset.card_range b
      rw [partialDensity, div_le_iff₀ hbR, one_mul]
      exact_mod_cast hcard
  have h_bdd_ge : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun b : ℕ => partialDensity (A + B) b) :=
    Filter.isBoundedUnder_of ⟨0, fun b => h_nonneg b⟩
  have h_bdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun b : ℕ => partialDensity (A + B) b) :=
    Filter.isBoundedUnder_of ⟨1, fun b => h_le_one b⟩
  have h_freq : ∀ ε : ℝ, 0 < ε →
      ∃ᶠ b in atTop, partialDensity (A + B) b ≤ ε := by
    intro ε hε
    rw [Filter.frequently_atTop]
    intro N₀
    have hpos : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
    have hε' : 0 < min ε (1 / ((N₀ : ℝ) + 1)) := lt_min hε (by positivity)
    obtain ⟨N, hN, hcard⟩ := density_tends_to_zero _ hε'
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hcard_eq : (Finset.Ico 0 N).filter (· ∈ A + B) = interIio (A + B) N := by
      rw [interIio, Nat.Ico_zero_eq_range]
    have hone : (1 : ℝ) ≤ (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) := by
      have h0 : (0 : ℕ) ∈ (Finset.Ico 0 N).filter (· ∈ A + B) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_rfl, hN⟩, zero_in_A_plus_B⟩
      exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
    refine ⟨N, ?_, ?_⟩
    · -- `N₀ ≤ N`: from `1 ≤ card ≤ ε' · N ≤ N/(N₀+1)`.
      have h1 : (1 : ℝ) ≤ 1 / ((N₀ : ℝ) + 1) * (N : ℝ) := by
        calc (1 : ℝ) ≤ (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ) := hone
          _ ≤ min ε (1 / ((N₀ : ℝ) + 1)) * (N : ℝ) := hcard
          _ ≤ 1 / ((N₀ : ℝ) + 1) * (N : ℝ) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hNR.le
      rw [one_div_mul_eq_div, le_div_iff₀ hpos, one_mul] at h1
      have h2 : N₀ + 1 ≤ N := by exact_mod_cast h1
      omega
    · -- `partialDensity (A+B) N ≤ ε`.
      rw [partialDensity, ← hcard_eq, div_le_iff₀ hNR]
      calc (((Finset.Ico 0 N).filter (· ∈ A + B)).card : ℝ)
          ≤ min ε (1 / ((N₀ : ℝ) + 1)) * (N : ℝ) := hcard
        _ ≤ ε * (N : ℝ) := mul_le_mul_of_nonneg_right (min_le_left _ _) hNR.le
  rw [lowerDensity]
  refine le_antisymm ?_ ?_
  · -- `liminf ≤ 0`: otherwise `liminf ≤ liminf/2` gives a contradiction.
    by_contra hlt
    push_neg at hlt
    have hhalf : 0 < atTop.liminf (fun b : ℕ => partialDensity (A + B) b) / 2 := by
      linarith
    have hle : atTop.liminf (fun b : ℕ => partialDensity (A + B) b) ≤
        atTop.liminf (fun b : ℕ => partialDensity (A + B) b) / 2 :=
      Filter.liminf_le_of_frequently_le (h_freq _ hhalf) h_bdd_ge
    linarith
  · -- `0 ≤ liminf`: the partial densities are nonnegative.
    exact Filter.le_liminf_of_le h_bdd_le.isCoboundedUnder_ge
      (Filter.Eventually.of_forall h_nonneg)

/--
**Corollary:** the lower density of `A + B` is *not* positive — i.e., the
positive_lower_density form of Erdős #125 fails.
-/
theorem not_positive_lowerDensity_AB : ¬ (0 < lowerDensity (A + B)) := by
  intro h
  have h0 : lowerDensity (A + B) = 0 := AB_lowerDensity_eq_zero
  rw [h0] at h
  exact lt_irrefl 0 h

end Erdos125Aristotle
