/-
# Erdős Problem #125 — `positive_lower_density` variant

## Status

The **positive_lower_density** variant of Erdős Problem #125 has been
**resolved in the negative** by DeepMind's AlphaProof Nexus system (2026-05-21,
arXiv:2605.22763v1). That is, the sumset $C = A + B$ where
$A = \{n \in \mathbb{N} : \text{digits of } n \text{ in base } 3 \text{ are } 0 \text{ or } 1\}$
and
$B = \{n \in \mathbb{N} : \text{digits of } n \text{ in base } 4 \text{ are } 0 \text{ or } 1\}$
has **lower density equal to zero**. The original Erdős conjecture asked whether
$\liminf_{x \to \infty} |C \cap [1,x]|/x > 0$; AlphaProof Nexus answered NO.

## Provenance

This file integrates DeepMind's AlphaProof Nexus Lean proof:
- Source: `APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`
- Repository: https://github.com/google-deepmind/alphaproof-nexus-results
- Paper: arXiv:2605.22763v1 (2026-05-21)
- Natural-language proof: `NaturalLanguageProofs/ErdosProblems/erdos125.pdf`

The original AlphaProof proof depends on `FormalConjectures.Util.ProblemImports`,
which in turn provides `Set.partialDensity` / `Set.lowerDensity` via
`FormalConjecturesForMathlib`. Since Lean Genius uses only Mathlib v4.26.0,
we inline the relevant density definitions below.

## Caveats

The AlphaProof Nexus proof is 370 lines of highly compressed automated-proof-search
tactic output. Many lemmas use elaborate one-line proofs that interleave dozens of
tactics including `bound`, `valid`, and other custom tactics from FormalConjectures.
A faithful line-by-line port is left as a follow-up task; this file presently
**states** each lemma with a `sorry` placeholder so the high-level structure
matches the AlphaProof source, and the dependency graph is correct.

## Proof strategy (from the natural-language note)

The key idea is a **multi-scale density argument**:
1. Use Dirichlet approximation (via irrationality of `log 4 / log 3`) to find
   integers `k, m` with `3^k ≈ 4^m`.
2. Decompose any `a ∈ A` as `a = a₁ · 3^k + a₀` with `a₁ ∈ A`, `a₀ ∈ A`, `a₀ < 3^k`
   (and similarly for `B` with `4^m`).
3. Show that at each scale, only a `5/6 + o(1)` fraction of the interval `[0, 3^k)`
   can be represented by `A + B` residues. This gives `density(A+B ∩ [0, N·3^k]) ≤
   (11/12) · density(A+B ∩ [0, N])`.
4. Iterating yields `density → 0`.

## References

- Burr, Erdős, Graham, Li (1996): original conjecture.
- Melfi (2001): `|C ∩ [1,x]| ≫ x^{0.965}`.
- Hasler, Melfi (2024): improved to `x^{0.9777}`, upper density `≤ 0.696`.
- **DeepMind AlphaProof Nexus (2026-05-21)**: lower density `= 0`. (This file.)
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Nat Pointwise Filter
open scoped Topology Classical

namespace Erdos125PositiveLowerDensity

/-! ## Density definitions (inlined from FormalConjecturesForMathlib) -/

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

/-! ## The digit-restricted sets A and B -/

/-- `A` = naturals whose base-3 digits are all `0` or `1`. -/
def A : Set ℕ := { x : ℕ | (Nat.digits 3 x).toFinset ⊆ {0, 1} }

/-- `B` = naturals whose base-4 digits are all `0` or `1`. -/
def B : Set ℕ := { x : ℕ | (Nat.digits 4 x).toFinset ⊆ {0, 1} }

/-! ## Supporting lemmas

The lemmas below mirror exactly the structure of the AlphaProof Nexus proof
(see https://github.com/google-deepmind/alphaproof-nexus-results, file
`APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`).
Their one-line AlphaProof tactic proofs do not port cleanly to a pure Mathlib
setup; we therefore state them with `sorry` here. A faithful line-by-line port
is tracked as a follow-up sub-issue. -/

lemma zero_in_A : 0 ∈ A := by
  -- AlphaProof: `norm_num`
  simp [A]

lemma zero_in_B : 0 ∈ B := by
  -- AlphaProof: `bound`
  simp [B]

lemma zero_in_A_plus_B : 0 ∈ A + B := by
  refine ⟨0, zero_in_A, 0, zero_in_B, ?_⟩
  simp

/-! ### Digit helper lemmas for `A` (base 3)

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

/-! ### Digit helper lemmas for `B` (base 4) -/

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
  sorry

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
  sorry

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

/-! ## Main theorem -/

/--
**AlphaProof Nexus result (2026-05-21):** the sumset `A + B` has
**lower density equal to zero**.

In particular, the `positive_lower_density` variant of Erdős Problem #125
is **resolved in the negative**: $\liminf_{x \to \infty} |C \cap [1,x]|/x = 0$.

Source: `APNOutputs/ErdosProblems/erdos_125.variants.positive_lower_density.lean`
in https://github.com/google-deepmind/alphaproof-nexus-results.
-/
theorem AB_lowerDensity_eq_zero : lowerDensity (A + B) = 0 := by
  sorry

/--
**Corollary:** the lower density of `A + B` is *not* positive — i.e., the
positive_lower_density form of Erdős #125 fails.
-/
theorem not_positive_lowerDensity_AB : ¬ (0 < lowerDensity (A + B)) := by
  intro h
  have h0 : lowerDensity (A + B) = 0 := AB_lowerDensity_eq_zero
  rw [h0] at h
  exact lt_irrefl 0 h

end Erdos125PositiveLowerDensity
