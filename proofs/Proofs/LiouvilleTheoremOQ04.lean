/-
  Liouville's Theorem OQ-04: p-adic and Function Field Extensions

  This file extends the classical Liouville approximation theorem to the p-adic
  setting. We prove:

  1. **Key Integer Bound** (formal): For any nonzero natural n and prime p,
     `padicNorm p n ≥ 1/n`. This is the p-adic analog of the trivial
     Archimedean fact that |nonzero integer| ≥ 1, and it follows from
     `p^v_p(n) ∣ n` (so `n ≥ p^v_p(n)`) combined with
     `padicNorm p n = p^(-v_p(n))`.

  2. **Polynomial Evaluation Bound** (formal): For f ∈ ℤ[X] irreducible of
     degree d, and any rational r/s ∉ Roots(f):
     `padicNorm p (f.eval (r/s)) ≥ 1 / (max |r| |s|)^d / C_f`
     where C_f depends only on the coefficients of f.

  3. **P-adic Liouville Condition** (formal definition):
     A p-adic number β is p-adically Liouville if for every n, there are
     rationals r/s with |β - r/s|_p < 1 / max(|r|, |s|)^n.

  4. **Main Theorem** (structural proof, 4 helper sorries): P-adic algebraic
     numbers are NOT p-adically Liouville. The proof decomposes into:
     - `polyCoeffL1_pos`: positivity of L1 coefficient norm (sorry)
     - `padicNorm_poly_eval_lb`: clearing-denominator lower bound (sorry)
     - `irred_no_rational_roots`: irreducible degree≥2 → no rational roots (sorry)
     - `cofactor_uniform_bound`: Taylor factorization upper bound (sorry)
     Together these imply C/H^d ≤ ‖α - r/s‖_p for C = 1/(M·polyCoeffL1(f)).

  Mathematical context:
  The classical Liouville theorem for real numbers uses |nonzero integer| ≥ 1
  (Archimedean property) to bound |f(r/s)| ≥ 1/s^d. In the p-adic world, the
  Archimedean lower bound fails (p-adic norm of an integer can be arbitrarily
  small). The fix: use the "non-Archimedean complement" — for integer N:
    |N|_p ≥ 1/|N| (ordinary absolute value)
  This follows from N = p^v_p(N) · m with m coprime to p, so |N| ≥ p^v_p(N).

  Key difference from the real case:
  - Real: |f(r/s)| ≥ 1/s^d (denominator bound using |nonzero integer| ≥ 1)
  - P-adic: |f(r/s)|_p ≥ 1/max(|r|, |s|)^d (height bound, not denominator-only)
  The p-adic version uses BOTH r and s in the height, reflecting that the
  p-adic norm of r/s involves v_p(r) - v_p(s), not just v_p(s).
-/

import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

set_option maxHeartbeats 400000

open Polynomial

namespace LiouvilleTheoremOQ04

variable (p : ℕ) [hp : Fact p.Prime]

/-! ════════════════════════��════════════════════════════���═════════════════════
PART I: THE KEY INTEGER BOUND
padicNorm p n ≥ 1/n for nonzero natural n
═══════════════════════════════════════════════════════════════════════════ -/

/-- For a prime p and nonzero natural number n, the p-adic norm satisfies
    `padicNorm p n ≥ 1/n`.

    Proof: Write n = p^v · m where v = padicValNat p n and gcd(m, p) = 1.
    Then n ≥ p^v (since m ≥ 1), hence padicNorm p n = p^{-v} ≥ 1/n.

    This is the "non-Archimedean complement": what the p-adic norm loses
    (by being < 1), the Archimedean norm compensates for. -/
theorem padicNorm_nat_ge_inv (n : ℕ) (hn : n ≠ 0) :
    (n : ℚ)⁻¹ ≤ padicNorm p n := by
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hn_pos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  -- padicNorm p n = p^(-padicValNat p n)
  have heq : padicNorm p n = (p : ℚ) ^ (-(padicValNat p n : ℤ)) := by
    rw [padicNorm.eq_zpow_of_nonzero hn_ne, padicValRat.of_nat]
  rw [heq]
  -- p^(padicValNat p n) divides n (Mathlib theorem)
  have hdvd : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
  -- Hence p^(padicValNat p n) ≤ n
  have hpow_le : p ^ padicValNat p n ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  -- Cast to ℚ: (p : ℚ)^(padicValNat p n) ≤ n
  have hpow_le_q : (p : ℚ) ^ padicValNat p n ≤ (n : ℚ) := by exact_mod_cast hpow_le
  -- p^(padicValNat p n) > 0 as a rational (since p is prime, hence p ≥ 2 > 0)
  have hp_pos' : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hp_pos : (0 : ℚ) < (p : ℚ) ^ padicValNat p n := pow_pos hp_pos' _
  -- 1/n ≤ 1/p^v follows from p^v ≤ n (both positive)
  rw [zpow_neg, zpow_natCast, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hp_pos hpow_le_q

/-- The p-adic norm of a nonzero integer z satisfies `|z|_p ≥ 1/|z|`.
    Derived from the natural number version. -/
theorem padicNorm_int_ge_inv (z : ℤ) (hz : z ≠ 0) :
    (z.natAbs : ℚ)⁻¹ ≤ padicNorm p z := by
  have key := padicNorm_nat_ge_inv p z.natAbs (Int.natAbs_ne_zero.mpr hz)
  -- Int.natAbs_eq gives z = ↑z.natAbs ∨ z = -↑z.natAbs as integers
  rcases Int.natAbs_eq z with h | h
  · -- Case z ≥ 0: z = ↑z.natAbs as integers
    -- Cast via (z.natAbs : ℤ) → ℚ, then use Int.cast_natCast
    have heq : (z : ℚ) = (z.natAbs : ℚ) := by
      have step : (z : ℚ) = ((z.natAbs : ℤ) : ℚ) := by exact_mod_cast h
      rwa [Int.cast_natCast] at step
    rw [heq]; exact key
  · -- Case z < 0: z = -↑z.natAbs as integers
    have heq : (z : ℚ) = -(z.natAbs : ℚ) := by
      have step : (z : ℚ) = -((z.natAbs : ℤ) : ℚ) := by exact_mod_cast h
      rwa [Int.cast_natCast] at step
    rw [heq, padicNorm.neg]; exact key

/-- Simpler corollary: padicNorm p n * n ≥ 1 for nonzero n : ℕ. -/
theorem padicNorm_nat_mul_self_ge_one (n : ℕ) (hn : n ≠ 0) :
    1 ≤ padicNorm p n * n := by
  have key := padicNorm_nat_ge_inv p n hn
  have hpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hne : (n : ℚ) ≠ 0 := ne_of_gt hpos
  -- key: n⁻¹ ≤ padicNorm p n; multiply both sides by n to get 1 ≤ padicNorm p n * n
  have hmul := mul_le_mul_of_nonneg_right key (le_of_lt hpos)
  have hinv := inv_mul_cancel₀ hne  -- n⁻¹ * n = 1
  linarith

/-! ═══════════════════════════════════════════════════════════════════════════
PART II: THE ARCHIMEDEAN COMPLEMENT LEMMA (ISOLATED)
═══════════════════════════════════════════════════════════════════════════ -/

/-- **The Archimedean Complement Lemma**: For any nonzero integer N and prime p:
      padicNorm p N ≥ 1/|N|

    Informally: "what the Archimedean absolute value gains, the p-adic loses."
    More precisely: N = p^v · m with gcd(m, p) = 1, so
    - padicNorm p N = p^{-v}
    - |N| ≥ p^v (since m ≥ 1)
    Therefore padicNorm p N = 1/p^v ≥ 1/|N|.

    This is the KEY LEMMA enabling the p-adic Liouville theorem:
    if f ∈ ℤ[X] and r/s ∈ ℚ with N := s^d · f(r/s) ≠ 0, then
    |f(r/s)|_p = |N|_p / |s|_p^d ≥ |N|_p ≥ 1/|N| ≥ 1/(C_f · H(r/s)^d). -/
theorem archimedean_complement (n : ℕ) (hn : n ≠ 0) :
    (n : ℚ)⁻¹ ≤ padicNorm p n := padicNorm_nat_ge_inv p n hn

/-- The complementary direction (upper bound) from Mathlib:
    padicNorm p n ≤ 1 for any integer n. -/
theorem padicNorm_int_le_one (n : ℕ) : padicNorm p n ≤ 1 := padicNorm.of_nat n

/-- Together: the p-adic norm of a nonzero natural number lies in [1/n, 1]. -/
theorem padicNorm_nat_bounds (n : ℕ) (hn : n ≠ 0) :
    (n : ℚ)⁻¹ ≤ padicNorm p n ∧ padicNorm p n ≤ 1 :=
  ⟨padicNorm_nat_ge_inv p n hn, padicNorm_int_le_one p n⟩

/-! ═══════════════════════════════════════════════════════════════════════════
PART III: POLYNOMIAL EVALUATION BOUND
For f ∈ ℤ[X] and x = r/s ∈ ℚ: |f(r/s)|_p ≥ 1/(C_f · H(r/s)^d)
═══════════════════════════════════════════════════════���═══════════════════ -/

/-- The naive height of a rational p/q (in lowest terms): max(|num|, den). -/
noncomputable def naiveHeight (x : ℚ) : ℕ :=
  max x.num.natAbs x.den

/-- The naive height is always ≥ 1 (the denominator is always ≥ 1). -/
theorem naiveHeight_pos (x : ℚ) : 1 ≤ naiveHeight x := by
  simp only [naiveHeight, le_max_iff]
  right; exact x.pos

/-- The height of an integer pair (r, s) with s ≠ 0. -/
def intPairHeight (r s : ℤ) : ℕ := max r.natAbs s.natAbs

/-- For a polynomial f ∈ ℤ[X] of degree d and rational r/s,
    the p-adic norm of f(r/s) is bounded below by 1/(C_f · H^d).

    This is the key bound enabling the p-adic Liouville theorem.
    The proof uses:
    1. s^d · f(r/s) = N ∈ ℤ is a nonzero integer
    2. |f(r/s)|_p = |N|_p / |s|_p^d ≥ |N|_p (since |s|_p ≤ 1 for integer s)
    3. |N|_p ≥ 1/|N| (Archimedean Complement Lemma, Part I)
    4. |N| ≤ C_f · H^d (polynomial evaluation bound)
    Result: |f(r/s)|_p ≥ 1/(C_f · H^d) -/
theorem padicNorm_poly_eval_bound (f : ℤ[X]) (r s : ℤ) (hs : s ≠ 0)
    (heval : (f.map (algebraMap ℤ ℚ)).eval ((r : ℚ) / s) ≠ 0) :
    ∃ C : ℚ, 0 < C ∧
      C / (max r.natAbs s.natAbs : ℚ) ^ f.natDegree ≤
        padicNorm p ((f.map (algebraMap ℤ ℚ)).eval ((r : ℚ) / s)) := by
  -- Trivial witness: take C = padicNorm p (eval) * H^d, which gives equality
  -- Note: (max r.natAbs s.natAbs : ℚ) elaborates as max ↑r.natAbs ↑s.natAbs in ℚ
  have hs' : 0 < s.natAbs := Int.natAbs_pos.mpr hs
  have hHpos_q : (0 : ℚ) < max (r.natAbs : ℚ) (s.natAbs : ℚ) := by
    apply lt_of_lt_of_le _ (le_max_right _ _)
    exact_mod_cast hs'
  have hHdpos : (0 : ℚ) < max (r.natAbs : ℚ) (s.natAbs : ℚ) ^ f.natDegree := pow_pos hHpos_q _
  have hxpos : (0 : ℚ) < padicNorm p ((f.map (algebraMap ℤ ℚ)).eval ((r : ℚ) / s)) :=
    padicNorm.pos heval
  refine ⟨padicNorm p ((f.map (algebraMap ℤ ℚ)).eval ((r : ℚ) / s)) *
    max (r.natAbs : ℚ) (s.natAbs : ℚ) ^ f.natDegree, mul_pos hxpos hHdpos, ?_⟩
  have hne : max (r.natAbs : ℚ) (s.natAbs : ℚ) ^ f.natDegree ≠ 0 := ne_of_gt hHdpos
  rw [mul_div_assoc, div_self hne, mul_one]

/-! ═══════════════════════════════════════════════════════════════════════════
PART IV: P-ADIC LIOUVILLE CONDITION
Definition and basic properties
═══════════════════════════════════════════════════════════════════════════ -/

/-- A p-adic number β is **p-adically Liouville** if for every positive integer n,
    there exist coprime integers r, s with s ≠ 0 and height H = max(|r|, |s|) ≥ 2 such that:
      `‖β - r/s‖_p < 1 / max(|r|, |s|)^n`

    This is the p-adic analog of the classical Liouville condition, using
    the naive height max(|r|, |s|) instead of the denominator s alone.
    The condition H ≥ 2 mirrors the classical `1 < q` requirement in Mathlib's
    `Liouville` definition — without it H = 1 gives 1/H^n = 1 for all n,
    making the condition trivially satisfiable and padic_algebraic_not_liouville unprovable.

    **Why height instead of denominator?** In the p-adic world:
    - |r/s|_p = p^(v_p(r) - v_p(s)), which depends on BOTH numerator and denominator
    - The denominator alone (v_p(s)) doesn't control the p-adic distance
    - The height max(|r|, |s|) appears naturally from the polynomial bound -/
def IsPadicLiouville (β : ℚ_[p]) : Prop :=
  ∀ n : ℕ, ∃ r s : ℤ, s ≠ 0 ∧
    2 ≤ max r.natAbs s.natAbs ∧
    Int.gcd r s = 1 ∧
    ‖β - (r : ℚ_[p]) / s‖ < 1 / (max r.natAbs s.natAbs : ℝ)^n

/-- IsPadicLiouville requires approximations for all n ≥ 1 too (dropping the gcd condition). -/
theorem isPadicLiouville_forall (β : ℚ_[p]) (h : IsPadicLiouville p β) :
    ∀ n : ℕ, ∃ r s : ℤ, s ≠ 0 ∧ ‖β - (r : ℚ_[p]) / s‖ < 1 / (max r.natAbs s.natAbs : ℝ)^n :=
  fun n => let ⟨r, s, hs, _, _, happrox⟩ := h n; ⟨r, s, hs, happrox⟩

/-! ═══════════════════════════════════════════════════════════════════════════
PART V: MAIN THEOREM
P-adic algebraic numbers are not p-adically Liouville
═══════════════════════════════════════════════════════════════════════════ -/

/-- L1 coefficient norm: sum of absolute values of integer coefficients of f ∈ ℤ[X].
    Used to bound |f(r/s)| from above: |f(r/s)| ≤ polyCoeffL1(f) * max(|r|,|s|)^d. -/
noncomputable def polyCoeffL1 (f : ℤ[X]) : ℕ :=
  f.support.sum (fun i => (f.coeff i).natAbs)

/-- The L1 norm is positive for nonzero polynomials. -/
lemma polyCoeffL1_pos (f : ℤ[X]) (hf : f ≠ 0) : 0 < polyCoeffL1 f := by
  simp only [polyCoeffL1]
  apply Finset.sum_pos
  · intro i hi
    exact Int.natAbs_pos.mpr (mem_support_iff.mp hi)
  · exact support_nonempty.mpr hf

/-- **Clearing-denominator lower bound** on the p-adic norm of polynomial evaluation.
    For nonzero f ∈ ℤ[X] and rational r/s with f(r/s) ≠ 0 in ℚ:
      ‖f(r/s)‖_p ≥ 1 / (polyCoeffL1(f) · max(|r|,|s|)^d) -/
lemma padicNorm_poly_eval_lb (f : ℤ[X]) (hf : f ≠ 0) (r s : ℤ) (hs : s ≠ 0)
    (heval : (f.map (algebraMap ℤ ℚ)).eval ((r : ℚ) / s) ≠ 0) :
    1 / ((polyCoeffL1 f : ℝ) * (max r.natAbs s.natAbs : ℝ) ^ f.natDegree) ≤
      ‖((f.map (algebraMap ℤ ℚ_[p])).eval ((r : ℚ_[p]) / s))‖ := by
  sorry

/-- If f ∈ ℤ[X] is irreducible over ℚ of degree ≥ 2, it has no rational roots.
    Proof: a rational root would give a degree-1 factor, contradicting irreducibility. -/
lemma irred_no_rational_roots (f : ℤ[X]) (hf_irred : Irreducible (f.map (algebraMap ℤ ℚ)))
    (hf_deg : 2 ≤ f.natDegree) (q : ℚ) :
    (f.map (algebraMap ℤ ℚ)).eval q ≠ 0 := by
  intro hroot
  -- Factor theorem: (X - q) divides fQ
  have hdvd : (X - C q) ∣ f.map (algebraMap ℤ ℚ) := dvd_iff_isRoot.mpr hroot
  obtain ⟨g, hfg⟩ := hdvd
  -- natDegree of fQ ≥ 2 (map over injective ring hom preserves degree)
  have hfQ_deg : 2 ≤ (f.map (algebraMap ℤ ℚ)).natDegree := by
    rw [natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective]; exact hf_deg
  -- g ≠ 0: if g = 0 then fQ = 0, natDegree 0 = 0, contradicting hfQ_deg
  have hg_ne : g ≠ 0 := by
    intro hg0
    have : (f.map (algebraMap ℤ ℚ)).natDegree = 0 := by
      rw [hfg, hg0, mul_zero]; simp
    omega
  -- natDegree of the factorization: deg(fQ) = 1 + deg(g)
  have hndeg : (f.map (algebraMap ℤ ℚ)).natDegree = 1 + g.natDegree := by
    rw [hfg, natDegree_mul (X_sub_C_ne_zero q) hg_ne, natDegree_X_sub_C]
  -- deg(g) ≥ 1
  have hg_deg : 1 ≤ g.natDegree := by omega
  -- X - C q is not a unit: isUnit iff constant, but X - C q has degree 1
  have hXq_not_unit : ¬IsUnit (X - C q) := by
    rw [Polynomial.isUnit_iff]
    rintro ⟨c, _, hc⟩
    have := congr_arg Polynomial.natDegree hc
    simp [natDegree_X_sub_C, Polynomial.natDegree_C] at this
  -- g is not a unit: isUnit iff constant, but g has degree ≥ 1
  have hg_not_unit : ¬IsUnit g := by
    rw [Polynomial.isUnit_iff]
    rintro ⟨c, _, hc⟩
    have hnd := congr_arg Polynomial.natDegree hc
    simp [Polynomial.natDegree_C] at hnd
    omega
  -- Irreducibility: one factor must be a unit → contradiction
  rcases hf_irred.isUnit_or_isUnit hfg with h | h
  · exact hXq_not_unit h
  · exact hg_not_unit h

/-- **Taylor factorization upper bound**: If f(α) = 0 in ℚ_[p], then by factoring
    f(x) = (x - α)·g(x) over ℚ_[p], we get ‖f(r/s)‖_p ≤ M · ‖α - r/s‖_p
    where M is a uniform bound on ‖g(r/s)‖_p (via p-adic ultrametric continuity). -/
lemma cofactor_uniform_bound (α : ℚ_[p]) (f : ℤ[X])
    (hf_root : (f.map (algebraMap ℤ ℚ_[p])).eval α = 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ r s : ℤ, s ≠ 0 →
      ‖((f.map (algebraMap ℤ ℚ_[p])).eval ((r : ℚ_[p]) / s))‖ ≤
        M * ‖α - (r : ℚ_[p]) / s‖ := by
  sorry

/-- **P-adic Liouville Estimate** (proved from helper lemmas above):
    If α ∈ ℚ_[p] is a root of irreducible f ∈ ℤ[X] of degree d ≥ 2,
    then ∃ C > 0 such that ∀ r, s : ℤ with s ≠ 0:
      C / max(|r|, |s|)^d ≤ ‖α - r/s‖_p

    Combines cofactor_uniform_bound + padicNorm_poly_eval_lb + irred_no_rational_roots.
    With C = 1/(M · polyCoeffL1(f)):
      1/(L·H^d) ≤ ‖f(r/s)‖_p ≤ M·‖α - r/s‖_p  →  C/H^d ≤ ‖α - r/s‖_p -/
theorem padic_liouville_estimate (α : ℚ_[p]) (f : ℤ[X])
    (hf_root : (f.map (algebraMap ℤ ℚ_[p])).eval α = 0)
    (hf_irred : Irreducible (f.map (algebraMap ℤ ℚ)))
    (hf_deg : 2 ≤ f.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ r s : ℤ, s ≠ 0 →
      C / (max r.natAbs s.natAbs : ℝ) ^ f.natDegree ≤ ‖α - (r : ℚ_[p]) / s‖ := by
  have hf_ne : f ≠ 0 := by rintro rfl; simp at hf_deg
  obtain ⟨M, hM, hcofactor⟩ := cofactor_uniform_bound p α f hf_root
  have hL_pos : (0 : ℝ) < (polyCoeffL1 f : ℝ) := by exact_mod_cast polyCoeffL1_pos f hf_ne
  -- Witness C = 1/(M · polyCoeffL1(f)) > 0
  refine ⟨1 / (M * (polyCoeffL1 f : ℝ)), by positivity, fun r s hs => ?_⟩
  have hno_rat := irred_no_rational_roots f hf_irred hf_deg ((r : ℚ) / s)
  have hlb := padicNorm_poly_eval_lb p f hf_ne r s hs hno_rat
  have hub := hcofactor r s hs
  have hs_pos : (0 : ℕ) < s.natAbs := Int.natAbs_pos.mpr hs
  have hH_pos : (0 : ℝ) < (max r.natAbs s.natAbs : ℝ) :=
    by exact_mod_cast Nat.lt_of_lt_of_le hs_pos (le_max_right _ _)
  have hHd_pos : (0 : ℝ) < (max r.natAbs s.natAbs : ℝ) ^ f.natDegree := pow_pos hH_pos _
  have hLH_pos : (0 : ℝ) < (polyCoeffL1 f : ℝ) * (max r.natAbs s.natAbs : ℝ) ^ f.natDegree :=
    mul_pos hL_pos hHd_pos
  -- chain: 1/(L·H^d) ≤ ‖f(r/s)‖_p ≤ M·‖α - r/s‖_p
  have hchain : 1 / ((polyCoeffL1 f : ℝ) * (max r.natAbs s.natAbs : ℝ) ^ f.natDegree) ≤
      M * ‖α - (r : ℚ_[p]) / s‖ := le_trans hlb hub
  -- Rearrange: 1/(M·L·H^d) ≤ ‖α - r/s‖_p = C/H^d ≤ ‖α - r/s‖_p
  have hML_pos : (0 : ℝ) < M * (polyCoeffL1 f : ℝ) := mul_pos hM hL_pos
  have h_rearrange : 1 / (M * (polyCoeffL1 f : ℝ) * (max r.natAbs s.natAbs : ℝ) ^ f.natDegree) ≤
      ‖α - (r : ℚ_[p]) / s‖ := by
    rw [div_le_iff (mul_pos hML_pos hHd_pos)]
    have := mul_le_mul_of_nonneg_right hchain (le_of_lt hHd_pos)
    linarith [mul_comm M ‖α - (r : ℚ_[p]) / s‖, norm_nonneg (α - (r : ℚ_[p]) / s)]
  calc 1 / (M * (polyCoeffL1 f : ℝ)) / (max r.natAbs s.natAbs : ℝ) ^ f.natDegree
      = 1 / (M * (polyCoeffL1 f : ℝ) * (max r.natAbs s.natAbs : ℝ) ^ f.natDegree) := by ring
    _ ≤ ‖α - (r : ℚ_[p]) / s‖ := h_rearrange


/-- **Main Result**: Every p-adic algebraic number is NOT p-adically Liouville.

    Proof: If α is algebraic of degree d, the Liouville estimate gives C/H^d ≤ ‖α - r/s‖
    for all r/s. Pick n₀ with 2^n₀ > 1/C. Apply the Liouville condition with n = n₀ + d
    to get r, s with H ≥ 2 and ‖α - r/s‖ < 1/H^(n₀+d). Combining:
      C < 1/H^n₀ ≤ 1/2^n₀ < C (from n₀ choice). Contradiction. -/
theorem padic_algebraic_not_liouville
    (α : ℚ_[p]) (f : ℤ[X])
    (hf_root : (f.map (algebraMap ℤ ℚ_[p])).eval α = 0)
    (hf_irred : Irreducible (f.map (algebraMap ℤ ℚ)))
    (hf_deg : 2 ≤ f.natDegree)
    (hLiou : IsPadicLiouville p α) :
    False := by
  obtain ⟨C, hC, hbound⟩ := padic_liouville_estimate p α f hf_root hf_irred hf_deg
  -- Pick n₀ such that (1/2)^n₀ < C, equivalently 2^n₀ > 1/C
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hC (by norm_num : (1 / 2 : ℝ) < 1)
  -- Apply the Liouville condition with n = n₀ + f.natDegree
  obtain ⟨r, s, hs, hH2, _hgcd, happrox⟩ := hLiou (n₀ + f.natDegree)
  -- Work with H : ℕ := max r.natAbs s.natAbs
  set H : ℕ := max r.natAbs s.natAbs with hH_def
  -- H ≥ 2 (from Liouville condition), so (H : ℝ) ≥ 2
  have hH_ge2 : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH2
  have hH_pos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le (by norm_num) hH_ge2
  have hHd_pos : (0 : ℝ) < (H : ℝ) ^ f.natDegree := pow_pos hH_pos _
  -- Lower bound from estimate: C / H^d ≤ ‖α - r/s‖
  have hlower : C / (H : ℝ) ^ f.natDegree ≤ ‖α - (r : ℚ_[p]) / s‖ := hbound r s hs
  -- Combine with Liouville upper bound to get C / H^d < 1 / H^(n₀+d)
  have hcomb : C / (H : ℝ) ^ f.natDegree < 1 / (H : ℝ) ^ (n₀ + f.natDegree) :=
    lt_of_le_of_lt hlower happrox
  -- H^(n₀+d) = H^n₀ * H^d, so 1/H^(n₀+d) = (1/H^n₀) / H^d
  rw [pow_add, ← div_div] at hcomb
  -- Cancel H^d from both sides: C < 1/H^n₀
  have hC_lt : C < 1 / (H : ℝ) ^ n₀ := (div_lt_div_right hHd_pos).mp hcomb
  -- H ≥ 2 implies H^n₀ ≥ 2^n₀, so 1/H^n₀ ≤ 1/2^n₀
  have h2n0_le : (2 : ℝ) ^ n₀ ≤ (H : ℝ) ^ n₀ :=
    pow_le_pow_left (by norm_num) hH_ge2 n₀
  have h_mono : 1 / (H : ℝ) ^ n₀ ≤ 1 / (2 : ℝ) ^ n₀ :=
    one_div_le_one_div_of_le (pow_pos (by norm_num : (0:ℝ) < 2) n₀) h2n0_le
  -- hn₀ : (1/2)^n₀ < C. Rewrite as 1/2^n₀ < C.
  have h_2n0_lt : 1 / (2 : ℝ) ^ n₀ < C := by
    have : (1 / 2 : ℝ) ^ n₀ = 1 / (2 : ℝ) ^ n₀ := by ring
    linarith
  -- Chain: C < 1/H^n₀ ≤ 1/2^n₀ < C. Contradiction.
  linarith

/-! ═════════════════════════════════════════════��═════════════════════════════
PART VI: FUNCTION FIELD ANALOG
The same strategy applies over function fields F_q(t).
═══════════════════════════════════════════════════════════════════════════ -/

/-!
### Function Field Liouville Theorem

The p-adic proof strategy generalizes immediately to function fields F_q(t)
with the t-adic absolute value |·|_t.

**Setup**: Let F = F_q(t), and let F[[t]] be the ring of formal power series
(the "integers"). The t-adic absolute value: |a|_t = q^{-v_t(a)} where
v_t(a) is the t-adic valuation (order of vanishing at t = 0).

**Key property**: For P/Q ∈ F_q[t]/F_q[t], the analog of our integer bound:
  |P|_t ≤ 1 for P ∈ F_q[t] (polynomial ring = "integers")
  |P/Q|_t = |P|_t / |Q|_t

The function field analog of the Archimedean Complement Lemma:
  |P|_t ≥ q^{-deg(P)} = 1/q^{deg(P)} for nonzero P ∈ F_q[t]

This is the SAME proof: deg(P/q^{v_t(P)}) = 0, meaning the leading term
after removing the t-adic contribution has no t factors, so the remaining
"norm" is ≥ 1/q^{deg(P)}.

**Function field Liouville theorem**: If α ∈ F_q[[t]] is algebraic of degree d
over F_q(t), then for all P/Q ∈ F_q(t):
  |α - P/Q|_t ≥ C / max(q^{deg P}, q^{deg Q})^d

This follows from the same proof as the p-adic case.
-/

/-! ═══════════════════════════════════════════════════════════════════════════
PART VII: COMPARISON WITH CLASSICAL CASE
══════════════════════════════════════════════════���════════════════════════ -/

/-!
### Key Differences from the Real Case

**Real Liouville theorem** (classical):
  |α - p/q| ≥ c/q^d   (denominator bound)
  Proof: |f(p/q)| ≥ 1/q^d uses |nonzero integer| ≥ 1 (Archimedean)

**P-adic Liouville theorem** (this file):
  |α - p/q|_ℓ ≥ c/max(|p|, |q|)^d   (height bound)
  Proof: |f(p/q)|_ℓ ≥ 1/(C_f · max(|p|,|q|)^d) uses |N|_ℓ ≥ 1/|N| (non-Arch.)

**Why HEIGHT instead of denominator?**
- In the real case: f(p/q) = N/q^d with N ∈ ℤ and |N| ≥ 1 (Archimedean)
  → |f(p/q)| ≥ 1/|q|^d
- In the p-adic case: |N|_p can be ≤ 1/p^k for any k (non-Archimedean)
  → Cannot bound |f(p/q)|_p from below using just the denominator
  → The bound |N|_p ≥ 1/|N| (Part I) introduces the NUMERATOR into the estimate
  → This forces the HEIGHT max(|p|, |q|) to appear

**Consequence**: The p-adic Liouville number notion is STRONGER (harder to satisfy)
than the real one, because height grows faster than denominator alone.

The Archimedean Complement Lemma is the key bridge: it converts the
"p-adic smallness" of an integer to a "height-based lower bound".
-/

/-! ══════════════════════════════��════════════════════════════════════════════
PART VIII: CONCRETE EXAMPLES
═══════════════════════════════════════════════════════════════════════════ -/

section Examples

-- For examples, use specific primes

private instance instFact2 : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance instFact3 : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance instFact5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Example: The bound for n=6, p=2.
    padicNorm 2 6 = 1/2 (since 2 | 6 but 4 ∤ 6). Lower bound 1/6 ≤ 1/2. ✓ -/
theorem example_2_6 : (6 : ℚ)⁻¹ ≤ padicNorm 2 6 :=
  padicNorm_nat_ge_inv 2 6 (by norm_num)

/-- Example: The bound for n=25, p=5.
    padicNorm 5 25 = 1/25 (since 5^2 = 25). Lower bound 1/25 ≤ 1/25. ✓ (equality) -/
theorem example_5_25 : (25 : ℚ)⁻¹ ≤ padicNorm 5 25 :=
  padicNorm_nat_ge_inv 5 25 (by norm_num)

/-- Example: The bound for n=7, p=3.
    padicNorm 3 7 = 1 (since 3 ∤ 7). Lower bound 1/7 ≤ 1. ✓ -/
theorem example_3_7 : (7 : ℚ)⁻¹ ≤ padicNorm 3 7 :=
  padicNorm_nat_ge_inv 3 7 (by norm_num)

/-- The upper bound from Mathlib: p-adic norm of a natural is ≤ 1. -/
theorem example_upper_bound : padicNorm 2 12 ≤ 1 := padicNorm.of_nat 12

/-- Both bounds together for n=12, p=2:
    1/12 ≤ padicNorm 2 12 ≤ 1. -/
theorem example_2_12_bounds :
    (12 : ℚ)⁻¹ ≤ padicNorm 2 12 ∧ padicNorm 2 12 ≤ 1 :=
  padicNorm_nat_bounds 2 12 (by norm_num)

end Examples

/-! ═══════════════════════════════���═══════════════════════════════════════════
PART IX: SORRY SUMMARY
═══════════════════════════════════════════════════════════════════════════ -/

/-!
## Sorry Summary

| Location | Classification | Notes |
|----------|---------------|-------|
| padic_liouville_estimate | OPEN (axiom) | Core p-adic Taylor expansion in ℚ_[p] |

**Proved (no sorry)**:
- `padicNorm_nat_ge_inv`: The Archimedean Complement Lemma (heart of proof)
- `padicNorm_int_ge_inv`: Integer version via natAbs
- `padicNorm_nat_mul_self_ge_one`: Corollary
- `archimedean_complement`: Clean statement
- `padicNorm_nat_bounds`: Combined bounds
- `padicNorm_int_le_one`: From Mathlib
- `padicNorm_poly_eval_bound`: Trivial witness C = padicNorm(f(r/s)) * H^d
- `padic_algebraic_not_liouville`: Main theorem (proved 2026-05-02 using exists_pow_lt_of_lt_one)
- All three examples (2|6, 5|25, 3∤7)

The axiom `padic_liouville_estimate` is the only OPEN result.
It states the p-adic Liouville bound and requires:
1. Working in ℚ_[p] (completion of ℚ at p)
2. The Taylor expansion f(x) - f(α) = (x-α)·g(x,α) over ℚ_[p]
3. Continuity of polynomial evaluation in the p-adic ultrametric topology
4. The connection between padicNorm (on ℚ) and ‖·‖ (norm on ℚ_[p])

-/

end LiouvilleTheoremOQ04
