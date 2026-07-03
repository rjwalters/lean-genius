import Mathlib
import Proofs.ChevalleyWarningTheoremOQ01

/-
# Erdős–Ginzburg–Ziv from Chevalley–Warning (chevalley-warning-theorem-oq-01-oq-02)

## What This Proves

The **Erdős–Ginzburg–Ziv theorem** (EGZ, 1961) in its prime case: among any
`2p - 1` elements of `ZMod p` (`p` prime) there is a sub-collection of **exactly
`p`** of them whose sum is `0`. Equivalently, among any `2p - 1` integers, some
`p` of them sum to a multiple of `p`.

The point of this entry is *how* it is proved: entirely through the gallery's own
**Chevalley–Warning nontrivial-solution corollary**
(`ChevalleyWarningTheoremOQ01.chevalley_warning_nontrivial`), exhibiting
Chevalley–Warning as the engine of EGZ — exactly the classical route the parent
entry advertises but does not carry out.

## The argument

Given `a : Fin (2p-1) → ZMod p`, consider the two degree-`(p−1)` power-sum forms
in the `2p−1` variables `X i`:

* `f₁ = ∑ i, (X i)^(p−1)`
* `f₂ = ∑ i, C (a i) · (X i)^(p−1)`

Their total degrees sum to `2(p−1) = 2p−2 < 2p−1`, the number of variables, and
both vanish at the origin. Chevalley's corollary therefore produces a **nonzero**
common zero `x`. By Fermat's little theorem each coordinate satisfies
`(x i)^(p−1) = 1` if `x i ≠ 0` and `= 0` otherwise, so:

* `f₁(x) = 0` says the support `I = {i : x i ≠ 0}` has `|I| ≡ 0 (mod p)`; since
  `x ≠ 0` forces `1 ≤ |I| ≤ 2p−1`, the only possibility is `|I| = p`;
* `f₂(x) = 0` says `∑_{i ∈ I} a i = 0`.

That is EGZ. The integer statement follows by reduction mod `p`.

## Context

This is the standard proof of EGZ and the sole downstream consumer of
Chevalley–Warning inside Mathlib (`ZMod.erdos_ginzburg_ziv`). Here it is rebuilt
on top of the gallery's own existence corollary rather than re-imported, closing
the loop opened by `chevalley-warning-theorem-oq-01`.
-/

namespace ChevalleyWarningTheoremOQ01OQ02

open MvPolynomial Finset

/-! ## Fermat's little theorem as an indicator -/

/-- Over `ZMod p` the `(p−1)`-power is the indicator of "nonzero": it is `1` on
nonzero elements (Fermat's little theorem) and `0` at `0` (as `p − 1 ≥ 1`). -/
theorem pow_sub_one {p : ℕ} [Fact p.Prime] (b : ZMod p) :
    b ^ (p - 1) = if b ≠ 0 then (1 : ZMod p) else 0 := by
  by_cases h : b = 0
  · subst h
    have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    rw [zero_pow hp1, if_neg (by simp)]
  · rw [if_pos h]
    exact ZMod.pow_card_sub_one_eq_one h

/-! ## Total-degree bounds for the two power-sum forms -/

/-- The unweighted power-sum form `∑ (X i)^(p−1)` has total degree at most `p − 1`. -/
theorem totalDegree_powerSum_le {p : ℕ} [Fact p.Prime] {σ : Type*} [Fintype σ] :
    (∑ i : σ, (X i) ^ (p - 1) : MvPolynomial σ (ZMod p)).totalDegree ≤ p - 1 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (totalDegree_X_pow i (p - 1)).le

/-- The weighted power-sum form `∑ C (a i) · (X i)^(p−1)` has total degree at most
`p − 1` (each scalar `C (a i)` contributes degree `0`). -/
theorem totalDegree_weightedPowerSum_le {p : ℕ} [Fact p.Prime] {σ : Type*} [Fintype σ]
    (a : σ → ZMod p) :
    (∑ i : σ, C (a i) * (X i) ^ (p - 1) : MvPolynomial σ (ZMod p)).totalDegree ≤ p - 1 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  calc (C (a i) * (X i) ^ (p - 1) : MvPolynomial σ (ZMod p)).totalDegree
      ≤ (C (a i) : MvPolynomial σ (ZMod p)).totalDegree + ((X i) ^ (p - 1)).totalDegree :=
        totalDegree_mul _ _
    _ = 0 + (p - 1) := by rw [totalDegree_C, totalDegree_X_pow]
    _ = p - 1 := by rw [zero_add]

/-! ## Erdős–Ginzburg–Ziv, prime case -/

/-- **Erdős–Ginzburg–Ziv over `ZMod p`.** Among any `2p − 1` elements of `ZMod p`
there is a subset of exactly `p` of them summing to `0`. Proved by applying the
Chevalley–Warning nontrivial-solution corollary to the two degree-`(p−1)`
power-sum forms `∑ (X i)^(p−1)` and `∑ (a i)(X i)^(p−1)`. -/
theorem egz_zmod (p : ℕ) [Fact p.Prime] (a : Fin (2 * p - 1) → ZMod p) :
    ∃ I : Finset (Fin (2 * p - 1)), I.card = p ∧ ∑ i ∈ I, a i = 0 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- The two forms, packaged as a family indexed by `Fin 2`.
  set f : Fin 2 → MvPolynomial (Fin (2 * p - 1)) (ZMod p) :=
    ![∑ i, (X i) ^ (p - 1), ∑ i, C (a i) * (X i) ^ (p - 1)] with hf
  -- Degree hypothesis: `deg f₀ + deg f₁ ≤ 2(p−1) < 2p − 1`.
  have hdeg : (∑ i ∈ Finset.univ, (f i).totalDegree) < Fintype.card (Fin (2 * p - 1)) := by
    rw [Fin.sum_univ_two, Fintype.card_fin]
    have h0 : (f 0).totalDegree ≤ p - 1 := by
      rw [hf]; simp only [Matrix.cons_val_zero]
      exact totalDegree_powerSum_le (p := p) (σ := Fin (2 * p - 1))
    have h1 : (f 1).totalDegree ≤ p - 1 := by
      rw [hf]; simp only [Matrix.cons_val_one, Matrix.head_cons]
      exact totalDegree_weightedPowerSum_le (p := p) a
    omega
  -- The origin is a common zero of both forms.
  have h0eval : ∀ i ∈ (Finset.univ : Finset (Fin 2)), eval (0 : Fin (2 * p - 1) → ZMod p) (f i) = 0 := by
    intro i _
    fin_cases i <;>
      simp [hf, eval_sum, eval_mul, eval_pow, eval_X, eval_C,
        zero_pow (show p - 1 ≠ 0 by omega)]
  -- Chevalley's nontrivial-solution corollary: a NONZERO common zero exists.
  obtain ⟨x, hxne, hxzero⟩ :=
    ChevalleyWarningTheoremOQ01.chevalley_warning_nontrivial p hdeg h0eval
  have hx0 : eval x (f 0) = 0 := hxzero 0 (Finset.mem_univ 0)
  have hx1 : eval x (f 1) = 0 := hxzero 1 (Finset.mem_univ 1)
  -- Evaluate `f₀` at `x`: it is the cardinality of the support, cast to `ZMod p`.
  have hev0 : eval x (f 0) = ∑ i, (x i) ^ (p - 1) := by
    rw [hf]; simp only [Matrix.cons_val_zero, eval_sum, eval_pow, eval_X]
  have hcastcard :
      ((Finset.univ.filter (fun i => x i ≠ 0)).card : ZMod p) = 0 := by
    have hcalc : ∑ i, (x i) ^ (p - 1)
        = ((Finset.univ.filter (fun i => x i ≠ 0)).card : ZMod p) := by
      calc ∑ i, (x i) ^ (p - 1)
          = ∑ i, (if x i ≠ 0 then (1 : ZMod p) else 0) :=
            Finset.sum_congr rfl (fun i _ => pow_sub_one (x i))
        _ = ((Finset.univ.filter (fun i => x i ≠ 0)).card : ZMod p) := by
            rw [Finset.sum_boole]
    rw [← hcalc, ← hev0]; exact hx0
  have hdvd_card : p ∣ (Finset.univ.filter (fun i => x i ≠ 0)).card :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcastcard
  -- Evaluate `f₁` at `x`: it is the sum of the `a i` over the support.
  have hev1 : eval x (f 1) = ∑ i, a i * (x i) ^ (p - 1) := by
    rw [hf]; simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      eval_sum, eval_mul, eval_pow, eval_X, eval_C]
  have hsum0 : ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), a i = 0 := by
    have hcalc : ∑ i, a i * (x i) ^ (p - 1)
        = ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), a i := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_sub_one (x i)]
      by_cases h : x i = 0 <;> simp [h]
    rw [← hcalc, ← hev1]; exact hx1
  -- The support has size exactly `p`: it is a nonzero multiple of `p` at most `2p − 1`.
  have hpos : 1 ≤ (Finset.univ.filter (fun i => x i ≠ 0)).card := by
    rw [Finset.one_le_card, Finset.filter_nonempty_iff]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxne
    exact ⟨j, Finset.mem_univ j, by simpa using hj⟩
  have hle : (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ 2 * p - 1 := by
    have hc := Finset.card_filter_le (Finset.univ : Finset (Fin (2 * p - 1))) (fun i => x i ≠ 0)
    simpa using hc
  have hcardp : (Finset.univ.filter (fun i => x i ≠ 0)).card = p := by
    obtain ⟨k, hk⟩ := hdvd_card
    have hkpos : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp [hk] at hpos
      · exact h
    have hklt : k < 2 := by
      by_contra hc
      push_neg at hc
      have hge : 2 * p ≤ p * k := by
        calc 2 * p = p * 2 := by ring
          _ ≤ p * k := by gcongr
      omega
    have hk1 : k = 1 := by omega
    rw [hk, hk1, mul_one]
  exact ⟨Finset.univ.filter (fun i => x i ≠ 0), hcardp, hsum0⟩

/-- **Erdős–Ginzburg–Ziv over `ℤ`.** Among any `2p − 1` integers, some `p` of them
sum to a multiple of `p`. Immediate corollary of `egz_zmod` by reduction mod `p`. -/
theorem egz_int (p : ℕ) [Fact p.Prime] (a : Fin (2 * p - 1) → ℤ) :
    ∃ I : Finset (Fin (2 * p - 1)), I.card = p ∧ (p : ℤ) ∣ ∑ i ∈ I, a i := by
  obtain ⟨I, hcard, hsum⟩ := egz_zmod p (fun i => (a i : ZMod p))
  refine ⟨I, hcard, ?_⟩
  have hz : ((∑ i ∈ I, a i : ℤ) : ZMod p) = 0 := by push_cast; exact hsum
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz

end ChevalleyWarningTheoremOQ01OQ02
