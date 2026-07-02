/-
Maclaurin's Inequality for Log-Concave Sequences

OQ-02 follow-up to newton-inductive-step-oq-02.  The parent development studies
Newton's inequality for the elementary symmetric means

    ē_k = e_k(x) / C(n,k),

whose defining property is *log-concavity*:  ē_k² ≥ ē_{k-1} · ē_{k+1}.  The open
question OQ1 of that entry asks for the full **Maclaurin inequality**

    ē_1 ≥ ē_2^{1/2} ≥ ē_3^{1/3} ≥ ⋯ ≥ ē_n^{1/n}.

This file proves the abstract engine that turns log-concavity into Maclaurin's
chain, for an *arbitrary* positive, normalized, log-concave sequence — the exact
mechanism by which Newton's inequality implies Maclaurin's.  It depends only on
Mathlib and is fully machine-checked (0 axioms, 0 sorries).

The mathematics is elementary and denominator-free at its core.  Write
r_j = a_{j+1}/a_j for the consecutive ratios.  Log-concavity says r is
non-increasing, so with a_0 = 1,

    a_k = ∏_{j<k} r_j ≥ r_k^k,

and multiplying by a_k^k > 0 gives the **cleared-denominator Maclaurin
inequality**

    a_k^{k+1} ≥ a_{k+1}^k.

A single `rpow` monotonicity step upgrades it to the classical radical form
a_k^{1/k} ≥ a_{k+1}^{1/(k+1)}.

To recover Maclaurin's inequality for the symmetric means, instantiate
`a := ē` and `N := n`: the hypothesis `a 0 = 1` is `e_0 / C(n,0) = 1`, positivity
holds for `x_i > 0`, and log-concavity is Newton's inequality
(`newton_inequality_means` of the parent chain).

Main results (0 axioms, 0 sorries):
1. `maclaurin_of_logConcave`      — a_k^{k+1} ≥ a_{k+1}^k   (cleared-denominator form)
2. `maclaurin_of_logConcave_rpow` — a_{k+1}^{1/(k+1)} ≤ a_k^{1/k}  (radical form)

References:
  - Maclaurin (1729), "A Second Letter ... concerning the Roots of Equations"
  - Hardy–Littlewood–Pólya (1952), Inequalities, Theorem 52
  - Newton (1707), Arithmetica Universalis
  - Parent proof: NewtonInductiveStepOQ02.lean (log-concavity of the means)
-/

import Mathlib

open Finset

namespace NewtonInductiveStepOQ02OQ02

variable (a : ℕ → ℝ)

/-- The consecutive ratio `r_j = a_{j+1} / a_j` of a real sequence. -/
noncomputable def ratio (j : ℕ) : ℝ := a (j + 1) / a j

/-- **Maclaurin's inequality, cleared-denominator (integer-power) form.**

    For any real sequence `a` that is strictly positive and log-concave on
    `{0, …, N}` with `a 0 = 1`, one has `a k ^ (k+1) ≥ a (k+1) ^ k` for every
    `k` with `k + 1 ≤ N`.

    Proof: the consecutive ratios `r_j = a_{j+1}/a_j` are non-increasing
    (log-concavity), so `a k = ∏_{j<k} r_j ≥ r_k^k`; multiplying by `a k^k`
    gives the claim. -/
theorem maclaurin_of_logConcave (N : ℕ)
    (hpos : ∀ i, i ≤ N → 0 < a i) (h0 : a 0 = 1)
    (hlc : ∀ i, 1 ≤ i → i + 1 ≤ N → a i ^ 2 ≥ a (i - 1) * a (i + 1)) :
    ∀ k, k + 1 ≤ N → a k ^ (k + 1) ≥ a (k + 1) ^ k := by
  -- Positivity of the ratios within range.
  have hr_pos : ∀ j, j + 1 ≤ N → 0 < ratio a j := by
    intro j hj
    unfold ratio
    exact div_pos (hpos (j + 1) hj) (hpos j (by omega))
  -- Recover the sequence as a running product of ratios.
  have prod_eq : ∀ m, m ≤ N → a m = ∏ j ∈ Finset.range m, ratio a j := by
    intro m
    induction m with
    | zero => intro _; simpa using h0
    | succ p ih =>
      intro hm
      rw [Finset.prod_range_succ, ← ih (by omega)]
      have hap : a p ≠ 0 := ne_of_gt (hpos p (by omega))
      unfold ratio
      rw [mul_div_cancel₀ (a (p + 1)) hap]
  -- Single-step monotonicity of the ratios (from log-concavity).
  have hstep : ∀ j, j + 2 ≤ N → ratio a (j + 1) ≤ ratio a j := by
    intro j hj
    have haj : 0 < a j := hpos j (by omega)
    have haj1 : 0 < a (j + 1) := hpos (j + 1) (by omega)
    have hc := hlc (j + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hc
    unfold ratio
    rw [div_le_div_iff₀ haj1 haj]
    nlinarith [hc]
  -- General monotonicity of the ratios over the range.
  have hmono : ∀ d j, j + d + 1 ≤ N → ratio a (j + d) ≤ ratio a j := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ e ih =>
      intro j hj
      have h1 : ratio a (j + (e + 1)) ≤ ratio a (j + e) := hstep (j + e) (by omega)
      exact le_trans h1 (ih j (by omega))
  -- Main inequality.
  intro k hk
  have hak_pos : 0 < a k := hpos k (by omega)
  have hrk_pos : 0 < ratio a k := hr_pos k hk
  -- Key step:  (ratio a k)^k ≤ a k.
  have key : ratio a k ^ k ≤ a k := by
    rw [prod_eq k (by omega)]
    calc ratio a k ^ k
        = ∏ _j ∈ Finset.range k, ratio a k := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ j ∈ Finset.range k, ratio a j := by
          apply Finset.prod_le_prod
          · intro i _; exact le_of_lt hrk_pos
          · intro j hj
            have hjk : j ≤ k := le_of_lt (Finset.mem_range.mp hj)
            have hmj := hmono (k - j) j (by omega)
            rwa [Nat.add_sub_cancel' hjk] at hmj
  -- a (k+1) = a k * ratio a k.
  have hak1 : a k * ratio a k = a (k + 1) := by
    have hak_ne : a k ≠ 0 := ne_of_gt hak_pos
    unfold ratio
    exact mul_div_cancel₀ (a (k + 1)) hak_ne
  rw [ge_iff_le, ← hak1, mul_pow]
  calc a k ^ k * ratio a k ^ k
      ≤ a k ^ k * a k := mul_le_mul_of_nonneg_left key (le_of_lt (pow_pos hak_pos k))
    _ = a k ^ (k + 1) := by rw [← pow_succ]

/-- **Maclaurin's inequality, classical radical form.**

    For a strictly positive, normalized, log-concave sequence on `{0, …, N}`,
    and `1 ≤ k` with `k + 1 ≤ N`,

        a_{k+1}^{1/(k+1)} ≤ a_k^{1/k}.

    Chaining over `k = 1, …, N-1` yields a_1 ≥ a_2^{1/2} ≥ ⋯ ≥ a_N^{1/N};
    with `a := ē` the symmetric means this is Maclaurin's inequality. -/
theorem maclaurin_of_logConcave_rpow (N : ℕ)
    (hpos : ∀ i, i ≤ N → 0 < a i) (h0 : a 0 = 1)
    (hlc : ∀ i, 1 ≤ i → i + 1 ≤ N → a i ^ 2 ≥ a (i - 1) * a (i + 1))
    (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ N) :
    a (k + 1) ^ ((1 : ℝ) / (k + 1)) ≤ a k ^ ((1 : ℝ) / k) := by
  have hLpos : 0 < a k := hpos k (by omega)
  have hRpos : 0 < a (k + 1) := hpos (k + 1) hkn
  have hcore : a (k + 1) ^ k ≤ a k ^ (k + 1) :=
    maclaurin_of_logConcave a N hpos h0 hlc k hkn
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  set z : ℝ := 1 / ((k : ℝ) * ((k : ℝ) + 1)) with hz
  have hz_nonneg : 0 ≤ z := by positivity
  -- Raise the cleared inequality to the power z.
  have hmono : (a (k + 1) ^ k) ^ z ≤ (a k ^ (k + 1)) ^ z :=
    Real.rpow_le_rpow (pow_nonneg hRpos.le k) hcore hz_nonneg
  -- Rewrite each side using rpow arithmetic.
  have hLrw : (a k ^ (k + 1)) ^ z = a k ^ ((1 : ℝ) / k) := by
    rw [← Real.rpow_natCast (a k) (k + 1), ← Real.rpow_mul hLpos.le]
    rw [show ((k + 1 : ℕ) : ℝ) * z = (1 : ℝ) / k from by
      rw [hz]; push_cast; field_simp]
  have hRrw : (a (k + 1) ^ k) ^ z = a (k + 1) ^ ((1 : ℝ) / (k + 1)) := by
    rw [← Real.rpow_natCast (a (k + 1)) k, ← Real.rpow_mul hRpos.le]
    rw [show (k : ℝ) * z = (1 : ℝ) / (k + 1) from by
      rw [hz]; field_simp]
  rw [hLrw, hRrw] at hmono
  exact hmono

end NewtonInductiveStepOQ02OQ02
