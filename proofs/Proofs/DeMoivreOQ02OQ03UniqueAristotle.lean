import Mathlib
import Proofs.DeMoivreOQ02OQ03

/-
# De Moivre OQ-02-03 — uniqueness of the Chebyshev minimizer (Aristotle companion)

The minimax *value* `2^(1-n)` is already fully verified in `Proofs.DeMoivreOQ02OQ03`
(`chebyshev_minimax`: achievability + optimality, 0 sorry / 0 axiom). The remaining
open frontier is **uniqueness**: the monic Chebyshev polynomial `Mₙ` is the *only*
monic degree-`n` polynomial whose sup-norm on `[-1,1]` equals `2^(1-n)`.

## Decomposition (this file)

The existing optimality proof (`monicChebyshev_minimax`) handles the *strict* case
`|p| < M`: strict sign alternation of `q := Mₙ - p` at the `n+1` extreme nodes yields
`n` strictly-separated *simple* interior roots, contradicting `deg q < n`. Uniqueness
is the *weak*-inequality case `|p| ≤ M`: the alternation is only weak (`≥ 0`), so a node
may itself be a root and the simple-root count no longer reaches `n`. The crux is a
single self-contained real-polynomial fact, isolated here as `weak_alternation_eq_zero`
(Mathlib-only — a good Aristotle / future-session target). Given the crux, uniqueness
follows mechanically from the already-verified node infrastructure, discharged in
`monicChebyshev_unique` below (no remaining sorry once the crux lands).

## Status (researcher-10, 2026-06-19)

The mechanical reduction `monicChebyshev_unique` was audited build-free against the
merged base file `Proofs.DeMoivreOQ02OQ03`: every referenced lemma exists with the
exact signature used here —
  * `monicChebyshev` (def, L178), `monicChebyshev_monic n hn` (L182),
  * `monicChebyshev_natDegree n` (L187), `monicChebyshev_eval_node n k hn` (L202).
`node_strict_anti` is `private` in the base file, hence the self-contained
re-derivation `node_strict_anti'` below. The reduction is therefore API-consistent and
purely mechanical (algebra over already-verified node equioscillation); the SOLE
remaining mathematical obligation is the crux `weak_alternation_eq_zero`.

Backends were both unavailable this session (Aristotle returned 404 / "Resource not
found"; the build host was saturated at load ~16 with ~100 MB free, so a Docker kernel
build was OOM-unsafe). This file is therefore **[build-pending]** and shipped as a
DRAFT so the deployer will not auto-merge it. The crux should be routed to Aristotle
(self-contained, `import Mathlib` only) the moment the backend recovers.

## Crux proof strategy — divided-difference (Lagrange) route

`weak_alternation_eq_zero`: `natDegree q < n`, nodes `x 0 > x 1 > … > x n` strictly
decreasing, weak alternation `0 ≤ (-1)^k · q(x k)` for `k ≤ n`. Show `q = 0`.

The earlier draft proposed the Rolle / root-multiplicity argument. A *cleaner* route,
fully realised below, avoids multiplicity entirely via Lagrange interpolation:

1. **`q` is its own interpolant.** With node set `s = range (n+1)` (injective via strict
   monotonicity) and `deg q < n + 1 = #s`, `Lagrange.interpolate_poly_eq_self` gives
   `q = interpolate s x (fun i ↦ q.eval (x i))`.
2. **The `n`-th coefficient is the `n`-th divided difference.** Expanding the interpolant
   `∑ i, C (q.eval (x i)) · Lagrange.basis s x i` and reading off `coeff n` (each basis
   polynomial has `natDegree = #s - 1 = n`, so its `coeff n` is its `leadingCoeff`,
   computed by `Lagrange.leadingCoeff_basis`) yields
   `q.coeff n = ∑ i ∈ range (n+1), q.eval (x i) / ∏ j ∈ (range (n+1)).erase i, (x i - x j)`.
   Since `natDegree q < n`, the left side is `0` (`coeff_eq_zero_of_natDegree_lt`).
3. **Every summand is `≥ 0`.** The weight `(∏ j ≠ i, (x i - x j))⁻¹` has sign `(-1)^i`
   (the sole self-contained obligation `node_divdiff_sign`: `i` negative factors `j < i`,
   the rest positive). Multiplying by `q.eval (x i)`, whose weak alternation gives
   `0 ≤ (-1)^i · q.eval (x i)`, the `(-1)^i` factors cancel and each term is `≥ 0`.
4. **Therefore every term is `0`** (`Finset.sum_eq_zero_iff_of_nonneg`), and as the weight
   is nonzero, `q.eval (x i) = 0` for all `i ≤ n`: `q` has `n + 1` distinct roots.
5. **Contradiction.** A nonzero `q` has at most `natDegree q < n` roots
   (`card_roots'`), but we exhibited `n + 1 > n` distinct roots, so `q = 0`.

The only remaining mathematical content is the elementary sign lemma `node_divdiff_sign`;
the entire reduction (steps 1–5) is the complete `weak_alternation_eq_zero` body below.

## Status (researcher-10, 2026-06-19, cont.)

The full divided-difference reduction is written out below (API-audited against
`Mathlib/LinearAlgebra/Lagrange.lean`: `interpolate_poly_eq_self`, `interpolate_apply`,
`natDegree_basis`, `leadingCoeff_basis`). The complete file (wrapper + `node_divdiff_sign`)
was submitted to Aristotle as project **52afa73c** for off-host compile-verification and
to discharge `node_divdiff_sign` (the local Docker build gate was closed at load ~10 / 4
containers). This remains a **[build-pending]** DRAFT; `node_divdiff_sign` is the sole
remaining `sorry`. (r7's job `3b070308` targets the same sign lemma independently.)
-/

open Polynomial Polynomial.Chebyshev Real

namespace DeMoivreOQ0203

/-- Strict monotonicity of the Chebyshev extreme nodes `cos(kπ/n)` over `0 ≤ k ≤ n`
(self-contained re-derivation; the base-file copy is `private`). -/
private theorem node_strict_anti' (n : ℕ) (hn : 0 < n) {i j : ℕ} (hj : j ≤ n)
    (hij : i < j) : Real.cos (j * π / n) < Real.cos (i * π / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hi_le : (i : ℝ) ≤ n := by exact_mod_cast (le_of_lt (lt_of_lt_of_le hij hj))
  have hj_le : (j : ℝ) ≤ n := by exact_mod_cast hj
  apply Real.strictAntiOn_cos
  · refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg i) hpi.le) hn'.le, ?_⟩
    rw [div_le_iff₀ hn']; nlinarith [hpi, hi_le]
  · refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg j) hpi.le) hn'.le, ?_⟩
    rw [div_le_iff₀ hn']; nlinarith [hpi, hj_le]
  · rw [div_lt_div_iff_of_pos_right hn']
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    nlinarith [hpi]

/-- **Sign of the `n`-th divided-difference weight.** For strictly-decreasing nodes
`x 0 > x 1 > … > x n` and `i ≤ n`, the weight `(∏_{j ≠ i} (x i - x j))⁻¹` has sign
`(-1)^i`: among the `n` factors `x i - x j` with `j ∈ {0,…,n}\{i}`, exactly the `i`
factors with `j < i` are negative (since `x j > x i`) and the rest positive, so the
product has sign `(-1)^i` and so does its inverse.

This elementary combinatorial sign fact is the **sole remaining obligation** behind
Chebyshev-minimax uniqueness; everything else (`weak_alternation_eq_zero` below) is the
mechanical Lagrange-interpolation reduction. Self-contained (Mathlib-only) — submitted to
Aristotle as project `52afa73c` (and independently `3b070308`). -/
theorem node_divdiff_sign (n : ℕ) (x : ℕ → ℝ)
    (hmono : ∀ k, k < n → x (k + 1) < x k) (i : ℕ) (hi : i ≤ n) :
    0 < (-1 : ℝ) ^ i * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹ := by
  sorry

/-- **Crux lemma.** Weak sign-alternation forces a low-degree polynomial to vanish: if a
real polynomial `q` of degree `< n` alternates weakly in sign at `n+1` strictly-decreasing
reals `x 0 > x 1 > … > x n`, i.e. `0 ≤ (-1)^k · q(x k)` for every `0 ≤ k ≤ n`, then `q = 0`.

Proved here in full via the divided-difference (Lagrange) route — see the file header for
the step-by-step strategy. Reduces to the single sign lemma `node_divdiff_sign`. -/
theorem weak_alternation_eq_zero (n : ℕ) (q : ℝ[X])
    (hdeg : q.natDegree < n) (x : ℕ → ℝ)
    (hmono : ∀ k, k < n → x (k + 1) < x k)
    (halt : ∀ k, k ≤ n → 0 ≤ (-1 : ℝ) ^ k * q.eval (x k)) :
    q = 0 := by
  classical
  by_contra hq
  -- Strict antitonicity of the nodes on `{0,…,n}`, from consecutive `hmono`.
  have hxanti : ∀ i j, i < j → j ≤ n → x j < x i := by
    intro i j
    induction j with
    | zero => intro h; exact absurd h (Nat.not_lt_zero i)
    | succ m ih =>
      intro hij hjn
      have hmn : m < n := by omega
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with h | h
      · rw [h]; exact hmono m hmn
      · exact lt_trans (hmono m hmn) (ih h (le_of_lt hmn))
  have hinj : Set.InjOn x (Finset.range (n + 1)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab.symm (ne_of_lt (hxanti a b h (by omega)))
    · exact h
    · exact absurd hab (ne_of_lt (hxanti b a h (by omega)))
  -- `q` equals its own Lagrange interpolant on the `n+1` nodes (deg `q < n+1 = #s`).
  have hself : Lagrange.interpolate (Finset.range (n + 1)) x (fun i => q.eval (x i)) = q := by
    apply Lagrange.interpolate_poly_eq_self hinj
    rw [Finset.card_range, Polynomial.degree_eq_natDegree hq]
    exact_mod_cast Nat.lt_succ_of_lt hdeg
  -- `coeff n` of the interpolant is the `n`-th divided difference of `q`.
  have hcoeff : q.coeff n = ∑ i ∈ Finset.range (n + 1),
      q.eval (x i) * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹ := by
    conv_lhs => rw [← hself]
    rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hdb : (Lagrange.basis (Finset.range (n + 1)) x i).natDegree = n := by
      rw [Lagrange.natDegree_basis hinj hi, Finset.card_range]
    have hbc : (Lagrange.basis (Finset.range (n + 1)) x i).coeff n
        = (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹ := by
      rw [← Lagrange.leadingCoeff_basis hinj hi]
      show (Lagrange.basis (Finset.range (n + 1)) x i).coeff n
          = (Lagrange.basis (Finset.range (n + 1)) x i).coeff
              (Lagrange.basis (Finset.range (n + 1)) x i).natDegree
      rw [hdb]
    simp only [Polynomial.coeff_C_mul, hbc]
  -- That divided difference is `0` because `deg q < n`.
  have hsum0 : ∑ i ∈ Finset.range (n + 1),
      q.eval (x i) * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹ = 0 := by
    rw [← hcoeff]; exact Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
  -- Each summand is `≥ 0`: the weight's sign `(-1)^i` cancels the value's sign.
  have hterm : ∀ i ∈ Finset.range (n + 1),
      0 ≤ q.eval (x i) * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹ := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hin : i ≤ n := by omega
    have hsign := node_divdiff_sign n x hmono i hin
    have halti := halt i hin
    have hsq : (-1 : ℝ) ^ i * (-1) ^ i = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨i, by ring⟩
    have key : q.eval (x i) * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹
        = ((-1 : ℝ) ^ i * q.eval (x i)) *
            ((-1 : ℝ) ^ i * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹) := by
      rw [show ((-1 : ℝ) ^ i * q.eval (x i)) *
              ((-1 : ℝ) ^ i * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹)
            = ((-1 : ℝ) ^ i * (-1) ^ i) *
                (q.eval (x i) * (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹) by ring,
          hsq, one_mul]
    rw [key]; exact mul_nonneg halti (le_of_lt hsign)
  -- A sum of nonnegatives is `0` ⟹ each is `0`; the nonzero weight forces `q (x i) = 0`.
  have heach := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum0
  have hroot : ∀ i ∈ Finset.range (n + 1), q.eval (x i) = 0 := by
    intro i hi
    have h0 := heach i hi
    simp only [Finset.mem_range] at hi
    have hsign := node_divdiff_sign n x hmono i (by omega)
    have hne : (∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j))⁻¹ ≠ 0 := by
      intro hz; rw [hz, mul_zero] at hsign; exact lt_irrefl 0 hsign
    exact (mul_eq_zero.mp h0).resolve_right hne
  -- `n+1` distinct roots contradict `deg q < n` (`card_roots'`).
  have hcardle : n + 1 ≤ q.natDegree := by
    calc n + 1 = ((Finset.range (n + 1)).image x).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ q.roots.toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨i, hi, rfl⟩ := hy
          rw [Multiset.mem_toFinset, Polynomial.mem_roots']
          exact ⟨hq, hroot i hi⟩
      _ ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
      _ ≤ q.natDegree := Polynomial.card_roots' q
  omega

/-- **Uniqueness of the Chebyshev minimizer.** Among monic real polynomials of
degree `n ≥ 1`, the monic Chebyshev polynomial `Mₙ` is the *unique* minimizer of the
sup-norm on `[-1,1]`: any monic degree-`n` polynomial whose values stay within
`2^(1-n)` on `[-1,1]` equals `Mₙ`. Reduced to `weak_alternation_eq_zero` via the
node infrastructure already verified in `Proofs.DeMoivreOQ02OQ03`. -/
theorem monicChebyshev_unique (p : ℝ[X]) (hp : p.Monic) (n : ℕ) (hn : 0 < n)
    (hpdeg : p.natDegree = n)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹) :
    p = monicChebyshev n := by
  classical
  set M : ℝ := ((2 : ℝ) ^ (n - 1))⁻¹ with hM_def
  set q : ℝ[X] := monicChebyshev n - p with hq_def
  -- `q` has degree `< n` (difference of two monic degree-`n` polynomials, or `0`).
  have hdeg : q.natDegree < n := by
    rcases eq_or_ne q 0 with h0 | hqne
    · rw [h0]; simpa using hn
    · have hpne : p ≠ 0 := hp.ne_zero
      have hMcne : monicChebyshev n ≠ 0 := (monicChebyshev_monic n hn).ne_zero
      have hdegM : (monicChebyshev n).degree = (n : WithBot ℕ) := by
        rw [degree_eq_natDegree hMcne, monicChebyshev_natDegree]
      have hdegp : p.degree = (n : WithBot ℕ) := by
        rw [degree_eq_natDegree hpne, hpdeg]
      have hlc : (monicChebyshev n).leadingCoeff = p.leadingCoeff := by
        rw [Monic.def.1 (monicChebyshev_monic n hn), Monic.def.1 hp]
      have hsub : (monicChebyshev n - p).degree < (monicChebyshev n).degree :=
        degree_sub_lt (by rw [hdegM, hdegp]) hMcne hlc
      rw [hdegM, ← hq_def] at hsub
      exact (natDegree_lt_iff_degree_lt hqne).mpr hsub
  -- Weak alternation of `q` at the extreme nodes `x k = cos(kπ/n)`.
  set x : ℕ → ℝ := fun k => Real.cos (k * π / n) with hx_def
  have hmono : ∀ k, k < n → x (k + 1) < x k := by
    intro k hk
    have h := node_strict_anti' n hn (Nat.succ_le_of_lt hk) (Nat.lt_succ_self k)
    simpa [hx_def, Nat.cast_add, Nat.cast_one] using h
  have halt : ∀ k, k ≤ n → 0 ≤ (-1 : ℝ) ^ k * q.eval (x k) := by
    intro k hk
    have hmem : Real.cos (k * π / n) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hev : q.eval (x k) = (-1) ^ k * M - p.eval (x k) := by
      rw [hx_def]; simp only
      rw [hq_def, eval_sub, monicChebyshev_eval_node n k hn, ← hM_def]
    have hsq : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨k, by ring⟩
    have hpb : (-1 : ℝ) ^ k * p.eval (x k) ≤ M := by
      calc (-1 : ℝ) ^ k * p.eval (x k)
          ≤ |(-1 : ℝ) ^ k * p.eval (x k)| := le_abs_self _
        _ = |p.eval (x k)| := by rw [abs_mul]; simp [abs_pow]
        _ ≤ M := by rw [hx_def]; simpa using hbound _ hmem
    have hcalc : (-1 : ℝ) ^ k * q.eval (x k)
        = ((-1) ^ k * (-1) ^ k) * M - (-1) ^ k * p.eval (x k) := by
      rw [hev]; ring
    rw [hcalc, hsq, one_mul]; linarith
  -- Crux: weak alternation at `n+1` nodes + degree `< n` ⟹ `q = 0`.
  have hq0 : q = 0 := weak_alternation_eq_zero n q hdeg x hmono halt
  -- `q = Mₙ - p = 0` ⟹ `p = Mₙ`.
  have hsub0 : monicChebyshev n - p = 0 := by rw [← hq_def]; exact hq0
  exact (sub_eq_zero.1 hsub0).symm

end DeMoivreOQ0203
