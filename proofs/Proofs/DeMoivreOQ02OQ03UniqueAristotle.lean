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
(Mathlib-only). Given the crux, uniqueness follows mechanically from the already-verified
node infrastructure, discharged in `monicChebyshev_unique` below.

## Crux proof strategy — divided-difference (Lagrange) route

`weak_alternation_eq_zero`: `natDegree q < n`, nodes `x 0 > x 1 > … > x n` strictly
decreasing, weak alternation `0 ≤ (-1)^k · q(x k)` for `k ≤ n`. Show `q = 0`.

The route avoids root-multiplicity reasoning entirely via Lagrange interpolation:

1. **`q` is its own interpolant.** With node set `s = range (n+1)` (injective via strict
   monotonicity) and `deg q < n + 1 = #s`, `Lagrange.eq_interpolate` gives
   `q = interpolate s x (fun i ↦ q.eval (x i))`.
2. **The `n`-th coefficient is the `n`-th divided difference.** Reading off `coeff n` of
   the interpolant (each basis polynomial has `natDegree = #s - 1 = n`, so its `coeff n`
   is its `leadingCoeff`, computed by `Lagrange.leadingCoeff_basis`) yields
   `q.coeff n = ∑ i, q.eval (x i) · (∏ j ∈ (range (n+1)).erase i, (x i - x j))⁻¹`.
   Since `natDegree q < n`, the left side is `0` (`coeff_eq_zero_of_natDegree_lt`).
3. **Every summand is `≥ 0`.** The denominator `∏ j ≠ i, (x i - x j)` has sign `(-1)^i`
   (the sole self-contained obligation `node_divdiff_sign`: the `i` factors `j < i` are
   negative, the rest positive), hence so does its inverse. Multiplying by `q.eval (x i)`,
   whose weak alternation gives `0 ≤ (-1)^i · q.eval (x i)`, the `(-1)^i` factors cancel.
4. **Therefore every term is `0`** (`Finset.sum_eq_zero_iff_of_nonneg`), and as the weight
   is nonzero, `q.eval (x i) = 0` for all `i ≤ n`: `q` vanishes at `n + 1` distinct points.
5. **Therefore `q = 0`** (`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`).

## Status (researcher-7, 2026-06-19) — crux discharged, build-verified

The sole obligation `node_divdiff_sign` was proved by Aristotle (project `3b070308`,
COMPLETE) by partitioning `(range (n+1)).erase i` into `range i` (negative factors) and
`Ioc i n` (positive factors). The complete file — `node_divdiff_sign` together with the
`weak_alternation_eq_zero` reduction — builds with **no `sorry`**, depending only on the
standard axioms `propext`, `Classical.choice`, `Quot.sound`. (Aristotle's verification ran
under `lean4:v4.28.0`; the one toolchain-sensitive step `hni : n = s.card - 1` is closed
here with `omega`, which is robust under this project's pinned `v4.26.0`.)
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

/-- **Sign of the `n`-th divided-difference denominator.** For strictly-decreasing nodes
`x 0 > x 1 > … > x n` (here as the antitonicity hypothesis `hanti`) and `i ≤ n`, the
product `∏_{j ≠ i} (x i - x j)` over `j ∈ {0,…,n}\{i}` has sign `(-1)^i`: exactly the `i`
factors with `j < i` are negative (since `x j > x i`) and the rest positive. Proof by
partitioning the index set into `range i` and `Ioc i n` and applying `Finset.prod_pos`.

Discharged by Aristotle (project `3b070308`). -/
private theorem node_divdiff_sign (n i : ℕ) (hi : i ≤ n) (x : ℕ → ℝ)
    (hanti : ∀ a b : ℕ, b ≤ n → a < b → x b < x a) :
    0 < (-1 : ℝ) ^ i * ∏ j ∈ (Finset.range (n + 1)).erase i, (x i - x j) := by
  have h_partition : ∏ j ∈ ((Finset.range (n + 1)).erase i), ((x i) - (x j)) = (∏ j ∈ ((Finset.range i)), ((x i) - (x j))) * (∏ j ∈ (Finset.Ioc i n), ((x i) - (x j))) := by
    rw [ ← Finset.prod_union ] ; congr ; ext ; simp_all +decide [ Finset.mem_erase, Finset.mem_range ] ; omega;
    exact Finset.disjoint_left.mpr fun y hy₁ hy₂ => by linarith [ Finset.mem_range.mp hy₁, Finset.mem_Ioc.mp hy₂ ] ;
  have h_lower_pos : 0 < ∏ j ∈ Finset.range i, (x j - x i) := by
    exact Finset.prod_pos fun j hj => sub_pos.mpr <| hanti _ _ hi <| Finset.mem_range.mp hj
  have h_lower_neg : (∏ j ∈ Finset.range i, (x i - x j)) = (-1 : ℝ) ^ i * (∏ j ∈ Finset.range i, (x j - x i)) := by
    rw [ ← Finset.prod_congr rfl fun _ _ => neg_sub _ _ ] ; rw [ Finset.prod_congr rfl fun _ _ => neg_eq_neg_one_mul _, Finset.prod_mul_distrib ] ; norm_num;
  by_cases hev : Even i <;> simp_all +decide [ mul_assoc ];
  · exact Finset.prod_pos fun j hj => sub_pos.mpr <| hanti _ _ ( by linarith [ Finset.mem_Ioc.mp hj ] ) <| by linarith [ Finset.mem_Ioc.mp hj ] ;
  · exact Finset.prod_pos fun j hj => sub_pos.mpr ( hanti _ _ ( by linarith [ Finset.mem_Ioc.mp hj ] ) ( by linarith [ Finset.mem_Ioc.mp hj ] ) )

/-- **Crux lemma.** Weak sign-alternation forces a low-degree polynomial to vanish: if a
real polynomial `q` of degree `< n` alternates weakly in sign at `n+1` strictly-decreasing
reals `x 0 > x 1 > … > x n`, i.e. `0 ≤ (-1)^k · q(x k)` for every `0 ≤ k ≤ n`, then `q = 0`.

Proved in full via the divided-difference (Lagrange) route — see the file header for the
step-by-step strategy. Reduces to the single sign lemma `node_divdiff_sign`. -/
theorem weak_alternation_eq_zero (n : ℕ) (q : ℝ[X])
    (hdeg : q.natDegree < n) (x : ℕ → ℝ)
    (hmono : ∀ k, k < n → x (k + 1) < x k)
    (halt : ∀ k, k ≤ n → 0 ≤ (-1 : ℝ) ^ k * q.eval (x k)) :
    q = 0 := by
  classical
  have hanti : ∀ a b : ℕ, b ≤ n → a < b → x b < x a := by
    intro a b
    induction b with
    | zero => intro _ h; exact absurd h (Nat.not_lt_zero a)
    | succ k ih =>
      intro hk hab
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hstep : x (k + 1) < x k := hmono k (Nat.lt_of_succ_le hk)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
      · exact lt_trans hstep (ih hk' h)
      · subst h; exact hstep
  set s : Finset ℕ := Finset.range (n + 1) with hs
  have hcard : s.card = n + 1 := by rw [hs, Finset.card_range]
  have hmem_iff : ∀ a, a ∈ s ↔ a ≤ n := by intro a; rw [hs, Finset.mem_range]; omega
  have hxne : ∀ a b, a ≤ n → b ≤ n → a ≠ b → x a ≠ x b := by
    intro a b ha hb hab
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have := hanti a b hb h; linarith
    · have := hanti b a ha h; linarith
  have hinj : Set.InjOn x ↑s := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hmem_iff] at ha hb
    by_contra hne
    exact hxne a b ha hb hne hab
  have hdeg' : q.degree < (s.card : WithBot ℕ) := by
    have h1 : q.natDegree < s.card := by rw [hcard]; omega
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast h1)
  have hself : q = Lagrange.interpolate s x (fun i => q.eval (x i)) :=
    Lagrange.eq_interpolate hinj hdeg'
  have hni : n = s.card - 1 := by omega
  have hidc : q.coeff n
      = ∑ i ∈ s, q.eval (x i) * (∏ j ∈ s.erase i, (x i - x j))⁻¹ := by
    conv_lhs => rw [hself]
    rw [Lagrange.interpolate_apply, finset_sum_coeff]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [coeff_C_mul]
    congr 1
    rw [hni, ← Lagrange.natDegree_basis hinj hi, ← leadingCoeff,
      Lagrange.leadingCoeff_basis hinj hi]
  have hsum0 : ∑ i ∈ s, q.eval (x i) * (∏ j ∈ s.erase i, (x i - x j))⁻¹ = 0 := by
    rw [← hidc, coeff_eq_zero_of_natDegree_lt hdeg]
  have hterm : ∀ i ∈ s, 0 ≤ q.eval (x i) * (∏ j ∈ s.erase i, (x i - x j))⁻¹ := by
    intro i hi
    have hi_le : i ≤ n := (hmem_iff i).mp hi
    set D : ℝ := ∏ j ∈ s.erase i, (x i - x j) with hD
    have he : ((-1 : ℝ) ^ i) * ((-1 : ℝ) ^ i) = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨i, rfl⟩
    have hDpos : 0 < (-1 : ℝ) ^ i * D := by rw [hD, hs]; exact node_divdiff_sign n i hi_le x hanti
    have hDipos : 0 < (-1 : ℝ) ^ i * D⁻¹ := by
      have hrw : (-1 : ℝ) ^ i * D⁻¹ = ((-1 : ℝ) ^ i * D)⁻¹ := by
        rw [mul_inv, inv_eq_of_mul_eq_one_right he]
      rw [hrw]; exact inv_pos.mpr hDpos
    have hcong : q.eval (x i) * D⁻¹
        = ((-1 : ℝ) ^ i * q.eval (x i)) * ((-1 : ℝ) ^ i * D⁻¹) := by
      have h : ((-1 : ℝ) ^ i * q.eval (x i)) * ((-1 : ℝ) ^ i * D⁻¹)
          = (((-1 : ℝ) ^ i) * ((-1 : ℝ) ^ i)) * (q.eval (x i) * D⁻¹) := by ring
      rw [h, he, one_mul]
    rw [hcong]
    exact mul_nonneg (halt i hi_le) (le_of_lt hDipos)
  have hroot : ∀ i ∈ s, q.eval (x i) = 0 := by
    intro i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum0 i hi
    have hDne : (∏ j ∈ s.erase i, (x i - x j)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hj_le : j ≤ n := (hmem_iff j).mp (Finset.mem_erase.mp hj).2
      exact sub_ne_zero.mpr (hxne i j ((hmem_iff i).mp hi) hj_le (Ne.symm hji))
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd (inv_eq_zero.mp h) hDne
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q (s.image x) ?_ ?_
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    exact hroot i hi
  · rw [Finset.card_image_of_injOn hinj, hcard]; omega

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
