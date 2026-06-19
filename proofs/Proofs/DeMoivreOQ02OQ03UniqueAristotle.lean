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

## Crux proof strategy (the genuinely new content over the strict case)

`weak_alternation_eq_zero`: `q ≠ 0`, `natDegree q < n`, nodes `x 0 > x 1 > … > x n`
strictly decreasing, weak alternation `0 ≤ (-1)^k · q(x k)` for `k ≤ n`. Show `q = 0`.

Assume `q ≠ 0` for contradiction. Two complementary cases partition the argument; the
first is already solved upstream, so only the second is new:

* **Case A — no node is a root** (`∀ k ≤ n, q.eval (x k) ≠ 0`). Then the weak
  alternation upgrades to *strict* alternation `0 < (-1)^k · q(x k)`, and the argument
  is identical to the verified strict proof inside `monicChebyshev_minimax`:
  consecutive nodes have strictly opposite signs, so `intermediate_value_uIcc` gives a
  root strictly between each of the `n` consecutive node pairs; `node_strict_anti'`
  makes the `n` roots distinct, contradicting `card_roots' : q.roots.card ≤ natDegree q`
  (`< n`). This case needs *no* multiplicity reasoning — it is the strict lemma verbatim.

* **Case B — some node is a root** (`∃ k ≤ n, q.eval (x k) = 0`). This is the part the
  strict proof does not cover. The standard fix counts roots **with multiplicity**:
  a node-root `x k` at which the sign does not strictly cross (the weak inequality is
  `≥ 0` on *both* neighbouring intervals) is a local extremum of `q`, hence also a root
  of the derivative `q'` (Rolle / `Polynomial.rootMultiplicity ≥ 2`). Summing these
  contributions over the `n` consecutive intervals still yields `≥ n` roots counted with
  multiplicity, again contradicting `q.roots.card ≤ natDegree q < n`. The Mathlib hooks
  are `Polynomial.le_rootMultiplicity_iff`, `Polynomial.roots` /
  `Polynomial.card_roots'`, and `Polynomial.rootMultiplicity` together with the
  derivative characterisation `Polynomial.rootMultiplicity_sub_one ... derivative`
  (a root of multiplicity `m ≥ 1` of `q` that is a non-crossing extremum is a root of
  `q'`). The clean accounting: assign to interval `[x (k+1), x k]` one unit of root mass;
  a node shared as a non-crossing zero contributes its extra multiplicity, so the total
  over `[x n, x 0]` is `≥ n`.

A fully formalised proof is the classical "a polynomial of degree `< n` that weakly
alternates in sign at `n+1` points must vanish" lemma (Markov/Chebyshev uniqueness).
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

/-- **Crux lemma (self-contained, Mathlib-only).** Weak sign-alternation forces a
low-degree polynomial to vanish. If a real polynomial `q` of degree `< n` alternates
weakly in sign at `n+1` strictly-decreasing reals `x 0 > x 1 > … > x n`, i.e.
`0 ≤ (-1)^k · q(x k)` for every `0 ≤ k ≤ n`, then `q = 0`.

This is the one open obligation behind Chebyshev minimax *uniqueness*. The strict
analogue (with `<`) is already discharged inside `monicChebyshev_minimax`; the weak
version is harder because an alternation node need not be a sign change, so roots must
be counted **with multiplicity** (Rolle: a non-crossing zero is a double root). See the
file header for the Case A / Case B decomposition and the Mathlib hooks. -/
theorem weak_alternation_eq_zero (n : ℕ) (q : ℝ[X])
    (hdeg : q.natDegree < n) (x : ℕ → ℝ)
    (hmono : ∀ k, k < n → x (k + 1) < x k)
    (halt : ∀ k, k ≤ n → 0 ≤ (-1 : ℝ) ^ k * q.eval (x k)) :
    q = 0 := by
  sorry

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
