/-
# The Aggregation (Lumping) Property of the Multinomial Distribution

*Open Question binomial-theorem-oq-03-oq-03 — "The Multinomial Distribution from
the Multinomial Theorem".*

The parent thread (BinomialTheoremOQ03) derives the **binomial** distribution and
its structural properties directly from the binomial theorem. A sibling thread
(BinomialTheoremOQ02OQ01OQ02) shows that each *single* coordinate `X_{i₀}` of a
`Multinomial(n, p)` vector is `Binomial(n, p_{i₀})`. This file proves the genuine
generalization that is the multinomial family's defining closure property:

> **Aggregation / lumping.** For *any* union of categories `A ⊆ s`, the aggregated
> count `X_A = ∑_{i ∈ A} X_i` is `Binomial(n, p_A)` with `p_A = ∑_{i ∈ A} p_i`.

In words: collapsing several categories of a multinomial vector into one
super-category again yields a binomial count. The single-coordinate marginal is
the special case `A = {i₀}`; full aggregation `A = s` recovers the deterministic
identity `X_s = n`.

## Proof Strategy: Probability Generating Function

We use the multinomial moment-generating identity (itself a repackaging of the
multinomial theorem). Plugging in the *block indicator* weight

    g(i) = if i ∈ A then t else 1

makes the generating product collapse to a single power of `t`:

    ∏_{i ∈ s} g(i)^{k(i)} = t^{∑_{i ∈ A} k(i)} = t^{X_A(k)},

while the base of the `n`-th power simplifies, using `∑_{i ∈ s} p_i = 1`, to

    ∑_{i ∈ s} p_i · g(i) = p_A · t + (1 - p_A).

Hence

    E[t^{X_A}] = (p_A · t + (1 - p_A))^n,

which is exactly the `Binomial(n, p_A)` probability generating function. Expanding
with the binomial theorem identifies the coefficients with the binomial PMF.

The single-coordinate result uses the *equality* indicator `g(i) = if i = i₀ …`;
here the only change is the *membership* indicator `g(i) = if i ∈ A …`, and the
whole argument goes through verbatim — which is precisely why aggregation is so
natural from the generating-function viewpoint.

## Mathlib Dependencies

- `Finset.sum_pow_eq_sum_piAntidiag` : the multinomial theorem
- `Finset.prod_ite_mem`, `Finset.sum_ite_mem` : collapse a block indicator product/sum
- `Finset.prod_pow_eq_pow_sum` : ∏ tᵏ⁽ⁱ⁾ = t^(∑ k(i))
- `Finset.inter_eq_right`, `Finset.sum_sdiff` : block / complement bookkeeping
- `add_pow` : binomial theorem expansion of the PGF

**Axiom count**: 0   **Sorry count**: 0
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace BinomialTheoremOQ03OQ03

open Finset BigOperators

/-! ## Setup: the multinomial PMF and its generating identity

These two declarations reproduce, self-containedly, the established convention of
the binomial-theorem thread (cf. `BinomialTheoremOQ02OQ01OQ02`,
`BinomialTheoremOQ02OQ01OQ03`), so this file depends only on Mathlib. -/

/-- The multinomial probability mass function:
`P(X = k) = multinomial(s, k) · ∏_{i ∈ s} p(i)^{k(i)}`. -/
noncomputable def multinomialProb {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (_n : ℕ) (k : α → ℕ) : ℝ :=
  (Nat.multinomial s k : ℝ) * ∏ i ∈ s, p i ^ k i

/-- **Multinomial generating identity.** For any weight `g`,
`(∑ᵢ p(i)·g(i))^n = ∑_{k:∑k=n} P(X=k) · ∏ᵢ g(i)^{k(i)}`. This is the multinomial
theorem with `f(i) = p(i)·g(i)`, with the `p` and `g` powers separated. -/
theorem multinomial_mgf_real {α : Type*} [DecidableEq α]
    (s : Finset α) (p g : α → ℝ) (n : ℕ) :
    (∑ i ∈ s, p i * g i) ^ n =
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * ∏ i ∈ s, g i ^ k i := by
  unfold multinomialProb
  rw [Finset.sum_pow_eq_sum_piAntidiag s (fun i => p i * g i) n]
  congr 1; ext k
  have prod_split : ∏ i ∈ s, (p i * g i) ^ k i =
      (∏ i ∈ s, p i ^ k i) * ∏ i ∈ s, g i ^ k i := by
    rw [← Finset.prod_mul_distrib]
    congr 1; ext i
    exact mul_pow (p i) (g i) (k i)
  rw [prod_split]; ring

/-- **Normalization.** When `∑ᵢ p(i) = 1`, the multinomial PMF sums to `1`. -/
theorem multinomialProb_sum_one {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k = 1 := by
  unfold multinomialProb
  have h := Finset.sum_pow_eq_sum_piAntidiag s p n
  rw [hp, one_pow] at h
  exact h.symm

/-! ## Main Theorem: the aggregation PGF -/

/-- **Aggregation PGF (main result).** For any block of categories `A ⊆ s`, the
probability generating function of the aggregated count `X_A = ∑_{i ∈ A} X_i` is

    E[t^{X_A}] = ∑_k P(X=k) · t^{∑_{i ∈ A} k(i)} = (p_A · t + (1 - p_A))^n,

where `p_A = ∑_{i ∈ A} p(i)`. This is exactly the `Binomial(n, p_A)` PGF, so the
aggregated count is binomially distributed: **the multinomial is closed under
category lumping.** -/
theorem multinomial_aggregate_pgf {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (A : Finset α) (hAs : A ⊆ s) (t : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (∑ i ∈ A, k i) =
    ((∑ i ∈ A, p i) * t + (1 - ∑ i ∈ A, p i)) ^ n := by
  -- Block indicator `g(i) = if i ∈ A then t else 1` collapses the generating
  -- product to `t^{∑_{i ∈ A} k(i)}`.
  have prod_simp : ∀ k : α → ℕ,
      ∏ i ∈ s, (if i ∈ A then t else (1 : ℝ)) ^ k i = t ^ (∑ i ∈ A, k i) := fun k => by
    have step : ∀ i ∈ s, (if i ∈ A then t else (1 : ℝ)) ^ k i
        = if i ∈ A then t ^ k i else 1 := by
      intro i _; split_ifs <;> simp
    rw [Finset.prod_congr rfl step, Finset.prod_ite_mem,
        Finset.inter_eq_right.mpr hAs, Finset.prod_pow_eq_pow_sum]
  -- The PGF base simplifies to `p_A · t + (1 - p_A)` using `∑_s p = 1`.
  have sum_simp : ∑ i ∈ s, p i * (if i ∈ A then t else (1 : ℝ))
      = (∑ i ∈ A, p i) * t + (1 - ∑ i ∈ A, p i) := by
    have h1 : ∑ i ∈ s, p i * (if i ∈ A then t else 1) =
              ∑ i ∈ s, p i + ∑ i ∈ s, (t - 1) * (if i ∈ A then p i else 0) := by
      rw [← Finset.sum_add_distrib]
      congr 1; ext i; split_ifs <;> ring
    rw [h1, hp, ← Finset.mul_sum, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr hAs]
    ring
  -- Assemble: rewrite the aggregated sum via the MGF identity, collapse, simplify.
  rw [show ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (∑ i ∈ A, k i) =
          (∑ i ∈ s, p i * (if i ∈ A then t else 1)) ^ n from by
    rw [multinomial_mgf_real s p (fun i => if i ∈ A then t else 1) n]
    apply Finset.sum_congr rfl; intro k _; rw [prod_simp k],
    sum_simp]

/-! ## Corollaries -/

/-- **Aggregated count is Binomial(n, p_A).** Expanding the aggregation PGF with the
binomial theorem identifies its coefficients with the `Binomial(n, p_A)` PMF:

    E[t^{X_A}] = ∑_{j=0}^{n} C(n,j) · p_A^j · (1 - p_A)^{n-j} · t^j. -/
theorem multinomial_aggregate_pgf_eq_binomial {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (A : Finset α) (hAs : A ⊆ s) (t : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (∑ i ∈ A, k i) =
    ∑ j ∈ Finset.range (n + 1),
      (Nat.choose n j : ℝ) * (∑ i ∈ A, p i) ^ j
        * (1 - ∑ i ∈ A, p i) ^ (n - j) * t ^ j := by
  rw [multinomial_aggregate_pgf s p n hp A hAs t, add_pow]
  congr 1; ext j; ring

/-- **Single-coordinate marginal as a special case.** Taking `A = {i₀}` recovers the
classical result that the marginal `X_{i₀}` is `Binomial(n, p_{i₀})`. -/
theorem multinomial_marginal_pgf_of_aggregate {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (t : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (k i₀) =
    (p i₀ * t + (1 - p i₀)) ^ n := by
  have h := multinomial_aggregate_pgf s p n hp {i₀}
    (Finset.singleton_subset_iff.mpr hi₀) t
  simpa using h

/-- **Complementary block.** Aggregating the complement `s \ A` is `Binomial(n, 1 - p_A)`
— the two-outcome lumping of a multinomial into "in `A`" vs "not in `A`". -/
theorem multinomial_aggregate_compl_pgf {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (A : Finset α) (hAs : A ⊆ s) (t : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (∑ i ∈ s \ A, k i) =
    ((1 - ∑ i ∈ A, p i) * t + (∑ i ∈ A, p i)) ^ n := by
  -- p over the complement is 1 - p_A.
  have hpc : ∑ i ∈ s \ A, p i = 1 - ∑ i ∈ A, p i := by
    have h := Finset.sum_sdiff (f := p) hAs
    rw [hp] at h; linarith
  have h := multinomial_aggregate_pgf s p n hp (s \ A) (Finset.sdiff_subset) t
  rw [hpc] at h
  have hsimp : (1 : ℝ) - (1 - ∑ i ∈ A, p i) = ∑ i ∈ A, p i := by ring
  rw [hsimp] at h
  exact h

/-- **Full aggregation is deterministic.** Lumping *all* categories together gives the
constant total `X_s = n`, so its PGF is `t^n`: with `p_s = 1` the binomial collapses to
a point mass at `n`. -/
theorem multinomial_aggregate_univ {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) (t : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (∑ i ∈ s, k i) = t ^ n := by
  have h := multinomial_aggregate_pgf s p n hp s (Finset.Subset.refl s) t
  rw [hp] at h
  simpa using h

/-! ## Concrete instance: a three-category multinomial -/

/-- **Worked example.** For a `Multinomial(n, p)` on `s = {0, 1, 2}` (encoded in `Fin 3`),
lumping categories `{0, 1}` together gives a `Binomial(n, p₀ + p₁)` count, whose PGF is
`((p₀ + p₁)·t + p₂)^n`. -/
theorem aggregate_fin3_example (p : Fin 3 → ℝ) (n : ℕ)
    (hp : p 0 + p 1 + p 2 = 1) (t : ℝ) :
    ∑ k ∈ (Finset.univ : Finset (Fin 3)).piAntidiag n,
      multinomialProb Finset.univ p n k * t ^ (k 0 + k 1) =
    ((p 0 + p 1) * t + p 2) ^ n := by
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 3)), p i = 1 := by
    rw [Fin.sum_univ_three]; linarith
  have h := multinomial_aggregate_pgf (Finset.univ : Finset (Fin 3)) p n hsum
    ({0, 1} : Finset (Fin 3)) (Finset.subset_univ _) t
  -- ∑_{i ∈ {0,1}} k i = k 0 + k 1 and ∑_{i ∈ {0,1}} p i = p 0 + p 1
  have hk : ∀ k : Fin 3 → ℕ, ∑ i ∈ ({0, 1} : Finset (Fin 3)), k i = k 0 + k 1 := by
    intro k; rw [Finset.sum_pair (by decide)]
  have hpA : ∑ i ∈ ({0, 1} : Finset (Fin 3)), p i = p 0 + p 1 :=
    Finset.sum_pair (by decide)
  have hp2 : (1 : ℝ) - (p 0 + p 1) = p 2 := by linarith
  rw [hpA, hp2] at h
  -- now h : ∑ k, P·t^(∑_{0,1} k) = ((p₀+p₁)·t + p₂)^n; align the exponent
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _; rw [hk k]

/-! ## Summary

For `(X₁, …, X_r) ~ Multinomial(n, p)` with `∑ᵢ pᵢ = 1` and any block `A`:

| theorem | statement |
|---|---|
| `multinomial_aggregate_pgf` | `E[t^{X_A}] = (p_A·t + (1-p_A))^n` |
| `multinomial_aggregate_pgf_eq_binomial` | matches the `Binomial(n, p_A)` PMF expansion |
| `multinomial_marginal_pgf_of_aggregate` | special case `A = {i₀}`: marginal is `Binomial(n, p_{i₀})` |
| `multinomial_aggregate_compl_pgf` | complement block is `Binomial(n, 1 - p_A)` |
| `multinomial_aggregate_univ` | full aggregation: `X_s = n` (PGF `t^n`) |

**Answer to the open question:** the multinomial distribution arises from, and is
characterized by, the multinomial theorem. Its single most distinctive structural
feature — closure under arbitrary category aggregation, with every lumped count
binomial — is a one-line consequence of the multinomial generating identity,
proved here from scratch with 0 axioms and 0 sorries.
-/

end BinomialTheoremOQ03OQ03
