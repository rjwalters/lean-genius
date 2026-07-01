/-
# Multinomial Covariance: `Cov(Xᵢ, Xⱼ) = − n · pᵢ · pⱼ`

If `(X₁,…,X_k) ~ Multinomial(n, p₁,…,p_k)`, then for `i ≠ j`

        Cov(Xᵢ, Xⱼ) = − n · pᵢ · pⱼ.

The off-diagonal entries of the multinomial covariance matrix are negative:
the components compete for the fixed total `n`, so an excess in one coordinate
depresses the others.

## Framework (inherited from the parent — combinatorial, NOT measure-theoretic)

The parent `BinomialTheoremOQ02OQ01OQ02` ("Marginal Distributions of Multinomial
Are Binomial", verified) works with explicit PMF values over `s.piAntidiag n`:

    multinomialProb s p n k = (Nat.multinomial s k) · ∏ i ∈ s, p i ^ k i

with expectations expressed as explicit finite sums
`E[f(X)] = ∑_{k ∈ s.piAntidiag n} multinomialProb s p n k · f(k)`.

## Proof strategy (PGF / differentiation route)

Rather than the finicky `k ↦ k − eᵢ − eⱼ` reindexing bijection, we extract moments
by differentiating probability generating functions, reusing the parent's
`multinomial_mgf_real` engine:

* `multinomial_pair_pgf` — the two-variable joint PGF of `(Xᵢ, Xⱼ)`:
  `∑_k P(k) · xᵏⁱ · yᵏʲ = (pᵢx + pⱼy + (1−pᵢ−pⱼ))ⁿ`  (same MGF collapse the parent
  used for the single-coordinate marginal, one level up).
* `multinomial_mean` — `E[Xᵢ] = n·pᵢ`, by differentiating the parent's marginal
  PGF once at `t = 1`.
* `multinomial_mixed_moment` — `E[XᵢXⱼ] = n(n−1)·pᵢpⱼ`, by differentiating the
  pair PGF once in `y` (giving an intermediate identity in `x`) and then once in
  `x`, both evaluated at `1`.  (`HasDerivAt.sum` term-by-term on the finite sum;
  `HasDerivAt.pow` / chain rule on the power tower; `HasDerivAt.unique` to equate
  the two sides.)
* `multinomial_covariance` — `E[XᵢXⱼ] − E[Xᵢ]·E[Xⱼ] = −n·pᵢpⱼ`, pure algebra
  `n(n−1)pᵢpⱼ − (npᵢ)(npⱼ) = −n·pᵢpⱼ`.

Kept as the explicit `E[XY] − E[X]E[Y]` difference (no measure-theoretic
`ProbabilityTheory.covariance`), matching the parent's self-contained setup.

Verified, 0 axioms, 0 sorries.
-/

import Proofs.BinomialTheoremOQ02OQ01OQ02
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace BinomialTheoremOQ02OQ01OQ02OQ02

open Finset BigOperators BinomialTheoremOQ02OQ01OQ02

/-! ## Joint PGF of a pair of coordinates -/

/-- **Pair PGF**: the joint probability generating function of `(Xᵢ, Xⱼ)` in a
multinomial equals the trinomial expansion

    E[x^{Xᵢ}·y^{Xⱼ}] = ∑_k P(X=k)·x^{k(i)}·y^{k(j)} = (pᵢ·x + pⱼ·y + (1−pᵢ−pⱼ))ⁿ.

Proof: apply the parent's `multinomial_mgf_real` with `g(a) = x` if `a = i`,
`y` if `a = j`, and `1` otherwise.  The product `∏ g(a)^{k(a)}` collapses to
`x^{k(i)}·y^{k(j)}` and the base sum `∑ p(a)·g(a)` collapses to
`pᵢ·x + pⱼ·y + (1−pᵢ−pⱼ)`. -/
theorem multinomial_pair_pgf {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) (x y : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * y ^ (k j) =
    (p i * x + p j * y + (1 - p i - p j)) ^ n := by
  -- Product collapse: ∏ a ∈ s, g(a)^{k a} = x^{k i} · y^{k j}.
  have prod_simp : ∀ k : α → ℕ,
      ∏ a ∈ s, (if a = i then x else if a = j then y else (1 : ℝ)) ^ k a
        = x ^ k i * y ^ k j := by
    intro k
    have hsub : ({i, j} : Finset α) ⊆ s := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    have hone : ∀ a ∈ s, a ∉ ({i, j} : Finset α) →
        (if a = i then x else if a = j then y else (1 : ℝ)) ^ k a = 1 := by
      intro a _ ha'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha'
      obtain ⟨hai, haj⟩ := ha'
      rw [if_neg hai, if_neg haj, one_pow]
    rw [← Finset.prod_subset hsub hone, Finset.prod_pair hij,
        if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
  -- Base sum collapse: ∑ a ∈ s, p a · g(a) = pᵢx + pⱼy + (1−pᵢ−pⱼ).
  have sum_simp : ∑ a ∈ s, p a * (if a = i then x else if a = j then y else (1 : ℝ))
      = p i * x + p j * y + (1 - p i - p j) := by
    have hstep : ∑ a ∈ s, p a * (if a = i then x else if a = j then y else (1 : ℝ))
        = ∑ a ∈ s, (p a + ((if a = i then p a * (x - 1) else 0)
            + (if a = j then p a * (y - 1) else 0))) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs with h1 h2 <;> try ring
      all_goals exact absurd (h1.symm.trans h2) hij
    rw [hstep, Finset.sum_add_distrib, Finset.sum_add_distrib, hp,
        Finset.sum_ite_eq' s i (fun a => p a * (x - 1)),
        Finset.sum_ite_eq' s j (fun a => p a * (y - 1)),
        if_pos hi, if_pos hj]
    ring
  have hmgf : ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * y ^ (k j)
      = (∑ a ∈ s, p a * (if a = i then x else if a = j then y else (1 : ℝ))) ^ n := by
    rw [multinomial_mgf_real s p (fun a => if a = i then x else if a = j then y else 1) n]
    apply Finset.sum_congr rfl
    intro k _
    rw [prod_simp k]; ring
  rw [hmgf, sum_simp]

/-! ## First moment (mean) of a single coordinate -/

/-- **Mean**: `E[Xᵢ] = ∑_k P(X=k)·k(i) = n·pᵢ`.

Proof: the parent's `multinomial_marginal_pgf` gives, for all `t`,
`∑_k P(X=k)·t^{k(i)} = (pᵢ·t + (1−pᵢ))ⁿ`.  Both sides are the same function of
`t`; differentiate at `t = 1`.  The left derivative is `∑_k P(X=k)·k(i)` (the mean);
the right derivative is `n·(pᵢ·1 + (1−pᵢ))^{n−1}·pᵢ = n·pᵢ`. -/
theorem multinomial_mean {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) {i : α} (hi : i ∈ s) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) = n * p i := by
  have hFG : (fun t : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (k i))
      = (fun t : ℝ => (p i * t + (1 - p i)) ^ n) := by
    funext t; exact multinomial_marginal_pgf s p n hp i hi t
  have hF : HasDerivAt
      (fun t : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (k i))
      (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * ((k i : ℝ) * (1 : ℝ) ^ (k i - 1))) 1 := by
    rw [show (fun t : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (k i))
        = ∑ k ∈ s.piAntidiag n, fun (t : ℝ) => multinomialProb s p n k * t ^ (k i) from by
          funext t; simp]
    exact HasDerivAt.sum fun k _ =>
      (hasDerivAt_pow (k i) (1 : ℝ)).const_mul (multinomialProb s p n k)
  have hG : HasDerivAt (fun t : ℝ => (p i * t + (1 - p i)) ^ n) ((n : ℝ) * p i) 1 := by
    have hb : HasDerivAt (fun t : ℝ => p i * t + (1 - p i)) (p i) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul (p i)).add_const (1 - p i)
    have key : (n : ℝ) * p i = (n : ℝ) * (p i * 1 + (1 - p i)) ^ (n - 1) * p i := by
      rw [show p i * (1 : ℝ) + (1 - p i) = 1 from by ring, one_pow, mul_one]
    rw [key]; exact hb.pow n
  rw [hFG] at hF
  have key := hF.unique hG
  simpa using key

/-! ## Mixed second moment -/

/-- **Mixed second moment**: `E[Xᵢ·Xⱼ] = ∑_k P(X=k)·k(i)·k(j) = n(n−1)·pᵢpⱼ` for `i ≠ j`.

Proof: differentiate the pair PGF `multinomial_pair_pgf`.  First differentiate in
`y` at `y = 1` (with `x` a parameter), obtaining the intermediate identity
`∑_k P(X=k)·x^{k(i)}·k(j) = n·(pᵢ·x + (1−pᵢ))^{n−1}·pⱼ` for all `x`.  Then
differentiate that in `x` at `x = 1`, obtaining
`∑_k P(X=k)·k(i)·k(j) = n(n−1)·pᵢpⱼ`. -/
theorem multinomial_mixed_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) * (k j : ℝ)
      = (n : ℝ) * ((n : ℝ) - 1) * p i * p j := by
  -- Stage 1: differentiate the pair PGF in y at y = 1 (parametrised by x).
  have stage1 : ∀ x : ℝ,
      (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * (k j : ℝ))
        = (n : ℝ) * (p i * x + (1 - p i)) ^ (n - 1) * p j := by
    intro x
    have hAB :
        (fun y : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * y ^ (k j))
        = (fun y : ℝ => (p i * x + p j * y + (1 - p i - p j)) ^ n) := by
      funext y; exact multinomial_pair_pgf s p n hp hi hj hij x y
    have hA : HasDerivAt
        (fun y : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * y ^ (k j))
        (∑ k ∈ s.piAntidiag n,
          multinomialProb s p n k * x ^ (k i) * ((k j : ℝ) * (1 : ℝ) ^ (k j - 1))) 1 := by
      rw [show (fun y : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * y ^ (k j))
          = ∑ k ∈ s.piAntidiag n, fun (y : ℝ) =>
              multinomialProb s p n k * x ^ (k i) * y ^ (k j) from by
            funext y; simp]
      exact HasDerivAt.sum fun k _ =>
        (hasDerivAt_pow (k j) (1 : ℝ)).const_mul (multinomialProb s p n k * x ^ (k i))
    have hB : HasDerivAt (fun y : ℝ => (p i * x + p j * y + (1 - p i - p j)) ^ n)
        ((n : ℝ) * (p i * x + (1 - p i)) ^ (n - 1) * p j) 1 := by
      have hb : HasDerivAt (fun y : ℝ => p i * x + p j * y + (1 - p i - p j)) (p j) 1 := by
        simpa using
          (((hasDerivAt_id (1 : ℝ)).const_mul (p j)).const_add (p i * x)).add_const
            (1 - p i - p j)
      have key : (n : ℝ) * (p i * x + (1 - p i)) ^ (n - 1) * p j
          = (n : ℝ) * (p i * x + p j * 1 + (1 - p i - p j)) ^ (n - 1) * p j := by
        rw [show p i * x + p j * (1 : ℝ) + (1 - p i - p j) = p i * x + (1 - p i) from by ring]
      rw [key]; exact hb.pow n
    rw [hAB] at hA
    have := hA.unique hB
    simpa using this
  -- Stage 2: differentiate the stage-1 identity in x at x = 1.
  have hPC :
      (fun x : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * (k j : ℝ))
      = (fun x : ℝ => (n : ℝ) * (p i * x + (1 - p i)) ^ (n - 1) * p j) := funext stage1
  have hψ : HasDerivAt
      (fun x : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * (k j : ℝ))
      (∑ k ∈ s.piAntidiag n,
        multinomialProb s p n k * ((k i : ℝ) * (1 : ℝ) ^ (k i - 1)) * (k j : ℝ)) 1 := by
    rw [show (fun x : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * x ^ (k i) * (k j : ℝ))
        = ∑ k ∈ s.piAntidiag n, fun (x : ℝ) =>
            multinomialProb s p n k * x ^ (k i) * (k j : ℝ) from by
          funext x; simp]
    exact HasDerivAt.sum fun k _ =>
      ((hasDerivAt_pow (k i) (1 : ℝ)).const_mul (multinomialProb s p n k)).mul_const ((k j : ℝ))
  have hχ : HasDerivAt (fun x : ℝ => (n : ℝ) * (p i * x + (1 - p i)) ^ (n - 1) * p j)
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * p i * p j) 1 := by
    have hb : HasDerivAt (fun x : ℝ => p i * x + (1 - p i)) (p i) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul (p i)).add_const (1 - p i)
    have key : (n : ℝ) * ((n - 1 : ℕ) : ℝ) * p i * p j
        = (n : ℝ) * (((n - 1 : ℕ) : ℝ) * (p i * 1 + (1 - p i)) ^ (n - 1 - 1) * p i) * p j := by
      rw [show p i * (1 : ℝ) + (1 - p i) = 1 from by ring, one_pow]; ring
    rw [key]
    exact ((hb.pow (n - 1)).const_mul (n : ℝ)).mul_const (p j)
  rw [hPC] at hψ
  have hfinal := hψ.unique hχ
  have hnn : (n : ℝ) * ((n - 1 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    cases n with
    | zero => simp
    | succ m => push_cast [Nat.succ_sub_one]; ring
  rw [← hnn]
  simpa using hfinal

/-! ## Headline: off-diagonal covariance -/

/-- **Multinomial covariance** (headline): for `i ≠ j`,

    Cov(Xᵢ, Xⱼ) = E[XᵢXⱼ] − E[Xᵢ]·E[Xⱼ] = −n·pᵢ·pⱼ.

Immediate from `multinomial_mixed_moment` (`E[XᵢXⱼ] = n(n−1)pᵢpⱼ`) and
`multinomial_mean` (`E[Xᵢ] = npᵢ`): `n(n−1)pᵢpⱼ − (npᵢ)(npⱼ) = −n·pᵢpⱼ`. -/
theorem multinomial_covariance {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) * (k j : ℝ))
      - (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ))
        * (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k j : ℝ))
      = -(n : ℝ) * p i * p j := by
  rw [multinomial_mixed_moment s p n hp hi hj hij,
      multinomial_mean s p n hp hi, multinomial_mean s p n hp hj]
  ring

end BinomialTheoremOQ02OQ01OQ02OQ02
