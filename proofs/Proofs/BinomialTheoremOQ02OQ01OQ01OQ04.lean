import Mathlib
import Proofs.BinomialTheoremOQ02OQ01OQ01

/-
# The full second-order structure of the multinomial distribution

## Open Question (slug: binomial-theorem-oq-02-oq-01-oq-01-oq-04)

The parent `binomial-theorem-oq-02-oq-01-oq-01` formalises the multinomial PMF and
proves the **mean** `E[Xᵢ] = n·pᵢ`, the **cross moment** `E[XᵢXⱼ] = n(n-1)pᵢpⱼ`
(for `i ≠ j`), and the **off-diagonal covariance** `Cov(Xᵢ,Xⱼ) = -n·pᵢ·pⱼ`
(again only for `i ≠ j`).  Its recorded follow-up asks for the **variance**
`Var(Xᵢ) = n·pᵢ·(1-pᵢ)` and **the full covariance matrix**.

The diagonal — the variance — is genuinely absent: the parent's covariance theorem
explicitly requires `i ≠ j`.  This entry closes that gap and assembles the complete
second-order description.

## What This Proves

All expectations are the discrete sums `∑_{k : ∑k = n} (value) · multinomial(s,k)·∏pⱼ^kⱼ`
over `s.piAntidiag n`, matching the parent's convention.

* `multinomial_second_factorial_moment` — the **diagonal second factorial moment**
    `E[Xᵢ(Xᵢ-1)] = n(n-1)·pᵢ²`,
  the single-coordinate analogue of the parent's cross moment, obtained by the same
  absorption bijection applied to coordinate `i` (the surviving factor `(kᵢ-1)`
  becomes the lowered count `k'ᵢ`, reducing the sum to `n·pᵢ` times the `(n-1)`-mean
  of `Xᵢ`).
* `multinomial_second_moment` — `E[Xᵢ²] = n(n-1)·pᵢ² + n·pᵢ`.
* `multinomial_variance` — the **variance** `Var(Xᵢ) = E[(Xᵢ - n·pᵢ)²] = n·pᵢ·(1-pᵢ)`,
  the missing diagonal of the covariance matrix.
* `multinomial_covariance_matrix` — the **unified covariance-matrix entry**, valid for
  *all* `i, j` (diagonal and off-diagonal at once):
    `Cov(Xᵢ,Xⱼ) = E[(Xᵢ-n·pᵢ)(Xⱼ-n·pⱼ)] = n·pᵢ·(δᵢⱼ - pⱼ)`,
  where `δᵢⱼ = if i = j then 1 else 0`.  Specialising `i = j` gives the variance
  `n·pᵢ(1-pᵢ)`; specialising `i ≠ j` recovers the parent's `-n·pᵢ·pⱼ`.  This is the
  `n·(diag(p) - p·pᵀ)` covariance matrix in coordinate form.

## How it connects to the parent

The off-diagonal case of `multinomial_covariance_matrix` is routed through the parent's
public `multinomial_covariance`: the centred summand `(kᵢ-npᵢ)(kⱼ-npⱼ)·w` and the
parent's `(kᵢkⱼ - n²pᵢpⱼ)·w` differ by a combination of `kᵢ·w` and `kⱼ·w` whose total
mass vanishes (each summing to `n·pᵢ` resp. `n·pⱼ` by `multinomial_mean`), so the two
sums coincide.  Only the diagonal genuinely needs the new absorption computation.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/

namespace BinomialTheoremOQ02OQ01OQ01OQ04

open Finset BigOperators
open scoped Nat
open BinomialTheoremOQ02OQ01OQ01 (multinomial_mean multinomial_covariance)

/-! ## Part 1: the absorption engine (re-derived; the parent's copies are private) -/

/-- **Absorption identity** (`ℕ` level).  For a composition `k` of `n` with `kᵢ ≥ 1`,
lowering the `i`-th count by one absorbs the factor `kᵢ` into `n`:
`kᵢ · multinomial(s,k) = n · multinomial(s, update k i (kᵢ-1))`. -/
private theorem absorb {α : Type*} [DecidableEq α] (s : Finset α)
    (k : α → ℕ) (n : ℕ) (i : α) (hi : i ∈ s) (hsum : ∑ j ∈ s, k j = n) (hki : k i ≠ 0) :
    k i * Nat.multinomial s k =
    n * Nat.multinomial s (Function.update k i (k i - 1)) := by
  have hn : n ≠ 0 := by
    have hle : k i ≤ ∑ j ∈ s, k j := Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    omega
  set P := ∏ j ∈ s.erase i, (k j)! with hP
  have hk_prod : (∏ j ∈ s, (k j)!) = (k i)! * P :=
    (Finset.mul_prod_erase s (fun j => (k j)!) hi).symm
  have hk'_prod : (∏ j ∈ s, ((Function.update k i (k i - 1)) j)!) = (k i - 1)! * P := by
    rw [← Finset.mul_prod_erase s (fun j => ((Function.update k i (k i - 1)) j)!) hi,
        Function.update_self]
    congr 1
    exact Finset.prod_congr rfl
      (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  have hsum' : (∑ j ∈ s, (Function.update k i (k i - 1)) j) = n - 1 := by
    rw [← Finset.add_sum_erase s (Function.update k i (k i - 1)) hi, Function.update_self]
    have hcong : (∑ j ∈ s.erase i, (Function.update k i (k i - 1)) j) = ∑ j ∈ s.erase i, k j :=
      Finset.sum_congr rfl
        (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    rw [hcong]
    have he : k i + ∑ j ∈ s.erase i, k j = n := by
      rw [Finset.add_sum_erase s k hi]; exact hsum
    omega
  have spec_k : (∏ j ∈ s, (k j)!) * Nat.multinomial s k = n ! := by
    rw [Nat.multinomial_spec s k, hsum]
  have spec_k' : (∏ j ∈ s, ((Function.update k i (k i - 1)) j)!) *
      Nat.multinomial s (Function.update k i (k i - 1)) = (n - 1)! := by
    rw [Nat.multinomial_spec s (Function.update k i (k i - 1)), hsum']
  have hpos : 0 < (k i - 1)! * P := by
    refine Nat.mul_pos (Nat.factorial_pos _) ?_
    rw [hP]; exact Finset.prod_pos (fun j _ => Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (k i - 1)! * P * (k i * Nat.multinomial s k)
      = (k i * (k i - 1)!) * P * Nat.multinomial s k := by ring
    _ = (k i)! * P * Nat.multinomial s k := by rw [Nat.mul_factorial_pred hki]
    _ = (∏ j ∈ s, (k j)!) * Nat.multinomial s k := by rw [hk_prod]
    _ = n ! := spec_k
    _ = n * (n - 1)! := (Nat.mul_factorial_pred hn).symm
    _ = n * ((∏ j ∈ s, ((Function.update k i (k i - 1)) j)!) *
            Nat.multinomial s (Function.update k i (k i - 1))) := by rw [spec_k']
    _ = n * ((k i - 1)! * P * Nat.multinomial s (Function.update k i (k i - 1))) := by
          rw [hk'_prod]
    _ = (k i - 1)! * P * (n * Nat.multinomial s (Function.update k i (k i - 1))) := by ring

/-- **Weighted absorption** (`ℝ` level): lowering the `i`-th count by one converts the
weighted summand `kᵢ·multinomial(s,k)·∏pⱼ^kⱼ` into `n·pᵢ·multinomial(s,k')·∏pⱼ^k'ⱼ`. -/
private theorem absorb_weighted {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (k : α → ℕ) (n : ℕ) (i : α)
    (hi : i ∈ s) (hsum : ∑ l ∈ s, k l = n) (hki : k i ≠ 0) :
    (k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
    = (n : ℝ) * p i * ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
        * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by
  have habs : (k i : ℝ) * (Nat.multinomial s k : ℝ)
      = (n : ℝ) * (Nat.multinomial s (Function.update k i (k i - 1)) : ℝ) := by
    exact_mod_cast absorb s k n i hi hsum hki
  have hprod : (∏ l ∈ s, p l ^ k l)
      = p i * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l := by
    have hL : (∏ l ∈ s, p l ^ k l) = p i ^ k i * ∏ l ∈ s.erase i, p l ^ k l :=
      (Finset.mul_prod_erase s (fun l => p l ^ k l) hi).symm
    have hR : (∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l)
        = p i ^ (k i - 1) * ∏ l ∈ s.erase i, p l ^ k l := by
      rw [← Finset.mul_prod_erase s (fun l => p l ^ (Function.update k i (k i - 1)) l) hi]
      congr 1
      · rw [Function.update_self]
      · exact Finset.prod_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
    rw [hL, hR, ← mul_assoc]
    congr 1
    rw [← pow_succ']
    congr 1
    omega
  calc (k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
      = ((k i : ℝ) * (Nat.multinomial s k : ℝ)) * (∏ l ∈ s, p l ^ k l) := by ring
    _ = ((n : ℝ) * (Nat.multinomial s (Function.update k i (k i - 1)) : ℝ))
          * (p i * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by rw [habs, hprod]
    _ = (n : ℝ) * p i * ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
          * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by ring

/-! ## Part 2: the diagonal second factorial moment -/

/-- **The diagonal second factorial moment** `E[Xᵢ(Xᵢ-1)] = n·(n-1)·pᵢ²`.

Proof: drop the `kᵢ = 0` terms and lower `Xᵢ` by the absorption bijection
`k ↦ update k i (kᵢ-1)`.  The remaining factor `(kᵢ-1)` equals the lowered count
`k'ᵢ`, so the sum becomes `n·pᵢ` times the *mean of `Xᵢ` in an `(n-1)`-trial
multinomial*, which is `(n-1)·pᵢ` by `multinomial_mean`. -/
theorem multinomial_second_factorial_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i : α) (hi : i ∈ s) :
    ∑ k ∈ s.piAntidiag n,
      (k i : ℝ) * ((k i : ℝ) - 1) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
    = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * p i * p i := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  rw [← Finset.sum_filter_of_ne (p := fun k => k i ≠ 0)
        (fun k _ hfk hzero => hfk (by rw [hzero]; simp))]
  rw [Finset.sum_nbij'
        (i := fun k => Function.update k i (k i - 1))
        (j := fun k' => Function.update k' i (k' i + 1))
        (t := s.piAntidiag (n - 1))
        (g := fun k' => (n : ℝ) * p i * (k' i : ℝ) *
          ((Nat.multinomial s k' : ℝ) * ∏ l ∈ s, p l ^ k' l))]
  · -- ∑ g = n·pᵢ · (mean of Xᵢ over n-1 trials) = n·pᵢ·(n-1)·pᵢ
    have hfac : ∑ k' ∈ s.piAntidiag (n - 1),
          (n : ℝ) * p i * (k' i : ℝ) * ((Nat.multinomial s k' : ℝ) * ∏ l ∈ s, p l ^ k' l)
        = (n : ℝ) * p i * ∑ k' ∈ s.piAntidiag (n - 1),
            (k' i : ℝ) * ((Nat.multinomial s k' : ℝ) * ∏ l ∈ s, p l ^ k' l) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k' _ => by ring)
    rw [hfac, multinomial_mean s p (n - 1) hp_sum hp_nonneg i hi]; ring
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, hksupp⟩, hki⟩ := hk
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, ?_⟩
    · have hcong : (∑ l ∈ s.erase i, (Function.update k i (k i - 1)) l) = ∑ l ∈ s.erase i, k l :=
        Finset.sum_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
      rw [← Finset.add_sum_erase s (Function.update k i (k i - 1)) hi, Function.update_self, hcong]
      have he : k i + ∑ l ∈ s.erase i, k l = n := by
        rw [Finset.add_sum_erase s k hi]; exact hksum
      omega
    · intro l hl
      by_cases hli : l = i
      · subst hli; exact hi
      · rw [Function.update_of_ne hli] at hl; exact hksupp l hl
  · intro k' hk'
    rw [Finset.mem_piAntidiag] at hk'
    obtain ⟨hk'sum, hk'supp⟩ := hk'
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hcong : (∑ l ∈ s.erase i, (Function.update k' i (k' i + 1)) l) = ∑ l ∈ s.erase i, k' l :=
        Finset.sum_congr rfl
          (fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)])
      rw [← Finset.add_sum_erase s (Function.update k' i (k' i + 1)) hi, Function.update_self, hcong]
      have he : k' i + ∑ l ∈ s.erase i, k' l = n - 1 := by
        rw [Finset.add_sum_erase s k' hi]; exact hk'sum
      omega
    · intro l hl
      by_cases hli : l = i
      · subst hli; exact hi
      · rw [Function.update_of_ne hli] at hl; exact hk'supp l hl
    · rw [Function.update_self]; exact Nat.succ_ne_zero _
  · intro k hk
    have hki : k i ≠ 0 := (Finset.mem_filter.mp hk).2
    funext l
    by_cases hli : l = i
    · subst hli; rw [Function.update_self, Function.update_self]; omega
    · rw [Function.update_of_ne hli, Function.update_of_ne hli]
  · intro k' hk'
    funext l
    by_cases hli : l = i
    · subst hli; rw [Function.update_self, Function.update_self]; omega
    · rw [Function.update_of_ne hli, Function.update_of_ne hli]
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, _⟩, hki⟩ := hk
    have hweighted := absorb_weighted s p k n i hi hksum hki
    have hki1 : 1 ≤ k i := Nat.one_le_iff_ne_zero.mpr hki
    have hrider : ((Function.update k i (k i - 1)) i : ℝ) = (k i : ℝ) - 1 := by
      rw [Function.update_self, Nat.cast_sub hki1, Nat.cast_one]
    calc (k i : ℝ) * ((k i : ℝ) - 1) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
        = ((k i : ℝ) - 1) * ((k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)) := by
          ring
      _ = ((k i : ℝ) - 1) * ((n : ℝ) * p i *
            ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
              * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l)) := by rw [hweighted]
      _ = (n : ℝ) * p i * ((Function.update k i (k i - 1)) i : ℝ) *
            ((Nat.multinomial s (Function.update k i (k i - 1)) : ℝ)
              * ∏ l ∈ s, p l ^ (Function.update k i (k i - 1)) l) := by rw [← hrider]; ring

/-! ## Part 3: second moment, variance, and the covariance matrix -/

/-- The **second moment** `E[Xᵢ²] = n·(n-1)·pᵢ² + n·pᵢ`, from `Xᵢ² = Xᵢ(Xᵢ-1) + Xᵢ`. -/
theorem multinomial_second_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i : α) (hi : i ∈ s) :
    ∑ k ∈ s.piAntidiag n,
      (k i : ℝ) ^ 2 * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
    = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * p i * p i + (n : ℝ) * p i := by
  have hfact := multinomial_second_factorial_moment s p n hp_sum hp_nonneg i hi
  have hmean := multinomial_mean s p n hp_sum hp_nonneg i hi
  have hsplit : ∀ k : α → ℕ,
      (k i : ℝ) ^ 2 * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
      = (k i : ℝ) * ((k i : ℝ) - 1) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
        + (k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, hfact, hmean]

/-- **The variance** `Var(Xᵢ) = E[(Xᵢ - n·pᵢ)²] = n·pᵢ·(1 - pᵢ)` — the missing
diagonal of the multinomial covariance matrix. -/
theorem multinomial_variance {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i : α) (hi : i ∈ s) :
    ∑ k ∈ s.piAntidiag n,
      ((k i : ℝ) - n * p i) ^ 2 * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
    = (n : ℝ) * p i * (1 - p i) := by
  have hmass : ∑ k ∈ s.piAntidiag n,
      (Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l = 1 := by
    rw [← Finset.sum_pow_eq_sum_piAntidiag s p n, hp_sum, one_pow]
  have hfact := multinomial_second_factorial_moment s p n hp_sum hp_nonneg i hi
  have hmean := multinomial_mean s p n hp_sum hp_nonneg i hi
  -- (kᵢ - npᵢ)² = kᵢ(kᵢ-1) + (1 - 2npᵢ)·kᵢ + (npᵢ)²
  have hsplit : ∀ k : α → ℕ,
      ((k i : ℝ) - n * p i) ^ 2 * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
      = (k i : ℝ) * ((k i : ℝ) - 1) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
        + (1 - 2 * (n * p i)) * ((k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l))
        + (n * p i) ^ 2 * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, Finset.sum_add_distrib,
      hfact, ← Finset.mul_sum, hmean, ← Finset.mul_sum, hmass, mul_one]
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  push_cast
  ring

/-- **The multinomial covariance matrix**, valid for *all* `i, j`:
`Cov(Xᵢ,Xⱼ) = E[(Xᵢ - n·pᵢ)(Xⱼ - n·pⱼ)] = n·pᵢ·(δᵢⱼ - pⱼ)`, where
`δᵢⱼ = if i = j then 1 else 0`.

The diagonal `i = j` is the variance `n·pᵢ(1-pᵢ)` (`multinomial_variance`); the
off-diagonal `i ≠ j` is the parent's `-n·pᵢ·pⱼ` (`multinomial_covariance`).  Together
this is `n·(diag(p) - p·pᵀ)`, the complete second-order law of the multinomial. -/
theorem multinomial_covariance_matrix {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i j : α) (hi : i ∈ s) (hj : j ∈ s) :
    ∑ k ∈ s.piAntidiag n,
      ((k i : ℝ) - n * p i) * ((k j : ℝ) - n * p j) *
        ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
    = (n : ℝ) * p i * ((if i = j then 1 else 0) - p j) := by
  by_cases hij : i = j
  · -- diagonal: the variance
    subst hij
    rw [if_pos rfl]
    have hvar := multinomial_variance s p n hp_sum hp_nonneg i hi
    rw [← hvar]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · -- off-diagonal: route through the parent's covariance
    rw [if_neg hij]
    have hmass : ∑ k ∈ s.piAntidiag n,
        (Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l = 1 := by
      rw [← Finset.sum_pow_eq_sum_piAntidiag s p n, hp_sum, one_pow]
    have hcov := multinomial_covariance s p n hp_sum hp_nonneg i j hi hj hij
    have hmeani := multinomial_mean s p n hp_sum hp_nonneg i hi
    have hmeanj := multinomial_mean s p n hp_sum hp_nonneg j hj
    -- centred summand = covariance summand + a vanishing linear combination
    have hsplit : ∀ k : α → ℕ,
        ((k i : ℝ) - n * p i) * ((k j : ℝ) - n * p j) *
            ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
        = ((k i : ℝ) * (k j : ℝ) - n * p i * (n * p j)) *
            ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l)
          + (-(n * p j)) * ((k i : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l))
          + (-(n * p i)) * ((k j : ℝ) * ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l))
          + (2 * (n * p i) * (n * p j)) *
              ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l) := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, hcov, ← Finset.mul_sum, hmeani, ← Finset.mul_sum, hmeanj,
        ← Finset.mul_sum, hmass, mul_one]
    ring

end BinomialTheoremOQ02OQ01OQ01OQ04
