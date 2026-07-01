/-
# The Legendre Core Recursion, proved from scratch

The parent entry `hermite-legendre-factorial` rewrites *each* Legendre summand
through Hermite's floor identity, but it still **cites** Mathlib's
`padicValNat_factorial` for the underlying formula
$$v_p(n!) = \sum_{i \ge 1} \left\lfloor \frac{n}{p^{\,i}} \right\rfloor .$$

This file removes that dependency.  We give a self-contained proof of the
**Legendre core recursion**
$$v_p(n!) \;=\; \left\lfloor \tfrac np \right\rfloor \;+\; v_p\!\left(\left\lfloor \tfrac np\right\rfloor!\right)$$
(equivalently `v_p((p·m)!) = m + v_p(m!)`), and then *derive* the full Legendre
formula from it by induction — never touching `padicValNat_factorial`.

## The argument

Write `q = ⌊n/p⌋`.  Factorisation is additive over products, so

$$v_p(n!) \;=\; \sum_{k=1}^{n} v_p(k).$$

A term `v_p(k)` vanishes unless `p ∣ k`.  The multiples of `p` in `[1,n]` are
exactly `p·1, p·2, …, p·q`, and `v_p(p·j) = 1 + v_p(j)` for `j ≥ 1`.  Hence

$$\sum_{k=1}^{n} v_p(k) \;=\; \sum_{j=1}^{q}\bigl(1 + v_p(j)\bigr)
   \;=\; q + \sum_{j=1}^{q} v_p(j) \;=\; q + v_p(q!),$$

which is the recursion.  Unfolding it `⌊\log_p n⌋` times gives Legendre's sum.

No axioms beyond Lean/Mathlib's foundations; `0` sorries.  We work with
`Nat.factorization p` throughout (which agrees with `padicValNat p` on primes,
`Nat.factorization_def`) because it carries the additive `factorization_mul` /
`factorization_prod` API.
-/
import Mathlib

open Finset

namespace HermiteLegendreFactorialOQ02

/-! ### The factorial as a sum of prime-power valuations -/

/-- `v_p(n!) = ∑_{k=1}^{n} v_p(k)`: the `p`-adic valuation of a factorial is the
sum of the valuations of its factors.  This is just additivity of
`Nat.factorization` over the product `n! = ∏_{k=1}^n k`. -/
theorem factorization_factorial_eq_sum (n p : ℕ) :
    (Nat.factorial n).factorization p = ∑ k ∈ Icc 1 n, (k.factorization p) := by
  rw [← Nat.Ico_succ_right]
  have hS : ∀ x ∈ Ico 1 (n + 1), x ≠ 0 := by
    intro x hx
    exact Nat.one_le_iff_ne_zero.mp (Finset.mem_Ico.mp hx).1
  rw [← Finset.prod_Ico_id_eq_factorial, Nat.factorization_prod hS,
    Finsupp.finset_sum_apply]

/-! ### The core recursion -/

/-- The multiples of `p` in `Icc 1 n` are exactly the image of `Icc 1 (n / p)`
under `j ↦ p * j`. -/
theorem image_mul_eq_filter_dvd {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (Icc 1 (n / p)).image (fun j => p * j) = (Icc 1 n).filter (fun k => p ∣ k) := by
  ext k
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, Dvd.intro j rfl⟩
    · calc 1 ≤ p * 1 := by simpa using hp
        _ ≤ p * j := by exact Nat.mul_le_mul_left p hj1
    · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp).mp hj2
  · rintro ⟨⟨hk1, hk2⟩, ⟨j, rfl⟩⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with hj | hj
      · simp [hj] at hk1
      · exact hj
    · exact Nat.le_div_iff_mul_le hp |>.mpr (by rw [mul_comm]; exact hk2)

/-- **Legendre core recursion.**  For a prime `p`,
`v_p(n!) = ⌊n/p⌋ + v_p(⌊n/p⌋!)`.  Proved from additivity of `Nat.factorization`
and the multiples-of-`p` reindexing — *not* from `padicValNat_factorial`. -/
theorem factorization_factorial_rec (n p : ℕ) (hp : p.Prime) :
    (Nat.factorial n).factorization p = n / p + (Nat.factorial (n / p)).factorization p := by
  rw [factorization_factorial_eq_sum n p, factorization_factorial_eq_sum (n / p) p]
  -- Drop the non-multiples (their valuation is 0), then reindex by `j ↦ p*j`.
  have hdrop : ∑ k ∈ (Icc 1 n).filter (fun k => p ∣ k), k.factorization p
             = ∑ k ∈ Icc 1 n, k.factorization p := by
    apply Finset.sum_filter_of_ne
    intro x _ hne
    by_contra hpx
    exact hne (Nat.factorization_eq_zero_of_not_dvd hpx)
  rw [← hdrop, ← image_mul_eq_filter_dvd hp.pos n]
  rw [Finset.sum_image (by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h)]
  -- Each factor: `v_p(p*j) = 1 + v_p(j)`.
  have hterm : ∀ j ∈ Icc 1 (n / p), (p * j).factorization p = 1 + j.factorization p := by
    intro j hj
    have hj0 : j ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hj).1
    rw [Nat.factorization_mul hp.pos.ne' hj0]
    simp [hp.factorization_self]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  simp [Nat.card_Icc]

/-! ### The `(p · m)!` form and the `padicValNat` bridge -/

/-- The multiplicative form of the core recursion: `v_p((p·m)!) = m + v_p(m!)`. -/
theorem factorization_factorial_mul (m p : ℕ) (hp : p.Prime) :
    (Nat.factorial (p * m)).factorization p = m + (Nat.factorial m).factorization p := by
  have h := factorization_factorial_rec (p * m) p hp
  rwa [Nat.mul_div_cancel_left m hp.pos] at h

/-- `Nat.factorization p` agrees with `padicValNat p` on primes, so the recursion
transfers verbatim to the `padicValNat` used by the parent entry. -/
theorem padicValNat_factorial_rec (n p : ℕ) (hp : p.Prime) :
    padicValNat p (Nat.factorial n) = n / p + padicValNat p (Nat.factorial (n / p)) := by
  rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
    factorization_factorial_rec n p hp]

/-! ### Legendre's formula, derived from the recursion -/

/-- **Legendre's formula, without citing `padicValNat_factorial`.**  Unfolding the
core recursion `b` times (any `b` with `Nat.log p n < b`) yields Legendre's sum
`v_p(n!) = ∑_{i=0}^{b-1} ⌊n / p^{i+1}⌋ = ⌊n/p⌋ + ⌊n/p²⌋ + …`.  The induction is on
the unfolding depth `b`.  Each step peels the leading `⌊n/p⌋` off the recursion
and matches the tail against the induction hypothesis applied to `⌊n/p⌋`, using
`⌊n/p^{i+2}⌋ = ⌊⌊n/p⌋ / p^{i+1}⌋` (`Nat.div_div_eq_div_mul`). -/
theorem factorization_factorial_legendre (n p b : ℕ) (hp : p.Prime)
    (hb : Nat.log p n < b) :
    (Nat.factorial n).factorization p = ∑ i ∈ range b, n / p ^ (i + 1) := by
  induction b generalizing n with
  | zero => omega
  | succ b ih =>
    -- The tail identity: v_p((n/p)!) = ∑_{i<b} ⌊n/p / p^{i+1}⌋.
    have hsub : (Nat.factorial (n / p)).factorization p = ∑ i ∈ range b, n / p / p ^ (i + 1) := by
      rcases Nat.eq_zero_or_pos (n / p) with h0 | h0
      · simp [h0, Nat.factorial_zero, Nat.factorization_one]
      · refine ih (n / p) ?_
        have hle : Nat.log p n ≤ b := Nat.lt_succ_iff.mp hb
        have hpn : p ≤ n := (Nat.one_le_div_iff hp.pos).mp h0
        have hpos : 0 < Nat.log p n := Nat.log_pos hp.one_lt hpn
        rw [Nat.log_div_base]; omega
    -- ⌊n/p^{i+2}⌋ = ⌊⌊n/p⌋/p^{i+1}⌋.
    have hpow : ∀ i, n / p ^ (i + 2) = n / p / p ^ (i + 1) := fun i => by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [factorization_factorial_rec n p hp,
      Finset.sum_range_succ' (fun i => n / p ^ (i + 1)) b]
    simp only [Nat.zero_add, pow_one]
    rw [Finset.sum_congr rfl (fun i _ => by rw [show i + 1 + 1 = i + 2 from rfl, hpow i]),
      hsub, add_comm]

/-- Legendre's formula in `padicValNat` form (the shape the parent cites from
Mathlib), now proved independently of `padicValNat_factorial`. -/
theorem padicValNat_factorial_legendre (n p b : ℕ) (hp : p.Prime)
    (hb : Nat.log p n < b) :
    padicValNat p (Nat.factorial n) = ∑ i ∈ range b, n / p ^ (i + 1) := by
  rw [← Nat.factorization_def _ hp, factorization_factorial_legendre n p b hp hb]

end HermiteLegendreFactorialOQ02
