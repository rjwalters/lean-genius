/-
  Strict, lower-bounded sharpening of the abundancy-index monotonicity along
  divisibility.

  The parent entry `abundant-number-oq-04`
  (`Proofs.AbundantDeficientDvdOQ04`) proves the *non-strict* monotonicity

  * `sigma_dvd_mono` — if `d ∣ n` and `n > 0` then `n · σ(d) ≤ d · σ(n)`,
    i.e. `σ(d)/d ≤ σ(n)/n`,

  via the scaled-divisor injection `e ↦ (n/d)·e`, which embeds `divisors d`
  into `divisors n`. This file sharpens that bound to a *strict* one at a
  *proper* divisor, and pins down a concrete minimum size for the jump.

  * `scaled_sigma_lt` — the strict scaled-divisor bound. For `0 < d` and
    `2 ≤ t`, the image `{t·e : e ∣ d}` is a subset of `divisors (d*t)` that
    omits the divisor `1` (since `t·e ≥ t ≥ 2 > 1`), so summing over the larger
    set gains at least that one extra term:
    `t · σ(d) + 1 ≤ σ(d*t)`.

  * `sigma_dvd_strict_mono` — the strict, lower-bounded monotonicity. If
    `d ∣ n` and `d < n` then
    `n · σ(d) + d ≤ d · σ(n)`,
    i.e. `d · σ(n) − n · σ(d) ≥ d > 0`. In abundancy-index form this quantifies
    the gap as `σ(n)/n − σ(d)/d ≥ 1/n > 0`.

  * `abundancy_gap_ge` — the rational corollary over `ℚ`:
    `σ(d)/d + 1/n ≤ σ(n)/n` for `d ∣ n`, `d < n`.

  As a sanity check we re-derive the parent's
  `deficient_of_proper_dvd_perfect` directly from the strict bound (no detour
  through the abundant-side closure lemmas): a proper divisor `d` of a perfect
  number `n` satisfies `σ(d) < 2d` because the strict gap forces
  `n · σ(d) < n · (2d)`.

  The intuition behind the strict gain is elementary: the divisors of `n = d·t`
  include all of the scaled divisors `{t·e : e ∣ d}` (already accounting for
  `t·σ(d)`), but they *also* include `1`, which is never of the form `t·e` when
  `t ≥ 2`. That one extra, otherwise-uncounted divisor forces the `+1`.

  The proof is axiom-free (no `sorry`, no `axiom`, no `native_decide`).
-/
import Mathlib
import Proofs.AbundantDeficientDvdOQ04

namespace AbundantStrictAbundancyOQ0401

open Finset
open AbundantDeficientDvdOQ04

/-- **Strict scaled-divisor bound.** For `0 < d` and `2 ≤ t`, the map `e ↦ t·e`
injects `divisors d` into `divisors (d*t)`, and the divisor `1` of `d*t` lies
outside the image (since every `t·e ≥ t ≥ 2`). Hence the sum over `divisors (d*t)`
strictly exceeds `t·σ(d)`, by at least the missing term `1`:
`t · σ(d) + 1 ≤ σ(d*t)`. This is the strict refinement of the parent's
`scaled_sigma_le`. -/
theorem scaled_sigma_lt (d t : ℕ) (hd : 0 < d) (ht : 2 ≤ t) :
    t * (∑ e ∈ d.divisors, e) + 1 ≤ ∑ e ∈ (d * t).divisors, e := by
  have htpos : 0 < t := by omega
  have hm : 0 < d * t := Nat.mul_pos hd htpos
  -- scaled divisors of `d` sit inside the divisors of `d * t`
  have hsub : d.divisors.image (fun e => t * e) ⊆ (d * t).divisors := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [Nat.mem_divisors] at he ⊢
    refine ⟨?_, hm.ne'⟩
    rw [mul_comm d t]
    exact mul_dvd_mul_left t he.1
  -- scaling is injective on `divisors d` since `t > 0`
  have hinj : Set.InjOn (fun e => t * e) (d.divisors : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left htpos h
  have himg : ∑ x ∈ d.divisors.image (fun e => t * e), x = t * (∑ e ∈ d.divisors, e) := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
  -- `1` is a divisor of `d*t` but is not a scaled divisor (every `t·e ≥ 2`)
  have h1mem : (1 : ℕ) ∈ (d * t).divisors := Nat.one_mem_divisors.mpr hm.ne'
  have h1notmem : (1 : ℕ) ∉ d.divisors.image (fun e => t * e) := by
    rw [Finset.mem_image]
    rintro ⟨e, he, heq⟩
    have hepos : 0 < e := Nat.pos_of_mem_divisors he
    have hge : 2 * 1 ≤ t * e := Nat.mul_le_mul ht hepos
    omega
  -- strict subset-sum: the larger set has the extra positive term `1`
  have hstrict :
      (∑ x ∈ d.divisors.image (fun e => t * e), x) < ∑ e ∈ (d * t).divisors, e :=
    Finset.sum_lt_sum_of_subset hsub h1mem h1notmem (by norm_num) (fun j _ _ => Nat.zero_le j)
  rw [himg] at hstrict
  omega

/-- **Strict, lower-bounded monotonicity of the abundancy index.** If `d ∣ n` and
`d < n` then
`n · σ(d) + d ≤ d · σ(n)`,
equivalently `d · σ(n) − n · σ(d) ≥ d > 0`, i.e. the abundancy index strictly
increases by at least `1/n` when passing to a proper multiple:
`σ(n)/n − σ(d)/d ≥ 1/n`. This sharpens the parent's non-strict `sigma_dvd_mono`.
The extra `+d` comes from the divisor `1` of `n`, which is never a scaled divisor
`(n/d)·e` of `d`. -/
theorem sigma_dvd_strict_mono {d n : ℕ} (hdvd : d ∣ n) (hlt : d < n) :
    n * (∑ e ∈ d.divisors, e) + d ≤ d * (∑ e ∈ n.divisors, e) := by
  obtain ⟨t, rfl⟩ := hdvd
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hlt
    · exact h
  -- `d < d*t` forces `t ≥ 2`
  have ht2 : 2 ≤ t := by
    have h1 : d * 1 < d * t := by simpa [Nat.mul_one] using hlt
    have := Nat.lt_of_mul_lt_mul_left h1
    omega
  have key : t * (∑ e ∈ d.divisors, e) + 1 ≤ ∑ e ∈ (d * t).divisors, e :=
    scaled_sigma_lt d t hd ht2
  calc (d * t) * (∑ e ∈ d.divisors, e) + d
      = d * (t * (∑ e ∈ d.divisors, e) + 1) := by ring
    _ ≤ d * (∑ e ∈ (d * t).divisors, e) := Nat.mul_le_mul_left d key

/-- **Abundancy gap over `ℚ`.** The cross-multiplied integer bound rephrased as a
genuine rational inequality: for `d ∣ n` with `d < n`,
`σ(d)/d + 1/n ≤ σ(n)/n`.
Thus the abundancy index `σ(·)/(·)` gains at least `1/n` on passing from `d` to
its proper multiple `n`. -/
theorem abundancy_gap_ge {d n : ℕ} (hdvd : d ∣ n) (hlt : d < n) :
    ((∑ e ∈ d.divisors, (e : ℚ)) / d) + 1 / n ≤ (∑ e ∈ n.divisors, (e : ℚ)) / n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le d) hlt
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hdne : (d : ℚ) ≠ 0 := ne_of_gt hdq
  have hnne : (n : ℚ) ≠ 0 := ne_of_gt hnq
  have hkey : n * (∑ e ∈ d.divisors, e) + d ≤ d * (∑ e ∈ n.divisors, e) :=
    sigma_dvd_strict_mono hdvd hlt
  -- cast the integer bound to ℚ (with the sums pushed inside the cast)
  have hkeyq : (n : ℚ) * (∑ e ∈ d.divisors, (e : ℚ)) + d ≤ d * (∑ e ∈ n.divisors, (e : ℚ)) := by
    have h : ((n * (∑ e ∈ d.divisors, e) + d : ℕ) : ℚ)
        ≤ ((d * (∑ e ∈ n.divisors, e) : ℕ) : ℚ) := by exact_mod_cast hkey
    push_cast at h
    linarith [h]
  rw [← sub_nonneg]
  have hrw :
      (∑ e ∈ n.divisors, (e : ℚ)) / n - ((∑ e ∈ d.divisors, (e : ℚ)) / d + 1 / n)
        = (d * (∑ e ∈ n.divisors, (e : ℚ)) - (n * (∑ e ∈ d.divisors, (e : ℚ)) + d))
            / (d * n) := by
    field_simp
  rw [hrw]
  apply div_nonneg
  · linarith [hkeyq]
  · positivity

/-- **Sanity check: every proper divisor of a perfect number is deficient.**
Re-derived directly from the strict gap `sigma_dvd_strict_mono` (rather than the
parent's detour through the abundant-side closure lemmas). If `n` is perfect with
`σ(n) = 2n`, a proper divisor `d` satisfies `n·σ(d) + d ≤ d·σ(n) = d·(2n)`, so
`n·σ(d) < n·(2d)`, whence `σ(d) < 2d`: `d` is deficient. -/
theorem deficient_of_proper_dvd_perfect' {d n : ℕ}
    (hp : n.Perfect) (hdvd : d ∣ n) (hlt : d < n) : d.Deficient := by
  have hnpos : 0 < n := hp.2
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
  -- `σ(n) = 2n` from perfection (Mathlib's `Nat.Perfect` is stated on properDivisors)
  have hσn : ∑ e ∈ n.divisors, e = 2 * n := by
    have h := hp.1
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega
  have hkey : n * (∑ e ∈ d.divisors, e) + d ≤ d * (∑ e ∈ n.divisors, e) :=
    sigma_dvd_strict_mono hdvd hlt
  rw [hσn] at hkey
  -- `n·σ(d) + d ≤ d·(2n) = n·(2d)`, so `n·σ(d) < n·(2d)`, giving `σ(d) < 2d`
  have hchain : n * (∑ e ∈ d.divisors, e) < n * (2 * d) := by nlinarith [hkey, hdpos, hnpos]
  have hσd : ∑ e ∈ d.divisors, e < 2 * d := Nat.lt_of_mul_lt_mul_left hchain
  exact (deficient_iff_sigma_lt_two_mul).mpr hσd

end AbundantStrictAbundancyOQ0401
