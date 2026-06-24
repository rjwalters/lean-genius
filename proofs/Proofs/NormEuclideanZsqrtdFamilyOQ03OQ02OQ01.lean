/-
  # Irreducibles of `ℤ[√d]` have prime or prime-squared norm (`-2 ≤ d < 0`)

  Open question (`bezout-identity-…-oq-03-oq-03-oq-02`, the PID/UFD + prime-norm
  entry):

    > Classify the irreducibles of `ℤ[√d]` by their norm.

  The parent file `NormEuclideanZsqrtdFamilyOQ03OQ02` proved the *sufficient*
  half of a norm criterion: an element whose norm has prime absolute value is
  irreducible (`irreducible_of_prime_norm`), and prime in the UFD range
  (`prime_of_prime_norm`).  This file proves the matching *necessary* half — the
  structural constraint a norm must satisfy for its element to be irreducible.

  ## What we prove

  * `irreducible_norm_eq_prime_or_sq` — for `-2 ≤ d < 0`, if `z` is irreducible
    in `ℤ[√d]` then `|N(z)|` is **either a rational prime `p` or its square
    `p²`**.  This is the classical dichotomy (split/ramified primes give norm
    `p`; inert rational primes give norm `p²`) and, together with the parent's
    sufficiency direction, pins the norm of every irreducible down to two
    possibilities.

  The mathematical engine is a divisibility argument: an irreducible (hence
  prime, in the UFD) `z` divides `N(z) = z · z̄`, so it divides the image of some
  rational prime `p`; taking norms of `↑p = z · w` gives `p² = |N(z)| · |N(w)|`,
  whence `|N(z)| ∣ p²` and — being `≠ 1` — equals `p` or `p²`.

  ## Supporting lemma

  * `exists_prime_dvd_natCast` — a prime element of `ℤ[√d]` dividing the image of
    a nonzero natural number divides the image of some rational prime.  Proved by
    strong induction on the natural number, peeling off prime factors.

  Status: PROVED — 0 sorries, 0 axioms, no `native_decide`.
  Tags: number-theory, quadratic-integers, euclidean-domain, ufd, irreducible, norm
-/
import Proofs.NormEuclideanZsqrtdFamilyOQ03OQ02

open Zsqrtd

namespace NormEuclideanZsqrtdFamilyIrredNorm

variable {d : ℤ}

/-! ### A prime element divides the image of a rational prime -/

/-- **A prime element of `ℤ[√d]` dividing `↑n` divides `↑p` for some rational prime
`p`.** If `z` is prime and divides the image of a nonzero natural number `n`, then
`z` divides the image of some prime `p` (necessarily a prime factor of `n`).

Proof by strong induction on `n`: factor off a rational prime `p ∣ n`, write
`n = p · k`, and split `z ∣ ↑p · ↑k`. Either `z ∣ ↑p` (done) or `z ∣ ↑k` and we
recurse on the smaller `k`. The base obstruction `n = 1` is impossible, since
`z ∣ 1` would make `z` a unit. -/
theorem exists_prime_dvd_natCast {z : ℤ√d} (hz : Prime z) :
    ∀ n : ℕ, n ≠ 0 → z ∣ ((n : ℤ) : ℤ√d) → ∃ p : ℕ, p.Prime ∧ z ∣ ((p : ℤ) : ℤ√d) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn0 hdvd
    rcases eq_or_ne n 1 with rfl | h1
    · -- `z ∣ 1` forces `z` to be a unit, contradicting primality.
      simp only [Nat.cast_one, Int.cast_one] at hdvd
      exact absurd (isUnit_of_dvd_one hdvd) hz.not_unit
    · -- Peel off a rational prime factor `p` of `n`, writing `n = p * k`.
      obtain ⟨p, pp, hpn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨k, rfl⟩ := hpn
      have hcast : ((↑(p * k) : ℤ) : ℤ√d) = ((p : ℤ) : ℤ√d) * ((k : ℤ) : ℤ√d) := by
        push_cast; ring
      rw [hcast] at hdvd
      rcases hz.dvd_or_dvd hdvd with hzp | hzk
      · exact ⟨p, pp, hzp⟩
      · -- `z ∣ ↑k`; recurse on the strictly smaller `k`.
        have hk0 : k ≠ 0 := by rintro rfl; simp at hn0
        have hlt : k < p * k := by
          have h2 := pp.two_le
          have hkpos := Nat.pos_of_ne_zero hk0
          nlinarith
        exact IH k hlt hk0 hzk

/-! ### The norm of an irreducible is a prime or a prime square -/

/-- **Irreducibles of `ℤ[√d]` have prime or prime-squared norm** (`-2 ≤ d < 0`).
If `z` is irreducible in `ℤ[√d]`, then the absolute value of its norm is either a
rational prime `p` or `p²`.

This is the necessary direction matching the parent's sufficient
`irreducible_of_prime_norm`: prime-norm elements are irreducible, and every
irreducible has norm `p` (the split/ramified case) or `p²` (the inert rational
prime case). The proof uses that, in the UFD, `z` is prime and divides
`N(z) = z · star z`, hence divides some rational prime `↑p`; comparing norms of
`↑p = z · w` gives `p² = |N(z)| · |N(w)|`, so `|N(z)| ∣ p²`, and being `≠ 1` it is
`p` or `p²`. -/
theorem irreducible_norm_eq_prime_or_sq (hd : d < 0) (hd2 : -2 ≤ d) {z : ℤ√d}
    (hz : Irreducible z) :
    ∃ p : ℕ, p.Prime ∧ (z.norm.natAbs = p ∨ z.norm.natAbs = p ^ 2) := by
  letI := NormEuclideanZsqrtdFamily.euclideanDomain d hd hd2
  -- In the UFD, irreducible ⟹ prime; and `z ≠ 0`, `N(z) ≠ 0`.
  have hzp : Prime z := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hz
  have hznz : z ≠ 0 := hzp.ne_zero
  have hnorm_ne : z.norm ≠ 0 := fun h => hznz ((Zsqrtd.norm_eq_zero_iff hd z).mp h)
  have hm0 : z.norm.natAbs ≠ 0 := fun h => hnorm_ne (Int.natAbs_eq_zero.mp h)
  -- `↑|N(z)| = N(z)` since the norm is nonnegative, and `z ∣ ↑N(z) = z · star z`.
  have hmnorm : ((z.norm.natAbs : ℤ)) = z.norm :=
    Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg hd.le z)
  have hdvd_m : z ∣ ((z.norm.natAbs : ℤ) : ℤ√d) := by
    have hc := Zsqrtd.norm_eq_mul_conj z
    rw [← hmnorm] at hc
    exact ⟨star z, hc⟩
  -- `z` divides the image of some rational prime `p`.
  obtain ⟨p, pp, hzp_dvd⟩ := exists_prime_dvd_natCast hzp _ hm0 hdvd_m
  obtain ⟨w, hw⟩ := hzp_dvd
  -- Comparing norms of `↑p = z · w`: `p² = N(z) · N(w)`.
  have hnp : ((p : ℤ) * (p : ℤ)) = z.norm * w.norm := by
    have h := congrArg Zsqrtd.norm hw
    rwa [Zsqrtd.norm_intCast, Zsqrtd.norm_mul] at h
  have hpp : p * p = z.norm.natAbs * w.norm.natAbs := by
    have h := congrArg Int.natAbs hnp
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using h
  -- Hence `|N(z)| ∣ p²` and `|N(z)| ≠ 1`, so `|N(z)| = p` or `p²`.
  have hmdvd : z.norm.natAbs ∣ p ^ 2 := ⟨w.norm.natAbs, by rw [pow_two]; exact hpp⟩
  have hm1 : z.norm.natAbs ≠ 1 := fun h => hzp.not_unit (Zsqrtd.norm_eq_one_iff.mp h)
  obtain ⟨k, hk2, hmk⟩ := (Nat.dvd_prime_pow pp).mp hmdvd
  interval_cases k
  · exact absurd (by simpa using hmk) hm1
  · exact ⟨p, pp, Or.inl (by simpa using hmk)⟩
  · exact ⟨p, pp, Or.inr (by simpa using hmk)⟩

end NormEuclideanZsqrtdFamilyIrredNorm
