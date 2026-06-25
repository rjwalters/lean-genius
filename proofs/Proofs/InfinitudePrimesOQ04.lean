import Mathlib

/-
# Infinitude of Primes OQ-04: Arithmetic Progressions of Primes (Green–Tao)

## Research Problem: infinitude-primes-oq-04

The headline is the **Green–Tao theorem (2004)**: the primes contain *arbitrarily long*
arithmetic progressions. That is, for every length `k` there is a `k`-term arithmetic
progression `a, a+d, …, a+(k-1)d` consisting entirely of primes. Its proof (Szemerédi's
theorem transferred to a pseudorandom majorant of the primes) is one of the deepest
results in modern analytic number theory and is *far* beyond what Lean/Mathlib can
currently formalize. We therefore record only its **statement** (`GreenTao`).

What we *can* prove cleanly, and what this file delivers (all axiom-free), are the sharp
elementary boundaries surrounding that statement:

1. **No infinite AP of primes** (`not_forall_prime_of_AP`). Green–Tao gives arbitrarily
   long *finite* progressions, but no single arithmetic progression can be *entirely*
   prime: if `a, a+d, a+2d, …` were all prime with `d ≥ 1`, then the term at index `a`
   equals `a + a·d = a·(1+d)`, a product of two factors `≥ 2`, hence composite. This is
   Euclid-simple and marks the exact frontier of Green–Tao: "arbitrarily long" cannot be
   upgraded to "infinite".

2. **Explicit witnesses** illustrating the finite content of Green–Tao:
   `5, 11, 17, 23, 29` (length 5, difference 6) and `7, 37, 67, 97, 127, 157`
   (length 6, difference 30) are progressions of primes.

3. **A structural constraint** (`six_dvd_diff`): in any 3-term progression of primes all
   exceeding 3, the common difference is divisible by 6 — the reason longer prime
   progressions force large common differences (in fact `d` must be divisible by every
   prime `≤ k`).

## References
- B. Green, T. Tao, "The primes contain arbitrarily long arithmetic progressions",
  *Annals of Mathematics* 167 (2008), 481–547 (announced 2004).
- Mathlib: `Nat.Prime`, `Nat.Prime.eq_one_or_self_of_dvd`.
-/

open Nat

namespace InfinitudePrimesOQ04

/-! ## Part I: The Green–Tao statement (statement only) -/

/-- **The Green–Tao theorem (2004), statement only.**
For every length `k` there exist a start `a` and common difference `d ≥ 1` such that
`a, a+d, …, a+(k-1)·d` are all prime. Proved by Green and Tao; its proof is beyond
current formalization, so only the statement is recorded here. -/
def GreenTao : Prop :=
  ∀ k : ℕ, ∃ a d : ℕ, 1 ≤ d ∧ ∀ i, i < k → (a + i * d).Prime

/-! ## Part II: No arithmetic progression consists entirely of primes

The sharp counterpoint to Green–Tao: "arbitrarily long" is best possible — it cannot be
strengthened to "infinite". -/

/-- **No infinite arithmetic progression of primes.**
For any start `a` and common difference `d ≥ 1`, the progression `n ↦ a + n·d` cannot be
prime at every index: the term at index `a` is `a·(1+d)`, a nontrivial product. -/
theorem not_forall_prime_of_AP (a d : ℕ) (hd : 1 ≤ d) :
    ¬ ∀ n : ℕ, (a + n * d).Prime := by
  intro h
  -- the term at index 0 is `a`, so `a` is prime (in particular `a ≥ 2`)
  have ha : a.Prime := by simpa using h 0
  -- the term at index `a` factors as `a·(1+d)`
  have hval : a + a * d = a * (1 + d) := by ring
  have hp : (a * (1 + d)).Prime := by rw [← hval]; exact h a
  -- `a` divides this prime, forcing `a = 1` or `a = a·(1+d)`
  rcases hp.eq_one_or_self_of_dvd a (dvd_mul_right a (1 + d)) with h1 | h2
  · exact absurd h1 ha.ne_one
  · -- `a = a·(1+d)`, yet `a·(1+d) ≥ a·2 > a` since `a ≥ 2` and `d ≥ 1`
    have hge : a * 2 ≤ a * (1 + d) := by gcongr; omega
    rw [← h2] at hge
    have h2a : 2 ≤ a := ha.two_le
    omega

/-- Equivalent contrapositive form: every nonconstant arithmetic progression contains a
composite (non-prime) term. -/
theorem exists_not_prime_in_AP (a d : ℕ) (hd : 1 ≤ d) :
    ∃ n : ℕ, ¬ (a + n * d).Prime := by
  by_contra h
  push_neg at h
  exact not_forall_prime_of_AP a d hd h

/-- The explicit composite term: in the progression `a + n·d` (with `a` prime, `d ≥ 1`),
the index `n = a` lands on the composite `a·(1+d)`. -/
theorem composite_at_index_self (a d : ℕ) (ha : a.Prime) (hd : 1 ≤ d) :
    ¬ (a + a * d).Prime := by
  have hval : a + a * d = a * (1 + d) := by ring
  rw [hval]
  intro hp
  rcases hp.eq_one_or_self_of_dvd a (dvd_mul_right a (1 + d)) with h1 | h2
  · exact absurd h1 ha.ne_one
  · have hge : a * 2 ≤ a * (1 + d) := by gcongr; omega
    rw [← h2] at hge
    have h2a : 2 ≤ a := ha.two_le
    omega

/-! ## Part III: Explicit finite progressions of primes (Green–Tao's content)

Concrete witnesses for small lengths `k`. These exhibit exactly what Green–Tao
guarantees: prime progressions of every length. -/

/-- A 5-term arithmetic progression of primes: `5, 11, 17, 23, 29` (common difference 6). -/
theorem prime_AP_length_five (i : ℕ) (hi : i < 5) : (5 + i * 6).Prime := by
  interval_cases i <;> norm_num

/-- A 6-term arithmetic progression of primes: `7, 37, 67, 97, 127, 157`
(common difference 30). -/
theorem prime_AP_length_six (i : ℕ) (hi : i < 6) : (7 + i * 30).Prime := by
  interval_cases i <;> norm_num

/-! ## Part IV: A structural constraint on prime progressions -/

/-- A prime exceeding 3 is divisible by neither 2 nor 3. -/
theorem not_two_three_dvd_of_prime (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) :
    ¬ 2 ∣ q ∧ ¬ 3 ∣ q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases hq.eq_one_or_self_of_dvd 2 h with h' | h' <;> omega
  · rcases hq.eq_one_or_self_of_dvd 3 h with h' | h' <;> omega

/-- If three numbers `p, p+d, p+2d` are each not divisible by 3, then `3 ∣ d`.
(Were `3 ∤ d`, the residues `p, p+d, p+2d` would cover all of `ℤ/3ℤ`, forcing one to be
`0 mod 3`.) Proved by exhausting the nine residue pairs in `ZMod 3`. -/
theorem three_dvd_of_AP (p d : ℕ) (h0 : ¬ 3 ∣ p) (h1 : ¬ 3 ∣ (p + d))
    (h2 : ¬ 3 ∣ (p + 2 * d)) : 3 ∣ d := by
  have key : ∀ x y : ZMod 3, x ≠ 0 → x + y ≠ 0 → x + 2 * y ≠ 0 → y = 0 := by decide
  have c0 : (p : ZMod 3) ≠ 0 :=
    fun hc => h0 ((ZMod.natCast_eq_zero_iff p 3).mp hc)
  have c1 : (p : ZMod 3) + (d : ZMod 3) ≠ 0 := by
    have h : ((p + d : ℕ) : ZMod 3) ≠ 0 :=
      fun hc => h1 ((ZMod.natCast_eq_zero_iff (p + d) 3).mp hc)
    simpa using h
  have c2 : (p : ZMod 3) + 2 * (d : ZMod 3) ≠ 0 := by
    have h : ((p + 2 * d : ℕ) : ZMod 3) ≠ 0 :=
      fun hc => h2 ((ZMod.natCast_eq_zero_iff (p + 2 * d) 3).mp hc)
    push_cast at h
    simpa using h
  have hy : (d : ZMod 3) = 0 := key _ _ c0 c1 c2
  exact (ZMod.natCast_eq_zero_iff d 3).mp hy

/-- **In any 3-term arithmetic progression of primes all exceeding 3, the common
difference is divisible by 6.**
If `p`, `p+d`, `p+2d` are all prime and `p > 3`, then `6 ∣ d`. (Each prime avoids the
residues `0 mod 2` and `0 mod 3`; if `d` were odd, `p` and `p+d` could not both be odd,
and if `3 ∤ d`, the three terms would cover all residues mod 3, forcing one to be a
multiple of 3.) -/
theorem six_dvd_diff (p d : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p + d).Prime) (hp2d : (p + 2 * d).Prime) : 6 ∣ d := by
  obtain ⟨hp2, hp3'⟩ := not_two_three_dvd_of_prime p hp hp3
  obtain ⟨hpd2, hpd3⟩ := not_two_three_dvd_of_prime (p + d) hpd (by omega)
  obtain ⟨hp2d2, hp2d3⟩ := not_two_three_dvd_of_prime (p + 2 * d) hp2d (by omega)
  -- `p` and `p+d` are both odd, so `d` is even
  have e2p : p % 2 ≠ 0 := fun h => hp2 (Nat.dvd_of_mod_eq_zero h)
  have e2pd : (p + d) % 2 ≠ 0 := fun h => hpd2 (Nat.dvd_of_mod_eq_zero h)
  have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
  -- the three terms avoid `0 mod 3`, so `3 ∣ d`
  have h3d : 3 ∣ d := three_dvd_of_AP p d hp3' hpd3 hp2d3
  -- `gcd(2,3) = 1`, so `6 = 2·3 ∣ d`
  have h6 : 2 * 3 ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2d h3d
  simpa using h6

end InfinitudePrimesOQ04
