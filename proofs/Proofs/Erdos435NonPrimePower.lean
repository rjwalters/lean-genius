/-
Erdős Problem #435 — The Non-Prime-Power Case (companion to Erdos435Problem.lean
and Erdos435PrimePowerObstruction.lean)

The restriction in Erdős #435 to integers `n` that are NOT prime powers is sharp.
The companion file `Erdos435PrimePowerObstruction.lean` proves the easy half: if
`n = p^k` then `p` divides every middle binomial coefficient `C(n, j)`
(`1 ≤ j < n`), so the gcd of the generators is `> 1` and no Frobenius number
exists.

This file proves the converse — the *reason* the problem is well-posed for
non-prime-powers:

    if `n` is not a prime power, then `gcd{C(n,1), …, C(n,n-1)} = 1`.

A numerical semigroup whose generators have gcd `1` has finite complement, so a
largest non-representable integer (the quantity the Hwang–Song formula computes)
exists. Together with the obstruction file this gives the full dichotomy:

    gcd{C(n,1), …, C(n,n-1)} = 1   ⟺   n is not a prime power.

The proof rests on Lucas' theorem (`Mathlib.Data.Nat.Choose.Lucas`). For each
prime `p ∣ n`, set `a = v_p(n)`. Then `C(n, p^a) ≡ n / p^a (mod p)` and
`n / p^a = ordCompl[p] n` is coprime to `p`, so `p ∤ C(n, p^a)`. Hence no prime
can divide all generators, i.e. the gcd is `1`.
-/
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Erdos435.NonPrimePower

open Finset

/-- **Lucas core lemma.**
For a prime `p` and `n > 0`, writing `a = v_p(n)` for the `p`-adic valuation of
`n`, the prime `p` does *not* divide `C(n, p^a)`.

By Lucas' theorem `C(n, p^a) ≡ C(n / p^a, 1) · ∏_{i<a} C(·, 0) ≡ n / p^a (mod p)`,
and `n / p^a = ordCompl[p] n` is coprime to `p`. -/
theorem not_dvd_choose_ordProj {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    ¬ p ∣ n.choose (p ^ (n.factorization p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set a := n.factorization p with ha
  -- Lucas' theorem, separating the top base-`p` block:
  --   C(n, p^a) ≡ C(n/p^a, p^a/p^a) · ∏_{i<a} C(n/p^i % p, p^a/p^i % p)  (mod p)
  have hl := Choose.choose_modEq_choose_mul_prod_range_choose (n := n) (k := p ^ a) (p := p) a
  rw [← ZMod.intCast_eq_intCast_iff] at hl
  -- The top quotient `p^a / p^a = 1`, and every lower block index `p^a / p^i % p = 0`.
  have hdiv : p ^ a / p ^ a = 1 := Nat.div_self (pow_pos hp.pos a)
  have hprod : (∏ i ∈ range a,
      ((n / p ^ i % p).choose (p ^ a / p ^ i % p) : ZMod p)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_range] at hi
    have hpd : p ^ a / p ^ i = p ^ (a - i) := Nat.pow_div (le_of_lt hi) hp.pos
    have hz : p ^ (a - i) % p = 0 := by
      have h1 : a - i = (a - i - 1) + 1 := by omega
      rw [h1, pow_succ']
      exact Nat.mul_mod_right p _
    rw [hpd, hz, Nat.choose_zero_right, Nat.cast_one]
  -- Cast the Lucas congruence into `ZMod p` and simplify.
  have key : ((n.choose (p ^ a) : ℕ) : ZMod p) = ((n / p ^ a : ℕ) : ZMod p) := by
    push_cast at hl
    rw [hl, hdiv, hprod, mul_one, Nat.choose_one_right]
  -- `p ∤ n / p^a = ordCompl[p] n`.
  have hco : ¬ p ∣ (n / p ^ a) := Nat.not_dvd_ordCompl hp hn.ne'
  -- Conclude.
  intro hdvd
  have : ((n.choose (p ^ a) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [key] at this
  exact hco ((ZMod.natCast_eq_zero_iff _ _).mp this)

/-- **The non-prime-power case.**
If `n ≥ 2` is not a prime power, then the generators `C(n,1), …, C(n,n-1)` are
globally coprime:
`gcd{C(n,1), …, C(n,n-1)} = 1`. -/
theorem gcd_generators_eq_one {n : ℕ} (hn2 : 2 ≤ n) (hnp : ¬ IsPrimePow n) :
    (Finset.Icc 1 (n - 1)).gcd (fun j => n.choose j) = 1 := by
  by_contra hg
  -- The gcd is `≠ 1`, so it has a prime factor `p`.
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  -- `p ∣ gcd ∣ C(n,1) = n`.
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := by rw [Finset.mem_Icc]; omega
  have hgdvd1 : (Finset.Icc 1 (n - 1)).gcd (fun j => n.choose j) ∣ n.choose 1 :=
    Finset.gcd_dvd h1mem
  rw [Nat.choose_one_right] at hgdvd1
  have hpn : p ∣ n := hpg.trans hgdvd1
  set a := n.factorization p with ha
  have hn0 : n ≠ 0 := by omega
  -- `a = v_p(n) ≥ 1` since `p ∣ n`.
  have hple : 1 ≤ a := hp.factorization_pos_of_dvd hn0 hpn
  -- `p^a · (n/p^a) = n`.
  have hsplit : p ^ a * (n / p ^ a) = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hpa_pos : 1 ≤ p ^ a := Nat.one_le_pow _ _ hp.pos
  -- `n/p^a ≥ 2`: otherwise `n = p^a`, a prime power, contradiction.
  have hoc_pos : 0 < n / p ^ a := Nat.ordCompl_pos p hn0
  have hoc_ne1 : n / p ^ a ≠ 1 := by
    intro h1
    apply hnp
    refine ⟨p, a, hp.prime, hple, ?_⟩
    rw [h1, mul_one] at hsplit
    exact hsplit
  have hoc2 : 2 ≤ n / p ^ a := by omega
  -- `p^a ≤ n - 1`: from `2 · p^a ≤ p^a · (n/p^a) = n`.
  have h2pa : p ^ a * 2 ≤ n := by
    calc p ^ a * 2 ≤ p ^ a * (n / p ^ a) := by gcongr
      _ = n := hsplit
  have hpa_le : p ^ a ≤ n - 1 := by omega
  -- `p^a` is a valid generator index.
  have hpa_mem : p ^ a ∈ Finset.Icc 1 (n - 1) := by rw [Finset.mem_Icc]; exact ⟨hpa_pos, hpa_le⟩
  -- `p ∣ gcd ∣ C(n, p^a)`, but the Lucas lemma says `p ∤ C(n, p^a)`.
  have hpdvd : p ∣ n.choose (p ^ a) := hpg.trans (Finset.gcd_dvd hpa_mem)
  exact not_dvd_choose_ordProj hp (by omega) hpdvd

end Erdos435.NonPrimePower
