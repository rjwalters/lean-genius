/-
Erdős Problem #1209: Sequences whose shifts avoid primes / squarefrees

Source: https://erdosproblems.com/1209
Status: OPEN (Erdős called the questions "quite hopeless"); a trivial
counterexample exists, and this file formalizes that counterexample.

Statement (informal):
Erdős asked questions about strictly increasing sequences A = {a₁ < a₂ < ⋯}
and the arithmetic nature of the shifts aₖ + k — in particular whether one can
force aₖ + k to be prime (resp. squarefree) infinitely often. In [Er80] Erdős
remarked that "unless I overlook a trivial way of getting a counterexample
these questions are quite hopeless". Indeed there is a trivial counterexample
(a variant of the construction in problem #429):

    define a₁ = 2, and for k ≥ 2 let aₖ > aₖ₋₁ be a prime with
        aₖ + k ≡ 0 (mod qₖ),
    where qₖ is a prime not dividing k.

The same idea with qₖ² in place of qₖ produces a counterexample to the
squarefree question (then qₖ² ∣ aₖ + k, so aₖ + k is not squarefree).
The sequence can be made to grow arbitrarily fast.

What this file proves (faithful formalization of the counterexample):

  * `exists_prime_add_not_prime`     — for every shift k ≥ 1 and every bound N
        there is a prime p > N with p + k composite (it is divisible by a prime
        q ∤ k, by Dirichlet's theorem on primes in arithmetic progressions);
  * `exists_prime_add_not_squarefree` — the qₖ² variant: a prime p > N with
        p + k divisible by a square q² > 1, hence not squarefree;
  * `erdos1209_prime_counterexample` — there is a STRICTLY INCREASING sequence
        a : ℕ → ℕ of primes, growing faster than any prescribed g, with
        aₖ + k never prime (k ≥ 1);
  * `erdos1209_squarefree_counterexample` — the same with "never squarefree".

The only nontrivial ingredient is Dirichlet's theorem on primes in arithmetic
progressions (`Nat.forall_exists_prime_gt_and_modEq`), which is in Mathlib.
The "grows arbitrarily fast" clause is captured by quantifying over an
arbitrary growth function g : ℕ → ℕ and requiring g k < a k for all k.

References:
- [Er80] P. Erdős, "Some applications of graph theory and combinatorial methods
  to number theory and geometry", 1980.
- Erdős problem #429 (the construction this is a variant of).

Tags: erdos, number-theory, primes, squarefree, dirichlet, arithmetic-progressions
-/

import Mathlib

namespace Erdos1209

/-- **Building block (prime shift).**
For every shift `k ≥ 1` and every bound `N`, there is a prime `p > N` such that
`p + k` is *not* prime.

Construction: pick a prime `q > k` (so `q ∤ k`). Then the residue `q - k` is a
unit mod `q`, so by Dirichlet's theorem there is a prime `p` larger than both `N`
and `q` with `p ≡ q - k (mod q)`. Hence `q ∣ p + k` with `1 < q < p + k`, so
`p + k` is composite. -/
theorem exists_prime_add_not_prime (k : ℕ) (hk : 1 ≤ k) (N : ℕ) :
    ∃ p, N < p ∧ p.Prime ∧ ¬ (p + k).Prime := by
  -- a prime `q` strictly larger than `k`
  obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 1)
  have hkq : k < q := hqk
  have hk0 : 0 < k := hk
  -- `q` does not divide the residue `q - k`
  have hndvd : ¬ q ∣ (q - k) := by
    intro hd
    have hqk' : q ∣ k := by
      have h := Nat.dvd_sub (dvd_refl q) hd
      rwa [Nat.sub_sub_self hkq.le] at h
    exact absurd (Nat.le_of_dvd hk0 hqk') (not_le.mpr hkq)
  -- hence `q - k` is coprime to `q`
  have hcop : (q - k).Coprime q :=
    Nat.coprime_comm.mp (hq.coprime_iff_not_dvd.mpr hndvd)
  -- Dirichlet: a prime `p` beyond `max N q` with `p ≡ q - k (mod q)`
  obtain ⟨p, hpgt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N q) hq.pos.ne' hcop
  have hNp : N < p := (le_max_left N q).trans_lt hpgt
  have hqp : q < p := (le_max_right N q).trans_lt hpgt
  -- `q ∣ p + k`
  have hdvd : q ∣ p + k := by
    have h1 : p + k ≡ (q - k) + k [MOD q] := hpmod.add_right k
    rw [Nat.sub_add_cancel hkq.le] at h1
    have h2 : p + k ≡ 0 [MOD q] := h1.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl q))
    exact Nat.modEq_zero_iff_dvd.mp h2
  refine ⟨p, hNp, hp, ?_⟩
  intro hpk
  rcases hpk.eq_one_or_self_of_dvd q hdvd with h | h
  · exact hq.one_lt.ne' h
  · have : q < p + k := hqp.trans_le (Nat.le_add_right p k)
    omega

/-- **Building block (squarefree shift).**
For every shift `k ≥ 1` and every bound `N`, there is a prime `p > N` such that
`p + k` is *not* squarefree.

Same idea as `exists_prime_add_not_prime` but with modulus `q²`: choose a prime
`p ≡ q² - k (mod q²)`, so `q² ∣ p + k` and the square `q·q > 1` divides `p + k`. -/
theorem exists_prime_add_not_squarefree (k : ℕ) (hk : 1 ≤ k) (N : ℕ) :
    ∃ p, N < p ∧ p.Prime ∧ ¬ Squarefree (p + k) := by
  obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 1)
  have hkq : k < q := hqk
  have hk0 : 0 < k := hk
  have hqle : q ≤ q ^ 2 := le_self_pow hq.one_lt.le (by norm_num)
  have hkq2 : k ≤ q ^ 2 := (hkq.le).trans hqle
  -- `q` does not divide the residue `q² - k`
  have hndvd : ¬ q ∣ (q ^ 2 - k) := by
    intro hd
    have hqdvd2 : q ∣ q ^ 2 := dvd_pow_self q (by norm_num)
    have hqk' : q ∣ k := by
      have h := Nat.dvd_sub hqdvd2 hd
      rwa [Nat.sub_sub_self hkq2] at h
    exact absurd (Nat.le_of_dvd hk0 hqk') (not_le.mpr hkq)
  -- hence `q² - k` is coprime to `q²`
  have hcop1 : (q ^ 2 - k).Coprime q :=
    Nat.coprime_comm.mp (hq.coprime_iff_not_dvd.mpr hndvd)
  have hcop : (q ^ 2 - k).Coprime (q ^ 2) :=
    (Nat.coprime_pow_right_iff (n := 2) (by norm_num) (q ^ 2 - k) q).mpr hcop1
  -- Dirichlet with modulus `q²`
  obtain ⟨p, hpgt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N q) (pow_ne_zero 2 hq.pos.ne') hcop
  have hNp : N < p := (le_max_left N q).trans_lt hpgt
  -- `q² ∣ p + k`
  have hdvd : q ^ 2 ∣ p + k := by
    have h1 : p + k ≡ (q ^ 2 - k) + k [MOD q ^ 2] := hpmod.add_right k
    rw [Nat.sub_add_cancel hkq2] at h1
    have h2 : p + k ≡ 0 [MOD q ^ 2] := h1.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))
    exact Nat.modEq_zero_iff_dvd.mp h2
  refine ⟨p, hNp, hp, ?_⟩
  intro hsf
  -- `Squarefree` forces the square factor `q` to be a unit, impossible for a prime
  have hunit : IsUnit q := hsf q (by rw [← pow_two]; exact hdvd)
  exact absurd (Nat.isUnit_iff.mp hunit) hq.one_lt.ne'

/-- Recursive skeleton for the strictly increasing sequence: `seq f 0 = f 0 0`
and `seq f (n+1) = f (n+1) (seq f n)`, so each term is built from a chooser `f`
that, given an index and the previous value, returns the next term. -/
private def seq (f : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0 0
  | (n + 1) => f (n + 1) (seq f n)

/-- **Generic builder.**
If for every index `k` and every bound `N` we can find some `p > N` satisfying a
per-index predicate `Q k`, then there is a *strictly increasing* sequence
`a : ℕ → ℕ` with `Q k (a k)` for all `k`. Each term is chosen larger than the
previous one, which yields strict monotonicity. -/
theorem exists_strictMono_forall {Q : ℕ → ℕ → Prop}
    (H : ∀ k N, ∃ p, N < p ∧ Q k p) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ k, Q k (a k) := by
  choose f hf using H
  refine ⟨seq f, strictMono_nat_of_lt_succ (fun n => ?_), ?_⟩
  · -- `seq f n < seq f (n+1) = f (n+1) (seq f n)` by the chooser's bound
    exact (hf (n + 1) (seq f n)).1
  · intro k
    cases k with
    | zero => exact (hf 0 0).2
    | succ n => exact (hf (n + 1) (seq f n)).2

/-- **Erdős #1209, prime counterexample.**
For any prescribed growth function `g`, there is a strictly increasing sequence
`a : ℕ → ℕ` of primes, with `a k > g k` for all `k` (so it can grow arbitrarily
fast), such that the shift `a k + k` is never prime for `k ≥ 1`.

This refutes the existence of any positive-density / fast-growth hypothesis that
would force the shifts `aₖ + k` to be prime infinitely often. -/
theorem erdos1209_prime_counterexample (g : ℕ → ℕ) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ k, g k < a k) ∧ (∀ k, (a k).Prime) ∧
      (∀ k, 1 ≤ k → ¬ (a k + k).Prime) := by
  -- the per-index predicate bundles primality, the growth bound, and the shift
  have H : ∀ k N, ∃ p, N < p ∧
      (p.Prime ∧ g k < p ∧ (1 ≤ k → ¬ (p + k).Prime)) := by
    intro k N
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · -- shift condition vacuous: just grab a large prime
      obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max N (g k) + 1)
      exact ⟨p, lt_of_le_of_lt (le_max_left N (g k)) (by omega), hp,
        lt_of_le_of_lt (le_max_right N (g k)) (by omega), fun h => absurd h (by omega)⟩
    · -- use the building block above with bound `max N (g k)`
      obtain ⟨p, hpgt, hp, hnp⟩ := exists_prime_add_not_prime k hk0 (max N (g k))
      exact ⟨p, (le_max_left N (g k)).trans_lt hpgt, hp,
        (le_max_right N (g k)).trans_lt hpgt, fun _ => hnp⟩
  obtain ⟨a, hmono, hspec⟩ := exists_strictMono_forall H
  exact ⟨a, hmono, fun k => (hspec k).2.1, fun k => (hspec k).1, fun k => (hspec k).2.2⟩

/-- **Erdős #1209, squarefree counterexample.**
For any prescribed growth function `g`, there is a strictly increasing sequence
`a : ℕ → ℕ` of primes, with `a k > g k` for all `k`, such that the shift
`a k + k` is never squarefree for `k ≥ 1`. -/
theorem erdos1209_squarefree_counterexample (g : ℕ → ℕ) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ k, g k < a k) ∧ (∀ k, (a k).Prime) ∧
      (∀ k, 1 ≤ k → ¬ Squarefree (a k + k)) := by
  have H : ∀ k N, ∃ p, N < p ∧
      (p.Prime ∧ g k < p ∧ (1 ≤ k → ¬ Squarefree (p + k))) := by
    intro k N
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max N (g k) + 1)
      exact ⟨p, lt_of_le_of_lt (le_max_left N (g k)) (by omega), hp,
        lt_of_le_of_lt (le_max_right N (g k)) (by omega), fun h => absurd h (by omega)⟩
    · obtain ⟨p, hpgt, hp, hnp⟩ := exists_prime_add_not_squarefree k hk0 (max N (g k))
      exact ⟨p, (le_max_left N (g k)).trans_lt hpgt, hp,
        (le_max_right N (g k)).trans_lt hpgt, fun _ => hnp⟩
  obtain ⟨a, hmono, hspec⟩ := exists_strictMono_forall H
  exact ⟨a, hmono, fun k => (hspec k).2.1, fun k => (hspec k).1, fun k => (hspec k).2.2⟩

end Erdos1209
