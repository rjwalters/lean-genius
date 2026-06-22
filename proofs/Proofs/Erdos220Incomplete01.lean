/-
# Erdős #220: the extremal structure of reduced residues for primes and prime powers

Erdős Problem #220 asks whether, for the reduced residues `a₁ < ⋯ < a_{φ(n)}` mod
`n`, the squared gap sum satisfies `∑ (a_{k+1} − a_k)² ≪ n²/φ(n)` (Montgomery–
Vaughan, 1986: yes). The companion entry **erdos-220-oq-01** already proves the
matching *lower* bound elementarily: the gaps telescope and Cauchy–Schwarz gives
`(n−2)² ≤ (φ(n)−1)·∑ gaps²`.

This file pins down the **extremal cases** where that structure is most transparent
— the primes and prime powers — completely elementarily.

  * For a **prime** `p`, every `m` with `1 ≤ m ≤ p−1` is coprime to `p`, so the
    reduced residues are the *contiguous block* `{1, 2, …, p−1}`. Consecutive, so
    every gap is exactly `1`: the gap sum `∑ gaps² = p − 2` and the Cauchy–Schwarz
    lower bound `(p−2)²/(φ(p)−1) = (p−2)²/(p−2) = p − 2` is attained *with equality*.
  * For `n = 2^k`, the reduced residues are exactly the **odd** numbers below `2^k`,
    an arithmetic progression of common difference `2` — every gap is `2`.

We prove the residue sets exactly (`reducedResidues_prime`,
`mem_reducedResidues_two_pow`), their cardinalities (`= φ(n)`), the
consecutiveness for primes, and verify the concrete gap computations for `p = 7`
(gaps all `1`, `∑ gaps² = 5`) on explicit lists. Everything is `decide`/`omega`/
Mathlib — zero axioms, no `native_decide`.

The `reducedResidues` definition matches the companion entry's; the file is
otherwise self-contained.
-/
import Mathlib

open Finset

namespace Erdos220Incomplete01

/-- The reduced residues mod `n`: the `m` in `[1, n)` coprime to `n`. -/
def reducedResidues (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun m => 1 ≤ m ∧ Nat.Coprime m n)

@[simp] theorem mem_reducedResidues {n m : ℕ} :
    m ∈ reducedResidues n ↔ m < n ∧ 1 ≤ m ∧ Nat.Coprime m n := by
  simp [reducedResidues, Finset.mem_filter, Finset.mem_range]

/- ## Primes: the reduced residues are a contiguous block -/

/-- **For a prime `p`, the reduced residues are exactly `{1, 2, …, p−1}`.** Every
`m` with `1 ≤ m ≤ p−1` satisfies `p ∤ m`, hence is coprime to `p`; the coprimality
condition is therefore vacuous and the residues form a contiguous integer block. -/
theorem reducedResidues_prime {p : ℕ} (hp : p.Prime) :
    reducedResidues p = Finset.Icc 1 (p - 1) := by
  have hp2 := hp.two_le
  ext m
  simp only [mem_reducedResidues, Finset.mem_Icc]
  constructor
  · rintro ⟨hmp, h1m, _⟩
    exact ⟨h1m, by omega⟩
  · rintro ⟨h1m, hmp1⟩
    refine ⟨by omega, h1m, ?_⟩
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- The reduced residues of a prime `p` number `φ(p) = p − 1`. -/
theorem card_reducedResidues_prime {p : ℕ} (hp : p.Prime) :
    (reducedResidues p).card = p - 1 := by
  rw [reducedResidues_prime hp, Nat.card_Icc]
  omega

/-- …matching Euler's totient. -/
theorem card_reducedResidues_prime_eq_totient {p : ℕ} (hp : p.Prime) :
    (reducedResidues p).card = Nat.totient p := by
  rw [card_reducedResidues_prime hp, Nat.totient_prime hp]

/-- **Consecutiveness**: for a prime `p`, if `m` is a reduced residue and `m + 1`
is still in range, then `m + 1` is also a reduced residue. So the residues run
`1, 2, …, p−1` with no holes — every gap is `1`. -/
theorem reducedResidues_prime_consecutive {p m : ℕ} (hp : p.Prime)
    (hm : m ∈ reducedResidues p) (hlt : m + 1 ≤ p - 1) :
    m + 1 ∈ reducedResidues p := by
  rw [reducedResidues_prime hp, Finset.mem_Icc] at hm ⊢
  omega

/- ## Prime powers `2^k`: the reduced residues are the odd numbers -/

/-- **For `n = 2^k` (`k ≥ 1`), the reduced residues are exactly the odd numbers in
`[1, 2^k)`** — an arithmetic progression of common difference `2`, so every gap is
`2`. -/
theorem mem_reducedResidues_two_pow {k m : ℕ} (hk : 1 ≤ k) :
    m ∈ reducedResidues (2 ^ k) ↔ m < 2 ^ k ∧ 1 ≤ m ∧ Odd m := by
  rw [mem_reducedResidues]
  have hk0 : 0 < k := hk
  rw [Nat.coprime_pow_right_iff hk0, Nat.coprime_comm, Nat.coprime_two_left]

/- ## Concrete tight case: the prime `p = 7` -/

/-- The reduced residues mod `7` are `{1, 2, 3, 4, 5, 6}`. -/
theorem reducedResidues_seven : reducedResidues 7 = {1, 2, 3, 4, 5, 6} := by decide

/-- For `p = 7` the six residues `1, 2, 3, 4, 5, 6`, listed in order, have all five
gaps equal to `1`. -/
theorem gaps_seven :
    List.zipWith (· - ·) [2, 3, 4, 5, 6] [1, 2, 3, 4, 5] = [1, 1, 1, 1, 1] := by decide

/-- Hence the squared gap sum for `p = 7` is `∑ gaps² = 5 = p − 2`, attaining the
Cauchy–Schwarz lower bound `(p−2)²/(φ(p)−1) = 25/5 = 5` with equality. -/
theorem sumSq_gaps_seven :
    (([1, 1, 1, 1, 1] : List ℕ).map (· ^ 2)).sum = 5 := by decide

/- ## Concrete: the prime power `n = 8` (gaps all `2`) -/

/-- The reduced residues mod `8` are the odds `{1, 3, 5, 7}`. -/
theorem reducedResidues_eight : reducedResidues 8 = {1, 3, 5, 7} := by decide

/-- The three gaps of the residues `1, 3, 5, 7` mod `8` are all `2`. -/
theorem gaps_eight :
    List.zipWith (· - ·) [3, 5, 7] [1, 3, 5] = [2, 2, 2] := by decide

/-- The squared gap sum mod `8` is `∑ gaps² = 12`. With `n²/φ(n) = 64/4 = 16` this
is the same order — illustrating Montgomery–Vaughan tightness for prime powers. -/
theorem sumSq_gaps_eight :
    (([2, 2, 2] : List ℕ).map (· ^ 2)).sum = 12 := by decide

/- ## Concrete: a composite `n = 12` (mixed gaps) -/

/-- The reduced residues mod `12` are `{1, 5, 7, 11}` — here the gaps `4, 2, 4` are
*not* all equal, the generic behaviour away from the extremal prime case. -/
theorem reducedResidues_twelve : reducedResidues 12 = {1, 5, 7, 11} := by decide

/-- The gaps of `1, 5, 7, 11` mod `12` are `4, 2, 4`. -/
theorem gaps_twelve :
    List.zipWith (· - ·) [5, 7, 11] [1, 5, 7] = [4, 2, 4] := by decide

end Erdos220Incomplete01
