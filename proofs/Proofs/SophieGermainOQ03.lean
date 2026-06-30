/-
# Sophie Germain Primes — Open Question 3: Cunningham Chain Length Bound

Parent gallery entry: `sophie-germain` (Sophie Germain Primes).

The open question asks: *"What is the longest known Cunningham chain of Sophie
Germain primes?"* The literal answer is an empirical record from prime-search
databases (the longest known first-kind Cunningham chain has length 19, found by
computer search) and is not a theorem one can prove. The *mathematically*
substantive content behind the question is the **obstruction** that makes long
chains rare: there is a hard ceiling on the length of a Cunningham chain in
terms of its starting prime.

## A Cunningham chain of the first kind

A Cunningham chain of the first kind is a sequence of primes
`p₀, p₁, …, p_{n-1}` with `p_{i+1} = 2·p_i + 1`. Equivalently each `p_i` (except
the last) is a Sophie Germain prime whose safe prime is the next link. Solving
the recurrence with `p₀ = a` gives the closed form

    p_i = 2^i · (a + 1) − 1.

## Main result

**Theorem (`cunningham_length_le_pred`).** A Cunningham chain of the first kind
whose starting prime `a` is odd (`a > 2`) has length at most `a − 1`.

**Proof.** Suppose the chain had length `≥ a`, so the term at index `a − 1`,
namely `c = 2^{a-1}·(a+1) − 1`, is prime. Modulo `a` we have `a + 1 ≡ 1` and,
by Fermat's little theorem (`a` an odd prime, so `gcd(2, a) = 1`),
`2^{a-1} ≡ 1`. Hence `c ≡ 1·1 − 1 ≡ 0 (mod a)`, i.e. `a ∣ c`. But
`c ≥ 2a + 1 > a > 1`, so `c` has the proper divisor `a` and is composite — a
contradiction. ∎

This is sharp: the bound `a − 1` is attained at `a = 3` (chain `3, 7`, length 2)
and at `a = 5` (chain `5, 11, 23, 47`, length 4); both are recorded below.

The even prime `a = 2` is genuinely excluded — the chain `2, 5, 11, 23, 47` has
length `5 > 2 − 1 = 1` — because Fermat's argument needs `a ∤ 2`.

**Status**: DEEP DIVE — verified, 0 axioms, original.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace SophieGermainOQ03

/-!
## Closed-form description of a Cunningham chain of the first kind
-/

/-- The `i`-th term of a (potential) Cunningham chain of the first kind starting
at `a`, given by the closed form `2^i · (a + 1) − 1`. -/
def cunninghamTerm (a i : ℕ) : ℕ := 2 ^ i * (a + 1) - 1

/-- A Cunningham chain of the first kind of length `n` starting at `a`: every one
of the first `n` closed-form terms is prime. -/
def IsCunninghamChainFirstKind (a n : ℕ) : Prop :=
  ∀ i, i < n → Nat.Prime (cunninghamTerm a i)

/-- The starting term is `a` itself: `cunninghamTerm a 0 = a`. -/
@[simp] theorem cunninghamTerm_zero (a : ℕ) : cunninghamTerm a 0 = a := by
  simp [cunninghamTerm]

/-- The closed form satisfies the defining recurrence `p_{i+1} = 2·p_i + 1`,
confirming `cunninghamTerm` describes exactly a first-kind Cunningham chain. -/
theorem cunninghamTerm_succ (a i : ℕ) :
    cunninghamTerm a (i + 1) = 2 * cunninghamTerm a i + 1 := by
  have h1 : 1 ≤ 2 ^ i * (a + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hX : 2 ^ (i + 1) * (a + 1) = 2 * (2 ^ i * (a + 1)) := by rw [pow_succ]; ring
  unfold cunninghamTerm
  rw [hX]
  -- 2 * Y - 1 = 2 * (Y - 1) + 1  where Y = 2^i * (a+1) ≥ 1
  omega

/-!
## The length bound

The key obstruction: if the chain reached length `a`, the term at index `a − 1`
would be divisible by `a` yet strictly larger than `a`, hence composite.
-/

/-- For an odd prime `a`, the closed-form term at index `a − 1` is divisible by
`a`. This is Fermat's little theorem packaged for the chain:
`2^{a-1}·(a+1) − 1 ≡ 0 (mod a)`. -/
theorem dvd_cunninghamTerm_pred (a : ℕ) (ha : Nat.Prime a) (ha2 : 2 < a) :
    a ∣ cunninghamTerm a (a - 1) := by
  -- 2 is coprime to a (a is an odd prime > 2)
  have hcop : (2 : ℕ).Coprime a := by
    rw [Nat.coprime_comm]
    refine (Nat.coprime_primes ha Nat.prime_two).mpr ?_
    omega
  -- Fermat: 2^(a-1) ≡ 1 [MOD a]
  have e1 : 2 ^ (a - 1) ≡ 1 [MOD a] :=
    Nat.ModEq.pow_card_sub_one_eq_one ha hcop
  -- a + 1 ≡ 1 [MOD a]
  have e2 : a + 1 ≡ 1 [MOD a] := Nat.add_modEq_right_iff.mpr dvd_rfl
  -- Multiply: 2^(a-1) * (a+1) ≡ 1 [MOD a]
  have key : (1 : ℕ) ≡ 2 ^ (a - 1) * (a + 1) [MOD a] := by
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≡ 2 ^ (a - 1) * (a + 1) [MOD a] := (e1.mul e2).symm
  have h1le : 1 ≤ 2 ^ (a - 1) * (a + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- Transfer to divisibility of the term (which carries the `- 1`)
  unfold cunninghamTerm
  exact (Nat.modEq_iff_dvd' h1le).mp key

/-- The closed-form term at index `a − 1` strictly exceeds `a` (for `a > 2`),
so combined with `a ∣ ·` it is composite. -/
theorem lt_cunninghamTerm_pred (a : ℕ) (ha2 : 2 < a) :
    a < cunninghamTerm a (a - 1) := by
  have hpow : 2 ≤ 2 ^ (a - 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hge : 2 * (a + 1) ≤ 2 ^ (a - 1) * (a + 1) :=
    Nat.mul_le_mul_right _ hpow
  unfold cunninghamTerm
  omega

/-- **Main theorem.** A Cunningham chain of the first kind starting at an odd
prime `a` has length at most `a − 1`.

The obstruction is Fermat's little theorem: the `a`-th link (index `a − 1`)
would be `≡ 0 (mod a)` and `> a`, hence composite, so the chain of primes cannot
reach that link. This is the mathematical content behind "how long can a
Cunningham chain be": short starting primes force short chains, and a record
chain of length `L` needs a starting prime `≥ L + 1`. -/
theorem cunningham_length_le_pred (a n : ℕ) (ha : Nat.Prime a) (ha2 : 2 < a)
    (hchain : IsCunninghamChainFirstKind a n) : n ≤ a - 1 := by
  by_contra h
  push_neg at h
  -- h : a - 1 < n, so the term at index a - 1 is in the chain and prime
  have hi : a - 1 < n := by omega
  have hcp : Nat.Prime (cunninghamTerm a (a - 1)) := hchain (a - 1) hi
  have hdvd : a ∣ cunninghamTerm a (a - 1) := dvd_cunninghamTerm_pred a ha ha2
  have hlt : a < cunninghamTerm a (a - 1) := lt_cunninghamTerm_pred a ha2
  -- a prime term divisible by a must equal a, contradicting a < term
  rcases hcp.eq_one_or_self_of_dvd a hdvd with h1 | h2
  · omega
  · omega

/-!
## Consequences and sharpness

The bound immediately constrains chains from small odd primes, and is attained.
-/

/-- A Cunningham chain of the first kind starting at `3` has length at most `2`
(realised by `3, 7`). -/
theorem length_le_two_from_three (n : ℕ) (hchain : IsCunninghamChainFirstKind 3 n) :
    n ≤ 2 :=
  cunningham_length_le_pred 3 n (by norm_num) (by norm_num) hchain

/-- A Cunningham chain of the first kind starting at `5` has length at most `4`
(realised by `5, 11, 23, 47`). -/
theorem length_le_four_from_five (n : ℕ) (hchain : IsCunninghamChainFirstKind 5 n) :
    n ≤ 4 :=
  cunningham_length_le_pred 5 n (by norm_num) (by norm_num) hchain

/-- A record chain of length `L` requires a starting prime of size at least
`L + 1`: contrapositive packaging of the main bound. -/
theorem starting_prime_ge (a n : ℕ) (ha : Nat.Prime a) (ha2 : 2 < a)
    (hchain : IsCunninghamChainFirstKind a n) : a ≥ n + 1 := by
  have := cunningham_length_le_pred a n ha ha2 hchain
  omega

/-- Sharpness at `a = 5`: the chain `5, 11, 23, 47` realises length `4`, so the
bound `5 − 1 = 4` of `length_le_four_from_five` is attained. -/
theorem chain_from_five_length_four : IsCunninghamChainFirstKind 5 4 := by
  intro i hi
  interval_cases i <;> · unfold cunninghamTerm; norm_num

/-- The chain from `5` cannot be extended to length `5`: the next link
`cunninghamTerm 5 4 = 95 = 5 · 19` is composite. Together with
`chain_from_five_length_four` this shows the maximal first-kind chain from `5`
has length exactly `4 = 5 − 1`. -/
theorem chain_from_five_not_length_five : ¬ IsCunninghamChainFirstKind 5 5 := by
  intro hchain
  have h95 : Nat.Prime (cunninghamTerm 5 4) := hchain 4 (by norm_num)
  rw [show cunninghamTerm 5 4 = 95 from by unfold cunninghamTerm; norm_num] at h95
  exact (by norm_num : ¬ Nat.Prime 95) h95

/-- Sharpness at `a = 3`: the chain `3, 7` realises length `2 = 3 − 1`. -/
theorem chain_from_three_length_two : IsCunninghamChainFirstKind 3 2 := by
  intro i hi
  interval_cases i <;> · unfold cunninghamTerm; norm_num

end SophieGermainOQ03
