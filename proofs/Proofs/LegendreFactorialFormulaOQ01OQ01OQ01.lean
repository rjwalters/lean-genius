/-
# The Explicit Recursive Carry Sequence Behind Kummer's Theorem

Kummer's theorem gives a strikingly combinatorial description of the
`p`-adic valuation of a binomial coefficient:

  `vₚ(C(n, k)) = #{ carries when adding k and n − k in base p }`.

Both Mathlib and the gallery's Kummer carry-count entry record this only with
the carry left *implicit*: the valuation is the cardinality of the overflow
set `{ i ∈ Ico 1 b | pⁱ ≤ k % pⁱ + (n−k) % pⁱ }` (Mathlib's
`Nat.Prime.emultiplicity_choose`).  The predicate `pⁱ ≤ k % pⁱ + (n−k) % pⁱ`
*is* the statement "a carry propagates into position `i`", but no carry is
ever named, and — crucially — the **schoolbook digit-by-digit carry
recurrence** that actually generates the carries is never stated.  The
gallery's multinomial Kummer entry explicitly flags "base-p carry counting"
as "not yet in Mathlib".

This file (open question `oq-01` of the Kummer carry-count entry, itself
`oq-01` of the Legendre's-formula entry) supplies the missing carry
*algorithm*.  We define the carry sequence explicitly,

  `carry p k m i = (k % pⁱ + m % pⁱ) / pⁱ ∈ {0, 1}`,

and prove that it satisfies the schoolbook carry recurrence

  `carry p k m (i+1) = (digitᵢ k + digitᵢ m + carry p k m i) / p`,

i.e. a carry out of position `i` is generated exactly when the two base-`p`
digits at position `i` plus the incoming carry reach `p`.  We then reassemble
the headline carry-count theorem on top of this explicit sequence,

  `padicValNat p (C(n, k)) = #{ i ∈ Ico 1 b | carry p k (n − k) i = 1 }`
                          = ∑ i ∈ Ico 1 b, carry p k (n − k) i.

Everything is fully verified: no `sorry`, no extra axioms, and no
`native_decide`.
-/

import Mathlib.Data.Nat.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

open Nat Finset

namespace KummerCarryRecurrence

/-! ## The carry sequence and base-`p` digits -/

/-- The base-`p` carry **into** digit position `i` when adding `k` and `m`.

It equals `1` exactly when the sum of the low-`i` digit blocks of `k` and `m`
overflows `pⁱ` (so that a unit must be carried into position `i`), and `0`
otherwise. -/
def carry (p k m i : ℕ) : ℕ := (k % p ^ i + m % p ^ i) / p ^ i

/-- The `i`-th base-`p` digit of `x`, namely `⌊x / pⁱ⌋ mod p`. -/
def digit (p x i : ℕ) : ℕ := x / p ^ i % p

/-- There is never a carry into the units position. -/
@[simp] theorem carry_zero (p k m : ℕ) : carry p k m 0 = 0 := by
  simp [carry, Nat.mod_one]

/-- A carry is a single bit: it is either `0` or `1`. -/
theorem carry_le_one (hp : 1 < p) (k m i : ℕ) : carry p k m i ≤ 1 := by
  have hq : 0 < p ^ i := pow_pos (by omega) i
  have hkq : k % p ^ i < p ^ i := Nat.mod_lt _ hq
  have hmq : m % p ^ i < p ^ i := Nat.mod_lt _ hq
  unfold carry
  have hlt : (k % p ^ i + m % p ^ i) / p ^ i < 2 := by
    apply Nat.div_lt_of_lt_mul; omega
  omega

/-- The carry into position `i` is exactly the overflow test on the low-`i`
digit blocks: `carry = 1` iff `pⁱ ≤ k % pⁱ + m % pⁱ`. -/
theorem carry_eq_one_iff (hp : 1 < p) (k m i : ℕ) :
    carry p k m i = 1 ↔ p ^ i ≤ k % p ^ i + m % p ^ i := by
  have hq : 0 < p ^ i := pow_pos (by omega) i
  have hle := carry_le_one hp k m i
  unfold carry at hle ⊢
  constructor
  · intro h
    have h1 : 1 ≤ (k % p ^ i + m % p ^ i) / p ^ i := by omega
    exact (Nat.one_le_div_iff hq).mp h1
  · intro h
    have h1 : 1 ≤ (k % p ^ i + m % p ^ i) / p ^ i := (Nat.one_le_div_iff hq).mpr h
    omega

/-! ## The schoolbook carry recurrence -/

/-- A division identity underlying the carry recurrence:
if `r < q` then `(q·Y + r) / (q·p) = Y / p`. -/
private theorem div_block {q : ℕ} (hq : 0 < q) {r : ℕ} (hr : r < q) (Y p : ℕ) :
    (q * Y + r) / (q * p) = Y / p := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_add_div hq, Nat.div_eq_of_lt hr, Nat.add_zero]

/-- **Kummer's carry recurrence.**  The carry into position `i+1` is generated
exactly by the schoolbook rule: add the two base-`p` digits at position `i`
together with the incoming carry, and carry out iff the result reaches `p`. -/
theorem carry_succ (hp : 1 < p) (k m i : ℕ) :
    carry p k m (i + 1) = (digit p k i + digit p m i + carry p k m i) / p := by
  have hq : 0 < p ^ i := pow_pos (by omega) i
  have hk : k % p ^ (i + 1) = k % p ^ i + p ^ i * digit p k i := Nat.mod_pow_succ
  have hm : m % p ^ (i + 1) = m % p ^ i + p ^ i * digit p m i := Nat.mod_pow_succ
  unfold carry
  rw [hk, hm, pow_succ]
  set q := p ^ i with hqdef
  set dk := digit p k i with hdk
  set dm := digit p m i with hdm
  set A := k % q + m % q with hA
  have hAlt : A % q < q := Nat.mod_lt _ hq
  have key : q * (A / q) + A % q = k % q + m % q := by rw [Nat.div_add_mod, hA]
  have hnum :
      k % q + q * dk + (m % q + q * dm) = q * (dk + dm + A / q) + A % q := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  rw [hnum]
  exact div_block hq hAlt _ _

/-! ## The headline Kummer carry-count theorem -/

/-- The number of carries occurring when adding `k` and `m` in base `p`,
counted over positions `1 ≤ i < b`. -/
def numCarries (p k m b : ℕ) : ℕ :=
  #{i ∈ Finset.Ico 1 b | carry p k m i = 1}

/-- **Kummer's theorem (carry-count form).**  The `p`-adic valuation of the
binomial coefficient `C(n, k)` equals the number of carries that occur when
`k` and `n − k` are added in base `p`.  Here `b` is any cutoff exceeding
`log_p n`, so that every nonzero carry position is counted. -/
theorem padicValNat_choose_eq_numCarries
    {p : ℕ} (hp : p.Prime) {n k : ℕ} (hkn : k ≤ n) {b : ℕ} (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) = numCarries p k (n - k) b := by
  have : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < n.choose k := Nat.choose_pos hkn
  have hbridge : (padicValNat p (n.choose k) : ℕ∞) = emultiplicity p (n.choose k) :=
    padicValNat_eq_emultiplicity hpos.ne'
  rw [hp.emultiplicity_choose hkn hnb] at hbridge
  have hfilter :
      #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}
        = numCarries p k (n - k) b := by
    unfold numCarries
    congr 1
    apply Finset.filter_congr
    intro i _
    exact (carry_eq_one_iff hp.one_lt k (n - k) i).symm
  rw [hfilter] at hbridge
  exact_mod_cast hbridge

/-- **Kummer's theorem (carry-sum form).**  Summing the carry bits over all
positions reproduces the `p`-adic valuation. -/
theorem padicValNat_choose_eq_sum_carries
    {p : ℕ} (hp : p.Prime) {n k : ℕ} (hkn : k ≤ n) {b : ℕ} (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) = ∑ i ∈ Finset.Ico 1 b, carry p k (n - k) i := by
  rw [padicValNat_choose_eq_numCarries hp hkn hnb]
  unfold numCarries
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hle := carry_le_one hp.one_lt k (n - k) i
  by_cases h : carry p k (n - k) i = 1
  · simp [h]
  · have h0 : carry p k (n - k) i = 0 := by omega
    simp [h0]

/-! ## Sanity checks (kernel evaluation, no `native_decide`) -/

/-- Adding `3 + 3 = 110₂` in base two produces two carries (at positions 1, 2):
`carry₁ = carry₂ = 1`, `carry₃ = 0`. -/
example : (∑ i ∈ Finset.Ico 1 4, carry 2 3 3 i) = 2 := by decide

/-- Consequently `v₂(C(6,3)) = v₂(20) = 2`. -/
example : padicValNat 2 (Nat.choose 6 3) = 2 := by
  have hlog : Nat.log 2 6 < 4 := Nat.log_lt_of_lt_pow (by norm_num) (by norm_num)
  have h := padicValNat_choose_eq_sum_carries (p := 2) (n := 6) (k := 3)
    (by norm_num) (b := 4) hlog
  rw [h]; decide

end KummerCarryRecurrence
