/-
# Erdős Problem #10 — Open Question 02, decidability keystone

**Parent.** Erdős Problem #10 — sums of a prime and powers of 2.

**Open question (oq-02).** *Granville–Soundararajan (1998).* Is every odd
integer `n > 1` the sum of a prime and **at most 3** powers of 2? (open)

## What this file adds

`Erdos10OQ02.lean` (S3) proved the **reduction lemma**: a sum of `≤ k` powers
of two is the same as a sum of `≤ k` *pairwise-distinct* powers of two
(`repWithAtMost_iff_repDistinct`). That collapses repeats but leaves the
exponents a priori unbounded, so it does not yet make membership a *finite*
search.

This file supplies the missing finiteness ingredient — the **exponent bound**
`a < 2^a ≤ n` — and uses it to upgrade the reduction lemma to a fully
**bounded** characterization:

> `n` is a sum of `≤ k` powers of two **iff** there is a `Nodup` multiset of
> exponents, each `≤ n`, of size `≤ k`, whose `powSum` is `n`.

Because the exponents now live in `{0, …, n}` and there are at most `k` of
them, only finitely many candidate multisets remain: membership is decidable.
We also bound the prime side (`p ≤ n`), giving a finite, two-sided search for
`IsPrimePlusKPowers`. This is exactly the shape a `decide`/`native_decide`
membership check consumes to discharge the concrete witnesses (the smallest
even integer needing 3 powers is `906`; Grechuk's `1117175146` is not a prime
plus `≤ 3` powers).

The numerical decision procedure these lemmas describe is validated end-to-end
in `research/problems/erdos-10-oq-02/verify_decidable_membership.py`
(`RepWithAtMost k n ⟺ bounded-distinct ⟺ popcount n ≤ k`; the bounded prime
form reproduces the `905`/`906` caps and the Grechuk witness).

**Build status.** Registered in `Proofs.lean` and machine-checked under the
pinned Lean toolchain. The proofs use only elementary `Multiset` algebra plus
the S3 lemmas.

### The explicit decidable instance (delivered in S5)

The bounded characterization here makes `Decidable (RepWithAtMost k n)` an
exercise, but the actual instance shipped in `Erdos10OQ02Popcount.lean` (S5)
takes a sharper route: rather than the `2^(n+1)`-candidate powerset search
`RepWithAtMost k n ↔ ∃ F ∈ (Finset.range (n+1)).powerset, F.card ≤ k ∧
(∑ a ∈ F, 2^a) = n`, it identifies the minimal distinct-power count with the
binary popcount (`(Nat.bitIndices n).length`), giving an `O(log n)` instance.
With that instance the witnesses `906 ∉ S_3`-style facts close by
`decide`/`native_decide`.

## References

- Granville, A.; Soundararajan, K. (1998). *A binary additive problem of Erdős
  and the order of `2 mod p²`.* Ramanujan J. 2, 283–298.
- Crocker, R. (1971). *On the sum of a prime and of two powers of two.*
  Pacific J. Math. 36, 103–107.
-/

import Mathlib.Tactic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Proofs.Erdos10OQ02

namespace Erdos10OQ02

/-! ## Part V: The exponent bound

The single new ingredient beyond the S3 reduction lemma: an exponent appearing
in a representation of `n` is `< n`, because `a < 2^a` and `2^a` is one of the
summands of `powSum`. -/

/-- `a < 2^a`, proved by elementary induction (no binary-representation API). -/
theorem lt_two_pow_self (a : ℕ) : a < 2 ^ a := by
  induction a with
  | zero => decide
  | succ n ih =>
    have h2 : 0 < 2 ^ n := pow_pos (by norm_num) n
    rw [pow_succ, Nat.mul_two]
    omega

/-- Each summand `2^a` is bounded by the whole sum: if `a ∈ s` then
`2^a ≤ powSum s`. -/
theorem twoPow_le_powSum {a : ℕ} {s : Multiset ℕ} (ha : a ∈ s) :
    2 ^ a ≤ powSum s := by
  show 2 ^ a ≤ (s.map (2 ^ ·)).sum
  exact Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
    (Multiset.mem_map_of_mem _ ha)

/-- **Exponent bound.** Any exponent occurring in a representation of `n` is
strictly less than `n`. -/
theorem exp_lt_of_powSum {a : ℕ} {s : Multiset ℕ} {n : ℕ}
    (ha : a ∈ s) (hsum : powSum s = n) : a < n := by
  have h1 : 2 ^ a ≤ n := hsum ▸ twoPow_le_powSum ha
  have h2 : a < 2 ^ a := lt_two_pow_self a
  omega

/-! ## Part VI: The bounded reduction lemma

Representability by `≤ k` powers of two is equivalent to representability by a
`Nodup` exponent multiset, of size `≤ k`, **all of whose exponents are `≤ n`**.
This pins the search to a finite set of candidate multisets. -/

/-- `n` is a sum of at most `k` powers of two with pairwise-distinct exponents,
each bounded by `n`. -/
def RepBoundedDistinct (k n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.Nodup ∧ s.card ≤ k ∧ (∀ a ∈ s, a ≤ n) ∧ powSum s = n

/-- **Bounded reduction lemma.** `RepWithAtMost` is equivalent to its
distinct-and-exponent-bounded form. The forward direction adds the exponent
bound from `exp_lt_of_powSum` on top of the S3 reduction lemma. -/
theorem repWithAtMost_iff_repBoundedDistinct (k n : ℕ) :
    RepWithAtMost k n ↔ RepBoundedDistinct k n := by
  constructor
  · intro h
    obtain ⟨s, hnd, hcard, hsum⟩ := (repWithAtMost_iff_repDistinct k n).mp h
    refine ⟨s, hnd, hcard, ?_, hsum⟩
    intro a ha
    have := exp_lt_of_powSum ha hsum
    omega
  · rintro ⟨s, _, hcard, _, hsum⟩
    exact ⟨s, hcard, hsum⟩

/-! ## Part VII: Bounding the prime side

In `IsPrimePlusKPowers k n` the prime is `≤ n` and the power-part is `n - p`,
so the search over `p` is finite as well. Combined with Part VI, membership
becomes a finite two-sided search. -/

/-- **Prime-side bound.** `IsPrimePlusKPowers k n` is equivalent to a search
over primes `p ≤ n` with a `≤ k`-power representation of `n - p`. -/
theorem isPrimePlusKPowers_bounded (k n : ℕ) :
    IsPrimePlusKPowers k n ↔
      ∃ p : ℕ, p ≤ n ∧ p.Prime ∧ RepWithAtMost k (n - p) := by
  constructor
  · rintro ⟨p, hp, m, hm, hn⟩
    refine ⟨p, by omega, hp, ?_⟩
    have hnp : n - p = m := by omega
    rwa [hnp]
  · rintro ⟨p, hpn, hp, hm⟩
    exact ⟨p, hp, n - p, hm, by omega⟩

/-- Fully bounded form: distinct, exponent-bounded power-part, prime `≤ n`.
This is the predicate a decision procedure enumerates. -/
theorem isPrimePlusKPowers_iff_bounded_distinct (k n : ℕ) :
    IsPrimePlusKPowers k n ↔
      ∃ p : ℕ, p ≤ n ∧ p.Prime ∧ RepBoundedDistinct k (n - p) := by
  rw [isPrimePlusKPowers_bounded]
  refine exists_congr (fun p => ?_)
  rw [repWithAtMost_iff_repBoundedDistinct]

#check @lt_two_pow_self
#check @exp_lt_of_powSum
#check @repWithAtMost_iff_repBoundedDistinct
#check @isPrimePlusKPowers_iff_bounded_distinct

/-! ## Part VIII: Decidability recipe (the powerset route, superseded by S5)

The explicit `Decidable (RepWithAtMost k n)` instance is the last mechanical
step. This section records the direct powerset route; the instance actually
shipped in `Erdos10OQ02Popcount.lean` (S5) uses the sharper `O(log n)` popcount
characterization instead. The target equivalence, with the search pinned to a
finite `Finset`:

  `RepWithAtMost k n ↔
     ∃ F ∈ (Finset.range (n + 1)).powerset, F.card ≤ k ∧ (∑ a ∈ F, 2 ^ a) = n`

whose right-hand side is `Decidable` (bounded `Finset` existential + decidable
`≤`/`=` on `ℕ`), so `decidable_of_iff _ (the_iff).symm` yields the instance.

Proof of the equivalence (both directions go through
`repWithAtMost_iff_repBoundedDistinct`):

* **→** From `RepBoundedDistinct` take the `Nodup` multiset `s` (card `≤ k`,
  every exponent `≤ n`, `powSum s = n`). Set `F := s.toFinset`.
    - `F ∈ powerset (range (n+1))`: `Finset.mem_powerset` + `Finset.subset_iff`;
      `a ∈ F ↔ a ∈ s` is `Multiset.mem_toFinset`, and `a ≤ n ⟹ a ∈ range (n+1)`
      by `Finset.mem_range` (`omega`).
    - `F.card ≤ k`: `Multiset.toFinset_card_of_nodup hnd`
      (`Data/Finset/Card.lean:188`) rewrites `#F = Multiset.card s ≤ k`.
    - `(∑ a ∈ F, 2^a) = n`: `Finset.sum_eq_multiset_sum` turns the sum into
      `(F.val.map (2^·)).sum`; `F.val = s` because `s` is `Nodup`
      (`Multiset.toFinset_eq hnd : Finset.mk s hnd = s.toFinset`, take `.val`,
      with `Multiset.Nodup.dedup`/`Multiset.toFinset_val`), so it equals
      `powSum s = n`.
* **←** Given `F` with `F.card ≤ k` and `(∑ a ∈ F, 2^a) = n`, set `s := F.val`
  (a `Nodup` multiset). Then `Multiset.card s = #F ≤ k` and
  `powSum s = (F.val.map (2^·)).sum = ∑ a ∈ F, 2^a = n`
  (again `Finset.sum_eq_multiset_sum`), giving `RepWithAtMost` directly
  (`⟨s, hcard, hsum⟩`).

With `Decidable (RepWithAtMost k n)` in hand, `Decidable (RepBoundedDistinct k n)`
and (via `isPrimePlusKPowers_iff_bounded_distinct` + `Nat.decidablePrime` over
`p ∈ Finset.range (n+1)`) `Decidable (IsPrimePlusKPowers k n)` follow, and the
concrete facts `¬ RepWithAtMost 2 905`, `¬ RepWithAtMost 3 906`-style and the
Grechuk witness `¬ IsPrimePlusKPowers 3 1117175146` close by
`decide`/`native_decide`. All arithmetic certified in
`research/problems/erdos-10-oq-02/verify_decidable_membership.py` (ALL CERTS PASS:
905/906 consecutive caps + Grechuk ∉ S₃, ∈ S₄). -/

end Erdos10OQ02
