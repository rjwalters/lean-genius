import Proofs.Erdos53Problem
import Mathlib.Analysis.SpecificLimits.Normed

/-
# Erdős Problem 53 — WIP-01: exponential richness of prime sets (axiom-free)

*Reference:* [erdosproblems.com/53](https://www.erdosproblems.com/53)

Problem 53 (Erdős–Szemerédi 1983, resolved by Chang 2003) asks whether, for every
fixed `k`, a sufficiently large finite set `A ⊆ ℤ` produces at least `|A|^k`
integers representable as sums or products of *distinct* elements. The deep
content — the bound for every `k` uniformly over **all** large `A` — stays
documented (not axiomatized) in `Erdos53Problem.lean`.

This companion sharpens the *easy* direction on a concrete family. The parent file
already proves, for a set `A` of distinct positive primes, that the multiplicative
side alone realises `2^{|A|} - 1` distinct subset products
(`Erdos53.subsetProducts_card_of_prime`). Here we observe that the additive side
contributes one genuinely new value — `0`, the empty subset sum, which is never a
product of positive primes — so the **full** representable set is exponentially
large:

* `subsetProducts_pos_of_prime` — every subset product of positive primes is `> 0`
  (hence `0` is not among them).
* `sumsOrProducts_card_ge_two_pow_of_prime` — `2^{|A|} ≤ |sumsOrProducts A|` for a
  set of distinct positive primes. The single strongest witness to the "easy"
  direction of Problem 53: the count is *exponential*, dwarfing every `|A|^k`.
* `sumsOrProducts_card_prime_pinned` — combined with the parent's trivial upper
  bracket, prime sets are pinned: `2^{|A|} ≤ |sumsOrProducts A| ≤ 2^{|A|+1}`.
* `sq_le_two_pow` — the elementary polynomial-vs-exponential bound `n^2 ≤ 2^n` for
  `n ≥ 4`, by induction (no analysis import).
* `erdosProblem53_prime_of_dominates` / `erdosProblem53_prime_exponent_two` — the
  honest conditional connection: on prime sets the `|A|^k` bound follows the moment
  `|A|^k ≤ 2^{|A|}`, instantiated concretely for `k = 2`, `N₀ = 4`.

All results are axiom-free (`propext / Classical.choice / Quot.sound` only). This is
a witness on the tractable side; Chang's theorem for arbitrary large sets remains
the open crux and is not touched here.
-/

namespace Erdos53

open Finset

/-- Every subset product of a set of **positive** primes is strictly positive.
    A nonempty product of positive integers is positive; the empty subset is
    filtered out of `subsetProducts`, so this covers the whole family — in
    particular `0 ∉ subsetProducts A`. -/
theorem subsetProducts_pos_of_prime {A : Finset ℤ} (hpos : ∀ p ∈ A, 0 < p)
    {x : ℤ} (hx : x ∈ subsetProducts A) : 0 < x := by
  rw [subsetProducts, Finset.mem_image] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSA, _⟩ := hS
  -- `∏_{a ∈ S} a > 0` since every factor is positive (`S ⊆ A`).
  exact Finset.prod_pos (fun a ha => hpos a (hSA ha))

/-- `0` is not a subset product of positive primes (immediate from positivity). -/
theorem zero_not_mem_subsetProducts_of_prime {A : Finset ℤ} (hpos : ∀ p ∈ A, 0 < p) :
    (0 : ℤ) ∉ subsetProducts A :=
  fun h => (lt_irrefl 0) (subsetProducts_pos_of_prime hpos h)

/-- **Exponential richness of prime sets.** For a set `A` of distinct positive
    primes, the number of integers representable as a sum or product of distinct
    elements is at least `2^{|A|}`.

    The parent's `subsetProducts_card_of_prime` gives `2^{|A|} - 1` distinct
    subset products, all positive; adjoining the empty subset **sum** `0` — which
    is not a subset product — yields `2^{|A|}` distinct representable integers, all
    inside `sumsOrProducts A`. This is the strongest possible witness on the easy
    direction of Problem 53: the representable count is *exponential* in `|A|`. -/
theorem sumsOrProducts_card_ge_two_pow_of_prime {A : Finset ℤ}
    (hA : ∀ p ∈ A, Prime p) (hpos : ∀ p ∈ A, 0 < p) :
    2 ^ A.card ≤ (sumsOrProducts A).card := by
  -- `insert 0 (subsetProducts A)` has exactly `2^{|A|}` elements and sits inside
  -- the representable set.
  have hcard : (insert (0 : ℤ) (subsetProducts A)).card = 2 ^ A.card := by
    rw [Finset.card_insert_of_notMem (zero_not_mem_subsetProducts_of_prime hpos),
      subsetProducts_card_of_prime hA hpos]
    exact Nat.sub_add_cancel (Nat.one_le_two_pow)
  have hsub : insert (0 : ℤ) (subsetProducts A) ⊆ sumsOrProducts A := by
    apply Finset.insert_subset
    · exact zero_mem_sumsOrProducts A
    · exact subsetProducts_subset_sumsOrProducts A
  calc 2 ^ A.card = (insert (0 : ℤ) (subsetProducts A)).card := hcard.symm
    _ ≤ (sumsOrProducts A).card := Finset.card_le_card hsub

/-- **Prime sets are pinned between `2^{|A|}` and `2^{|A|+1}`.** Combining the
    exponential lower bound above with the parent's trivial upper bracket
    `sumsOrProducts_card_le`, the representable count of a distinct-positive-prime
    set is squeezed into a single doubling interval. -/
theorem sumsOrProducts_card_prime_pinned {A : Finset ℤ}
    (hA : ∀ p ∈ A, Prime p) (hpos : ∀ p ∈ A, 0 < p) :
    2 ^ A.card ≤ (sumsOrProducts A).card ∧
      (sumsOrProducts A).card ≤ 2 ^ (A.card + 1) :=
  ⟨sumsOrProducts_card_ge_two_pow_of_prime hA hpos, sumsOrProducts_card_le A⟩

/-- **Elementary polynomial-vs-exponential bound.** `n^2 ≤ 2^n` for every `n ≥ 4`,
    proved by induction on `n` with no analysis import. The step uses
    `2·n^2 ≥ (n+1)^2` for `n ≥ 3` (equivalently `n^2 - 2n - 1 ≥ 0`). Used to make
    the Problem-53 connection for prime sets concrete at `k = 2`. -/
theorem sq_le_two_pow : ∀ n : ℕ, 4 ≤ n → n ^ 2 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
      intro h
      rcases Nat.lt_or_ge m 4 with hm | hm
      · -- only `m + 1 = 4` survives `4 ≤ m + 1` with `m < 4`
        interval_cases m <;> simp_all
      · have hstep : m ^ 2 ≤ 2 ^ m := ih hm
        have hexp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
        -- `(m+1)^2 ≤ 2·m^2 ≤ 2·2^m = 2^{m+1}`, the first bound from `m ≥ 3`.
        have hsq : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by nlinarith [hm]
        calc (m + 1) ^ 2 ≤ 2 * m ^ 2 := hsq
          _ ≤ 2 * 2 ^ m := by exact Nat.mul_le_mul_left 2 hstep
          _ = 2 ^ (m + 1) := hexp.symm

/-- **Problem 53 on prime sets, conditional form (honest framing).** If the target
    exponent satisfies `|A|^k ≤ 2^{|A|}`, then a distinct-positive-prime set already
    realises at least `|A|^k` representable integers. This is *not* Chang's theorem
    (which holds for arbitrary large `A`, not just primes) — it records that the
    prime family is never the obstruction, the `|A|^k` bound failing on it only if
    exponential growth itself failed. -/
theorem erdosProblem53_prime_of_dominates {A : Finset ℤ} {k : ℕ}
    (hA : ∀ p ∈ A, Prime p) (hpos : ∀ p ∈ A, 0 < p)
    (hdom : A.card ^ k ≤ 2 ^ A.card) :
    A.card ^ k ≤ (sumsOrProducts A).card :=
  le_trans hdom (sumsOrProducts_card_ge_two_pow_of_prime hA hpos)

/-- **Problem 53 on prime sets, exponent `k = 2`.** With the explicit threshold
    `|A| ≥ 4` (so `sq_le_two_pow` supplies `|A|^2 ≤ 2^{|A|}`), every set of distinct
    positive primes realises at least `|A|^2` representable integers — the first
    superlinear instance, witnessed unconditionally on the prime family. -/
theorem erdosProblem53_prime_exponent_two {A : Finset ℤ}
    (hA : ∀ p ∈ A, Prime p) (hpos : ∀ p ∈ A, 0 < p) (hbig : 4 ≤ A.card) :
    A.card ^ 2 ≤ (sumsOrProducts A).card :=
  erdosProblem53_prime_of_dominates hA hpos (sq_le_two_pow A.card hbig)


open Asymptotics Filter in
/-- **General polynomial-vs-exponential domination.** For every exponent `k` there is a
    threshold `N` beyond which `n^k ≤ 2^n`. Generalises the explicit `sq_le_two_pow`
    (`k = 2`, threshold `4`) to all `k`, via `n^k =o[atTop] 2^n`
    (`isLittleO_pow_const_const_pow_of_one_lt`) cast back to `ℕ`. -/
theorem exists_pow_le_two_pow (k : ℕ) : ∃ N, ∀ n : ℕ, N ≤ n → n ^ k ≤ 2 ^ n := by
  have h : (fun n : ℕ => (n : ℝ) ^ k) =o[atTop] fun n => (2 : ℝ) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k (by norm_num)
  have hev := h.eventuallyLE
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hb
  exact_mod_cast hb

/-- **Problem 53 on prime sets, arbitrary exponent `k` (eventual form).** For each `k`
    there is a threshold `N` such that every set of distinct positive primes with
    `|A| ≥ N` realises at least `|A|^k` representable integers. Generalises
    `erdosProblem53_prime_exponent_two` from `k = 2` to all `k`, so the prime family
    unconditionally exhibits arbitrary polynomial growth of `|sumsOrProducts A|`. -/
theorem erdosProblem53_prime_exponent_eventually (k : ℕ) :
    ∃ N, ∀ (A : Finset ℤ), (∀ p ∈ A, Prime p) → (∀ p ∈ A, 0 < p) → N ≤ A.card →
      A.card ^ k ≤ (sumsOrProducts A).card := by
  obtain ⟨N, hN⟩ := exists_pow_le_two_pow k
  exact ⟨N, fun A hA hpos hbig =>
    erdosProblem53_prime_of_dominates hA hpos (hN _ hbig)⟩


/-!
## Parity separation sharpens the easy-direction constant

The bound `sumsOrProducts_card_ge_two_pow_of_prime` counts the `2^{|A|} - 1`
distinct subset **products** and adjoins the single new subset **sum** `0`,
giving `2^{|A|}`. That uses only *one* additive value. On a set of distinct
**odd** primes we can do strictly better with a genuinely new mechanism —
**parity separation** of the two operations:

* every nonempty subset product of odd numbers is **odd**
  (`subsetProducts_odd_of_odd`);
* `0` and every two-element subset sum `p + q` of odd numbers is **even**.

So the products and this family of even sums are overlap-free. Fixing the least
element `p = min A` and ranging over the two-element subsets `{p, q}`
(`q ≠ p`) yields `|A| - 1` distinct even positive sums, all injective in `q`;
together with `0` that is `|A|` even values, none of them a subset product. The
count therefore jumps from `2^{|A|}` to `2^{|A|} + |A| - 1`
(`sumsOrProducts_card_ge_odd_prime`). This is a lower-order sharpening of the
*easy* direction (it does not touch Chang's theorem for arbitrary large sets),
but the mechanism — the additive and multiplicative sides cannot collide on the
even numbers — is a real structural fact about Problem 53's two operations.
-/

/-- **Odd subset products.** Every nonempty subset product of a set of **odd**
    integers is odd (a product of odd integers is odd). This is the
    multiplicative half of the parity-separation observation: it forces every
    element of `subsetProducts A` into the odd residue class, disjoint from the
    even subset sums used below. -/
theorem subsetProducts_odd_of_odd {A : Finset ℤ} (hodd : ∀ p ∈ A, Odd p)
    {x : ℤ} (hx : x ∈ subsetProducts A) : Odd x := by
  rw [subsetProducts, Finset.mem_image] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSA, _⟩ := hS
  -- a product of odd factors is odd, by induction over the Finset product
  exact Finset.prod_induction id (fun z => Odd z) (fun _ _ ha hb => ha.mul hb)
    odd_one (fun i hi => hodd i (hSA hi))

/-- **Parity-sharpened richness of odd-prime sets.** For a nonempty set `A` of
    distinct **odd** positive primes,
    `2^{|A|} + |A| - 1 ≤ |sumsOrProducts A|` — strictly stronger than
    `sumsOrProducts_card_ge_two_pow_of_prime` (which gives `2^{|A|}`).

    The `2^{|A|} - 1` subset products are all odd; adjoining the `|A|` *even*
    values `{0} ∪ { min A + q : q ∈ A, q ≠ min A }` (which are pairwise distinct
    and never subset products, by parity) adds exactly `|A|` fresh integers. The
    gain over the base bound is the linear term `|A| - 1`. -/
theorem sumsOrProducts_card_ge_odd_prime {A : Finset ℤ}
    (hA : ∀ p ∈ A, Prime p) (hpos : ∀ p ∈ A, 0 < p) (hodd : ∀ p ∈ A, Odd p)
    (hne : A.Nonempty) :
    2 ^ A.card + A.card - 1 ≤ (sumsOrProducts A).card := by
  classical
  set p := A.min' hne with hp_def
  have hpA : p ∈ A := A.min'_mem hne
  -- the even family: `0` together with the star sums `p + q`, `q ∈ A.erase p`.
  set E : Finset ℤ := insert 0 ((A.erase p).image (fun q => p + q)) with hE_def
  -- `E ⊆ subsetSums A`: `0` is the empty sum, `p + q = ({p, q}).sum id`.
  have hEsub : E ⊆ subsetSums A := by
    intro e he
    rw [hE_def, Finset.mem_insert] at he
    rcases he with rfl | he
    · exact zero_mem_subsetSums A
    · rw [Finset.mem_image] at he
      obtain ⟨q, hq, rfl⟩ := he
      have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
      have hqA : q ∈ A := (Finset.mem_erase.mp hq).2
      refine Finset.mem_image.mpr ⟨{p, q}, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpA
        · exact hqA
      · simp [Finset.sum_pair (Ne.symm hqp)]
  -- `|E| = |A|`: the `|A| - 1` distinct star sums plus `0`.
  have hEcard : E.card = A.card := by
    have himg : ((A.erase p).image (fun q => p + q)).card = (A.erase p).card :=
      Finset.card_image_of_injective _ (add_right_injective p)
    have h0 : (0 : ℤ) ∉ (A.erase p).image (fun q => p + q) := by
      rw [Finset.mem_image]
      rintro ⟨q, hq, hq0⟩
      have hqA : q ∈ A := (Finset.mem_erase.mp hq).2
      have := hpos p hpA
      have := hpos q hqA
      omega
    rw [hE_def, Finset.card_insert_of_not_mem h0, himg,
      Finset.card_erase_of_mem hpA]
    have : 1 ≤ A.card := Finset.card_pos.mpr hne
    omega
  -- `E` (all even) is disjoint from `subsetProducts A` (all odd).
  have hdisj : Disjoint E (subsetProducts A) := by
    rw [Finset.disjoint_left]
    intro e heE heP
    have heven : Even e := by
      rw [hE_def, Finset.mem_insert] at heE
      rcases heE with rfl | he
      · exact even_zero
      · rw [Finset.mem_image] at he
        obtain ⟨q, hq, rfl⟩ := he
        have hqA : q ∈ A := (Finset.mem_erase.mp hq).2
        exact (hodd p hpA).add_odd (hodd q hqA)
    exact (Int.even_iff_not_odd.mp heven) (subsetProducts_odd_of_odd hodd heP)
  -- combine: `E ∪ subsetProducts A ⊆ sumsOrProducts A`, disjoint union counts add.
  have hunion : E ∪ subsetProducts A ⊆ sumsOrProducts A :=
    Finset.union_subset (hEsub.trans (subsetSums_subset_sumsOrProducts A))
      (subsetProducts_subset_sumsOrProducts A)
  have hcard : (E ∪ subsetProducts A).card = E.card + (subsetProducts A).card :=
    Finset.card_union_of_disjoint hdisj
  have hPcard : (subsetProducts A).card = 2 ^ A.card - 1 :=
    subsetProducts_card_of_prime hA hpos
  have h1 : 1 ≤ 2 ^ A.card := Nat.one_le_two_pow
  have key : A.card + (2 ^ A.card - 1) ≤ (sumsOrProducts A).card := by
    calc A.card + (2 ^ A.card - 1)
        = E.card + (subsetProducts A).card := by rw [hEcard, hPcard]
      _ = (E ∪ subsetProducts A).card := hcard.symm
      _ ≤ (sumsOrProducts A).card := Finset.card_le_card hunion
  omega


end Erdos53
