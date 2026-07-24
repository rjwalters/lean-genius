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
    rw [hE_def, Finset.card_insert_of_notMem h0, himg,
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
      · exact ⟨0, by norm_num⟩
      · rw [Finset.mem_image] at he
        obtain ⟨q, hq, rfl⟩ := he
        have hqA : q ∈ A := (Finset.mem_erase.mp hq).2
        exact (hodd p hpA).add_odd (hodd q hqA)
    -- an integer cannot be both even and odd
    obtain ⟨r, hr⟩ := heven
    obtain ⟨k, hk⟩ := subsetProducts_odd_of_odd hodd heP
    omega
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


/-!
## Quadratic additive lower bound for arbitrary positive sets (Erdős chain)

Every bound above is specific to the **prime** family — the exponential richness
comes from the multiplicative side (unique factorisation makes subset products
injective). This section proves the first bound in this development that holds for
**arbitrary** sets of distinct positive integers, with no primality whatsoever:

> For any finite `A ⊆ ℤ` with all elements positive,
> `|subsetSums A| ≥ |A|·(|A|+1)/2 + 1`.

This is the classical Erdős subset-sums argument, by induction on `|A|`: remove
the maximum `m = max A` and observe that the `|A|` sums
`{T} ∪ { T - a : a ∈ A, a ≠ m }` (where `T = Σ A`) are pairwise distinct and each
**strictly exceeds** `T - m = Σ (A \ {m})`, which bounds every subset sum of
`A \ {m}` from above. So each induction step contributes `|A|` fresh values on top
of the recursive count, and the triangular number accumulates.

Consequences recorded below:

* `subsetSums_card_ge_quadratic` — `n(n+1) + 2 ≤ 2·|subsetSums A|` (doubled form,
  division-free), hence `n(n+1)/2 + 1 ≤ |subsetSums A|`.
* `sumsOrProducts_card_ge_quadratic` — the same bound for the full representable
  set, i.e. quadratic-in-`|A|` growth for **all** positive sets, the `k = 1` case
  of Problem 53 with a full extra factor `~|A|/2` to spare.
* `sumsOrProducts_card_superlinear` — for every linear rate `C` there is a
  threshold beyond which every positive set satisfies
  `C·|A| ≤ |sumsOrProducts A|`.

The mechanism (monotone chain via top-element removal) is genuinely additive and
independent of the parity/primality separations above. It still falls short of
Chang's theorem — `n(n+1)/2 + 1 < n^2` for `n ≥ 3`, so even `k = 2` over all sets
remains untouched — but it moves the unconditional frontier from "prime sets only"
to "all positive sets".
-/

/-- The full sum `Σ A` is a subset sum (take `S = A` in the powerset). -/
theorem sum_mem_subsetSums (A : Finset ℤ) : A.sum id ∈ subsetSums A := by
  rw [subsetSums, Finset.mem_image]
  exact ⟨A, Finset.mem_powerset.mpr Finset.Subset.rfl, rfl⟩

/-- Dropping a single element from the full sum stays a subset sum:
    `Σ A - a` is the sum over `A.erase a`. -/
theorem sum_sub_mem_subsetSums {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    A.sum id - a ∈ subsetSums A := by
  rw [subsetSums, Finset.mem_image]
  refine ⟨A.erase a, Finset.mem_powerset.mpr (fun x hx => Finset.mem_of_mem_erase hx), ?_⟩
  rw [Finset.sum_erase_eq_sub ha, id_eq]

/-- On a set of **nonnegative** integers, every subset sum is at most the full
    sum `Σ A` (monotonicity of sums under subset inclusion). -/
theorem mem_subsetSums_le_sum {A : Finset ℤ} (hnn : ∀ a ∈ A, 0 ≤ a)
    {s : ℤ} (hs : s ∈ subsetSums A) : s ≤ A.sum id := by
  rw [subsetSums, Finset.mem_image] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_powerset] at hS
  exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun a ha _ => hnn a ha)

/-- **Erdős quadratic bound, induction core.** For any set `A` of `n` distinct
    positive integers, `n(n+1) + 2 ≤ 2·|subsetSums A|` (the division-free form of
    `|subsetSums A| ≥ n(n+1)/2 + 1`).

    Induction on `n`, removing `m = max A`: every subset sum of `A' = A.erase m`
    is at most `T - m` (where `T = Σ A`), while the `n` values
    `{T} ∪ { T - a : a ∈ A', a ≠ m }` are distinct subset sums of `A` strictly
    above `T - m`. So the count grows by at least `n` at each step. -/
theorem subsetSums_card_quadratic :
    ∀ (n : ℕ) (A : Finset ℤ), A.card = n → (∀ a ∈ A, 0 < a) →
      n * (n + 1) + 2 ≤ 2 * (subsetSums A).card := by
  intro n
  induction n with
  | zero =>
      intro A hcard _
      rw [Finset.card_eq_zero] at hcard
      subst hcard
      rw [subsetSums_empty]
      simp
  | succ n ih =>
      intro A hcard hpos
      have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      set m := A.max' hne with hm_def
      have hmA : m ∈ A := A.max'_mem hne
      have hm_pos : 0 < m := hpos m hmA
      set A' := A.erase m with hA'_def
      have hcard' : A'.card = n := by
        rw [hA'_def, Finset.card_erase_of_mem hmA, hcard]
        omega
      have hpos' : ∀ a ∈ A', 0 < a := fun a ha => hpos a (Finset.mem_of_mem_erase ha)
      have IH : n * (n + 1) + 2 ≤ 2 * (subsetSums A').card := ih A' hcard' hpos'
      set T := A.sum id with hT_def
      -- the erased set sums to exactly `T - m`
      have hT' : A'.sum id = T - m := by
        rw [hA'_def, Finset.sum_erase_eq_sub hmA, id_eq]
      -- the `n + 1` "large" subset sums: `T` itself and `T - a` for `a ∈ A'`
      set B : Finset ℤ := insert T (A'.image (fun a => T - a)) with hB_def
      have hBsub : B ⊆ subsetSums A := by
        intro b hb
        rw [hB_def, Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact sum_mem_subsetSums A
        · rw [Finset.mem_image] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          exact sum_sub_mem_subsetSums (Finset.mem_of_mem_erase ha)
      have hBcard : B.card = n + 1 := by
        have himg : (A'.image (fun a => T - a)).card = A'.card :=
          Finset.card_image_of_injective _ sub_right_injective
        have hT_not : T ∉ A'.image (fun a => T - a) := by
          rw [Finset.mem_image]
          rintro ⟨a, ha, haeq⟩
          have := hpos' a ha
          omega
        rw [hB_def, Finset.card_insert_of_notMem hT_not, himg, hcard']
      -- separation: every subset sum of `A'` is `≤ T - m`, every element of `B`
      -- is `> T - m` (for `T - a` because `a < m` by maximality; for `T` because
      -- `m > 0`)
      have hlt : ∀ x ∈ subsetSums A', ∀ b ∈ B, x < b := by
        intro x hx b hb
        have hxle : x ≤ T - m := by
          have h1 := mem_subsetSums_le_sum (fun a ha => (hpos' a ha).le) hx
          rwa [hT'] at h1
        rw [hB_def, Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · omega
        · rw [Finset.mem_image] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          have hane : a ≠ m := (Finset.mem_erase.mp ha).1
          have halt : a < m :=
            lt_of_le_of_ne (A.le_max' a (Finset.mem_of_mem_erase ha)) hane
          omega
      have hdisj : Disjoint (subsetSums A') B := by
        rw [Finset.disjoint_left]
        intro x hx hxB
        exact absurd (hlt x hx x hxB) (lt_irrefl x)
      have hunion : subsetSums A' ∪ B ⊆ subsetSums A :=
        Finset.union_subset
          (subsetSums_mono (fun x hx => Finset.mem_of_mem_erase hx)) hBsub
      have hcount : (subsetSums A').card + (n + 1) ≤ (subsetSums A).card := by
        have h := Finset.card_le_card hunion
        rwa [Finset.card_union_of_disjoint hdisj, hBcard] at h
      nlinarith [IH, hcount]

/-- **Erdős quadratic bound (doubled form).** For any set `A` of distinct positive
    integers, `|A|·(|A|+1) + 2 ≤ 2·|subsetSums A|` — the additive side **alone**
    realises quadratically many values, with no primality assumption. -/
theorem subsetSums_card_ge_quadratic {A : Finset ℤ} (hpos : ∀ a ∈ A, 0 < a) :
    A.card * (A.card + 1) + 2 ≤ 2 * (subsetSums A).card :=
  subsetSums_card_quadratic A.card A rfl hpos

/-- **Erdős quadratic bound (division form).** `|A|·(|A|+1)/2 + 1 ≤ |subsetSums A|`
    for distinct positive integers — the classical triangular-number statement.
    Sharp for `A = {1, 2, …, n}`, whose subset sums are exactly `[0, n(n+1)/2]`. -/
theorem subsetSums_card_ge_quadratic' {A : Finset ℤ} (hpos : ∀ a ∈ A, 0 < a) :
    A.card * (A.card + 1) / 2 + 1 ≤ (subsetSums A).card := by
  have h := subsetSums_card_ge_quadratic hpos
  generalize A.card * (A.card + 1) = q at h ⊢
  omega

/-- **Quadratic growth of the representable set over ALL positive sets.** For any
    finite set of distinct positive integers — no primality, no parity, no
    superincreasing structure — `|A|·(|A|+1) + 2 ≤ 2·|sumsOrProducts A|`. The
    first unconditional bound in this development whose scope matches Problem 53's
    quantifier "for any large `A`" (restricted to positive elements): the easy
    linear bound `card_le_sumsOrProducts` is beaten by a full factor `~|A|/2`. -/
theorem sumsOrProducts_card_ge_quadratic {A : Finset ℤ} (hpos : ∀ a ∈ A, 0 < a) :
    A.card * (A.card + 1) + 2 ≤ 2 * (sumsOrProducts A).card :=
  le_trans (subsetSums_card_ge_quadratic hpos)
    (Nat.mul_le_mul_left 2 (Finset.card_le_card (subsetSums_subset_sumsOrProducts A)))

/-- **Superlinearity over all positive sets.** For every linear rate `C` there is
    a threshold `N` (explicitly `N = 2C`) beyond which every set of distinct
    positive integers satisfies `C·|A| ≤ |sumsOrProducts A|`. Strengthens the
    `k = 1` case of Problem 53 on positive sets from "at least `|A|`" to "at least
    any prescribed multiple of `|A|`". -/
theorem sumsOrProducts_card_superlinear (C : ℕ) :
    ∃ N, ∀ A : Finset ℤ, (∀ a ∈ A, 0 < a) → N ≤ A.card →
      C * A.card ≤ (sumsOrProducts A).card := by
  refine ⟨2 * C, fun A hpos hbig => ?_⟩
  have h := sumsOrProducts_card_ge_quadratic hpos
  have hsq : 2 * C * A.card ≤ A.card * A.card :=
    Nat.mul_le_mul_right A.card hbig
  nlinarith [h, hsq]

/-!
## Quadratic multiplicative lower bound for sets of integers ≥ 2 (product chain)

The quadratic chain above is purely **additive**: it bounds `subsetSums`. This
section proves its exact multiplicative mirror, moving the unconditional
`subsetProducts` frontier from "prime sets only" (`2^{|A|} − 1`, unique
factorisation) to **arbitrary sets of integers `≥ 2`**:

> For any finite `A ⊆ ℤ` with all elements `> 1`,
> `|subsetProducts A| ≥ |A|·(|A|+1)/2`.

Same top-element-removal chain, transposed: remove `m = max A` and observe that
the `|A|` products `{Π A} ∪ { Π (A.erase a) : a ∈ A, a ≠ m }` are pairwise
distinct and each strictly exceeds `Π (A.erase m)`, which bounds every subset
product of `A.erase m` from above. The transposition is not mechanical, because
the multiplicative monoid of `ℤ` is not an ordered monoid (negatives flip
inequalities) and `ℤ` has no exact division:

* "subset product `≤` full product" comes from **divisibility plus positivity**
  (`Finset.prod_dvd_prod_of_subset` + `Int.le_of_dvd`), not sum monotonicity;
* the fresh values are written `Π (A.erase a)` — never `P / a` — and all their
  comparisons go through **cancellation** on `Π (A.erase a) · a = Π A`
  (`mul_left_cancel₀`, `lt_of_mul_lt_mul_right`), not subtraction;
* the elements-`> 1` hypothesis is genuinely needed where the additive chain
  needed only `> 0`: with `1 ∈ A` the fresh value `Π (A.erase 1) = Π A`
  collides with the full product (injectivity dies), matching the additive
  chain's failure at `0 ∈ A`.

The bound differs from the additive one by exactly the missing `+1`:
`subsetProducts` excludes the empty subset (there is no multiplicative
analogue of the free value `0`). It is **sharp**: for the geometric set
`A = {2, 4, …, 2^n}` the subset products are `2^s` for `s` a nonempty subset
sum of `{1, …, n}`, i.e. exactly the `n(n+1)/2` values `2^1, …, 2^{n(n+1)/2}`
(remark, not formalised here). Together with `subsetSums_card_ge_quadratic`
this shows each side of Problem 53 is *individually* quadratic on its natural
domain — the open content of Erdős–Szemerédi/Chang is that sums and products
cannot both stay near-minimal *simultaneously*.
-/

/-- The full product `Π A` is a subset product (take `S = A`), for nonempty `A`. -/
theorem prod_mem_subsetProducts {A : Finset ℤ} (hA : A.Nonempty) :
    A.prod id ∈ subsetProducts A := by
  rw [subsetProducts, Finset.mem_image]
  exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hA⟩, rfl⟩

/-- Erasing one element leaves a subset product, provided something remains:
    `Π (A.erase a) ∈ subsetProducts A` when `A.erase a` is nonempty. -/
theorem prod_erase_mem_subsetProducts {A : Finset ℤ} {a : ℤ} (hne : (A.erase a).Nonempty) :
    (A.erase a).prod id ∈ subsetProducts A := by
  rw [subsetProducts, Finset.mem_image]
  exact ⟨A.erase a, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
    (fun x hx => Finset.mem_of_mem_erase hx), hne⟩, rfl⟩

/-- On a set of **positive** integers every subset product is at most the full
    product `Π A`: a subset product divides the full product
    (`Finset.prod_dvd_prod_of_subset`), and a positive divisor of a positive
    integer is at most it (`Int.le_of_dvd`). The multiplicative counterpart of
    `mem_subsetSums_le_sum` — sum monotonicity is unavailable because `ℤ` under
    `*` is not an ordered monoid. -/
theorem mem_subsetProducts_le_prod {A : Finset ℤ} (hpos : ∀ a ∈ A, 0 < a)
    {x : ℤ} (hx : x ∈ subsetProducts A) : x ≤ A.prod id := by
  rw [subsetProducts, Finset.mem_image] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact Int.le_of_dvd (Finset.prod_pos (fun i hi => hpos i hi))
    (Finset.prod_dvd_prod_of_subset S A id hS.1)

/-- **Multiplicative Erdős chain, induction core.** For any set `A` of `n`
    distinct integers `> 1`, `n(n+1) ≤ 2·|subsetProducts A|` (the division-free
    form of `|subsetProducts A| ≥ n(n+1)/2`).

    Induction on `n`, removing `m = max A`: every subset product of
    `A' = A.erase m` divides — hence is at most — `Q = Π A'`, while the `n`
    values `{Π A} ∪ { Π (A.erase a) : a ∈ A' }` are distinct subset products of
    `A` strictly above `Q`. All comparisons run through cancellation on
    `Π (A.erase a) · a = Π A = Q · m`: from `a < m` and `Q > 0` follows
    `Π (A.erase a) > Q`, and from `m > 1` follows `Π A > Q`. -/
theorem subsetProducts_card_quadratic :
    ∀ (n : ℕ) (A : Finset ℤ), A.card = n → (∀ a ∈ A, 1 < a) →
      n * (n + 1) ≤ 2 * (subsetProducts A).card := by
  intro n
  induction n with
  | zero =>
      intro A hcard _
      simp
  | succ n ih =>
      intro A hcard hgt
      have hpos : ∀ a ∈ A, (0 : ℤ) < a := fun a ha => lt_trans zero_lt_one (hgt a ha)
      have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      set m := A.max' hne with hm_def
      have hmA : m ∈ A := A.max'_mem hne
      set A' := A.erase m with hA'_def
      have hcard' : A'.card = n := by
        rw [hA'_def, Finset.card_erase_of_mem hmA, hcard]
        omega
      have hgt' : ∀ a ∈ A', (1 : ℤ) < a := fun a ha => hgt a (Finset.mem_of_mem_erase ha)
      have hpos' : ∀ a ∈ A', (0 : ℤ) < a := fun a ha => hpos a (Finset.mem_of_mem_erase ha)
      have IH : n * (n + 1) ≤ 2 * (subsetProducts A').card := ih A' hcard' hgt'
      set P := A.prod id with hP_def
      set Q := A'.prod id with hQ_def
      have hQpos : (0 : ℤ) < Q := Finset.prod_pos (fun i hi => hpos' i hi)
      -- the erased set multiplies back up to the full product
      have hQm : Q * m = P := by
        rw [hQ_def, hA'_def, hP_def]
        simpa using Finset.prod_erase_mul A id hmA
      -- the generic one-element-erased product recombination law
      have hRmul : ∀ a ∈ A, (A.erase a).prod id * a = P := by
        intro a ha
        rw [hP_def]
        simpa using Finset.prod_erase_mul A id ha
      -- the `n + 1` "large" subset products: `P` itself and `Π (A.erase a)` for `a ∈ A'`
      set B : Finset ℤ := insert P (A'.image (fun a => (A.erase a).prod id)) with hB_def
      have hBsub : B ⊆ subsetProducts A := by
        intro b hb
        rw [hB_def, Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact prod_mem_subsetProducts hne
        · rw [Finset.mem_image] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          have hma : m ∈ A.erase a :=
            Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp ha).1 h.symm, hmA⟩
          exact prod_erase_mem_subsetProducts ⟨m, hma⟩
      -- each fresh product strictly exceeds `Q`
      have hRgtQ : ∀ a ∈ A', Q < (A.erase a).prod id := by
        intro a ha
        have haA : a ∈ A := Finset.mem_of_mem_erase ha
        have halt : a < m :=
          lt_of_le_of_ne (A.le_max' a haA) (Finset.mem_erase.mp ha).1
        have hkey : Q * a < (A.erase a).prod id * a := by
          calc Q * a < Q * m := mul_lt_mul_of_pos_left halt hQpos
            _ = P := hQm
            _ = (A.erase a).prod id * a := (hRmul a haA).symm
        exact lt_of_mul_lt_mul_right hkey (hpos a haA).le
      have hPgtQ : Q < P := by
        have h1 : Q * 1 < Q * m := mul_lt_mul_of_pos_left (hgt m hmA) hQpos
        rw [mul_one, hQm] at h1
        exact h1
      have hBcard : B.card = n + 1 := by
        have hinj : Set.InjOn (fun a => (A.erase a).prod id) A' := by
          intro a ha b hb hab
          have ha' : a ∈ A' := Finset.mem_coe.mp ha
          have hb' : b ∈ A' := Finset.mem_coe.mp hb
          have haA : a ∈ A := Finset.mem_of_mem_erase ha'
          have hbA : b ∈ A := Finset.mem_of_mem_erase hb'
          have hRpos : (0 : ℤ) < (A.erase a).prod id := lt_trans hQpos (hRgtQ a ha')
          have hab' : (A.erase a).prod id = (A.erase b).prod id := hab
          have h : (A.erase a).prod id * a = (A.erase a).prod id * b := by
            rw [hRmul a haA, hab']
            exact (hRmul b hbA).symm
          exact mul_left_cancel₀ (ne_of_gt hRpos) h
        have himg : (A'.image (fun a => (A.erase a).prod id)).card = A'.card :=
          Finset.card_image_of_injOn hinj
        have hP_not : P ∉ A'.image (fun a => (A.erase a).prod id) := by
          rw [Finset.mem_image]
          rintro ⟨a, ha, haeq⟩
          have haA : a ∈ A := Finset.mem_of_mem_erase ha
          have hRpos : (0 : ℤ) < (A.erase a).prod id := lt_trans hQpos (hRgtQ a ha)
          -- `Π (A.erase a) = P` forces `a = 1`, impossible for elements `> 1`
          have h1 : (A.erase a).prod id * a = (A.erase a).prod id * 1 := by
            rw [mul_one, hRmul a haA, haeq]
          have := mul_left_cancel₀ (ne_of_gt hRpos) h1
          exact absurd this (ne_of_gt (hgt a haA))
        rw [hB_def, Finset.card_insert_of_notMem hP_not, himg, hcard']
      -- separation: every subset product of `A'` is `≤ Q`, every element of `B` is `> Q`
      have hlt : ∀ x ∈ subsetProducts A', ∀ b ∈ B, x < b := by
        intro x hx b hb
        have hxle : x ≤ Q := mem_subsetProducts_le_prod hpos' hx
        rw [hB_def, Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact lt_of_le_of_lt hxle hPgtQ
        · rw [Finset.mem_image] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          exact lt_of_le_of_lt hxle (hRgtQ a ha)
      have hdisj : Disjoint (subsetProducts A') B := by
        rw [Finset.disjoint_left]
        intro x hx hxB
        exact absurd (hlt x hx x hxB) (lt_irrefl x)
      have hunion : subsetProducts A' ∪ B ⊆ subsetProducts A :=
        Finset.union_subset
          (subsetProducts_mono (fun x hx => Finset.mem_of_mem_erase hx)) hBsub
      have hcount : (subsetProducts A').card + (n + 1) ≤ (subsetProducts A).card := by
        have h := Finset.card_le_card hunion
        rwa [Finset.card_union_of_disjoint hdisj, hBcard] at h
      nlinarith [IH, hcount]

/-- **Multiplicative quadratic bound (doubled form).** For any set `A` of
    distinct integers `> 1`, `|A|·(|A|+1) ≤ 2·|subsetProducts A|` — the
    multiplicative side **alone** realises quadratically many values, with no
    primality assumption. Mirror of `subsetSums_card_ge_quadratic`; the missing
    `+2` is the excluded empty subset. -/
theorem subsetProducts_card_ge_quadratic {A : Finset ℤ} (hgt : ∀ a ∈ A, 1 < a) :
    A.card * (A.card + 1) ≤ 2 * (subsetProducts A).card :=
  subsetProducts_card_quadratic A.card A rfl hgt

/-- **Multiplicative quadratic bound (division form).**
    `|A|·(|A|+1)/2 ≤ |subsetProducts A|` for distinct integers `> 1` — sharp for
    the geometric progression `{2, 4, …, 2^n}`, whose subset products are exactly
    `2^1, …, 2^{n(n+1)/2}`. -/
theorem subsetProducts_card_ge_quadratic' {A : Finset ℤ} (hgt : ∀ a ∈ A, 1 < a) :
    A.card * (A.card + 1) / 2 ≤ (subsetProducts A).card := by
  have h := subsetProducts_card_ge_quadratic hgt
  omega

/-
## Sharpness: positivity cannot be weakened to nonzero (negative-elements route refuted)

The Erdős quadratic chain (`subsetSums_card_ge_quadratic'`) assumes every element
positive.  The natural weakening — allow negative elements, requiring only `a ≠ 0`
(the additive mirror of the multiplicative chain excluding `1`) — is FALSE, and not
by an accident of small cases: for EVERY `n ≥ 2` the witness `{-1, 1, 2, …, n-1}`
has all its subset sums inside `[-1, (n-1)n/2]`, hence at most `(n-1)n/2 + 2` of
them, short of the triangular bound `n(n+1)/2 + 1` by a margin growing linearly in
`n`.  Mixed signs permit genuine additive cancellation, and the max-removal chain's
"fresh values above the old total" mechanism is irreparably sign-dependent.  This
closes the last elementary rung recorded for this node: any signed extension needs a
materially different, cancellation-aware mechanism.
-/

/-- Gauss summation, `Icc` form: `2·(1 + 2 + ⋯ + m) = m(m+1)`. -/
theorem two_mul_sum_Icc_id (m : ℕ) : 2 * (Finset.Icc 1 m).sum id = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 k), mul_add, ih, id_eq]
      ring

/-- **Positivity is essential in the additive quadratic chain.**  For every `n ≥ 2`
    there is a set of `n` distinct *nonzero* integers — the single negative element
    `-1` together with `1, 2, …, n-1` — whose subset-sum count violates the
    triangular bound of `subsetSums_card_ge_quadratic'` (stated here in the file's
    doubled form; the failure margin is `2(n-1)`).  So the hypothesis `0 < a`
    cannot be weakened to `a ≠ 0`: one negative element already breaks the bound at
    every size. -/
theorem subsetSums_quadratic_fails_of_negative (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset ℤ, A.card = n ∧ (∀ a ∈ A, a ≠ 0) ∧
      2 * (subsetSums A).card < n * (n + 1) + 2 := by
  classical
  -- The positive part `P = {1, …, n-1}` and the witness `A = insert (-1) P`.
  set P : Finset ℤ := (Finset.Icc 1 (n - 1)).image (fun i : ℕ => (i : ℤ)) with hP
  have hPpos : ∀ a ∈ P, (0 : ℤ) < a := by
    intro a ha
    rw [hP, Finset.mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact_mod_cast (Finset.mem_Icc.mp hi).1
  have hneg : (-1 : ℤ) ∉ P := fun h => absurd (hPpos _ h) (by norm_num)
  refine ⟨insert (-1 : ℤ) P, ?_, ?_, ?_⟩
  · -- `|A| = n`: the `n-1` positives plus the fresh element `-1`.
    rw [Finset.card_insert_of_notMem hneg, hP,
        Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
    omega
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | h
    · norm_num
    · exact ne_of_gt (hPpos a h)
  · -- Every subset sum lies in `[-1, T]` with `T = ∑ P`: the `-1` can lower a sum
    -- by at most `1`, and the positive part contributes at most the full total.
    set T : ℤ := P.sum id with hT
    have hsub : subsetSums (insert (-1 : ℤ) P) ⊆ Finset.Icc (-1 : ℤ) T := by
      intro x hx
      rw [subsetSums, Finset.mem_image] at hx
      obtain ⟨S, hS, rfl⟩ := hx
      rw [Finset.mem_powerset] at hS
      have hS' : S.erase (-1) ⊆ P := by
        intro a ha
        rcases Finset.mem_insert.mp (hS (Finset.mem_of_mem_erase ha)) with h | h
        · exact absurd h (Finset.ne_of_mem_erase ha)
        · exact h
      have h0 : (0 : ℤ) ≤ (S.erase (-1)).sum id :=
        Finset.sum_nonneg fun a ha => le_of_lt (hPpos a (hS' ha))
      have hle : (S.erase (-1)).sum id ≤ T :=
        Finset.sum_le_sum_of_subset_of_nonneg hS'
          (fun a ha _ => le_of_lt (hPpos a ha))
      rw [Finset.mem_Icc]
      by_cases hm : (-1 : ℤ) ∈ S
      · rw [← Finset.insert_erase hm, Finset.sum_insert (Finset.notMem_erase _ _)]
        simp only [id_eq] at h0 hle ⊢
        omega
      · rw [Finset.erase_eq_self.mpr hm] at h0 hle
        exact ⟨le_trans (by norm_num) h0, hle⟩
    -- Count: `|Icc (-1) T| = Tn + 2` where `Tn = 1 + 2 + ⋯ + (n-1)`.
    have hTn : T = (((Finset.Icc 1 (n - 1)).sum id : ℕ) : ℤ) := by
      rw [hT, hP, Finset.sum_image (fun a _ b _ h => Nat.cast_injective h)]
      push_cast
      simp only [id_eq]
    have hIcc : (Finset.Icc (-1 : ℤ) T).card = (Finset.Icc 1 (n - 1)).sum id + 2 := by
      rw [Int.card_Icc, hTn]
      omega
    have hcard : (subsetSums (insert (-1 : ℤ) P)).card ≤ (Finset.Icc 1 (n - 1)).sum id + 2 := by
      rw [← hIcc]
      exact Finset.card_le_card hsub
    -- Gauss + arithmetic: `2·Tn + 4 = (n-1)n + 4 < n(n+1) + 2` for `n ≥ 2`.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hgauss : 2 * (Finset.Icc 1 (m + 2 - 1)).sum id = (m + 1) * (m + 2) := by
      have h := two_mul_sum_Icc_id (m + 1)
      have hred : m + 2 - 1 = m + 1 := rfl
      rw [hred]
      linarith [h]
    nlinarith [hcard, hgauss]

/-- Concrete illustration at the smallest size: `{1, -1}` realises only the three
    subset sums `{0, 1, -1}` — one short of the four demanded of two-element
    positive sets by `subsetSums_card_ge_quadratic'`. -/
theorem subsetSums_pair_neg_card : (subsetSums {(1 : ℤ), -1}).card = 3 := by decide

end Erdos53
