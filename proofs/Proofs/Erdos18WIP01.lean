/-
  Erdős Problem #18 — Practical Numbers: an infinite family + a necessary condition

  Source: https://erdosproblems.com/18
  Parent: `Proofs/Erdos18Problem.lean` (defines `IsPractical`, `IsRepresentable`,
  `divisors`, `PracticalNumbers` and a handful of finite `decide`-checked examples).

  A positive integer `m` is *practical* if every `1 ≤ k < m` is a sum of distinct
  divisors of `m`. The parent file establishes practicality only for the finitely
  many worked examples `1, 2, 4, 6, 8` (each by `decide`). This file supplies the
  first *structural* results — statements covering infinitely many `m` at once:

  * `repr_lt_two_pow` — every `k < 2^n` is a sum of distinct powers of two drawn
    from `{2^0, …, 2^{n-1}}` (the finite binary-representation lemma).
  * `two_pow_practical` — **every power of two is practical**. This is an
    infinite family of practical numbers, proved once and for all rather than
    case-by-case.
  * `infinite_practicalNumbers` — **there are infinitely many practical numbers**
    (the powers of two, via injectivity of `n ↦ 2^n`).
  * `two_dvd_of_practical` / `even_of_practical` — a matching *necessary* condition:
    any practical `m ≥ 3` is even (to represent `2`, the divisor `2` itself must be
    used, since `1` is the only smaller divisor).

  It then adds a *closure* result — a genuine multiplication rule generating new
  practical numbers from old ones (the simplest instance of the Stewart product
  criterion `n ≤ σ(m) + 1 ⟹ mn practical`, here `n = 2`):

  * `two_mul_practical` — **if `m` is practical then so is `2m`.** Every `k < 2m`
    splits as `k = 2q + r` with `r ∈ {0,1}` and `q ≤ m - 1`; represent `q` by
    divisors of `m`, double that representation (`d ∣ m ⟹ 2d ∣ 2m`) to reach `2q`,
    and add the divisor `1` when `r = 1`.
  * `two_pow_mul_practical` — iterating: `2^n · m` is practical whenever `m` is.
    This produces infinitely many *new* families, e.g. `2^n · 6`, beyond the pure
    powers of two.

  Finally, two structural bounds:

  * `two_mul_sub_one_le_sigma` — for practical `m`, the sum of divisors obeys
    `σ(m) ≥ 2m − 1` (`m − 1` is a sum of proper divisors, plus the divisor `m`).
  * `odd_practical_eq_one` — the only *odd* practical number is `1` (immediate from
    the evenness necessary condition).

  Finally, the reusable inductive brick behind Stewart's product criterion, with a
  sharpening of the representability range it yields:

  * `subsetSum_interval_extend` — if a coin set `S` represents every `k ≤ N` as a
    distinct-subset sum, then adjoining a coin `d ≤ N + 1` (with `d ∉ S`) extends the
    represented interval to every `k ≤ N + d`. This is the general induction step of
    which `two_mul_practical`'s doubling argument is one instance.
  * `representable_le_two_mul_sub_one_of_practical` — for practical `m`, *every*
    `k ≤ 2m − 1` is a sum of distinct divisors of `m` (not merely `k < m`): the proper
    divisors cover `[0, m − 1]`, and adjoining the divisor `m` reaches `2m − 1`. This
    matches the `σ(m) ≥ 2m − 1` bound exactly.

  Folding the extension step along a list yields the full engine behind the
  Stewart–Sierpiński characterisation of practicality:

  * `subsetSum_covers_of_chain` — a *coin chain* (a duplicate-free list in which each
    entry is `≤ 1 +` the sum of all earlier entries) represents, as distinct-subset
    sums, every value up to its total sum. Reverse induction folding
    `subsetSum_interval_extend` from `∅`.
  * `representable_of_chain_divisors` — if such a chain consists of divisors of `m`,
    every `k ≤ (chain sum)` is a sum of distinct divisors of `m`. Exhibiting a divisor
    chain reaching `m − 1` is precisely the sufficient half of Stewart–Sierpiński.
  * `practical_of_divisor_chain` — the criterion packaged as a reusable *test*: one
    divisor chain reaching `m − 1` certifies `m` practical.
  * `twenty_practical`, `twentyeight_practical` — concrete applications. Both `20 = 2²·5`
    and `28 = 2²·7` have a non-practical odd part, so they lie beyond `two_pow_mul_practical`
    (which needs a practical base); the chain engine reaches them directly.

  The chain engine also yields a *multiplicative closure* rule, and — as the
  headline structural theorem — closure directly from practicality itself:

  * `practical_mul_of_chains` — if `a` carries a proper-divisor coin chain reaching
    `a − 1` and `b` a divisor coin chain reaching `b − 1`, then `a·b` is practical
    (witness chain `chain(a) ++ a · chain(b)`).
  * `practical_mul` — **the product of two practical numbers is practical**, with no
    chain hypotheses at all (Stewart 1954). A Euclidean argument: to represent
    `N < a·b`, write `N = q·b + r` with `q < a`, `r < b`; scale a divisor
    representation of `q` (from practicality of `a`) by `b`, and adjoin a divisor
    representation of `r` (from practicality of `b`). The scaled coins are `≥ b`, the
    `r`-coins are `< b`, so the two sets are disjoint and their union sums to `N`.
  * `practical_pow` — consequently every power `m^k` of a practical `m` is practical.

  Finally, the *sharp* form of representability, closing the gap left by the `2m − 1`
  bound above:

  * `finset_chain_covers` — a `Finset`-native coin-covering engine: if every element of a
    finite `S ⊆ ℕ` is at most `1 +` the sum of the strictly smaller elements, then every
    `k ≤ ∑ S` is a distinct-subset sum. Strong induction peeling off `max' S`; no
    sorted-list index bookkeeping.
  * `representable_le_sigma_of_practical` — for practical `m`, **every `k ≤ σ(m) = ∑_{d ∣ m} d`
    is a sum of distinct divisors of `m`.** The full divisor set is a coin chain (for a
    divisor `d`, the smaller divisors already sum to `≥ d − 1`, since `d − 1 < m` is a
    distinct-divisor sum using only divisors `< d`), so `finset_chain_covers` covers
    `[0, σ(m)]` exactly — sharpening `representable_le_two_mul_sub_one_of_practical` up to
    the `two_mul_sub_one_le_sigma` bound.

  Sharp representability in turn unlocks the classical *multiplicative* sufficient
  condition and its most famous corollary:

  * `mul_practical_of_le_succ_sigma` — **Stewart–Sierpiński**: if `m` is practical and
    `1 ≤ n ≤ σ(m) + 1`, then `n · m` is practical. Two-scale coin argument: split
    `q = n·a + b` with `b < n` and `a < m`; represent `b ≤ n − 1 ≤ σ(m)` and
    `a < m ≤ σ(m)` by divisors of `m`, keep the `b`-coins (each `< n`) and scale the
    `a`-coins by `n` (each `≥ n`, all dividing `n·m`), so the two families are disjoint.
  * `factorial_practical` — **every factorial `n!` is practical**: `(k+1)! = (k+1)·k!`
    and `k + 1 ≤ σ(k!) + 1` (since `σ(k!) ≥ k! ≥ k`), so the sufficient condition applies
    at each step from `0! = 1`. A super-exponentially growing infinite family, alongside
    the geometric family of powers of two.
  * `two_pow_mul_three_pow_practical` — the **3-smooth family `2^a · 3^b` (`a ≥ 1`)** is
    practical, by iterating the criterion with multiplier `3` (`3 ≤ σ(2^a·3^b) + 1`
    always holds). It reaches `18 = 2·3²` (`eighteen_practical`), which `practical_mul`
    cannot — `18`'s only nontrivial factorisation `2·9` has the non-practical `9`.

  The characterisation is then closed into a genuine *iff*:

  * `divisor_chain_of_practical` — the **necessary** divisor-gap condition: for practical
    `m`, every divisor `d ∣ m` obeys `d ≤ 1 + ∑_{e ∣ m, e < d} e` (to represent `d − 1 < m`
    only smaller divisors are available). The converse of the `finset_chain_covers`
    sufficiency, previously used only as an inline step inside
    `representable_le_sigma_of_practical`.
  * `practical_of_divisor_chain_condition` — the **sufficient** direction packaged from
    `finset_chain_covers` on the full divisor set.
  * `practical_iff_divisor_chain` — **`m` practical ⟺ `1 ≤ m` and its divisors form a coin
    chain** (each divisor `≤ 1 +` the sum of the smaller divisors). This is the full
    Stewart–Sierpiński characterisation in purely divisor-theoretic form.

  All results are axiom-free (`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`) and contain no `sorry`.
-/

import Mathlib
import Proofs.Erdos18Problem

open Set Finset Function Nat

namespace Erdos18

/- ## An infinite family: powers of two are practical -/

/-- Every `k < 2^n` is a sum of distinct powers of two drawn from `{2^0, …, 2^{n-1}}`.
This is the finite binary-representation fact underlying practicality of `2^n`. -/
theorem repr_lt_two_pow : ∀ (n k : ℕ), k < 2 ^ n →
    ∃ S : Finset ℕ, S ⊆ (Finset.range n).image (2 ^ ·) ∧ S.sum id = k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    simp only [pow_zero, Nat.lt_one_iff] at hk
    subst hk
    exact ⟨∅, by simp, by simp⟩
  | succ n ih =>
    intro k hk
    have hrs : (Finset.range n).image (2 ^ ·) ⊆ (Finset.range (n + 1)).image (2 ^ ·) := by
      apply Finset.image_subset_image
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    by_cases hkn : k < 2 ^ n
    · obtain ⟨S, hS, hsum⟩ := ih k hkn
      exact ⟨S, hS.trans hrs, hsum⟩
    · rw [not_lt] at hkn
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      have hk' : k - 2 ^ n < 2 ^ n := by omega
      obtain ⟨S, hS, hsum⟩ := ih (k - 2 ^ n) hk'
      have hnotmem : 2 ^ n ∉ S := by
        intro hmem
        have hx := hS hmem
        rw [Finset.mem_image] at hx
        obtain ⟨i, hi, hie⟩ := hx
        rw [Finset.mem_range] at hi
        have : (2 : ℕ) ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hi
        omega
      refine ⟨insert (2 ^ n) S, ?_, ?_⟩
      · rw [Finset.insert_subset_iff]
        refine ⟨?_, hS.trans hrs⟩
        rw [Finset.mem_image]
        exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩
      · rw [Finset.sum_insert hnotmem, hsum]
        simp only [id_eq]
        omega

/-- The powers `{2^i : i < n}` are all divisors of `2^n`. -/
theorem image_two_pow_subset_divisors (n : ℕ) :
    (Finset.range n).image (2 ^ ·) ⊆ divisors (2 ^ n) := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range] at hi
  show (2 : ℕ) ^ i ∈ (2 ^ n).divisors
  rw [Nat.mem_divisors]
  exact ⟨pow_dvd_pow 2 (le_of_lt hi), by positivity⟩

/-- **Every power of two is practical.** An infinite family of practical numbers,
proved uniformly (contrast the parent's finite `decide`-checked examples). -/
theorem two_pow_practical (n : ℕ) : IsPractical (2 ^ n) := by
  refine ⟨Nat.one_le_pow n 2 (by norm_num), ?_⟩
  intro k _ hkm
  obtain ⟨S, hS, hsum⟩ := repr_lt_two_pow n k hkm
  exact ⟨S, hS.trans (image_two_pow_subset_divisors n), hsum⟩

/-- **There are infinitely many practical numbers** — namely the powers of two. -/
theorem infinite_practicalNumbers : PracticalNumbers.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 2 ^ n) (Nat.pow_right_injective (le_refl 2))
  intro n
  exact two_pow_practical n

/- ## A matching necessary condition: practical `m ≥ 3` is even -/

/-- **A practical number `m ≥ 3` is even.** To represent `2` as a sum of distinct
divisors of `m`, since `1` is the only divisor below `2`, the divisor `2` itself
must appear — hence `2 ∣ m`. -/
theorem two_dvd_of_practical {m : ℕ} (hm : 3 ≤ m) (h : IsPractical m) : 2 ∣ m := by
  obtain ⟨S, hS, hsum⟩ := h.2 2 (by omega) (by omega)
  have hsub12 : S ⊆ {1, 2} := by
    intro x hx
    have hxdiv : x ∈ m.divisors := hS hx
    have hxpos : 1 ≤ x := Nat.pos_of_mem_divisors hxdiv
    have hxle : x ≤ 2 := by
      have hle := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
      rw [hsum, id_eq] at hle
      exact hle
    interval_cases x <;> simp
  have h2mem : 2 ∈ S := by
    by_contra h2
    have hS1 : S ⊆ {1} := by
      intro x hx
      have hx12 := hsub12 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx12 ⊢
      rcases hx12 with h1 | h2'
      · exact h1
      · exact absurd (h2' ▸ hx) h2
    have hle : S.sum id ≤ ({1} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hS1
    rw [hsum, Finset.sum_singleton, id_eq] at hle
    omega
  exact (Nat.mem_divisors.mp (hS h2mem)).1

/-- Restated: a practical number `m ≥ 3` is `Even`. -/
theorem even_of_practical {m : ℕ} (hm : 3 ≤ m) (h : IsPractical m) : Even m := by
  obtain ⟨c, hc⟩ := two_dvd_of_practical hm h
  exact ⟨c, by omega⟩

/- ## Closure under doubling: `m` practical ⟹ `2m` practical

The core building block is that a representation by divisors of `m` doubles to one
by divisors of `2m`: if `d ∣ m` then `2d ∣ 2m`, so `S ↦ 2·S` sends distinct
divisors of `m` to distinct divisors of `2m` while doubling the subset sum. -/

/-- Doubling a divisor-subset doubles its sum (the map `d ↦ 2d` is injective). -/
theorem sum_image_two_mul (S : Finset ℕ) :
    (S.image (2 * ·)).sum id = 2 * S.sum id := by
  rw [Finset.sum_image (fun a _ b _ hab => by omega), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => rfl)

/-- If `S` is a set of divisors of `m`, then `2·S` is a set of divisors of `2m`
(since `d ∣ m ⟹ 2d ∣ 2m`, and `m ≠ 0` forces `2m ≠ 0`). -/
theorem image_two_mul_subset_divisors {S : Finset ℕ} {m : ℕ} (hS : S ⊆ divisors m) :
    S.image (2 * ·) ⊆ divisors (2 * m) := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have hdm := hS hd
  rw [divisors, Nat.mem_divisors] at hdm
  rw [divisors, Nat.mem_divisors]
  exact ⟨Nat.mul_dvd_mul_left 2 hdm.1, Nat.mul_ne_zero two_ne_zero hdm.2⟩

/-- If `q` is a sum of distinct divisors of `m`, then `2q` is a sum of distinct
divisors of `2m`. -/
theorem repr_two_mul {q m : ℕ} (h : IsRepresentable q m) :
    IsRepresentable (2 * q) (2 * m) := by
  obtain ⟨S, hS, hsum⟩ := h
  exact ⟨S.image (2 * ·), image_two_mul_subset_divisors hS,
    by rw [sum_image_two_mul, hsum]⟩

/-- If `q` is a sum of distinct divisors of `m` (with `m ≥ 1`), then `2q + 1` is a
sum of distinct divisors of `2m`: double the representation of `q`, then adjoin the
divisor `1` (which, being odd, is not among the doubled — hence even — divisors). -/
theorem repr_two_mul_add_one {q m : ℕ} (hm : 1 ≤ m) (h : IsRepresentable q m) :
    IsRepresentable (2 * q + 1) (2 * m) := by
  obtain ⟨S, hS, hsum⟩ := h
  have h1notmem : (1 : ℕ) ∉ S.image (2 * ·) := by
    rw [Finset.mem_image]; rintro ⟨d, _, hd⟩; omega
  refine ⟨insert 1 (S.image (2 * ·)), ?_, ?_⟩
  · rw [Finset.insert_subset_iff]
    refine ⟨?_, image_two_mul_subset_divisors hS⟩
    rw [divisors, Nat.mem_divisors]
    exact ⟨one_dvd _, Nat.mul_ne_zero two_ne_zero (by omega)⟩
  · rw [Finset.sum_insert h1notmem, sum_image_two_mul, hsum]
    simp only [id_eq]; omega

/-- **If `m` is practical, then `2m` is practical.** A concrete new-family generator:
the divisors of `2m` include every divisor `d` of `m` and its double `2d`, which
suffices to represent every `k < 2m`. This is the `n = 2` case of the Stewart
product criterion. -/
theorem two_mul_practical {m : ℕ} (h : IsPractical m) : IsPractical (2 * m) := by
  obtain ⟨hm1, hrep⟩ := h
  refine ⟨by omega, ?_⟩
  intro k _ hk2m
  have hqlt : k / 2 < m := by omega
  have hqrep : IsRepresentable (k / 2) m := by
    rcases Nat.eq_zero_or_pos (k / 2) with hq0 | hqpos
    · rw [hq0]; exact zero_isRepresentable m
    · exact hrep (k / 2) hqpos hqlt
  rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
  · rw [show k = 2 * (k / 2) by omega]; exact repr_two_mul hqrep
  · rw [show k = 2 * (k / 2) + 1 by omega]; exact repr_two_mul_add_one hm1 hqrep

/-- Iterating `two_mul_practical`: `2^n · m` is practical whenever `m` is. -/
theorem two_pow_mul_practical (n : ℕ) {m : ℕ} (h : IsPractical m) :
    IsPractical (2 ^ n * m) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [show 2 ^ (n + 1) * m = 2 * (2 ^ n * m) by ring]
    exact two_mul_practical ih

/-- A concrete new infinite family beyond the powers of two: `2^n · 6` is practical
(e.g. `6, 12, 24, 48, …`). -/
theorem two_pow_mul_six_practical (n : ℕ) : IsPractical (2 ^ n * 6) :=
  two_pow_mul_practical n six_practical

/- ## Structural bounds -/

/-- **For practical `m`, the sum of divisors satisfies `σ(m) ≥ 2m − 1`.** Since `m − 1`
is a sum of divisors, and any such subset must avoid `m` itself (`m > m − 1`), it is a
sum of *proper* divisors; adjoining the divisor `m` gives `σ(m) ≥ (m − 1) + m`. -/
theorem two_mul_sub_one_le_sigma {m : ℕ} (h : IsPractical m) :
    2 * m - 1 ≤ (divisors m).sum id := by
  obtain ⟨hm1, hrep⟩ := h
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · interval_cases m
    simp [divisors, Nat.divisors_one]
  · obtain ⟨S, hS, hsum⟩ := hrep (m - 1) (by omega) (by omega)
    have hmS : m ∉ S := by
      intro hmem
      have hle := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hmem
      rw [hsum, id_eq] at hle
      omega
    have hsub : insert m S ⊆ divisors m := by
      rw [Finset.insert_subset_iff]
      refine ⟨?_, hS⟩
      rw [divisors, Nat.mem_divisors]
      exact ⟨dvd_refl m, by omega⟩
    have hle : (insert m S).sum id ≤ (divisors m).sum id :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_insert hmS, hsum, id_eq] at hle
    omega

/-- **The only odd practical number is `1`.** A practical `m ≥ 3` is even
(`even_of_practical`), so an odd practical number is `< 3`, hence `1`. -/
theorem odd_practical_eq_one {m : ℕ} (h : IsPractical m) (hodd : Odd m) : m = 1 := by
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · obtain ⟨b, hb⟩ := hodd
    have hm1 := h.1
    omega
  · exfalso
    obtain ⟨a, ha⟩ := even_of_practical hge h
    obtain ⟨b, hb⟩ := hodd
    omega

/- ## The interval-covering brick and a sharpened representability range

The engine behind Stewart's product criterion is a single inductive step: if a
finite set `S` of "coins" already represents (as distinct-subset sums) every value
in the interval `[0, N]`, then adjoining one further coin `d ≤ N + 1` extends the
represented interval seamlessly to `[0, N + d]`. (The bound `d ≤ N + 1` is exactly
what prevents a gap opening at `N + 1`.) This is the reusable induction step; the
`two_mul_practical` doubling proof above is one hand-rolled instance of it. -/

/-- **Interval-covering extension step.** If every `k ≤ N` is a distinct-subset sum
of `S`, and `d ∉ S` satisfies `d ≤ N + 1`, then every `k ≤ N + d` is a
distinct-subset sum of `insert d S`. Values `k ≤ N` reuse the old representation;
values `N < k ≤ N + d` take the representation of `k - d ≤ N` and adjoin `d`. -/
theorem subsetSum_interval_extend {S : Finset ℕ} {N d : ℕ}
    (hcov : ∀ k, k ≤ N → ∃ T ⊆ S, T.sum id = k)
    (hdN : d ≤ N + 1) (hdS : d ∉ S) :
    ∀ k, k ≤ N + d → ∃ T ⊆ insert d S, T.sum id = k := by
  intro k hk
  by_cases hkN : k ≤ N
  · obtain ⟨T, hT, hTsum⟩ := hcov k hkN
    exact ⟨T, hT.trans (Finset.subset_insert d S), hTsum⟩
  · rw [not_le] at hkN
    have hkd : k - d ≤ N := by omega
    obtain ⟨T, hT, hTsum⟩ := hcov (k - d) hkd
    have hdT : d ∉ T := fun hmem => hdS (hT hmem)
    refine ⟨insert d T, ?_, ?_⟩
    · rw [Finset.insert_subset_iff]
      exact ⟨Finset.mem_insert_self d S, hT.trans (Finset.subset_insert d S)⟩
    · rw [Finset.sum_insert hdT, hTsum]
      simp only [id_eq]
      omega

/-- **For practical `m`, every `k ≤ 2m − 1` is a sum of distinct divisors of `m`.**
This sharpens the definition (which only asks for `k < m`) by one full multiple of
`m`. Proof: the *proper* divisors `(divisors m).erase m` already represent every
`k ≤ m − 1` (a representation of `k < m` can never use the divisor `m`, being too
large); the divisor `m` itself satisfies `m ≤ (m − 1) + 1`, so `subsetSum_interval_extend`
pushes the represented range out to `(m − 1) + m = 2m − 1`. Compare
`two_mul_sub_one_le_sigma`, which shows `σ(m) ≥ 2m − 1`: the represented range is
exactly as large as that lower bound allows. -/
theorem representable_le_two_mul_sub_one_of_practical {m : ℕ} (h : IsPractical m) :
    ∀ k, k ≤ 2 * m - 1 → IsRepresentable k m := by
  obtain ⟨hm1, hrep⟩ := h
  have hmdvd : m ∈ divisors m := by
    rw [divisors, Nat.mem_divisors]; exact ⟨dvd_refl m, by omega⟩
  -- The proper divisors represent every value below `m`.
  have hcov : ∀ k, k ≤ m - 1 → ∃ T ⊆ (divisors m).erase m, T.sum id = k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact ⟨∅, Finset.empty_subset _, by simp [hk0]⟩
    · obtain ⟨T, hT, hTsum⟩ := hrep k hkpos (by omega)
      refine ⟨T, ?_, hTsum⟩
      intro x hx
      rw [Finset.mem_erase]
      have hxdiv := hT hx
      have hxle : x ≤ k := by
        have hle := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
        rwa [hTsum, id_eq] at hle
      exact ⟨by omega, hxdiv⟩
  -- Adjoin the divisor `m` to reach `2m − 1`.
  have key := subsetSum_interval_extend hcov (d := m)
    (by omega : m ≤ (m - 1) + 1) (Finset.notMem_erase m (divisors m))
  intro k hk
  obtain ⟨T, hT, hTsum⟩ := key k (by omega)
  rw [Finset.insert_erase hmdvd] at hT
  exact ⟨T, hT, hTsum⟩

/- ## The chain-covering engine

Folding `subsetSum_interval_extend` from the empty set along a list of coins yields
the full engine behind Stewart's product criterion: a *coin chain* — a duplicate-free
list in which each coin is at most one more than the sum of all preceding coins — covers
every value up to its total sum. (Reading a coin chain of divisors of `m` from `1`
upward is exactly the Stewart–Sierpiński characterisation of practicality.) -/

/-- **Chain-covering theorem.** If `l` is a duplicate-free list of naturals in which
each entry `l[i]` is at most `1 +` the sum of the entries before it, then every
`k ≤ l.sum` is a distinct-subset sum of `l.toFinset`. Proved by reverse induction on
`l`: the empty list covers `{0}`, and appending a coin `d ≤ 1 + (previous sum)` extends
the covered interval via `subsetSum_interval_extend`. -/
theorem subsetSum_covers_of_chain :
    ∀ (l : List ℕ), l.Nodup →
      (∀ i, (h : i < l.length) → l[i] ≤ 1 + (l.take i).sum) →
      ∀ k, k ≤ l.sum → ∃ T ⊆ l.toFinset, T.sum id = k := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _ _ k hk
    simp only [List.sum_nil, Nat.le_zero] at hk
    exact ⟨∅, by simp, by simp [hk]⟩
  | append_singleton xs d ih =>
    intro hnd hchain
    have hlenapp : (xs ++ [d]).length = xs.length + 1 := by simp
    rw [List.nodup_append] at hnd
    have hxs_nd : xs.Nodup := hnd.1
    have hd_notin : d ∉ xs := fun hmem => hnd.2.2 d hmem d (by simp) rfl
    -- The chain condition restricts to the prefix `xs`.
    have hchain_xs : ∀ i, (h : i < xs.length) → xs[i] ≤ 1 + (xs.take i).sum := by
      intro i hi
      have hi' : i < (xs ++ [d]).length := by rw [hlenapp]; omega
      have hc := hchain i hi'
      rwa [List.getElem_append_left hi, List.take_append_of_le_length (le_of_lt hi)] at hc
    -- The last coin `d` obeys `d ≤ 1 + (sum of the prefix)`.
    have hd_bound : d ≤ 1 + xs.sum := by
      have hlen : xs.length < (xs ++ [d]).length := by rw [hlenapp]; omega
      have hc := hchain xs.length hlen
      rwa [List.getElem_concat_length rfl, List.take_left] at hc
    -- Cover the prefix, then push out by `d`.
    have hcov := ih hxs_nd hchain_xs
    have hd_fin : d ∉ xs.toFinset := by rwa [List.mem_toFinset]
    have hext := subsetSum_interval_extend (S := xs.toFinset) (N := xs.sum) (d := d)
      hcov (by omega) hd_fin
    intro k hk
    have hk' : k ≤ xs.sum + d := by rwa [List.sum_append, List.sum_singleton] at hk
    obtain ⟨T, hT, hTsum⟩ := hext k hk'
    have hset : insert d xs.toFinset = (xs ++ [d]).toFinset := by
      ext a
      simp only [Finset.mem_insert, List.mem_toFinset, List.toFinset_append,
        Finset.mem_union, List.mem_singleton]
      tauto
    exact ⟨T, hset ▸ hT, hTsum⟩

/-- **Bridge to representability.** If a coin chain consists entirely of divisors of
`m`, then every `k ≤ (chain sum)` is a sum of distinct divisors of `m`. Exhibiting such
a chain that reaches `m − 1` is exactly what it takes to prove `m` practical — this is
the sufficient half of the Stewart–Sierpiński criterion. -/
theorem representable_of_chain_divisors {m : ℕ} {l : List ℕ}
    (hdvd : ∀ d ∈ l, d ∈ divisors m) (hnd : l.Nodup)
    (hchain : ∀ i, (h : i < l.length) → l[i] ≤ 1 + (l.take i).sum) :
    ∀ k, k ≤ l.sum → IsRepresentable k m := by
  intro k hk
  obtain ⟨T, hT, hTsum⟩ := subsetSum_covers_of_chain l hnd hchain k hk
  refine ⟨T, ?_, hTsum⟩
  intro x hx
  have hxl := hT hx
  rw [List.mem_toFinset] at hxl
  exact hdvd x hxl

/-- **Practicality test (sufficient half of Stewart–Sierpiński).** To prove `m`
practical it suffices to exhibit *one* duplicate-free coin chain of divisors of `m`
whose running sums never leave a gap (each coin `≤ 1 +` the sum of the earlier ones)
and whose total reaches `m − 1`. Then every `1 ≤ k < m` — indeed every `k ≤ (chain
sum)` — is a distinct-divisor sum by `representable_of_chain_divisors`. This packages
the chain engine into a single reusable criterion. -/
theorem practical_of_divisor_chain {m : ℕ} (hm : 1 ≤ m) {l : List ℕ}
    (hdvd : ∀ d ∈ l, d ∈ divisors m) (hnd : l.Nodup)
    (hchain : ∀ i, (h : i < l.length) → l[i] ≤ 1 + (l.take i).sum)
    (hreach : m - 1 ≤ l.sum) : IsPractical m := by
  refine ⟨hm, fun k hk1 hkm =>
    representable_of_chain_divisors hdvd hnd hchain k (by omega)⟩

/- ## Multiplicative closure

Practical numbers are closed under multiplication. The chain engine makes this
concrete: if `a` has a coin chain of *proper* divisors reaching `a − 1` and `b` has
one of divisors reaching `b − 1`, then interleaving gives a coin chain for `a·b`.
The chain for `a·b` is `chain(a) ++ a · chain(b)`: the `a`-coins cover `[0, ≥ a−1]`,
and each scaled coin `a·e` first fires at value `a ≤ 1 + (a-chain sum)`, so no gap
ever opens. Its total reaches `(a−1) + a·(b−1) = a·b − 1`, certifying `a·b` practical
by `practical_of_divisor_chain`. This is the multiplicative half of the structure
theory of practical numbers (Stewart 1954). -/

/-- Scaling a list of coins by `a` scales its sum by `a`. -/
theorem sum_map_mul_left (a : ℕ) : ∀ (l : List ℕ),
    (l.map (a * ·)).sum = a * l.sum := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **Concatenating coin chains with an offset.** If `l₁` is a coin chain and every
entry of `l₂` is at most `1 +` the running sum *offset by* the whole of `l₁.sum`, then
`l₁ ++ l₂` is a coin chain. (This is exactly the condition needed to graft a second,
"raised" chain onto the end of a first without opening a gap.) -/
theorem chain_append {l₁ l₂ : List ℕ}
    (h₁ : ∀ i, (h : i < l₁.length) → l₁[i] ≤ 1 + (l₁.take i).sum)
    (h₂ : ∀ j, (h : j < l₂.length) → l₂[j] ≤ 1 + l₁.sum + (l₂.take j).sum) :
    ∀ i, (h : i < (l₁ ++ l₂).length) →
      (l₁ ++ l₂)[i] ≤ 1 + ((l₁ ++ l₂).take i).sum := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hi1 : i < l₁.length
  · rw [List.getElem_append_left hi1, List.take_append_of_le_length (le_of_lt hi1)]
    exact h₁ i hi1
  · push_neg at hi1
    obtain ⟨j, rfl⟩ : ∃ j, i = l₁.length + j := ⟨i - l₁.length, by omega⟩
    have hjlt : j < l₂.length := by omega
    have hget : (l₁ ++ l₂)[l₁.length + j]'(by rw [List.length_append]; omega) = l₂[j] := by
      rw [List.getElem_append_right (Nat.le_add_right l₁.length j)]; congr 1; omega
    have htake : ((l₁ ++ l₂).take (l₁.length + j)).sum = l₁.sum + (l₂.take j).sum := by
      rw [List.take_append, List.sum_append, Nat.add_sub_cancel_left,
          List.take_of_length_le (Nat.le_add_right _ _)]
    rw [hget, htake]
    have hc := h₂ j hjlt
    omega

/-- **Multiplicative closure of practical numbers (chain form).** If `la` is a
duplicate-free coin chain of *proper* divisors of `a` (each `< a`) reaching `a − 1`,
and `lb` is a coin chain of divisors of `b` reaching `b − 1`, then `a·b` is practical.
The witnessing chain is `la ++ lb.map (a · ·)`: its entries are all divisors of `a·b`
(the `la`-entries divide `a`, the scaled entries `a·e` divide `a·b`), it is
duplicate-free (the `la`-entries are `< a` while the scaled entries are `≥ a`), it
satisfies the coin-chain condition by `chain_append` (the first scaled coin is `a ≤ 1 +
la.sum`), and its total `la.sum + a·lb.sum ≥ (a−1) + a·(b−1) = a·b − 1`. Hence
`practical_of_divisor_chain` applies. -/
theorem practical_mul_of_chains {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    {la lb : List ℕ}
    (hla_dvd : ∀ d ∈ la, d ∈ divisors a) (hla_lt : ∀ d ∈ la, d < a)
    (hla_nd : la.Nodup)
    (hla_chain : ∀ i, (h : i < la.length) → la[i] ≤ 1 + (la.take i).sum)
    (hla_reach : a - 1 ≤ la.sum)
    (hlb_dvd : ∀ d ∈ lb, d ∈ divisors b) (hlb_nd : lb.Nodup)
    (hlb_chain : ∀ i, (h : i < lb.length) → lb[i] ≤ 1 + (lb.take i).sum)
    (hlb_reach : b - 1 ≤ lb.sum) :
    IsPractical (a * b) := by
  have hab : a * b ≠ 0 := by positivity
  set L := la ++ lb.map (a * ·) with hL
  have ha_le : a ≤ 1 + la.sum := by omega
  apply practical_of_divisor_chain (m := a * b) (by simpa using Nat.mul_le_mul ha hb) (l := L)
  · -- every coin divides `a * b`
    intro d hd
    rw [hL, List.mem_append] at hd
    rcases hd with hd | hd
    · have hd' := Nat.mem_divisors.mp (hla_dvd d hd)
      exact Nat.mem_divisors.mpr ⟨hd'.1.trans ⟨b, rfl⟩, hab⟩
    · rw [List.mem_map] at hd
      obtain ⟨e, he, rfl⟩ := hd
      have hedvd := Nat.mem_divisors.mp (hlb_dvd e he)
      exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_left a hedvd.1, hab⟩
  · -- the concatenated chain is duplicate-free
    rw [hL, List.nodup_append]
    refine ⟨hla_nd, hlb_nd.map (mul_right_injective₀ (by omega : a ≠ 0)), ?_⟩
    intro x hx y hy
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hy
    have hepos : 0 < e := Nat.pos_of_mem_divisors (hlb_dvd e he)
    have hxlt := hla_lt x hx
    have hle : a ≤ a * e := Nat.le_mul_of_pos_right a hepos
    omega
  · -- the coin-chain condition, via `chain_append`
    rw [hL]
    apply chain_append hla_chain
    intro j hj
    rw [List.length_map] at hj
    rw [List.getElem_map, ← List.map_take, sum_map_mul_left]
    have hcj := hlb_chain j hj
    have hmul : a * lb[j] ≤ a * (1 + (lb.take j).sum) := Nat.mul_le_mul (le_refl a) hcj
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · -- the total reaches `a * b - 1`
    rw [hL, List.sum_append, sum_map_mul_left]
    have h3 : a * (b - 1) + a = a * b := by
      cases b with
      | zero => omega
      | succ n => simp [Nat.mul_succ]
    have hmul : a * (b - 1) ≤ a * lb.sum := Nat.mul_le_mul (le_refl a) hlb_reach
    omega

/- ## Full multiplicative closure (directly from practicality)

`practical_mul_of_chains` above takes explicit coin chains as input. In fact
practicality *alone* suffices: the product of any two practical numbers is
practical, with no chain hypotheses. This is the headline structural theorem of
Stewart (1954). The proof is a Euclidean argument. To represent `N < a·b`, write
`N = q·b + r` with `0 ≤ r < b` and `q < a`. Practicality of `a` represents `q` as a
sum of distinct divisors of `a`; scaling that representation by `b` gives distinct
divisors of `a·b` summing to `q·b`, each `≥ b`. Practicality of `b` represents `r`
as a sum of distinct divisors of `b` — hence of `a·b` — each `≤ r < b`. The two coin
sets are disjoint (one lies `≥ b`, the other `< b`), so their union represents
`q·b + r = N`. -/

/-- Scaling a divisor-subset on the right by `b ≥ 1` scales its sum by `b` (the map
`d ↦ d·b` is injective, so `Finset.sum_image` applies). -/
theorem sum_image_mul_right {b : ℕ} (hb : 1 ≤ b) (D : Finset ℕ) :
    (D.image (· * b)).sum id = D.sum id * b := by
  rw [Finset.sum_image (fun x _ y _ h => mul_right_cancel₀ (by omega : b ≠ 0) h),
      Finset.sum_mul]
  simp only [id_eq]

/-- If `D` is a set of divisors of `a`, then `b · D` is a set of divisors of `a·b`
(`d ∣ a ⟹ d·b ∣ a·b`, and `b ≠ 0` keeps `a·b ≠ 0`). The right-scaled analogue of
`image_two_mul_subset_divisors`. -/
theorem image_mul_right_subset_divisors {D : Finset ℕ} {a b : ℕ}
    (hb : b ≠ 0) (hD : D ⊆ divisors a) :
    D.image (· * b) ⊆ divisors (a * b) := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have hdm := Nat.mem_divisors.mp (hD hd)
  exact Nat.mem_divisors.mpr ⟨mul_dvd_mul_right hdm.1 b, Nat.mul_ne_zero hdm.2 hb⟩

/-- **Multiplicative closure of practical numbers (Stewart 1954).** The product of
two practical numbers is practical — proved directly from the definition, with no
coin-chain hypotheses (contrast `practical_mul_of_chains`). To represent an arbitrary
`N < a·b`, split it as `N = q·b + r` with `q < a` and `r < b`: represent `q` by
divisors of `a` and scale by `b` (each scaled coin `≥ b`), represent `r` by divisors
of `b` (each coin `≤ r < b`); the two coin sets are disjoint and their union — all
divisors of `a·b` — sums to `N`. -/
theorem practical_mul {a b : ℕ} (ha : IsPractical a) (hb : IsPractical b) :
    IsPractical (a * b) := by
  obtain ⟨ha1, harep⟩ := ha
  obtain ⟨hb1, hbrep⟩ := hb
  have hb0 : 0 < b := hb1
  have hab0 : a * b ≠ 0 := by positivity
  refine ⟨Nat.one_le_iff_ne_zero.mpr hab0, ?_⟩
  intro N _ hNab
  -- Euclidean split `N = q·b + r`, with `q < a` and `r < b`.
  obtain ⟨q, r, hrb, hNqr⟩ : ∃ q r, r < b ∧ N = q * b + r :=
    ⟨N / b, N % b, Nat.mod_lt N hb0, by
      rw [Nat.mul_comm (N / b) b]; exact (Nat.div_add_mod N b).symm⟩
  have hqa : q < a := by
    by_contra hqa
    rw [not_lt] at hqa
    have : a * b ≤ q * b := Nat.mul_le_mul hqa (le_refl b)
    omega
  -- Represent `q` by divisors of `a` and `r` by divisors of `b`.
  obtain ⟨D, hD, hDsum⟩ : IsRepresentable q a := by
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · rw [hq0]; exact zero_isRepresentable a
    · exact harep q hqpos hqa
  obtain ⟨E, hE, hEsum⟩ : IsRepresentable r b := by
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · rw [hr0]; exact zero_isRepresentable b
    · exact hbrep r hrpos hrb
  -- The scaled coins `b · D` are `≥ b`; the `r`-coins `E` are `< b`; hence disjoint.
  have hD'_ge : ∀ x ∈ D.image (· * b), b ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors (hD hd)
    calc b = 1 * b := (Nat.one_mul b).symm
      _ ≤ d * b := Nat.mul_le_mul hdpos (le_refl b)
  have hE_lt : ∀ y ∈ E, y < b := by
    intro y hy
    have hyle : y ≤ r := by
      have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hy
      rwa [hEsum, id_eq] at this
    omega
  have hdisj : Disjoint (D.image (· * b)) E := by
    rw [Finset.disjoint_left]
    intro z hzD hzE
    have h1 := hD'_ge z hzD
    have h2 := hE_lt z hzE
    omega
  refine ⟨D.image (· * b) ∪ E, ?_, ?_⟩
  · -- every coin divides `a · b`
    apply Finset.union_subset
    · exact image_mul_right_subset_divisors hb0.ne' hD
    · intro y hy
      have hyb := Nat.mem_divisors.mp (hE hy)
      exact Nat.mem_divisors.mpr ⟨hyb.1.trans (dvd_mul_left b a), hab0⟩
  · -- the union sums to `q·b + r = N`
    rw [Finset.sum_union hdisj, sum_image_mul_right hb1 D, hDsum, hEsum]
    omega

/-- **Powers of a practical number are practical.** Immediate from multiplicative
closure by induction: `m^0 = 1` is practical, and `m^{k+1} = m^k · m`. -/
theorem practical_pow {m : ℕ} (h : IsPractical m) : ∀ k, IsPractical (m ^ k)
  | 0 => by simpa using one_practical
  | k + 1 => by rw [pow_succ]; exact practical_mul (practical_pow h k) h

/-- **`48 = 8 · 6` is practical**, directly from multiplicative closure of the two
practical factors (no chain bookkeeping). -/
theorem fortyeight_practical : IsPractical 48 := by
  have h : (48 : ℕ) = 8 * 6 := by norm_num
  rw [h]; exact practical_mul eight_practical six_practical

/-- **`20` is practical** — via the divisor chain `1, 2, 4, 5, 10` (running sums
`1, 3, 7, 12, 22`, each coin at most one past the previous total, reaching `22 ≥ 19`).
Note `20 = 2² · 5`: its odd part `5` is *not* practical, so `20` lies beyond the reach
of `two_pow_mul_practical` (which needs a practical base). The chain engine finds it. -/
theorem twenty_practical : IsPractical 20 := by
  apply practical_of_divisor_chain (m := 20) (l := [1, 2, 4, 5, 10]) (by norm_num)
  · intro d hd; fin_cases hd <;> decide
  · decide
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> simp
  · decide

/-- **`28` is practical** (the perfect number) — via the divisor chain `1, 2, 4, 7, 14`
(running sums `1, 3, 7, 14, 28`, reaching `28 ≥ 27`). As with `20`, the odd part `7` of
`28 = 2² · 7` is not practical, so the doubling lemmas miss it; the chain engine does not. -/
theorem twentyeight_practical : IsPractical 28 := by
  apply practical_of_divisor_chain (m := 28) (l := [1, 2, 4, 7, 14]) (by norm_num)
  · intro d hd; fin_cases hd <;> decide
  · decide
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> simp
  · decide

/-- **`36` is practical** — as the product `6 · 6`, via multiplicative closure. Each
factor `6` carries the proper-divisor coin chain `1, 2, 3` (all `< 6`, reaching
`6 ≥ 5`), so `practical_mul_of_chains` certifies `36 = 2² · 3²`. Note `36` is out of
reach of `two_pow_mul_practical`: writing `36 = 2² · 9`, the odd part `9` is not
practical, so no power-of-two doubling produces it — closure under multiplication
does. -/
theorem thirtysix_practical : IsPractical 36 := by
  have h6 : (36 : ℕ) = 6 * 6 := by norm_num
  rw [h6]
  refine practical_mul_of_chains (a := 6) (b := 6) (by norm_num) (by norm_num)
    (la := [1, 2, 3]) (lb := [1, 2, 3]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro d hd; fin_cases hd <;> decide
  · intro d hd; fin_cases hd <;> decide
  · decide
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> simp
  · decide
  · intro d hd; fin_cases hd <;> decide
  · decide
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i <;> simp
  · decide

/- ## Sharp σ-representability: the coin chain of *all* divisors

`representable_le_two_mul_sub_one_of_practical` reaches only `2m − 1`, while
`two_mul_sub_one_le_sigma` shows the sum of divisors already satisfies `σ(m) ≥ 2m − 1`.
For abundant `m` these differ (e.g. `m = 12`: `2m − 1 = 23 < 28 = σ(12)`). This section
closes the gap: for practical `m`, the *entire* set of divisors — read in increasing
order — is a coin chain, so every `k ≤ σ(m)` is a sum of distinct divisors. The
represented range is then exactly `[0, σ(m)]`, the sharp form of the representability
half of the Stewart–Sierpiński theory.

The engine is a `Finset`-native restatement of the chain-covering theorem, proved by
strong induction peeling off the largest coin, which avoids all sorted-list index
bookkeeping. -/

/-- **Finset coin-covering engine.** If every element `s` of a finite set `S ⊆ ℕ` is at
most `1 +` the sum of the strictly smaller elements of `S`, then every `k ≤ ∑ S` is a
sum of a distinct subset of `S`. Proved by strong induction: peel off the maximum coin
`d = max' S`; the coins below it are exactly `S.erase d`, whose total is `≥ d − 1` by the
chain condition on `d`, so either `k` already fits in `S.erase d` or `k − d` does. -/
theorem finset_chain_covers :
    ∀ (S : Finset ℕ), (∀ s ∈ S, s ≤ 1 + ∑ t ∈ S.filter (· < s), t) →
      ∀ k, k ≤ ∑ s ∈ S, s → ∃ T ⊆ S, ∑ t ∈ T, t = k := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hchain k hk
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      simp only [Finset.sum_empty, Nat.le_zero] at hk
      exact ⟨∅, Finset.empty_subset _, by simp [hk]⟩
    · set d := S.max' hS with hd
      have hdmem : d ∈ S := S.max'_mem hS
      set S' := S.erase d with hS'
      have hS'sub : S' ⊂ S := Finset.erase_ssubset hdmem
      -- Everything strictly below `d` is precisely `S.erase d`.
      have hfil : S.filter (· < d) = S' := by
        ext a
        simp only [hS', Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨haS, had⟩; exact ⟨by omega, haS⟩
        · rintro ⟨hane, haS⟩
          exact ⟨haS, lt_of_le_of_ne (S.le_max' a haS) hane⟩
      -- The chain condition restricts to the smaller set `S'`.
      have hchain' : ∀ s ∈ S', s ≤ 1 + ∑ t ∈ S'.filter (· < s), t := by
        intro s hs
        have hsS : s ∈ S := Finset.mem_of_mem_erase hs
        have hsd : s < d := lt_of_le_of_ne (S.le_max' s hsS) (Finset.ne_of_mem_erase hs)
        have hfe : S'.filter (· < s) = S.filter (· < s) := by
          ext a
          simp only [hS', Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, haS⟩, has⟩; exact ⟨haS, has⟩
          · rintro ⟨haS, has⟩; exact ⟨⟨by omega, haS⟩, has⟩
        rw [hfe]; exact hchain s hsS
      -- The largest coin `d` is `≤ 1 + (sum of the rest)`.
      have hdbound : d ≤ 1 + ∑ t ∈ S', t := by
        have := hchain d hdmem; rwa [hfil] at this
      have hsum' : ∑ t ∈ S, t = (∑ t ∈ S', t) + d :=
        (Finset.sum_erase_add S _ hdmem).symm
      by_cases hkd : k ≤ ∑ t ∈ S', t
      · obtain ⟨T, hT, hTsum⟩ := ih S' hS'sub hchain' k hkd
        exact ⟨T, hT.trans (Finset.erase_subset _ _), hTsum⟩
      · push_neg at hkd
        have hkd2 : k - d ≤ ∑ t ∈ S', t := by omega
        obtain ⟨T, hT, hTsum⟩ := ih S' hS'sub hchain' (k - d) hkd2
        have hdT : d ∉ T := fun h => (Finset.mem_erase.mp (hT h)).1 rfl
        refine ⟨insert d T, ?_, ?_⟩
        · rw [Finset.insert_subset_iff]
          exact ⟨hdmem, hT.trans (Finset.erase_subset _ _)⟩
        · rw [Finset.sum_insert hdT, hTsum]; omega

/-- **Sharp σ-representability.** For practical `m`, *every* `k ≤ σ(m) = ∑_{d ∣ m} d` is a
sum of distinct divisors of `m` — the represented interval is the full `[0, σ(m)]`.

The sorted list of divisors is a coin chain: for a divisor `d`, the value `d − 1 < m` is a
distinct-divisor sum (practicality), and every divisor it uses is `≤ d − 1 < d`, hence lies
among the divisors below `d`; so those sum to `≥ d − 1`, i.e. `d ≤ 1 + ∑_{d' ∣ m, d' < d} d'`.
Feeding this to `finset_chain_covers` covers `[0, σ(m)]`. This strictly sharpens
`representable_le_two_mul_sub_one_of_practical` (which stops at `2m − 1`) up to the exact
bound allowed by `two_mul_sub_one_le_sigma`. -/
theorem representable_le_sigma_of_practical {m : ℕ} (h : IsPractical m) :
    ∀ k, k ≤ ∑ d ∈ divisors m, d → IsRepresentable k m := by
  obtain ⟨hm1, hrep⟩ := h
  -- Every divisor `s` satisfies the chain condition against the smaller divisors.
  have hchain : ∀ s ∈ divisors m, s ≤ 1 + ∑ t ∈ (divisors m).filter (· < s), t := by
    intro s hs
    have hsmem : s ∈ m.divisors := by rw [divisors] at hs; exact hs
    have hsdvd : s ∣ m := (Nat.mem_divisors.mp hsmem).1
    have hspos : 1 ≤ s := Nat.pos_of_mem_divisors hsmem
    have hsm : s ≤ m := Nat.le_of_dvd hm1 hsdvd
    rcases Nat.lt_or_ge s 2 with h1 | h2
    · omega
    · set k := s - 1 with hk
      have hk1 : 1 ≤ k := by omega
      have hkm : k < m := by omega
      obtain ⟨T, hT, hTsum⟩ := hrep k hk1 hkm
      have hTsub : T ⊆ (divisors m).filter (· < s) := by
        intro x hx
        rw [Finset.mem_filter]
        have hxle : x ≤ k := by
          have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
          rwa [hTsum, id_eq] at this
        exact ⟨hT hx, by omega⟩
      have hsum_le : ∑ t ∈ T, t ≤ ∑ t ∈ (divisors m).filter (· < s), t :=
        Finset.sum_le_sum_of_subset hTsub
      have hbridge : ∑ t ∈ T, t = k := by simpa [id_eq] using hTsum
      omega
  intro k hk
  obtain ⟨T, hT, hTsum⟩ := finset_chain_covers (divisors m) hchain k hk
  exact ⟨T, hT, by simpa [id_eq] using hTsum⟩

/- ## The Stewart–Sierpiński sufficient condition and practicality of factorials

The sharp representability lemma `representable_le_sigma_of_practical` unlocks the
classical *multiplicative* sufficient condition of Stewart (1954) and Sierpiński (1955):

* `mul_practical_of_le_succ_sigma` — if `m` is practical and `1 ≤ n ≤ σ(m) + 1`, then
  `n · m` is again practical. The proof is a clean two-scale coin argument. To represent
  `q < n·m`, Euclidean-divide `q = n·a + b` with `0 ≤ b < n` and `0 ≤ a < m`. Since
  `b ≤ n − 1 ≤ σ(m)` and `a < m ≤ σ(m)`, sharp representability writes both `b` and `a`
  as sums of distinct divisors of `m`. Keep the `b`-coins as they are (divisors of `m`,
  hence of `n·m`) and scale the `a`-coins by `n` (each `n·d ∣ n·m`). The `b`-coins sum to
  `b < n` so each is `< n`, while every scaled coin is `≥ n`; the two coin sets are
  therefore disjoint and their union is a set of distinct divisors of `n·m` summing to
  `n·a + b = q`.

* `factorial_practical` — **every factorial `n!` is practical** (a classical fact):
  `(k+1)! = (k+1)·k!` and `k + 1 ≤ σ(k!) + 1` because `σ(k!) ≥ k! ≥ k`, so the sufficient
  condition applies at each step from the base `0! = 1`. This is an infinite family of
  practical numbers of *super-exponential* growth, complementing the geometric family of
  powers of two (`two_pow_practical`).

Both results are axiom-free. -/

/-- **Stewart–Sierpiński sufficient condition.** If `m` is practical and
`1 ≤ n ≤ σ(m) + 1` (where `σ(m) = ∑_{d ∣ m} d`), then `n · m` is practical. -/
theorem mul_practical_of_le_succ_sigma {m n : ℕ} (h : IsPractical m)
    (hn1 : 1 ≤ n) (hn : n ≤ 1 + ∑ d ∈ divisors m, d) :
    IsPractical (n * m) := by
  have hm1 : 1 ≤ m := h.1
  have hnpos : 0 < n := hn1
  have hmpos : 0 < m := hm1
  have hnm1 : 0 < n * m := Nat.mul_pos hnpos hmpos
  have hnm0 : n * m ≠ 0 := by omega
  -- `m ≤ σ(m)`, since `m` is a divisor of itself.
  have hsig_ge : m ≤ ∑ d ∈ divisors m, d := by
    apply Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
    exact Nat.mem_divisors.mpr ⟨dvd_refl m, by omega⟩
  refine ⟨hnm1, ?_⟩
  intro q hq1 hqnm
  -- Euclidean split: `q = n * a + b` with `b < n` and `a < m`.
  set a := q / n with ha
  set b := q % n with hb
  have hbn : b < n := Nat.mod_lt q hnpos
  have hqab : n * a + b = q := Nat.div_add_mod q n
  have ham : a < m := Nat.div_lt_of_lt_mul hqnm
  -- Represent `b ≤ n - 1 ≤ σ(m)` and `a < m ≤ σ(m)` by distinct divisors of `m`.
  obtain ⟨B, hBsub, hBsum⟩ := representable_le_sigma_of_practical h b (by omega)
  obtain ⟨A, hAsub, hAsum⟩ := representable_le_sigma_of_practical h a (by omega)
  -- The large-coin set: scale each `a`-coin by `n`.
  set Aset : Finset ℕ := A.image (fun d => n * d) with hAset
  have hinj : ∀ x ∈ A, ∀ y ∈ A, n * x = n * y → x = y :=
    fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hnpos hxy
  -- Both coin families are divisors of `n * m`.
  have hBdiv : B ⊆ divisors (n * m) := by
    intro x hx
    have hxm : x ∣ m := (Nat.mem_divisors.mp (hBsub hx)).1
    exact Nat.mem_divisors.mpr ⟨hxm.trans (dvd_mul_left m n), hnm0⟩
  have hAdiv : Aset ⊆ divisors (n * m) := by
    intro x hx
    rw [hAset, Finset.mem_image] at hx
    obtain ⟨d, hdA, rfl⟩ := hx
    have hdm : d ∣ m := (Nat.mem_divisors.mp (hAsub hdA)).1
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left n hdm, hnm0⟩
  -- Small coins are `< n` (they sum to `b < n`); large coins are `≥ n`.
  have hBlt : ∀ x ∈ B, x < n := by
    intro x hx
    have hxle : x ≤ b := by
      have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
      rwa [hBsum, id_eq] at this
    omega
  have hAge : ∀ x ∈ Aset, n ≤ x := by
    intro x hx
    rw [hAset, Finset.mem_image] at hx
    obtain ⟨d, hdA, rfl⟩ := hx
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (hAsub hdA)
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * d := Nat.mul_le_mul_left n hd1
  have hdisj : Disjoint B Aset := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    have := hBlt x hxB
    have := hAge x hxA
    omega
  -- Assemble the union and compute its divisor-sum.
  refine ⟨B ∪ Aset, ?_, ?_⟩
  · rw [Finset.union_subset_iff]; exact ⟨hBdiv, hAdiv⟩
  · have hAsetsum : (Aset).sum id = n * a := by
      rw [hAset, Finset.sum_image hinj]
      have : ∑ d ∈ A, id (n * d) = n * ∑ d ∈ A, id d := by
        simp only [id_eq]; rw [Finset.mul_sum]
      rw [this, hAsum]
    rw [Finset.sum_union hdisj, hBsum, hAsetsum]
    omega

/-- **Every factorial is practical.** By the Stewart–Sierpiński sufficient condition,
`(k+1)! = (k+1)·k!` is practical whenever `k! ` is, because `k + 1 ≤ σ(k!) + 1`
(indeed `σ(k!) ≥ k! ≥ k`). Starting from `0! = 1`, induction gives a practical `n!` for
every `n` — an infinite, super-exponentially growing family of practical numbers. -/
theorem factorial_practical : ∀ n : ℕ, IsPractical (n !) := by
  intro n
  induction n with
  | zero => simpa using one_practical
  | succ k ih =>
    rw [Nat.factorial_succ]
    refine mul_practical_of_le_succ_sigma ih (by omega) ?_
    have hfac_le : (k !) ≤ ∑ d ∈ divisors (k !), d := by
      apply Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
      exact Nat.mem_divisors.mpr ⟨dvd_refl _, Nat.factorial_ne_zero k⟩
    have hkfac : k ≤ k ! := Nat.self_le_factorial k
    omega

/-- **The 3-smooth family `2^a · 3^b` (`a ≥ 1`) is practical.** Iterated single-prime
application of `mul_practical_of_le_succ_sigma` with multiplier `n = 3`: at each step
`3 ≤ σ(2^a·3^b) + 1` because `σ(2^a·3^b) ≥ 2^a·3^b ≥ 2`. This reaches numbers such as
`18 = 2·3²` that lie beyond `practical_mul` — `18` is not a product of two practical
numbers (its only nontrivial factorisation `2 · 9` has the non-practical `9`), yet the
criterion certifies it directly. -/
theorem two_pow_mul_three_pow_practical (a b : ℕ) (ha : 1 ≤ a) :
    IsPractical (2 ^ a * 3 ^ b) := by
  induction b with
  | zero => simpa using two_pow_practical a
  | succ b ih =>
    have hrw : 2 ^ a * 3 ^ (b + 1) = 3 * (2 ^ a * 3 ^ b) := by ring
    rw [hrw]
    refine mul_practical_of_le_succ_sigma ih (by omega) ?_
    have h2a : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have hm2 : 2 ≤ 2 ^ a * 3 ^ b :=
      calc 2 = 2 * 1 := (Nat.mul_one 2).symm
        _ ≤ 2 ^ a * 3 ^ b := Nat.mul_le_mul h2a (Nat.one_le_pow b 3 (by norm_num))
    have hsig : 2 ^ a * 3 ^ b ≤ ∑ d ∈ divisors (2 ^ a * 3 ^ b), d := by
      apply Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
      exact Nat.mem_divisors.mpr ⟨dvd_refl _, by positivity⟩
    omega

/-- `18 = 2 · 3²` is practical — a concrete member of the 3-smooth family that
`practical_mul` cannot reach (its odd part `9` is not practical). -/
theorem eighteen_practical : IsPractical 18 := by
  have := two_pow_mul_three_pow_practical 1 2 (le_refl 1)
  norm_num at this
  exact this

/- ## The full Stewart–Sierpiński characterisation (an `iff`)

The sufficiency engine `finset_chain_covers` and the sharp-representability lemma
`representable_le_sigma_of_practical` together pin practicality down to a single
*divisor-gap* condition on the divisor set, giving a complete characterisation:

  `m` is practical  ⟺  `1 ≤ m` and every divisor `d ∣ m` satisfies
  `d ≤ 1 + ∑_{e ∣ m, e < d} e`.

The condition says the sorted divisors `1 = d₁ < d₂ < … < d_τ = m` form a *coin chain*:
each divisor is at most one more than the sum of all smaller divisors, so no gap in the
subset-sum reachability ever opens. This is precisely Stewart's/Sierpiński's criterion,
here in its purely divisor-theoretic (rather than prime-factorisation) form.

* `divisor_chain_of_practical` — the **necessary** half: extracted from the coin-chain
  argument already used inside `representable_le_sigma_of_practical`. If `d ∣ m` with
  `d ≥ 2`, then `d − 1 < m` is a distinct-divisor sum (practicality), and every divisor it
  uses is `≤ d − 1 < d`, so those smaller divisors already sum to `≥ d − 1`.
* `practical_of_divisor_chain_condition` — the **sufficient** half: `finset_chain_covers`
  on the full divisor set covers `[0, σ(m)] ⊇ [0, m)`, hence every `1 ≤ k < m` is
  representable.
* `practical_iff_divisor_chain` — the two directions packaged as an `iff`. -/

/-- **Necessary divisor-gap condition.** If `m` is practical then every divisor `d ∣ m`
satisfies `d ≤ 1 + ∑_{e ∣ m, e < d} e`: to represent `d − 1 < m` only divisors `< d` are
available, so they already sum to at least `d − 1`. This is the converse of the coin-chain
sufficiency `finset_chain_covers`. -/
theorem divisor_chain_of_practical {m : ℕ} (h : IsPractical m) :
    ∀ d ∈ divisors m, d ≤ 1 + ∑ e ∈ (divisors m).filter (· < d), e := by
  obtain ⟨hm1, hrep⟩ := h
  intro s hs
  have hsmem : s ∈ m.divisors := by rw [divisors] at hs; exact hs
  have hsdvd : s ∣ m := (Nat.mem_divisors.mp hsmem).1
  have hspos : 1 ≤ s := Nat.pos_of_mem_divisors hsmem
  have hsm : s ≤ m := Nat.le_of_dvd hm1 hsdvd
  rcases Nat.lt_or_ge s 2 with h1 | h2
  · omega
  · set k := s - 1 with hk
    have hk1 : 1 ≤ k := by omega
    have hkm : k < m := by omega
    obtain ⟨T, hT, hTsum⟩ := hrep k hk1 hkm
    have hTsub : T ⊆ (divisors m).filter (· < s) := by
      intro x hx
      rw [Finset.mem_filter]
      have hxle : x ≤ k := by
        have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
        rwa [hTsum, id_eq] at this
      exact ⟨hT hx, by omega⟩
    have hsum_le : ∑ t ∈ T, t ≤ ∑ t ∈ (divisors m).filter (· < s), t :=
      Finset.sum_le_sum_of_subset hTsub
    have hbridge : ∑ t ∈ T, t = k := by simpa [id_eq] using hTsum
    omega

/-- **Sufficient divisor-gap condition.** If `1 ≤ m` and every divisor `d ∣ m` satisfies
`d ≤ 1 + ∑_{e ∣ m, e < d} e`, then `m` is practical. The full divisor set is a coin chain,
so `finset_chain_covers` represents every `k ≤ σ(m)`, in particular every `1 ≤ k < m`. -/
theorem practical_of_divisor_chain_condition {m : ℕ} (hm1 : 1 ≤ m)
    (hchain : ∀ d ∈ divisors m, d ≤ 1 + ∑ e ∈ (divisors m).filter (· < d), e) :
    IsPractical m := by
  refine ⟨hm1, ?_⟩
  intro k hk1 hkm
  have hmmem : m ∈ divisors m := by
    rw [divisors]; exact Nat.mem_divisors.mpr ⟨dvd_refl _, by omega⟩
  have hksig : k ≤ ∑ d ∈ divisors m, d := by
    have hmle : m ≤ ∑ d ∈ divisors m, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hmmem
    omega
  obtain ⟨T, hT, hTsum⟩ := finset_chain_covers (divisors m) hchain k hksig
  exact ⟨T, hT, by simpa [id_eq] using hTsum⟩

/-- **Stewart–Sierpiński characterisation.** `m` is practical iff `1 ≤ m` and its divisors
form a coin chain: every divisor `d` is at most `1 +` the sum of the strictly smaller
divisors. Combines `divisor_chain_of_practical` (necessity) and
`practical_of_divisor_chain_condition` (sufficiency). -/
theorem practical_iff_divisor_chain {m : ℕ} :
    IsPractical m ↔
      1 ≤ m ∧ ∀ d ∈ divisors m, d ≤ 1 + ∑ e ∈ (divisors m).filter (· < d), e :=
  ⟨fun h => ⟨h.1, divisor_chain_of_practical h⟩,
    fun ⟨hm1, hchain⟩ => practical_of_divisor_chain_condition hm1 hchain⟩

/-- **Consecutive-integer closure.** If `n` is practical then so is `n·(n+1)`. Immediate
from the Stewart–Sierpiński sufficient condition with multiplier `n + 1`: since `n ∣ n`,
`σ(n) ≥ n`, hence `n + 1 ≤ σ(n) + 1`. Iterating produces a rapidly growing family
(`2 → 6 → 42 → …`), the "practical" analogue of Sylvester's sequence. -/
theorem succ_mul_self_practical {n : ℕ} (h : IsPractical n) :
    IsPractical ((n + 1) * n) := by
  refine mul_practical_of_le_succ_sigma h (by omega) ?_
  have hn1 : 1 ≤ n := h.1
  have hnmem : n ∈ divisors n := by
    rw [divisors]; exact Nat.mem_divisors.mpr ⟨dvd_refl _, by omega⟩
  have hnle : n ≤ ∑ d ∈ divisors n, d :=
    Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hnmem
  omega

/- ## Powers of two as a multiplier base: the Euclid-form family

The Stewart–Sierpiński sufficient condition `mul_practical_of_le_succ_sigma` is at its
sharpest when the practical base is a power of two, because there the divisor sum
`σ(2^k)` is *exactly* `2^{k+1} − 1` (the geometric series `1 + 2 + ⋯ + 2^k`). This yields
a clean, easily-applied criterion and, as a corollary, the practicality of every even
perfect number.

* `sum_range_two_pow` / `sum_divisors_two_pow` — `σ(2^k) = 2^{k+1} − 1`.
* `two_pow_mul_practical_of_le` — for every `1 ≤ n ≤ 2^{k+1}`, the number `2^k · n` is
  practical. This is a strict generalisation of `two_mul_practical` (the case `n = 2`) and
  of the ad-hoc families `two_pow_mul_six_practical`.
* `euclid_form_practical` — `2^k · (2^{k+1} − 1)` is practical for every `k`. When
  `2^{k+1} − 1` is a Mersenne prime this is *precisely* Euclid's even perfect number
  (`k = 1 → 6`, `k = 2 → 28`, `k = 4 → 496`, …), so **every even perfect number is
  practical** — recovering `twentyeight_practical` as the uniform special case `k = 2`.

All results are axiom-free. -/

/-- **Geometric series of powers of two.** `∑_{i=0}^{k} 2^i = 2^{k+1} − 1`. -/
theorem sum_range_two_pow (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [pow_succ]; ring
    omega

/-- **The divisor sum of a power of two.** `σ(2^k) = ∑_{d ∣ 2^k} d = 2^{k+1} − 1`. The
divisors of `2^k` are exactly `{2^0, 2^1, …, 2^k}`, whose sum is the geometric series
`sum_range_two_pow`. -/
theorem sum_divisors_two_pow (k : ℕ) :
    ∑ d ∈ divisors (2 ^ k), d = 2 ^ (k + 1) - 1 := by
  rw [divisors, Nat.sum_divisors_prime_pow Nat.prime_two]
  exact sum_range_two_pow k

/-- **Sharp power-of-two multiplier criterion.** For every `1 ≤ n ≤ 2^{k+1}`, the number
`2^k · n` is practical. Immediate from `mul_practical_of_le_succ_sigma` applied to the
practical base `2^k`, since `1 + σ(2^k) = 2^{k+1}`. Generalises `two_mul_practical`
(`n = 2`). -/
theorem two_pow_mul_practical_of_le {k n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ (k + 1)) :
    IsPractical (2 ^ k * n) := by
  have hbase : IsPractical (2 ^ k) := two_pow_practical k
  have hσ : n ≤ 1 + ∑ d ∈ divisors (2 ^ k), d := by
    rw [sum_divisors_two_pow]
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega
  have hres := mul_practical_of_le_succ_sigma hbase hn1 hσ
  rwa [Nat.mul_comm n (2 ^ k)] at hres

/-- **Euclid-form numbers are practical.** `2^k · (2^{k+1} − 1)` is practical for every
`k`. When `2^{k+1} − 1` is prime this is the even perfect number of Euclid's construction,
so this theorem shows in particular that **every even perfect number is practical**. -/
theorem euclid_form_practical (k : ℕ) :
    IsPractical (2 ^ k * (2 ^ (k + 1) - 1)) := by
  have hge : 2 ≤ 2 ^ (k + 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  apply two_pow_mul_practical_of_le
  · omega
  · omega

/-- **`496` is practical** — the third even perfect number, `496 = 2^4 · (2^5 − 1) = 16·31`,
as the Euclid-form instance `k = 4`. -/
theorem four_ninety_six_practical : IsPractical 496 := by
  have h := euclid_form_practical 4
  norm_num at h
  exact h

/- ## Repeated multiplication by a fixed factor

The Stewart–Sierpiński criterion `mul_practical_of_le_succ_sigma` lets us append a single
multiplier `n ≤ σ(m) + 1` to a practical base `m`. A key structural observation is that
this can be *iterated with the same multiplier*: once `n ≤ σ(m) + 1`, the number
`m · nᵇ` is practical for **every** `b`. The point is that multiplying by `n` only enlarges
the divisor sum (`m ∣ m · nᵇ`, so `σ(m) ≤ σ(m · nᵇ)`), so the gap condition `n ≤ σ(·) + 1`
is *preserved* at every step and never has to be re-checked.

* `sigma_le_sigma_of_dvd` — divisor-sum monotonicity: `m ∣ M` (with `M ≠ 0`) implies
  `σ(m) ≤ σ(M)`, since `divisors m ⊆ divisors M`.
* `repeated_mul_practical` — the iteration: `IsPractical m` and `1 ≤ n ≤ σ(m) + 1` imply
  `IsPractical (m · nᵇ)` for all `b`. This subsumes `two_pow_mul_three_pow_practical`
  (take `m = 2^a`, `n = 3`) and, unlike a naive "`k`-smooth numbers are practical" claim,
  keeps the *honest* σ-gap hypothesis — recall `10 = 2 · 5` is **not** practical because
  `5 > σ(2) + 1 = 4`.
* `two_pow_mul_five_pow_practical` — a concrete new family `2^a · 5^b` (for `a ≥ 2`, where
  `5 ≤ σ(2^a) + 1 = 2^{a+1}`), yielding e.g. `hundred_practical` (`100 = 2² · 5²`), a
  number that `practical_mul` cannot reach (it has no factorisation into two nontrivial
  practical numbers).

All results are axiom-free. -/

/-- **Divisor-sum monotonicity under divisibility.** If `m ∣ M` and `M ≠ 0` then
`σ(m) = ∑_{d ∣ m} d ≤ ∑_{d ∣ M} d = σ(M)`, because every divisor of `m` is a divisor of
`M` (`Nat.divisors_subset_of_dvd`) and the summand `id` is nonnegative. -/
theorem sigma_le_sigma_of_dvd {m M : ℕ} (hMne : M ≠ 0) (hdvd : m ∣ M) :
    ∑ d ∈ divisors m, d ≤ ∑ d ∈ divisors M, d := by
  apply Finset.sum_le_sum_of_subset
  exact Nat.divisors_subset_of_dvd hMne hdvd

/-- **Iterated multiplication by a fixed factor preserves practicality.** If `m` is
practical and `1 ≤ n ≤ σ(m) + 1`, then `m · nᵇ` is practical for every `b`. The gap
condition survives each step: `m ∣ m · nᵇ` gives `σ(m) ≤ σ(m · nᵇ)`
(`sigma_le_sigma_of_dvd`), so `n ≤ σ(m) + 1 ≤ σ(m · nᵇ) + 1` and one more application of
`mul_practical_of_le_succ_sigma` appends another factor of `n`. Strictly generalises
`two_pow_mul_three_pow_practical`. -/
theorem repeated_mul_practical {m n : ℕ} (hm : IsPractical m) (hn1 : 1 ≤ n)
    (hnle : n ≤ 1 + ∑ d ∈ divisors m, d) : ∀ b, IsPractical (m * n ^ b) := by
  have hm1 : 1 ≤ m := hm.1
  intro b
  induction b with
  | zero => simpa using hm
  | succ b ih =>
    have hrw : m * n ^ (b + 1) = n * (m * n ^ b) := by ring
    rw [hrw]
    refine mul_practical_of_le_succ_sigma ih hn1 ?_
    have hMne : m * n ^ b ≠ 0 := Nat.mul_ne_zero (by omega) (pow_ne_zero b (by omega))
    have hmono : ∑ d ∈ divisors m, d ≤ ∑ d ∈ divisors (m * n ^ b), d :=
      sigma_le_sigma_of_dvd hMne (dvd_mul_right m (n ^ b))
    omega

/-- **The family `2^a · 5^b` is practical for `a ≥ 2`.** Since `σ(2^a) + 1 = 2^{a+1} ≥ 8 ≥ 5`
whenever `a ≥ 2`, the multiplier `5` satisfies the σ-gap condition, so
`repeated_mul_practical` appends every power `5^b`. Note the constraint `a ≥ 2` is
necessary: `2 · 5 = 10` is **not** practical. -/
theorem two_pow_mul_five_pow_practical (a b : ℕ) (ha : 2 ≤ a) :
    IsPractical (2 ^ a * 5 ^ b) := by
  apply repeated_mul_practical (two_pow_practical a) (by norm_num) ?_ b
  rw [sum_divisors_two_pow]
  have h8 : (8 : ℕ) ≤ 2 ^ (a + 1) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
  omega

/-- `100 = 2² · 5²` is practical — a concrete member of the `2^a · 5^b` family, and one
that `practical_mul` cannot reach: `100` has no factorisation `100 = a · b` with both
`a, b` nontrivial practical numbers (its only practical proper divisors are `1, 2, 4, 20`,
and none of `50, 25` is practical). -/
theorem hundred_practical : IsPractical 100 := by
  have h := two_pow_mul_five_pow_practical 2 2 (le_refl 2)
  norm_num at h
  exact h

/-! ## Primorials are practical

The **primorial** `n#  = ∏_{p ≤ n, p prime} p` (Mathlib's `primorial n`) is the product
of all primes up to `n`. Primorials are a classical family of practical numbers. We prove
`IsPractical (primorial n)` for every `n` — a second infinite family (alongside factorials
and powers of two) generated purely from the Stewart–Sierpiński sufficient condition.

The proof is a clean induction with no appeal to Bertrand's postulate: the only new prime
that can enter `primorial (n+1)` is `n+1` itself, and the gap condition `n+1 ≤ σ(n#) + 1`
holds because `n ≤ n#` (`Nat.le_primorial_self`) and `n# ≤ σ(n#)`. -/

/-- **Recursion for the primorial.** `primorial (n+1)` acquires the factor `n+1` exactly
when `n+1` is prime, and is otherwise unchanged. -/
theorem primorial_succ_eq (n : ℕ) :
    primorial (n + 1) = (if (n + 1).Prime then n + 1 else 1) * primorial n := by
  unfold primorial
  rw [Finset.range_add_one, Finset.filter_insert]
  have hnotmem : (n + 1) ∉ Finset.filter Nat.Prime (Finset.range (n + 1)) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    rintro ⟨h, _⟩; omega
  by_cases hp : (n + 1).Prime
  · rw [if_pos hp, if_pos hp, Finset.prod_insert hnotmem]
  · rw [if_neg hp, if_neg hp, one_mul]

/-- **Every primorial is practical.** By the Stewart–Sierpiński sufficient condition,
`primorial (k+1)` is either `primorial k` (when `k+1` is composite) or `(k+1)·primorial k`
(when `k+1` is prime); in the prime case the multiplier `k+1` satisfies
`k + 1 ≤ σ(primorial k) + 1` since `k ≤ primorial k ≤ σ(primorial k)`
(`Nat.le_primorial_self` and self-divisibility). Starting from `primorial 0 = 1`, induction
gives a practical `primorial n` for every `n` — the classical primorial family, obtained
without Bertrand's postulate. -/
theorem primorial_practical : ∀ n : ℕ, IsPractical (primorial n) := by
  intro n
  induction n with
  | zero => rw [primorial_zero]; exact one_practical
  | succ k ih =>
    rw [primorial_succ_eq]
    by_cases hp : (k + 1).Prime
    · rw [if_pos hp]
      refine mul_practical_of_le_succ_sigma ih (by omega) ?_
      have hsig : primorial k ≤ ∑ d ∈ divisors (primorial k), d := by
        apply Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
        exact Nat.mem_divisors.mpr ⟨dvd_refl _, (primorial_pos k).ne'⟩
      have hle : k ≤ primorial k := le_primorial_self
      omega
    · rw [if_neg hp, one_mul]; exact ih

/-- `210 = 2 · 3 · 5 · 7 = primorial 7` is practical — the product of the first four primes,
and a member of the primorial family that lies beyond the factorial and prime-power families
covered earlier. -/
theorem two_hundred_ten_practical : IsPractical 210 := by
  have h := primorial_practical 7
  have he : primorial 7 = 210 := by decide
  rwa [he] at h

/- ## Bounds on the divisor-completeness index `h`

`h m` (defined in the parent `Erdos18Problem.lean`) is the least size of a
*single* set `S` of divisors of `m` from which every `1 ≤ k < m` can be
assembled as a subset sum — the size of a "universal representing set". This
section supplies the first theorems about it (the parent's "Known Bounds on
h(m)" section is otherwise empty), pinning it between a logarithm and the
divisor count: `log₂ m ≤ h m ≤ d(m)`.

**Caveat — this is not the Erdős prize quantity.** Erdős #18 concerns a
*different* index: the maximum over `k < m` of the *fewest* divisors needed to
represent that particular `k` (Vose 1985: infinitely many `m` with that index
`≪ √(log m)`). The parent `h` is the universal-set size, which
`le_two_pow_h` below shows is always `≥ log₂ m`. In particular the parent's
`conjecture_part2_weak` (`h(n!) < n^ε`) is *false as stated for this `h`*, since
`log₂(n!) = Θ(n log n)` is superpolynomial (see `factorial_le_two_pow_h`). The
subadditivity theorem in `Erdos18OQ01.lean` is correct for this universal-set
`h`, so the resolution is to *rename* the parent `h` and introduce the
max-representation-length index for the conjectures (mechanic follow-up). -/

/-- **Upper bound `h m ≤ d(m)`.** For practical `m`, the full divisor set already
represents every `1 ≤ k < m`, so a universal representing set needs no more
divisors than `m` has. -/
theorem h_le_card_divisors {m : ℕ} (hm : IsPractical m) :
    h m ≤ (divisors m).card := by
  apply Nat.sInf_le
  exact ⟨divisors m, Finset.Subset.refl _, rfl, fun k hk1 hkm => hm.2 k hk1 hkm⟩

/-- **Lower bound `m ≤ 2 ^ h m`.** A universal representing set `S` of size `h m`
admits only `2 ^ |S|` distinct subset sums, yet these must realise the `m`
values `0, 1, …, m − 1`. Hence `log₂ m ≤ h m`. -/
theorem le_two_pow_h {m : ℕ} (hm : IsPractical m) :
    m ≤ 2 ^ h m := by
  have hne : { s : ℕ | ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.card = s ∧
      ∀ k, 1 ≤ k → k < m → ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = k }.Nonempty :=
    ⟨(divisors m).card, divisors m, Finset.Subset.refl _, rfl,
      fun k hk1 hkm => hm.2 k hk1 hkm⟩
  obtain ⟨S, hSdvd, hScard, hScov⟩ := Nat.sInf_mem hne
  have hScard' : S.card = h m := hScard
  have hsub : Finset.range m ⊆ (S.powerset).image (fun T => T.sum id) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _),
        by simp [hk0]⟩
    · obtain ⟨T, hTS, hTsum⟩ := hScov k hk1 hk
      exact Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr hTS, hTsum⟩
  calc m = (Finset.range m).card := (Finset.card_range m).symm
    _ ≤ ((S.powerset).image (fun T => T.sum id)).card := Finset.card_le_card hsub
    _ ≤ (S.powerset).card := Finset.card_image_le
    _ = 2 ^ S.card := Finset.card_powerset S
    _ = 2 ^ h m := by rw [hScard']

/-- **Consequence for factorials.** Applying `le_two_pow_h` to `n !` (practical by
`factorial_practical`): the universal representing-set index satisfies
`n ! ≤ 2 ^ h (n !)`. Because `log₂(n!) = Θ(n log n)` is superpolynomial in `n`,
this refutes the parent's `conjecture_part2_weak` (`h(n!) < n^ε`) *for this `h`* —
formal evidence that the parent `h` is the universal-set size rather than the
Erdős max-representation-length index (Vose `≪ √log m`) the prize concerns. -/
theorem factorial_le_two_pow_h (n : ℕ) : n ! ≤ 2 ^ h (n !) :=
  le_two_pow_h (factorial_practical n)

/- ## The corrected Erdős #18 index `hErdos` (max-representation-length)

The parent `h m` is the **universal representing-set size** — the fewest divisors
that jointly represent *every* `1 ≤ k < m`. `le_two_pow_h` / `factorial_le_two_pow_h`
show it is superpolynomial on factorials (`m ≤ 2 ^ h m`), so it is *not* the quantity
Erdős Problem #18 concerns. The prize index (Vose 1985, `≪ √(log m)` infinitely often)
is the **worst-case fewest-divisors** count: for each `k` take the *minimum* number of
divisors of `m` summing to `k`, then the *maximum* over `1 ≤ k < m`.

This section supplies the correct definition and the elementary sandwich
`1 ≤ hErdos m ≤ h m ≤ d(m)` for practical `m ≥ 2` — pinning the corrected index
below the (over-counting) universal-set index — and re-homes the two prize
conjectures onto `hErdos`. The deep upper bound (`hErdos(n!)` polynomially small,
Vose/Erdős) is stated as a conjecture `Prop`, not proved here. -/

/-- `repLength m k` — the fewest divisors of `m` whose distinct sum is `k`
(`0` at `k = 0`, via the empty set). -/
noncomputable def repLength (m k : ℕ) : ℕ :=
  sInf { t : ℕ | ∃ T : Finset ℕ, T ⊆ divisors m ∧ T.card = t ∧ T.sum id = k }

/-- `hErdos m` — the Erdős #18 index: the worst case, over `1 ≤ k < m`, of the
fewest divisors of `m` needed to represent `k`, i.e. `max_{k < m} repLength m k`.
This — not the universal-set `h` — is the quantity the prize conjectures concern. -/
noncomputable def hErdos (m : ℕ) : ℕ :=
  (Finset.range m).sup (fun k => repLength m k)

/-- For practical `m` and `1 ≤ k < m` the minimum is attained: there is a divisor
set of size exactly `repLength m k` summing to `k`. -/
theorem repLength_spec {m k : ℕ} (hm : IsPractical m) (hk1 : 1 ≤ k) (hkm : k < m) :
    ∃ T : Finset ℕ, T ⊆ divisors m ∧ T.card = repLength m k ∧ T.sum id = k := by
  have hmem : repLength m k ∈ { t : ℕ | ∃ T : Finset ℕ, T ⊆ divisors m ∧
      T.card = t ∧ T.sum id = k } := by
    apply Nat.sInf_mem
    obtain ⟨T, hTsub, hTsum⟩ := hm.2 k hk1 hkm
    exact ⟨T.card, T, hTsub, rfl, hTsum⟩
  exact hmem

/-- **`repLength m k ≤ h m`** for `k < m`. The universal representing set of size
`h m` already represents each individual `k`, so the per-`k` minimum never exceeds
it. -/
theorem repLength_le_h {m k : ℕ} (hm : IsPractical m) (hkm : k < m) :
    repLength m k ≤ h m := by
  have hne : { s : ℕ | ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.card = s ∧
      ∀ k, 1 ≤ k → k < m → ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = k }.Nonempty :=
    ⟨(divisors m).card, divisors m, Finset.Subset.refl _, rfl,
      fun k hk1 hkm => hm.2 k hk1 hkm⟩
  obtain ⟨S, hSdvd, hScard, hScov⟩ := Nat.sInf_mem hne
  have hScard' : S.card = h m := hScard
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · calc repLength m k ≤ 0 :=
          Nat.sInf_le ⟨∅, Finset.empty_subset _, Finset.card_empty, by simp [h0]⟩
      _ ≤ h m := Nat.zero_le _
  · obtain ⟨T, hTS, hTsum⟩ := hScov k hpos hkm
    calc repLength m k ≤ T.card :=
          Nat.sInf_le ⟨T, hTS.trans hSdvd, rfl, hTsum⟩
      _ ≤ S.card := Finset.card_le_card hTS
      _ = h m := hScard'

/-- **`hErdos m ≤ h m`** for practical `m`: the corrected index is dominated by the
universal-set index — formal confirmation that the parent `h` over-counts. -/
theorem hErdos_le_h {m : ℕ} (hm : IsPractical m) : hErdos m ≤ h m := by
  unfold hErdos
  apply Finset.sup_le
  intro k hk
  rw [Finset.mem_range] at hk
  exact repLength_le_h hm hk

/-- **`hErdos m ≤ d(m)`** for practical `m`, chaining `hErdos_le_h` with
`h_le_card_divisors`. -/
theorem hErdos_le_card_divisors {m : ℕ} (hm : IsPractical m) :
    hErdos m ≤ (divisors m).card :=
  (hErdos_le_h hm).trans (h_le_card_divisors hm)

/-- Representing `1` needs at least one divisor (the empty set sums to `0`), so for
`m ≥ 2` we have `1 ≤ repLength m 1`. -/
theorem one_le_repLength_one {m : ℕ} (hm : 2 ≤ m) : 1 ≤ repLength m 1 := by
  rcases Nat.eq_zero_or_pos (repLength m 1) with h0 | h1
  · exfalso
    have hmem : repLength m 1 ∈ { t : ℕ | ∃ T : Finset ℕ, T ⊆ divisors m ∧
        T.card = t ∧ T.sum id = 1 } := by
      apply Nat.sInf_mem
      refine ⟨1, {1}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact Nat.one_mem_divisors.mpr (by omega)
      · simp
      · simp
    rw [h0] at hmem
    obtain ⟨T, _, hTcard, hTsum⟩ := hmem
    rw [Finset.card_eq_zero] at hTcard
    subst hTcard
    simp at hTsum
  · exact h1

/-- **`1 ≤ hErdos m`** for `m ≥ 2`: representing `k = 1` already costs one divisor. -/
theorem one_le_hErdos {m : ℕ} (hm : 2 ≤ m) : 1 ≤ hErdos m := by
  calc 1 ≤ repLength m 1 := one_le_repLength_one hm
    _ ≤ hErdos m := by
        unfold hErdos
        exact Finset.le_sup (by rw [Finset.mem_range]; omega)

/- ## An exact `hErdos` value: powers of two

`hErdos(2^k) = k`. This is the first *exact* value of the corrected Erdős #18 index,
and it is extremal: `k = log₂(2^k)` is the *largest* the index can be for a number of
that size (it always satisfies `hErdos m ≤ h m ≤ d(m)` and here `d(2^k) = k+1`). Powers
of two are the worst case for the index — the diametric opposite of the conjectured
factorial behaviour `hErdos(n!) < n^{o(1)}` (Vose), which this vein leaves deep. -/

/-- The proper power-of-two divisors `{2^0,…,2^{k-1}}` of `2^k` sum to `2^k − 1`. -/
theorem sum_image_two_pow_range (k : ℕ) :
    ((Finset.range k).image (2 ^ ·)).sum id = 2 ^ k - 1 := by
  rw [Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective (le_refl 2) h)]
  cases k with
  | zero => simp
  | succ n => simpa using sum_range_two_pow n

/-- **Any distinct-divisor representation of `2^k − 1` uses at least `k` divisors.**
The divisors of `2^k` are `2^0,…,2^k`; a set summing to `2^k − 1 < 2^k` cannot use `2^k`,
so it lies in `{2^0,…,2^{k-1}}`, which sums to *exactly* `2^k − 1`. Dropping any one of
those `k` powers strictly lowers the sum, so all `k` are required. -/
theorem two_pow_sub_one_card_ge {k : ℕ} {T : Finset ℕ}
    (hT : T ⊆ divisors (2 ^ k)) (hsum : T.sum id = 2 ^ k - 1) : k ≤ T.card := by
  set P := (Finset.range k).image (2 ^ ·) with hP
  have hPcard : P.card = k := by
    rw [hP, Finset.card_image_of_injective _ (Nat.pow_right_injective (le_refl 2)),
      Finset.card_range]
  have hPsum : P.sum id = 2 ^ k - 1 := sum_image_two_pow_range k
  -- Every element of `T` is a proper power of two, so `T ⊆ P`.
  have hTP : T ⊆ P := by
    intro x hxT
    have hxle : x ≤ 2 ^ k - 1 := by
      have hh : x ≤ T.sum id := by
        have hs := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hxT
        simpa using hs
      rw [hsum] at hh
      exact hh
    have hxdvd : x ∣ 2 ^ k := (Nat.mem_divisors.mp (hT hxT)).1
    obtain ⟨j, _hjk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hxdvd
    have hjlt : j < k := by
      by_contra hjc
      rw [not_lt] at hjc
      have h1 : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjc
      have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    rw [hP, Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hjlt, rfl⟩
  -- If `|T| < k = |P|`, `T` misses a power, dropping its sum below `2^k − 1`.
  by_contra hlt
  rw [not_le] at hlt
  have hcardlt : T.card < P.card := by rw [hPcard]; exact hlt
  have hne : T ≠ P := fun h => by rw [h] at hcardlt; exact lt_irrefl _ hcardlt
  obtain ⟨x, hxP, hxnT⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hTP hne)
  have hxpos : 0 < x :=
    Nat.pos_of_mem_divisors (image_two_pow_subset_divisors k hxP)
  have hkey : T.sum id < P.sum id :=
    Finset.sum_lt_sum_of_subset hTP hxP hxnT hxpos (fun j _ _ => Nat.zero_le _)
  rw [hsum, hPsum] at hkey
  exact lt_irrefl _ hkey

/-- **Upper half of `hErdos(2^k) = k`.** Every `j < 2^k` is a sum of at most `k` powers
of two (its binary digits), so `repLength (2^k) j ≤ k`. -/
theorem repLength_two_pow_le {k j : ℕ} (hj : j < 2 ^ k) : repLength (2 ^ k) j ≤ k := by
  obtain ⟨S, hS, hsum⟩ := repr_lt_two_pow k j hj
  have hScard : S.card ≤ k :=
    calc S.card ≤ ((Finset.range k).image (2 ^ ·)).card := Finset.card_le_card hS
      _ ≤ (Finset.range k).card := Finset.card_image_le
      _ = k := Finset.card_range k
  calc repLength (2 ^ k) j ≤ S.card :=
        Nat.sInf_le ⟨S, hS.trans (image_two_pow_subset_divisors k), rfl, hsum⟩
    _ ≤ k := hScard

/-- **Exact `hErdos` for powers of two: `hErdos(2^k) = k`.** The corrected Erdős #18
index of `2^k` equals its `log₂` — the *maximum* possible for a number of that size.
Upper bound: each `j < 2^k` needs at most its `k` binary digits (`repLength_two_pow_le`).
Lower bound: the all-ones value `2^k − 1` needs all `k` powers `2^0,…,2^{k-1}`
(`two_pow_sub_one_card_ge`). -/
theorem hErdos_two_pow (k : ℕ) : hErdos (2 ^ k) = k := by
  refine le_antisymm ?_ ?_
  · unfold hErdos
    apply Finset.sup_le
    intro j hj
    rw [Finset.mem_range] at hj
    exact repLength_two_pow_le hj
  · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]; exact Nat.zero_le _
    · have hk1 : 1 ≤ 2 ^ k - 1 := by
        have h2 : 2 ≤ 2 ^ k :=
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hkpos
        omega
      have hklt : 2 ^ k - 1 < 2 ^ k := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      have hk_le : k ≤ repLength (2 ^ k) (2 ^ k - 1) := by
        unfold repLength
        apply le_csInf
        · obtain ⟨T, hTsub, hTsum⟩ := (two_pow_practical k).2 (2 ^ k - 1) hk1 hklt
          exact ⟨T.card, T, hTsub, rfl, hTsum⟩
        · rintro t ⟨T, hTsub, rfl, hTsum⟩
          exact two_pow_sub_one_card_ge hTsub hTsum
      calc k ≤ repLength (2 ^ k) (2 ^ k - 1) := hk_le
        _ ≤ hErdos (2 ^ k) := by
            unfold hErdos
            exact Finset.le_sup (Finset.mem_range.mpr hklt)

/- ## Subadditivity of the corrected index `hErdos`

`hErdos(a·b) ≤ hErdos a + hErdos b` for practical `a, b`. This is the
multiplicative-subadditivity law for the *correct* Erdős #18 index — the analogue,
for `hErdos`, of the universal-set subadditivity `h(mn) ≤ h(m) + h(n)` that
`Erdos18OQ01` proves for the parent (over-counting) `h`. It is the mechanism behind
the conjectured smallness of `hErdos(n!)`: bounding a product's index by the sum of
its factors' indices is exactly how one controls a factorial through its prime-power
factorisation (Vose's `hErdos(n!) ≪ √log(n!)` is the deep quantitative form, still
out of reach; this brick is its qualitative skeleton). The proof reuses the Euclidean
coin split of `practical_mul` but tracks *cardinalities*: a minimum-size representation
of the quotient scaled by `b`, disjointly unioned with a minimum-size representation of
the remainder. -/

/-- `repLength m 0 = 0`: the empty set of divisors already sums to `0`. -/
theorem repLength_zero (m : ℕ) : repLength m 0 = 0 := by
  have h : repLength m 0 ≤ 0 :=
    Nat.sInf_le ⟨∅, Finset.empty_subset _, Finset.card_empty, by simp⟩
  omega

/-- Sharpened `repLength_spec` also covering `k = 0`: for practical `m` and `k < m`
there is a divisor set of size *exactly* `repLength m k` summing to `k`. -/
theorem repLength_spec' {m k : ℕ} (hm : IsPractical m) (hkm : k < m) :
    ∃ T : Finset ℕ, T ⊆ divisors m ∧ T.card = repLength m k ∧ T.sum id = k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    exact ⟨∅, Finset.empty_subset _, by rw [Finset.card_empty, repLength_zero], by simp⟩
  · exact repLength_spec hm hk1 hkm

/-- **Pointwise product bound for `repLength`.** For practical `a, b` and `N < a·b`,
representing `N = (N/b)·b + N%b` costs at most `repLength a (N/b) + repLength b (N%b)`
divisors of `a·b`: take a minimum-size representation of the quotient by divisors of
`a`, scale it by `b` (coins `≥ b`), and disjointly adjoin a minimum-size representation
of the remainder by divisors of `b` (coins `< b`). -/
theorem repLength_mul_le {a b : ℕ} (ha : IsPractical a) (hb : IsPractical b)
    {N : ℕ} (hN : N < a * b) :
    repLength (a * b) N ≤ repLength a (N / b) + repLength b (N % b) := by
  have hb0 : 0 < b := hb.1
  have ha0 : 0 < a := ha.1
  have hbne : b ≠ 0 := by omega
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero (by omega) hbne
  set q := N / b with hq
  set r := N % b with hr
  have hrb : r < b := Nat.mod_lt N hb0
  have hNqr : N = q * b + r := by
    rw [hq, hr, Nat.mul_comm]; exact (Nat.div_add_mod N b).symm
  have hqa : q < a := by
    by_contra hc
    rw [not_lt] at hc
    have h1 : a * b ≤ q * b := Nat.mul_le_mul hc (le_refl b)
    have h2 : q * b ≤ N := Nat.div_mul_le_self N b
    omega
  obtain ⟨D, hD, hDcard, hDsum⟩ := repLength_spec' ha hqa
  obtain ⟨E, hE, hEcard, hEsum⟩ := repLength_spec' hb hrb
  -- scaled coins `≥ b`; remainder coins `≤ r < b`; hence the two sets are disjoint
  have hD'_ge : ∀ x ∈ D.image (· * b), b ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors (hD hd)
    calc b = 1 * b := (Nat.one_mul b).symm
      _ ≤ d * b := Nat.mul_le_mul hdpos (le_refl b)
  have hE_lt : ∀ y ∈ E, y < b := by
    intro y hy
    have hyle : y ≤ r := by
      have := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hy
      rwa [hEsum, id_eq] at this
    omega
  have hdisj : Disjoint (D.image (· * b)) E := by
    rw [Finset.disjoint_left]
    intro z hzD hzE
    have h1 := hD'_ge z hzD
    have h2 := hE_lt z hzE
    omega
  have hunion_sub : D.image (· * b) ∪ E ⊆ divisors (a * b) := by
    apply Finset.union_subset
    · exact image_mul_right_subset_divisors hbne hD
    · intro y hy
      have hyb := Nat.mem_divisors.mp (hE hy)
      exact Nat.mem_divisors.mpr ⟨hyb.1.trans (dvd_mul_left b a), hab0⟩
  have hunion_sum : (D.image (· * b) ∪ E).sum id = N := by
    rw [Finset.sum_union hdisj, sum_image_mul_right hb.1 D, hDsum, hEsum, hNqr]
  have hunion_card :
      (D.image (· * b) ∪ E).card = repLength a q + repLength b r := by
    rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun x y h => mul_right_cancel₀ hbne h),
        hDcard, hEcard]
  calc repLength (a * b) N
      ≤ (D.image (· * b) ∪ E).card :=
        Nat.sInf_le ⟨_, hunion_sub, rfl, hunion_sum⟩
    _ = repLength a q + repLength b r := hunion_card

/-- **Subadditivity of the corrected Erdős #18 index:**
`hErdos(a·b) ≤ hErdos a + hErdos b` for practical `a, b`. Every `N < a·b` splits as
quotient-plus-remainder, and its `repLength` is bounded by the two factors' `repLength`s
(`repLength_mul_le`), each of which is at most the corresponding `hErdos`. This is the
correct-index counterpart of the parent `Erdos18OQ01` subadditivity for the
universal-set `h`. -/
theorem hErdos_mul_le {a b : ℕ} (ha : IsPractical a) (hb : IsPractical b) :
    hErdos (a * b) ≤ hErdos a + hErdos b := by
  have hb0 : 0 < b := hb.1
  unfold hErdos
  apply Finset.sup_le
  intro N hN
  rw [Finset.mem_range] at hN
  have hqa : N / b < a := by
    by_contra hc
    rw [not_lt] at hc
    have h1 : a * b ≤ (N / b) * b := Nat.mul_le_mul hc (le_refl b)
    have h2 : (N / b) * b ≤ N := Nat.div_mul_le_self N b
    omega
  have hrb : N % b < b := Nat.mod_lt N hb0
  calc repLength (a * b) N
      ≤ repLength a (N / b) + repLength b (N % b) := repLength_mul_le ha hb hN
    _ ≤ (Finset.range a).sup (fun k => repLength a k)
          + (Finset.range b).sup (fun k => repLength b k) :=
        Nat.add_le_add (Finset.le_sup (Finset.mem_range.mpr hqa))
          (Finset.le_sup (Finset.mem_range.mpr hrb))

/-- **`hErdos(m^k) ≤ k · hErdos m`** for practical `m`: iterate subadditivity. A clean
qualitative consequence — the index of a prime-power (or any perfect power) grows at most
linearly in the exponent. For `m = 2` this is tight (`hErdos(2^k) = k`, `hErdos_two_pow`),
so the bound cannot be improved in general. -/
theorem hErdos_pow_le {m : ℕ} (hm : IsPractical m) :
    ∀ k, hErdos (m ^ k) ≤ k * hErdos m
  | 0 => by
      have h1 : hErdos (m ^ 0) = 0 := by
        rw [pow_zero]; unfold hErdos; simp [Finset.range_one, repLength_zero]
      rw [h1]; exact Nat.zero_le _
  | k + 1 => by
      calc hErdos (m ^ (k + 1)) = hErdos (m ^ k * m) := by rw [pow_succ]
        _ ≤ hErdos (m ^ k) + hErdos m := hErdos_mul_le (practical_pow hm k) hm
        _ ≤ k * hErdos m + hErdos m := Nat.add_le_add_right (hErdos_pow_le hm k) _
        _ = (k + 1) * hErdos m := by ring

/- ## An information-theoretic lower bound for the corrected index

`le_two_pow_h` bounded the *universal-set* index from below — `m ≤ 2^(h m)`, i.e.
`h m ≥ log₂ m` — which is exactly what made the parent's `conjecture_part2_weak`
false as stated. The corrected index `hErdos` escapes that argument (a small
per-`k` budget does not force a small universal set), but it cannot escape
counting entirely: each `k < m` is a sum of at most `hErdos m` of the `d(m)`
divisors of `m`, distinct `k` use distinct divisor subsets, and a `d`-element
set has at most `∑_{i ≤ t} C(d, i) ≤ (d+1)^t` subsets of size at most `t`.
Hence

  `m ≤ (d(m)+1)^(hErdos m)`,   i.e.   `hErdos m ≥ log m / log (d(m)+1)`.

This is the correct-index analogue of `le_two_pow_h`, and it locates exactly why
the prize conjecture `hErdos(n!) < n^{o(1)}` can survive: only because `d(n!)`
is super-polynomial in `n` (`log d(n!) ≍ n / log n`). Quantitatively the bound
forces `hErdos(n!) ≳ (log n)²` — comfortably below Vose's upper bound
`O(√log(n!)) = O(√(n log n))`, but already unbounded: the corrected index of
`n!` genuinely tends to infinity, so the prize question is a race between two
growing quantities, not a claim of boundedness. -/

/-- Geometric-series cap `∑_{i ≤ t} d^i ≤ (d+1)^t`, used to convert the
binomial-sum subset count into a clean power. -/
theorem sum_pow_le_succ_pow (d t : ℕ) :
    ∑ i ∈ Finset.range (t + 1), d ^ i ≤ (d + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ]
      have h1 : d ^ (t + 1) ≤ d * (d + 1) ^ t := by
        have h2 : d ^ (t + 1) = d * d ^ t := by ring
        rw [h2]
        exact Nat.mul_le_mul (le_refl d) (Nat.pow_le_pow_left (by omega) t)
      calc (∑ i ∈ Finset.range (t + 1), d ^ i) + d ^ (t + 1)
          ≤ (d + 1) ^ t + d * (d + 1) ^ t := Nat.add_le_add ih h1
        _ = (d + 1) ^ (t + 1) := by ring

/-- A `d`-element set has at most `∑_{i ≤ t} C(d, i) ≤ (d+1)^t` subsets of size
at most `t`: the size-`≤ t` slice of the powerset sits inside the union of the
`powersetCard i` layers for `i ≤ t`. -/
theorem card_powerset_filter_card_le (D : Finset ℕ) (t : ℕ) :
    (D.powerset.filter (fun T => T.card ≤ t)).card ≤ (D.card + 1) ^ t := by
  classical
  have hsub : D.powerset.filter (fun T => T.card ≤ t) ⊆
      (Finset.range (t + 1)).biUnion (fun i => Finset.powersetCard i D) := by
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    rw [Finset.mem_biUnion]
    exact ⟨T.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨hT.1, rfl⟩⟩
  calc (D.powerset.filter (fun T => T.card ≤ t)).card
      ≤ ((Finset.range (t + 1)).biUnion (fun i => Finset.powersetCard i D)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (t + 1), (Finset.powersetCard i D).card :=
        Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (t + 1), D.card.choose i :=
        Finset.sum_congr rfl fun i _ => Finset.card_powersetCard i D
    _ ≤ ∑ i ∈ Finset.range (t + 1), D.card ^ i :=
        Finset.sum_le_sum fun i _ => Nat.choose_le_pow D.card i
    _ ≤ (D.card + 1) ^ t := sum_pow_le_succ_pow D.card t

/-- **Injection step**: for practical `m`, distinct `k < m` have distinct
minimum-size representing sets (the sum recovers `k`), all of size at most
`hErdos m` — so `m` is at most the number of subsets of `divisors m` of size at
most `hErdos m`. -/
theorem le_card_small_subsets_of_practical {m : ℕ} (hm : IsPractical m) :
    m ≤ ((divisors m).powerset.filter (fun T => T.card ≤ hErdos m)).card := by
  classical
  have hspec : ∀ k : ℕ, ∃ T : Finset ℕ, k < m →
      T ⊆ divisors m ∧ T.card = repLength m k ∧ T.sum id = k := by
    intro k
    by_cases hk : k < m
    · obtain ⟨T, h1, h2, h3⟩ := repLength_spec' hm hk
      exact ⟨T, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h => absurd h hk⟩
  choose f hf using hspec
  have hmaps : Set.MapsTo f (Finset.range m : Set ℕ)
      (((divisors m).powerset.filter (fun T => T.card ≤ hErdos m)) :
        Set (Finset ℕ)) := by
    intro k hk
    rw [Finset.mem_coe, Finset.mem_range] at hk
    obtain ⟨h1, h2, h3⟩ := hf k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨h1, ?_⟩
    rw [h2]
    unfold hErdos
    exact Finset.le_sup (Finset.mem_range.mpr hk)
  have hinj : Set.InjOn f (Finset.range m : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
    have h₁ := (hf k₁ hk₁).2.2
    have h₂ := (hf k₂ hk₂).2.2
    rw [← h₁, ← h₂, heq]
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rwa [Finset.card_range] at hcard

/-- **Information-theoretic lower bound for `hErdos`** (power form): for
practical `m`, `m ≤ (d(m)+1)^(hErdos m)` — equivalently
`hErdos m ≥ log m / log (d(m)+1)`. The correct-index analogue of
`le_two_pow_h`. -/
theorem le_succ_card_divisors_pow_hErdos {m : ℕ} (hm : IsPractical m) :
    m ≤ ((divisors m).card + 1) ^ hErdos m :=
  (le_card_small_subsets_of_practical hm).trans
    (card_powerset_filter_card_le (divisors m) (hErdos m))

/-- Contrapositive reading of the lower bound: any `t` with `(d(m)+1)^t < m` is a
strict lower bound for `hErdos m`. -/
theorem lt_hErdos_of_pow_lt {m t : ℕ} (hm : IsPractical m)
    (h : ((divisors m).card + 1) ^ t < m) : t < hErdos m := by
  by_contra hle
  rw [not_lt] at hle
  have hb := le_succ_card_divisors_pow_hErdos hm
  have hmono : ((divisors m).card + 1) ^ hErdos m ≤ ((divisors m).card + 1) ^ t :=
    Nat.pow_le_pow_right (by omega) hle
  omega

/-- **Erdős #18, Part 2 ($250), corrected.** The prize question `h(n!) < n^{o(1)}`
stated over the correct index `hErdos`. Contrast `conjecture_part2_weak`, which is
*false* for the parent's universal-set `h` (`factorial_le_two_pow_h`). -/
def conjecture_part2_weak_erdos : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n ≥ N, (hErdos n.factorial : ℝ) < n ^ ε

/-- **Erdős #18, Part 1, corrected** — infinitely many practical `m` whose correct
index `hErdos m` is doubly-logarithmically bounded. -/
def conjecture_part1_erdos : Prop :=
  ∃ C : ℝ, C > 0 ∧
    Set.Infinite { m : ℕ | IsPractical m ∧
      (hErdos m : ℝ) < (Real.log (Real.log m)) ^ C }

/- ## The upper-half divisor gap: `hErdos m = 1` exactly at `m = 2`, and the
first composite exact values

No divisor of `m` lies strictly between `m/2` and `m`: a proper divisor `d < m`
has cofactor at least `2`, so `2d ≤ m`. Hence any target `k` with `m < 2k` and
`k < m` is not itself a divisor, and every distinct-divisor representation of it
needs at least **two** divisors. Taking `k = m − 1` (for `m ≥ 3`) pins
`hErdos m ≥ 2`, so the corrected index equals `1` exactly at `m = 2`
(`hErdos_eq_one_iff`) — the complete list of small values starts
`hErdos 1 = 0`, `hErdos 2 = 1`, and `≥ 2` from then on.

The same gap argument yields the first exact values beyond the extremal powers
of two (`hErdos_two_pow`):

* `hErdos 6 = 2` — the first practical number that is not a power of two. Upper
  bound: six explicit minimum representations (`4 = 1+3`, `5 = 2+3`). Lower
  bound: `k = 5` lies in the gap `(3, 6)`.
* `hErdos 12 = 3` — the subadditivity `hErdos(2·6) ≤ hErdos 2 + hErdos 6` is
  **tight** here: `k = 11` genuinely needs three divisors (`11 = 1 + 4 + 6`;
  the largest two-divisor sum below `12` is `4 + 6 = 10`), confirmed by a finite
  kernel check over the 64 subsets of `divisors 12`. Note the counting bound
  `lt_hErdos_of_pow_lt` gives only `hErdos 12 ≥ 2` (`(d(12)+1)^1 = 7 < 12 ≤ 49`),
  so the combinatorial gap argument is strictly sharper here. -/

/-- Any witness set bounds `repLength`: if `T ⊆ divisors m` sums to `k`, then
`repLength m k ≤ |T|`. -/
theorem repLength_le_of_witness {m k : ℕ} {T : Finset ℕ} (hsub : T ⊆ divisors m)
    (hsum : T.sum id = k) : repLength m k ≤ T.card :=
  Nat.sInf_le ⟨T, hsub, rfl, hsum⟩

/-- **No divisor in the upper half**: a proper divisor `d < m` satisfies
`2d ≤ m` — its cofactor is at least `2`. -/
theorem two_mul_le_of_dvd_of_lt {d m : ℕ} (hdvd : d ∣ m) (hlt : d < m) :
    2 * d ≤ m := by
  obtain ⟨c, rfl⟩ := hdvd
  rcases c with _ | _ | c
  · omega
  · omega
  · have h2 : d * 2 ≤ d * (c + 1 + 1) := Nat.mul_le_mul (le_refl d) (by omega)
    omega

/-- **Two divisors are needed in the upper half**: if `T ⊆ divisors m` sums to
`k` with `m < 2k` and `k < m`, then `|T| ≥ 2`. Indeed `k ≥ 1` (so `T ≠ ∅`), and
a singleton `{d}` would make `k = d` a divisor lying in the forbidden interval
`(m/2, m)` (`two_mul_le_of_dvd_of_lt`). -/
theorem two_le_card_of_sum_upper_half {m k : ℕ} {T : Finset ℕ}
    (hsub : T ⊆ divisors m) (hsum : T.sum id = k) (hk2 : m < 2 * k)
    (hkm : k < m) : 2 ≤ T.card := by
  by_contra hlt
  rw [not_le] at hlt
  rcases Finset.eq_empty_or_nonempty T with rfl | hne
  · rw [Finset.sum_empty] at hsum
    omega
  · have hcard1 : T.card = 1 := by
      have hpos := Finset.card_pos.mpr hne
      omega
    obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp hcard1
    rw [Finset.sum_singleton, id_eq] at hsum
    subst hsum
    have hdvd : d ∣ m :=
      (Nat.mem_divisors.mp (hsub (Finset.mem_singleton_self d))).1
    have hhalf := two_mul_le_of_dvd_of_lt hdvd hkm
    omega

/-- **Lower bound from the upper-half gap**: for practical `m`, any target in
the open upper half (`m < 2k`, `k < m`) has `repLength m k ≥ 2`. -/
theorem two_le_repLength_of_upper_half {m k : ℕ} (hm : IsPractical m)
    (hk2 : m < 2 * k) (hkm : k < m) : 2 ≤ repLength m k := by
  unfold repLength
  apply le_csInf
  · obtain ⟨T, hTsub, hTsum⟩ := hm.2 k (by omega) hkm
    exact ⟨T.card, T, hTsub, rfl, hTsum⟩
  · rintro t ⟨T, hTsub, rfl, hTsum⟩
    exact two_le_card_of_sum_upper_half hTsub hTsum hk2 hkm

/-- **`hErdos m ≥ 2` for practical `m ≥ 3`**: the value `k = m − 1` lies in the
upper-half gap. Together with `one_le_hErdos` this pins all small values of the
corrected index. -/
theorem two_le_hErdos {m : ℕ} (hm : IsPractical m) (hm3 : 3 ≤ m) :
    2 ≤ hErdos m := by
  have h1 : 2 ≤ repLength m (m - 1) :=
    two_le_repLength_of_upper_half hm (by omega) (by omega)
  calc 2 ≤ repLength m (m - 1) := h1
    _ ≤ hErdos m := by
        unfold hErdos
        exact Finset.le_sup (Finset.mem_range.mpr (by omega))

/-- `hErdos 1 = 0`: the only value to cover is `k = 0`, handled by `∅`. -/
theorem hErdos_one : hErdos 1 = 0 := by
  unfold hErdos
  simp [Finset.range_one, repLength_zero]

/-- `hErdos 2 = 1` — the power-of-two formula at `k = 1`. -/
theorem hErdos_two : hErdos 2 = 1 := by
  have h := hErdos_two_pow 1
  norm_num at h
  exact h

/-- **`hErdos m = 1` exactly at `m = 2`** (over practical `m`): `m = 1` gives
index `0`, and every practical `m ≥ 3` needs two divisors somewhere
(`two_le_hErdos`). -/
theorem hErdos_eq_one_iff {m : ℕ} (hm : IsPractical m) :
    hErdos m = 1 ↔ m = 2 := by
  constructor
  · intro h1
    by_contra hne
    have hm1 : 1 ≤ m := hm.1
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · interval_cases m
      · rw [hErdos_one] at h1
        omega
      · exact hne rfl
    · have h2 := two_le_hErdos hm hge
      omega
  · rintro rfl
    exact hErdos_two

/-- **`hErdos 6 = 2`** — the first exact value of the corrected index at a
practical number that is not a power of two. Upper bound: every `k < 6` has a
representation by at most two divisors of `6` (`4 = 1+3`, `5 = 2+3`). Lower
bound: `k = 5` lies in the upper-half gap `(3, 6)`. -/
theorem hErdos_six : hErdos 6 = 2 := by
  refine le_antisymm ?_ ?_
  · unfold hErdos
    apply Finset.sup_le
    intro k hk
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [repLength_zero]
      omega
    · exact (repLength_le_of_witness (T := {1}) (by decide) (by decide)).trans
        (by decide)
    · exact (repLength_le_of_witness (T := {2}) (by decide) (by decide)).trans
        (by decide)
    · exact (repLength_le_of_witness (T := {3}) (by decide) (by decide)).trans
        (by decide)
    · exact (repLength_le_of_witness (T := {1, 3}) (by decide) (by decide)).trans
        (by decide)
    · exact (repLength_le_of_witness (T := {2, 3}) (by decide) (by decide)).trans
        (by decide)
  · calc 2 ≤ repLength 6 5 :=
          two_le_repLength_of_upper_half six_practical (by omega) (by omega)
      _ ≤ hErdos 6 := by
          unfold hErdos
          exact Finset.le_sup (Finset.mem_range.mpr (by omega))

/-- `12` is practical — via the decision procedure. -/
theorem twelve_practical : IsPractical 12 := by decide

/-- **Kernel check**: every subset of `divisors 12 = {1,2,3,4,6,12}` summing to
`11` has at least three elements — the largest two-divisor sum below `12` is
`4 + 6 = 10`. A finite `decide` over the 64 subsets. -/
theorem three_le_card_of_sum_eleven :
    ∀ T ∈ (divisors 12).powerset, T.sum id = 11 → 3 ≤ T.card := by decide

/-- `repLength 12 11 ≥ 3`: the target `11` genuinely needs three divisors. -/
theorem three_le_repLength_twelve_eleven : 3 ≤ repLength 12 11 := by
  unfold repLength
  apply le_csInf
  · obtain ⟨T, hTsub, hTsum⟩ := twelve_practical.2 11 (by omega) (by omega)
    exact ⟨T.card, T, hTsub, rfl, hTsum⟩
  · rintro t ⟨T, hTsub, rfl, hTsum⟩
    exact three_le_card_of_sum_eleven T (Finset.mem_powerset.mpr hTsub) hTsum

/-- **`hErdos 12 = 3`: subadditivity is tight.** Upper bound:
`hErdos(2·6) ≤ hErdos 2 + hErdos 6 = 1 + 2` (`hErdos_mul_le`). Lower bound:
`k = 11` needs three divisors (`three_le_repLength_twelve_eleven`). The counting
bound `lt_hErdos_of_pow_lt` gives only `hErdos 12 ≥ 2` here, so the tight value
comes from the combinatorial check, and the subadditive upper bound is attained
with equality at the factorisation `12 = 2 · 6`. -/
theorem hErdos_twelve : hErdos 12 = 3 := by
  refine le_antisymm ?_ ?_
  · have h : hErdos (2 * 6) ≤ hErdos 2 + hErdos 6 :=
      hErdos_mul_le two_practical six_practical
    rw [hErdos_two, hErdos_six] at h
    calc hErdos 12 = hErdos (2 * 6) := by norm_num
      _ ≤ 1 + 2 := h
      _ = 3 := by norm_num
  · calc 3 ≤ repLength 12 11 := three_le_repLength_twelve_eleven
      _ ≤ hErdos 12 := by
          unfold hErdos
          exact Finset.le_sup (Finset.mem_range.mpr (by omega))

/- ## Decide-powered exact-value engines, and `hErdos 24 = 3`, `hErdos 30 = 4`

The exact values so far (`hErdos 6 = 2`, `hErdos 12 = 3`) were computed by hand:
one `repLength_le_of_witness` invocation per target `k` for the upper bound, and a
bespoke kernel check for the lower bound. The two **engines** below reduce *any*
concrete exact value to two `decide` calls:

* `hErdos_le_of_witnesses` — upper bound: a kernel search finding, for every
  `k < m`, some divisor subset of size `≤ t` summing to `k`;
* `le_repLength_of_card` / `le_hErdos_of_card` — lower bound: a kernel check
  that every divisor subset summing to one chosen hard target `k` has `≥ t`
  elements.

With them we pin two new exact values, each carrying theory-level information:

* **`hErdos 24 = 3`** — the first *strict* instance of subadditivity:
  `hErdos (4·6) = 3 < 2 + 2 = hErdos 4 + hErdos 6` (`hErdos_mul_lt_four_six`),
  in contrast to `12 = 2·6` where the subadditive bound is attained.
* **`hErdos 30 = 4`** — `30` has *no* factorisation into practical parts
  (`15`, `10`, `5` are not practical), so `hErdos_mul_le` gives no upper bound at
  all and the engine is the only available route. Moreover `24` and `30` both
  have `d(m) = 8` divisors, yet their indices differ (`3` vs `4`): the index
  depends on the divisor *structure*, not the divisor count. The counting bound
  `lt_hErdos_of_pow_lt` gives only `≥ 2` for both, and the upper-half gap only
  `≥ 2`; the hard target `k = 29` (`29 = 15+10+3+1` is forced, no three divisors
  of `30` sum to `29`) needs the full kernel check. -/

/-- **Upper-bound engine**: if a kernel search finds, for every `k < m`, a divisor
subset of size `≤ t` summing to `k`, then `hErdos m ≤ t`. Reduces the upper half
of any concrete exact-value computation to one `decide`. -/
theorem hErdos_le_of_witnesses {m t : ℕ}
    (h : ∀ k ∈ Finset.range m, ∃ T ∈ (divisors m).powerset, T.card ≤ t ∧ T.sum id = k) :
    hErdos m ≤ t := by
  unfold hErdos
  apply Finset.sup_le
  intro k hk
  obtain ⟨T, hTpow, hTcard, hTsum⟩ := h k hk
  exact (repLength_le_of_witness (Finset.mem_powerset.mp hTpow) hTsum).trans hTcard

/-- **Lower-bound engine (per target)**: if every divisor subset summing to `k`
has at least `t` elements (a finite kernel check over the powerset), then
`t ≤ repLength m k`. Generalises the bespoke `three_le_repLength_twelve_eleven`. -/
theorem le_repLength_of_card {m k t : ℕ} (hm : IsPractical m) (hk1 : 1 ≤ k)
    (hkm : k < m)
    (h : ∀ T ∈ (divisors m).powerset, T.sum id = k → t ≤ T.card) :
    t ≤ repLength m k := by
  unfold repLength
  apply le_csInf
  · obtain ⟨T, hTsub, hTsum⟩ := hm.2 k hk1 hkm
    exact ⟨T.card, T, hTsub, rfl, hTsum⟩
  · rintro s ⟨T, hTsub, rfl, hTsum⟩
    exact h T (Finset.mem_powerset.mpr hTsub) hTsum

/-- **Lower-bound engine (index)**: one hard target `k < m` needing `≥ t` divisors
forces `t ≤ hErdos m`. -/
theorem le_hErdos_of_card {m k t : ℕ} (hm : IsPractical m) (hk1 : 1 ≤ k)
    (hkm : k < m)
    (h : ∀ T ∈ (divisors m).powerset, T.sum id = k → t ≤ T.card) :
    t ≤ hErdos m := by
  refine (le_repLength_of_card hm hk1 hkm h).trans ?_
  unfold hErdos
  exact Finset.le_sup (Finset.mem_range.mpr hkm)

/-- `24` is practical — decision procedure. -/
theorem twentyfour_practical : IsPractical 24 := by decide

set_option maxRecDepth 20000 in
/-- **`hErdos 24 = 3`.** Upper: the engine finds `≤ 3`-divisor representations for
all `k < 24` (the two-divisor sums from `{1,2,3,4,6,8,12}` reach up to `20`, and
`12 + 8 + {1,2,3}` covers `21, 22, 23`). Lower: no two divisors of `24` sum to
`23` (max two-divisor sum below `24` is `12 + 8 = 20`), so `k = 23` needs three. -/
theorem hErdos_twentyfour : hErdos 24 = 3 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 23) twentyfour_practical (by omega) (by omega)
    (by decide)

/-- `hErdos 4 = 2` — the power-of-two formula at `k = 2`. -/
theorem hErdos_four : hErdos 4 = 2 := by
  have h := hErdos_two_pow 2
  norm_num at h
  exact h

/-- **Subadditivity can be strict**: `hErdos (4·6) = 3 < 2 + 2 = hErdos 4 + hErdos 6`.
Contrast with `12 = 2·6`, where `hErdos 12 = 3 = 1 + 2` attains the subadditive
bound (`hErdos_twelve`). So `hErdos_mul_le` is tight at some factorisations and
strict at others — even for the same kind of split of highly practical numbers. -/
theorem hErdos_mul_lt_four_six : hErdos (4 * 6) < hErdos 4 + hErdos 6 := by
  have h24 : (4 * 6 : ℕ) = 24 := by norm_num
  rw [h24, hErdos_twentyfour, hErdos_four, hErdos_six]
  norm_num

/-- `30` is practical — decision procedure. -/
theorem thirty_practical : IsPractical 30 := by decide

set_option maxRecDepth 20000 in
/-- **`hErdos 30 = 4`** — the first exact value out of reach of *both* prior
methods: `30 = 2·3·5` has no factorisation into practical parts, so
`hErdos_mul_le` is inapplicable, and the upper-half gap gives only `≥ 2`. The
hard target is `k = 29`: the only representation is `29 = 15 + 10 + 3 + 1`
(no three divisors of `30` sum to `29`), so four divisors are needed. Note
`d(24) = d(30) = 8` while `hErdos 24 = 3 ≠ 4 = hErdos 30`: the index sees the
divisor structure, not the divisor count. -/
theorem hErdos_thirty : hErdos 30 = 4 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 29) thirty_practical (by omega) (by omega)
    (by decide)

/- ## The record-setter question: least practical `m` with `hErdos m = t`

With the engines the exact-value table extends far enough to answer, for
`t ≤ 4`, the natural "record-setter" question: what is the LEAST practical `m`
with `hErdos m = t`?  The answer is `2^t` — the powers of two, exactly the
family where the index formula `hErdos (2^k) = k` is available — because every
practical number below `2^t` (there are only finitely many: `1, 2, 4, 6, 8, 12`
below `16`) has index `≤ t − 1`.

Three new engine values feed this:

* **`hErdos 18 = 3`** — like `30`, the number `18 = 2·3²` has NO factorisation
  into practical parts (`9`, `3` are odd), so `hErdos_mul_le` is silent and the
  engine is the only route.  Hard target `k = 17` (two-divisor sums from
  `{1,2,3,6,9}` reach only `15`).
* **`hErdos 20 = 4`** — the target `k = 18` is the UNIQUE hard target
  (`18 = 10+5+2+1` is forced: no three divisors of `20` sum to `18`).  Two
  theory consequences: `20 < 24` yet `hErdos 20 = 4 > 3 = hErdos 24` — the
  index is NOT monotone along practical numbers — and `d(20) = 6 < 8 = d(24)`
  with the larger index on the smaller divisor count, sharpening the
  structure-not-count moral of the `24`/`30` pair.
* **`hErdos 28 = 4`** — hard target `k = 27` (`27 = 14+7+4+2` forced; the
  three-divisor sums from `{1,2,4,7,14}` top out at `25`).

The record-setter results themselves (`IsLeast` statements):
`minimal_hErdos_two/three/four` — least practical `m` with index `2, 3, 4` is
`4, 8, 16`.  Whether the pattern `2^t` persists for all `t` is genuinely open
here: it would follow from the general upper bound `hErdos m ≤ log₂ m` for
practical `m`, which fails to be greedy-provable (practical numbers can have
consecutive-divisor ratio `> 2`, e.g. `6 → 13` in `78`), so it is recorded as
a question, not a theorem. -/

set_option maxRecDepth 20000 in
/-- **`hErdos 18 = 3`** — engine-only, like `30`: `18 = 2·3²` has no
factorisation into practical parts, so `hErdos_mul_le` gives nothing.  Hard
target `k = 17`: the two-divisor sums of `{1,2,3,6,9}` reach only `9+6 = 15`. -/
theorem hErdos_eighteen : hErdos 18 = 3 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 17) eighteen_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 20000 in
/-- **`hErdos 20 = 4`** — unique hard target `k = 18` (`18 = 10+5+2+1` forced;
no three divisors of `20` sum to `18`).  Note `20 < 24` with
`hErdos 20 = 4 > 3 = hErdos 24`: the index is not monotone along practical
numbers, and `d(20) = 6 < 8 = d(24)` puts the LARGER index on the SMALLER
divisor count. -/
theorem hErdos_twenty : hErdos 20 = 4 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 18) twenty_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 20000 in
/-- **`hErdos 28 = 4`** — hard target `k = 27` (`27 = 14+7+4+2` forced; the
three-divisor sums of `{1,2,4,7,14}` top out at `14+7+4 = 25`). -/
theorem hErdos_twentyeight : hErdos 28 = 4 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 27) twentyeight_practical (by omega) (by omega)
    (by decide)

/-- `hErdos 8 = 3` — the power-of-two formula at `k = 3`. -/
theorem hErdos_eight : hErdos 8 = 3 := by
  have h := hErdos_two_pow 3
  norm_num at h
  exact h

/-- `hErdos 16 = 4` — the power-of-two formula at `k = 4`. -/
theorem hErdos_sixteen : hErdos 16 = 4 := by
  have h := hErdos_two_pow 4
  norm_num at h
  exact h

/-- **Every practical number below `16` has index at most `3`.**  The practical
numbers below `16` are exactly `1, 2, 4, 6, 8, 12` (each non-practical value is
excluded by a kernel `decide`), and their indices `0, 1, 2, 2, 3, 3` are all
known exactly. -/
theorem hErdos_le_three_of_lt_sixteen {m : ℕ} (hm : IsPractical m)
    (hlt : m < 16) : hErdos m ≤ 3 := by
  interval_cases m
  · exact absurd hm (by decide)
  · simp [hErdos_one]
  · simp [hErdos_two]
  · exact absurd hm (by decide)
  · simp [hErdos_four]
  · exact absurd hm (by decide)
  · simp [hErdos_six]
  · exact absurd hm (by decide)
  · simp [hErdos_eight]
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · simp [hErdos_twelve]
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)

/-- **Record-setter at `t = 4`: the least practical number with index `4` is
`16 = 2⁴`.**  Membership is the power-of-two formula; minimality is
`hErdos_le_three_of_lt_sixteen`. -/
theorem minimal_hErdos_four :
    IsLeast { m : ℕ | IsPractical m ∧ hErdos m = 4 } 16 := by
  constructor
  · exact ⟨by decide, hErdos_sixteen⟩
  · rintro m ⟨hpr, h4⟩
    by_contra hlt
    push Not at hlt
    have := hErdos_le_three_of_lt_sixteen hpr hlt
    omega

/-- **Record-setter at `t = 3`: the least practical number with index `3` is
`8 = 2³`.**  The practical numbers below `8` are `1, 2, 4, 6` with indices
`0, 1, 2, 2`. -/
theorem minimal_hErdos_three :
    IsLeast { m : ℕ | IsPractical m ∧ hErdos m = 3 } 8 := by
  constructor
  · exact ⟨by decide, hErdos_eight⟩
  · rintro m ⟨hpr, h3⟩
    by_contra hlt
    push Not at hlt
    have h : hErdos m ≤ 2 := by
      interval_cases m
      · exact absurd hpr (by decide)
      · simp [hErdos_one]
      · simp [hErdos_two]
      · exact absurd hpr (by decide)
      · simp [hErdos_four]
      · exact absurd hpr (by decide)
      · simp [hErdos_six]
      · exact absurd hpr (by decide)
    omega

/-- **Record-setter at `t = 2`: the least practical number with index `2` is
`4 = 2²`.**  The practical numbers below `4` are `1, 2` with indices `0, 1`. -/
theorem minimal_hErdos_two :
    IsLeast { m : ℕ | IsPractical m ∧ hErdos m = 2 } 4 := by
  constructor
  · exact ⟨by decide, hErdos_four⟩
  · rintro m ⟨hpr, h2⟩
    by_contra hlt
    push Not at hlt
    have h : hErdos m ≤ 1 := by
      interval_cases m
      · exact absurd hpr (by decide)
      · simp [hErdos_one]
      · simp [hErdos_two]
      · exact absurd hpr (by decide)
    omega

/-- `hErdos 32 = 5` — the power-of-two formula at `k = 5`. -/
theorem hErdos_thirtytwo : hErdos 32 = 5 := by
  have h := hErdos_two_pow 5
  norm_num at h
  exact h

/-- **Every practical number below `32` has index at most `4`.**  The practical
numbers in `[16, 32)` are `16, 18, 20, 24, 28, 30`, all pinned at index `≤ 4`
by the engine values; below `16` the bound is
`hErdos_le_three_of_lt_sixteen`. -/
theorem hErdos_le_four_of_lt_thirtytwo {m : ℕ} (hm : IsPractical m)
    (hlt : m < 32) : hErdos m ≤ 4 := by
  by_cases h16 : m < 16
  · exact (hErdos_le_three_of_lt_sixteen hm h16).trans (by omega)
  · push Not at h16
    interval_cases m
    · simp [hErdos_sixteen]
    · exact absurd hm (by decide)
    · simp [hErdos_eighteen]
    · exact absurd hm (by decide)
    · simp [hErdos_twenty]
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · simp [hErdos_twentyfour]
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · simp [hErdos_twentyeight]
    · exact absurd hm (by decide)
    · simp [hErdos_thirty]
    · exact absurd hm (by decide)

/-- **Record-setter at `t = 5`: the least practical number with index `5` is
`32 = 2⁵`.**  The record-setter sequence for `t = 1, …, 5` is
`2, 4, 8, 16, 32` — so far exactly the powers of two, the family where the
index formula `hErdos (2^k) = k` holds.  Whether this persists for all `t`
is open (see the section comment). -/
theorem minimal_hErdos_five :
    IsLeast { m : ℕ | IsPractical m ∧ hErdos m = 5 } 32 := by
  constructor
  · exact ⟨by decide, hErdos_thirtytwo⟩
  · rintro m ⟨hpr, h5⟩
    by_contra hlt
    push Not at hlt
    have := hErdos_le_four_of_lt_thirtytwo hpr hlt
    omega

/- ## Record-setter at `t = 6`: the threshold crosses `64`

The `t = 6` rung needs `hErdos m ≤ 5` for every practical `m < 64`.  Below `32`
this is `hErdos_le_four_of_lt_thirtytwo`; the practical numbers in `[32, 64)`
are exactly `32, 36, 40, 42, 48, 54, 56, 60`.  Five of the seven new numbers
fall to subadditivity alone — `36 = 6·6`, `40 = 2·20`, `48 = 2·24`,
`56 = 2·28`, `60 = 2·30`, each factor practical with its index already pinned —
so only `42 = 2·3·7` and `54 = 2·3³` need the kernel engine: like `18` and
`30`, neither has a factorisation into two practical parts (`21, 14, 7` and
`27, 9, 3` all fail), so `hErdos_mul_le` is silent on them.

A structural remark falls out of the bounds: every practical number in
`[32, 64)` other than `32` itself has index `≤ 4` — within this block the
power of two is the UNIQUE practical number attaining index `5`.  The
record-setter is not merely first, it is (locally) alone at its record. -/

/-- `hErdos 36 ≤ 4` — subadditivity at the practical split `36 = 6 · 6`. -/
theorem hErdos_thirtysix_le : hErdos 36 ≤ 4 := by
  have h : hErdos (6 * 6) ≤ hErdos 6 + hErdos 6 :=
    hErdos_mul_le six_practical six_practical
  rw [hErdos_six] at h
  calc hErdos 36 = hErdos (6 * 6) := by norm_num
    _ ≤ 2 + 2 := h
    _ ≤ 4 := by norm_num

/-- `hErdos 40 ≤ 5` — subadditivity at the practical split `40 = 2 · 20`. -/
theorem hErdos_forty_le : hErdos 40 ≤ 5 := by
  have h : hErdos (2 * 20) ≤ hErdos 2 + hErdos 20 :=
    hErdos_mul_le two_practical twenty_practical
  rw [hErdos_two, hErdos_twenty] at h
  calc hErdos 40 = hErdos (2 * 20) := by norm_num
    _ ≤ 1 + 4 := h
    _ ≤ 5 := by norm_num

set_option maxRecDepth 20000 in
/-- `hErdos 42 ≤ 4` — engine-only, like `18` and `30`: `42 = 2·3·7` has no
factorisation into two practical parts (`21`, `14`, `7` are not practical), so
`hErdos_mul_le` is silent.  The kernel finds `≤ 4`-divisor representations from
`{1,2,3,6,7,14,21}` for all `k < 42` (e.g. `40 = 21+14+3+2`, `41 = 21+14+6`). -/
theorem hErdos_fortytwo_le : hErdos 42 ≤ 4 :=
  hErdos_le_of_witnesses (by decide)

/-- `hErdos 48 ≤ 4` — subadditivity at the practical split `48 = 2 · 24`. -/
theorem hErdos_fortyeight_le : hErdos 48 ≤ 4 := by
  have h : hErdos (2 * 24) ≤ hErdos 2 + hErdos 24 :=
    hErdos_mul_le two_practical twentyfour_practical
  rw [hErdos_two, hErdos_twentyfour] at h
  calc hErdos 48 = hErdos (2 * 24) := by norm_num
    _ ≤ 1 + 3 := h
    _ ≤ 4 := by norm_num

set_option maxRecDepth 20000 in
/-- `hErdos 54 ≤ 4` — engine-only: `54 = 2·3³` has no factorisation into two
practical parts (`27`, `9`, `3` are not practical).  The kernel finds
`≤ 4`-divisor representations from `{1,2,3,6,9,18,27}` for all `k < 54`
(e.g. `53 = 27+18+6+2`, `49 = 27+18+3+1`). -/
theorem hErdos_fiftyfour_le : hErdos 54 ≤ 4 :=
  hErdos_le_of_witnesses (by decide)

/-- `hErdos 56 ≤ 5` — subadditivity at the practical split `56 = 2 · 28`. -/
theorem hErdos_fiftysix_le : hErdos 56 ≤ 5 := by
  have h : hErdos (2 * 28) ≤ hErdos 2 + hErdos 28 :=
    hErdos_mul_le two_practical twentyeight_practical
  rw [hErdos_two, hErdos_twentyeight] at h
  calc hErdos 56 = hErdos (2 * 28) := by norm_num
    _ ≤ 1 + 4 := h
    _ ≤ 5 := by norm_num

/-- `hErdos 60 ≤ 5` — subadditivity at the practical split `60 = 2 · 30`. -/
theorem hErdos_sixty_le : hErdos 60 ≤ 5 := by
  have h : hErdos (2 * 30) ≤ hErdos 2 + hErdos 30 :=
    hErdos_mul_le two_practical thirty_practical
  rw [hErdos_two, hErdos_thirty] at h
  calc hErdos 60 = hErdos (2 * 30) := by norm_num
    _ ≤ 1 + 4 := h
    _ ≤ 5 := by norm_num

/-- `hErdos 64 = 6` — the power-of-two formula at `k = 6`. -/
theorem hErdos_sixtyfour : hErdos 64 = 6 := by
  have h := hErdos_two_pow 6
  norm_num at h
  exact h

set_option maxRecDepth 40000 in
/-- **Every practical number below `64` has index at most `5`.**  Below `32`
this is `hErdos_le_four_of_lt_thirtytwo`; the practical numbers in `[32, 64)`
are `32, 36, 40, 42, 48, 54, 56, 60` (each non-practical value excluded by a
kernel `decide`), bounded by the engine values and subadditive splits above.
In fact only `32` attains `5` — the other seven are all `≤ 4` (subadditivity
gives `≤ 4` outright for `36` and `48`; `40, 56, 60` land at `≤ 5` only
because the crude split through `2 · m'` spends a divisor on the factor `2`). -/
theorem hErdos_le_five_of_lt_sixtyfour {m : ℕ} (hm : IsPractical m)
    (hlt : m < 64) : hErdos m ≤ 5 := by
  by_cases h32 : m < 32
  · exact (hErdos_le_four_of_lt_thirtytwo hm h32).trans (by omega)
  · push Not at h32
    interval_cases m
    · simp [hErdos_thirtytwo]
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_thirtysix_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_forty_le
    · exact absurd hm (by decide)
    · exact hErdos_fortytwo_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_fortyeight_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_fiftyfour_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact hErdos_fiftysix_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_sixty_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)

set_option maxRecDepth 20000 in
/-- **Record-setter at `t = 6`: the least practical number with index `6` is
`64 = 2⁶`.**  The record-setter sequence for `t = 1, …, 6` is
`2, 4, 8, 16, 32, 64` — exactly the powers of two, the family where the index
formula `hErdos (2^k) = k` holds.  This rung is the first where the
practical numbers strictly between consecutive records split by METHOD:
subadditive splits handle `36, 40, 48, 56, 60` and the kernel engine is needed
only for the two practically-unsplittable numbers `42` and `54`.  Whether
`2^t` remains the record-setter for all `t` is open (see the `t ≤ 5` section
comment: it would follow from `hErdos m ≤ log₂ m` for practical `m`, which
resists the greedy argument). -/
theorem minimal_hErdos_six :
    IsLeast { m : ℕ | IsPractical m ∧ hErdos m = 6 } 64 := by
  constructor
  · exact ⟨by decide, hErdos_sixtyfour⟩
  · rintro m ⟨hpr, h6⟩
    by_contra hlt
    push Not at hlt
    have := hErdos_le_five_of_lt_sixtyfour hpr hlt
    omega

/- ## Record-setter at `t = 7`, and the first failure of local uniqueness

The `t = 7` rung needs `hErdos m ≤ 6` for every practical `m < 128`.  The
practical numbers in `[64, 128)` are exactly
`64, 66, 72, 78, 80, 84, 88, 90, 96, 100, 104, 108, 112, 120, 126`.  The
split-vs-engine dichotomy of the `t = 6` rung persists at scale: seven of the
fourteen new numbers fall to subadditivity through a practical split `2 · m'`
(`72, 80, 84, 96, 108, 112, 120` — each cofactor's bound already pinned in the
`[32, 64)` block), and the seven remaining — `66 = 2·3·11`, `78 = 2·3·13`,
`88 = 2³·11`, `90 = 2·3²·5`, `100 = 2²·5²`, `104 = 2³·13`, `126 = 2·3²·7` —
have no factorisation into two practical parts, so `hErdos_mul_le` is silent
and the kernel engines pin them (with exact values, not just upper bounds).

The structural surprise sits in the engine values.  At `t = 5` the record `32`
was locally unique — no other practical number in `[32, 64)` attains index
`5`.  At `t = 6` local uniqueness FAILS, four times over:

  `hErdos 78 = hErdos 88 = hErdos 100 = hErdos 104 = 6 = hErdos 64`.

All four ties are practically-unsplittable numbers whose divisor list jumps by
a ratio `> 2` just past a short prefix.  `78 = 2·3·13` (divisor gap `6 → 13`)
is precisely the number on which greedy halving for the conjectured
`hErdos m ≤ log₂ m` was seen to fail (`t ≤ 5` section comment) — and here that
same gap forces a maximal-length representation: the only divisor subset of
`78` summing to the hard target `77` is `{1, 2, 3, 6, 26, 39}`, i.e. all six
divisors below `78` except `13`.  Note the ties probe the conjectured
logarithmic bound without breaching it: `6 = log₂ 64 ≤ log₂ 78`.

Not settled here (the octave's full index-`6` census): `80, 112, 120` carry
only the crude split bound `≤ 6`, so this file does not decide whether they
too attain `6` (their true indices are `5, 5, 4`, but pinning them needs
engine uppers, and `d(120) = 16` makes that the first genuinely expensive
kernel search — `2¹⁵` subsets per target).  What IS settled: every practical
number below `128` has index `≤ 6`, so the record-setter sequence continues
`2, 4, 8, 16, 32, 64, 128` — exactly the powers of two through `t = 7`. -/

set_option maxRecDepth 40000 in
/-- `40` is practical — decision procedure. -/
theorem forty_practical : IsPractical 40 := by decide

set_option maxRecDepth 40000 in
/-- `42` is practical — decision procedure. -/
theorem fortytwo_practical : IsPractical 42 := by decide

set_option maxRecDepth 40000 in
/-- `54` is practical — decision procedure. -/
theorem fiftyfour_practical : IsPractical 54 := by decide

set_option maxRecDepth 40000 in
/-- `56` is practical — decision procedure. -/
theorem fiftysix_practical : IsPractical 56 := by decide

set_option maxRecDepth 40000 in
/-- `60` is practical — decision procedure. -/
theorem sixty_practical : IsPractical 60 := by decide

set_option maxRecDepth 40000 in
/-- `66` is practical — decision procedure. -/
theorem sixtysix_practical : IsPractical 66 := by decide

set_option maxRecDepth 40000 in
/-- `78` is practical — decision procedure. -/
theorem seventyeight_practical : IsPractical 78 := by decide

set_option maxRecDepth 40000 in
/-- `88` is practical — decision procedure. -/
theorem eightyeight_practical : IsPractical 88 := by decide

set_option maxRecDepth 40000 in
/-- `90` is practical — decision procedure. -/
theorem ninety_practical : IsPractical 90 := by decide

set_option maxRecDepth 40000 in
/-- `104` is practical — decision procedure. -/
theorem onehundredfour_practical : IsPractical 104 := by decide

set_option maxRecDepth 40000 in
/-- `126` is practical — decision procedure. -/
theorem onetwentysix_practical : IsPractical 126 := by decide

set_option maxRecDepth 20000 in
/-- **`hErdos 66 = 5`** — engine-only: `66 = 2·3·11` has no factorisation into
two practical parts (`33`, `22`, `11` are not practical).  Hard target
`k = 65`: the only divisor subset summing to `65` is `{1, 3, 6, 22, 33}` (the
complement of `{2, 11}` in the proper divisors, which total `78`). -/
theorem hErdos_sixtysix : hErdos 66 = 5 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 65) sixtysix_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 20000 in
/-- **`hErdos 78 = 6` — the first tie with a power-of-two record.**
Engine-only: `78 = 2·3·13` has no practical split (`39`, `26`, `13` fail).
Hard target `k = 77`: the proper divisors `{1, 2, 3, 6, 13, 26, 39}` total
`90`, so a subset sums to `77` iff its complement sums to `13` — and the only
such complement is `{13}` itself (the gap `6 → 13` leaves `1+2+3+6 = 12 < 13`).
The unique representation `77 = 1+2+3+6+26+39` uses six divisors. -/
theorem hErdos_seventyeight : hErdos 78 = 6 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 77) seventyeight_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 20000 in
/-- **`hErdos 88 = 6`** — engine-only: `88 = 2³·11` has no practical split
(`44`, `22`, `11` fail).  Hard target `k = 84`: the proper divisors
`{1, 2, 4, 8, 11, 22, 44}` total `92`, and the only subset summing to the
complement value `8` is `{8}` itself, so `84 = 1+2+4+11+22+44` is forced —
six divisors. -/
theorem hErdos_eightyeight : hErdos 88 = 6 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 84) eightyeight_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 40000 in
/-- **`hErdos 90 = 4`** — engine-only: `90 = 2·3²·5` has no practical split
(`45`, `30·3`, `18·5`, `15·6`, `10·9` all involve a non-practical factor).
Despite eleven proper divisors the index stays at `4` (e.g. hard target
`k = 67 = 45+18+3+1`). The contrast with `88` (eight divisors, index `6`)
shows again that the index tracks divisor STRUCTURE, not divisor count. -/
theorem hErdos_ninety : hErdos 90 = 4 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 67) ninety_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 20000 in
/-- **`hErdos 100 = 6`** — engine-only: `100 = 2²·5²` has no practical split
(`50`, `25`, `20·5`, `10·10` all involve a non-practical factor).  Hard target
`k = 93`: the proper divisors `{1, 2, 4, 5, 10, 20, 25, 50}` total `117`, and
the only subset summing to the complement value `24` is `{4, 20}`, forcing
`93 = 1+2+5+10+25+50` — six divisors. -/
theorem hErdos_onehundred : hErdos 100 = 6 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 93) hundred_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 20000 in
/-- **`hErdos 104 = 6`** — engine-only: `104 = 2³·13` has no practical split
(`52`, `26`, `13` fail).  Like its sibling `88 = 2³·11`, the prime gap
`8 → 13` in the divisor list forces six-divisor representations (hard target
`k = 98`). -/
theorem hErdos_onehundredfour : hErdos 104 = 6 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 98) onehundredfour_practical (by omega) (by omega)
    (by decide)

set_option maxRecDepth 40000 in
/-- **`hErdos 126 = 4`** — engine-only: `126 = 2·3²·7` has no practical split
(`63`, `21`, `18·7`, `14·9`, `42·3` all involve a non-practical factor).
Eleven proper divisors, index only `4` (hard target `k = 89 = 63+21+3+2`) —
the third practically-unsplittable number in this octave (after `90`) whose
index stays LOW, in contrast to the four record-tying ones. -/
theorem hErdos_onetwentysix : hErdos 126 = 4 := by
  refine le_antisymm (hErdos_le_of_witnesses (by decide)) ?_
  exact le_hErdos_of_card (k := 89) onetwentysix_practical (by omega) (by omega)
    (by decide)

/-- `hErdos 72 ≤ 5` — subadditivity at the practical split `72 = 2 · 36`. -/
theorem hErdos_seventytwo_le : hErdos 72 ≤ 5 := by
  have h : hErdos (2 * 36) ≤ hErdos 2 + hErdos 36 :=
    hErdos_mul_le two_practical thirtysix_practical
  have h36 := hErdos_thirtysix_le
  rw [hErdos_two] at h
  have h72 : hErdos 72 = hErdos (2 * 36) := by norm_num
  omega

/-- `hErdos 80 ≤ 6` — subadditivity at the practical split `80 = 2 · 40`. -/
theorem hErdos_eighty_le : hErdos 80 ≤ 6 := by
  have h : hErdos (2 * 40) ≤ hErdos 2 + hErdos 40 :=
    hErdos_mul_le two_practical forty_practical
  have h40 := hErdos_forty_le
  rw [hErdos_two] at h
  have h80 : hErdos 80 = hErdos (2 * 40) := by norm_num
  omega

/-- `hErdos 84 ≤ 5` — subadditivity at the practical split `84 = 2 · 42`. -/
theorem hErdos_eightyfour_le : hErdos 84 ≤ 5 := by
  have h : hErdos (2 * 42) ≤ hErdos 2 + hErdos 42 :=
    hErdos_mul_le two_practical fortytwo_practical
  have h42 := hErdos_fortytwo_le
  rw [hErdos_two] at h
  have h84 : hErdos 84 = hErdos (2 * 42) := by norm_num
  omega

/-- `hErdos 96 ≤ 5` — subadditivity at the practical split `96 = 2 · 48`. -/
theorem hErdos_ninetysix_le : hErdos 96 ≤ 5 := by
  have h : hErdos (2 * 48) ≤ hErdos 2 + hErdos 48 :=
    hErdos_mul_le two_practical fortyeight_practical
  have h48 := hErdos_fortyeight_le
  rw [hErdos_two] at h
  have h96 : hErdos 96 = hErdos (2 * 48) := by norm_num
  omega

/-- `hErdos 108 ≤ 5` — subadditivity at the practical split `108 = 2 · 54`. -/
theorem hErdos_onehundredeight_le : hErdos 108 ≤ 5 := by
  have h : hErdos (2 * 54) ≤ hErdos 2 + hErdos 54 :=
    hErdos_mul_le two_practical fiftyfour_practical
  have h54 := hErdos_fiftyfour_le
  rw [hErdos_two] at h
  have h108 : hErdos 108 = hErdos (2 * 54) := by norm_num
  omega

/-- `hErdos 112 ≤ 6` — subadditivity at the practical split `112 = 2 · 56`. -/
theorem hErdos_onehundredtwelve_le : hErdos 112 ≤ 6 := by
  have h : hErdos (2 * 56) ≤ hErdos 2 + hErdos 56 :=
    hErdos_mul_le two_practical fiftysix_practical
  have h56 := hErdos_fiftysix_le
  rw [hErdos_two] at h
  have h112 : hErdos 112 = hErdos (2 * 56) := by norm_num
  omega

/-- `hErdos 120 ≤ 6` — subadditivity at the practical split `120 = 2 · 60`. -/
theorem hErdos_onetwenty_le : hErdos 120 ≤ 6 := by
  have h : hErdos (2 * 60) ≤ hErdos 2 + hErdos 60 :=
    hErdos_mul_le two_practical sixty_practical
  have h60 := hErdos_sixty_le
  rw [hErdos_two] at h
  have h120 : hErdos 120 = hErdos (2 * 60) := by norm_num
  omega

/-- `hErdos 128 = 7` — the power-of-two formula at `k = 7`. -/
theorem hErdos_onetwentyeight : hErdos 128 = 7 := by
  have h := hErdos_two_pow 7
  norm_num at h
  exact h

set_option maxRecDepth 80000 in
/-- **Every practical number below `128` has index at most `6`.**  Below `64`
this is `hErdos_le_five_of_lt_sixtyfour`; the practical numbers in `[64, 128)`
are `64, 66, 72, 78, 80, 84, 88, 90, 96, 100, 104, 108, 112, 120, 126` (each
non-practical value excluded by a kernel `decide`), bounded by the engine
values and subadditive splits above.  Unlike the previous octave, the bound
`≤ 6` is attained five times here: by `64` and by the four ties
`78, 88, 100, 104`. -/
theorem hErdos_le_six_of_lt_onetwentyeight {m : ℕ} (hm : IsPractical m)
    (hlt : m < 128) : hErdos m ≤ 6 := by
  by_cases h64 : m < 64
  · exact (hErdos_le_five_of_lt_sixtyfour hm h64).trans (by omega)
  · push Not at h64
    interval_cases m
    · simp [hErdos_sixtyfour]
    · exact absurd hm (by decide)
    · simp [hErdos_sixtysix]
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_seventytwo_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · simp [hErdos_seventyeight]
    · exact absurd hm (by decide)
    · exact hErdos_eighty_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_eightyfour_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · simp [hErdos_eightyeight]
    · exact absurd hm (by decide)
    · simp [hErdos_ninety]
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_ninetysix_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · simp [hErdos_onehundred]
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · simp [hErdos_onehundredfour]
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onehundredeight_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onehundredtwelve_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onetwenty_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · simp [hErdos_onetwentysix]
    · exact absurd hm (by decide)

set_option maxRecDepth 40000 in
/-- **Record-setter at `t = 7`: the least practical number with index `7` is
`128 = 2⁷`.**  The record-setter sequence for `t = 1, …, 7` is
`2, 4, 8, 16, 32, 64, 128` — exactly the powers of two.  This rung is the
first where the record's predecessor octave contains OTHER practical numbers
attaining the previous record index (`78, 88, 100, 104` all have index `6`,
like `64`), so the conjectured persistence of `2^t` as record-setter can no
longer be read off from local uniqueness — the powers of two now lead only by
position, not by isolation. -/
theorem minimal_hErdos_seven :
    IsLeast { m : ℕ | IsPractical m ∧ hErdos m = 7 } 128 := by
  constructor
  · exact ⟨by decide, hErdos_onetwentyeight⟩
  · rintro m ⟨hpr, h7⟩
    by_contra hlt
    push Not at hlt
    have := hErdos_le_six_of_lt_onetwentyeight hpr hlt
    omega

/-- **Local uniqueness of the record fails at `t = 6`**: a practical number
strictly between `64` and `128` attains index `6`.  (Witness `78`; in fact
`88`, `100`, `104` do too — see their exact values.)  Contrast with `t = 5`:
`32` is the unique index-`5` practical number in `[32, 64)` (see the `t = 6`
section comment — the other seven practicals there all have true index
`≤ 4`), so this is the first octave in which the power of two shares its
record. -/
theorem record_index_six_not_locally_unique :
    ∃ m, IsPractical m ∧ 64 < m ∧ m < 128 ∧ hErdos m = 6 :=
  ⟨78, seventyeight_practical, by norm_num, by norm_num, hErdos_seventyeight⟩

/-! ### The record-setter at `t = 8`: the sub-family upper engine and the octave `[128, 256)`

The octave `[128, 256)` contains 25 practical numbers.  Fifteen admit a
practical split `m = 2 * (m/2)` whose subadditive bound already lands at
`<= 7`; the other ten (`140, 150, 162, 196, 198, 204, 210, 220, 228, 234`)
are practically-unsplittable, and two of them (`210` with `d = 16`, and the
split-but-loose `240` with `d = 20`) have divisor counts that make the full
powerset search of `hErdos_le_of_witnesses` infeasible.  The *sub-family*
engine below restricts the kernel search to a hand-picked coin chain
`S ⊆ divisors m`, cutting the search space from `2^d(m)` to `2^|S|` subsets.
Each sub-family was chosen so the kernel certifies the *tight* upper bound
(the Python-computed true index), not merely `<= 7` — this is what makes the
local-uniqueness theorem at the end of the section possible. -/

/-- **Sub-family upper-bound engine**: like `hErdos_le_of_witnesses`, but the
kernel searches only a chosen `S ⊆ divisors m` instead of the full divisor
set.  For `m` with many divisors (`d(240) = 20`, `d(210) = 16`) the full
powerset has up to `2^20` subsets and the plain engine's `decide` is
infeasible; a well-chosen coin chain of 9-11 divisors certifies the same
bound at `2^9`-`2^11` subsets. -/
theorem hErdos_le_of_witnesses_from (S : Finset ℕ) {m t : ℕ}
    (hS : S ⊆ divisors m)
    (h : ∀ k ∈ Finset.range m, ∃ T ∈ S.powerset, T.card ≤ t ∧ T.sum id = k) :
    hErdos m ≤ t := by
  unfold hErdos
  apply Finset.sup_le
  intro k hk
  obtain ⟨T, hTpow, hTcard, hTsum⟩ := h k hk
  exact (repLength_le_of_witness ((Finset.mem_powerset.mp hTpow).trans hS)
    hTsum).trans hTcard

/-- `hErdos 132 ≤ 6` — subadditivity at the practical split `132 = 2 · 66`. -/
theorem hErdos_onethirtytwo_le : hErdos 132 ≤ 6 := by
  have h : hErdos (2 * 66) ≤ hErdos 2 + hErdos 66 :=
    hErdos_mul_le two_practical sixtysix_practical
  rw [hErdos_two, hErdos_sixtysix] at h
  calc hErdos 132 = hErdos (2 * 66) := by norm_num
    _ ≤ 1 + 5 := h
    _ ≤ 6 := by norm_num

/-- `hErdos 144 ≤ 6` — subadditivity at the practical split `144 = 2 · 72`. -/
theorem hErdos_onefortyfour_le : hErdos 144 ≤ 6 := by
  have h72p : IsPractical 72 := by
    simpa using two_mul_practical thirtysix_practical
  have h : hErdos (2 * 72) ≤ hErdos 2 + hErdos 72 :=
    hErdos_mul_le two_practical h72p
  have hhalf := hErdos_seventytwo_le
  rw [hErdos_two] at h
  have hm : hErdos 144 = hErdos (2 * 72) := by norm_num
  omega

/-- `hErdos 168 ≤ 6` — subadditivity at the practical split `168 = 2 · 84`. -/
theorem hErdos_onesixtyeight_le : hErdos 168 ≤ 6 := by
  have h84p : IsPractical 84 := by
    simpa using two_mul_practical fortytwo_practical
  have h : hErdos (2 * 84) ≤ hErdos 2 + hErdos 84 :=
    hErdos_mul_le two_practical h84p
  have hhalf := hErdos_eightyfour_le
  rw [hErdos_two] at h
  have hm : hErdos 168 = hErdos (2 * 84) := by norm_num
  omega

/-- `hErdos 180 ≤ 5` — subadditivity at the practical split `180 = 2 · 90`. -/
theorem hErdos_oneeighty_le : hErdos 180 ≤ 5 := by
  have h : hErdos (2 * 90) ≤ hErdos 2 + hErdos 90 :=
    hErdos_mul_le two_practical ninety_practical
  rw [hErdos_two, hErdos_ninety] at h
  calc hErdos 180 = hErdos (2 * 90) := by norm_num
    _ ≤ 1 + 4 := h
    _ ≤ 5 := by norm_num

/-- `hErdos 192 ≤ 6` — subadditivity at the practical split `192 = 2 · 96`. -/
theorem hErdos_oneninetytwo_le : hErdos 192 ≤ 6 := by
  have h96p : IsPractical 96 := by
    simpa using two_mul_practical fortyeight_practical
  have h : hErdos (2 * 96) ≤ hErdos 2 + hErdos 96 :=
    hErdos_mul_le two_practical h96p
  have hhalf := hErdos_ninetysix_le
  rw [hErdos_two] at h
  have hm : hErdos 192 = hErdos (2 * 96) := by norm_num
  omega

/-- `hErdos 216 ≤ 6` — subadditivity at the practical split `216 = 2 · 108`. -/
theorem hErdos_twosixteen_le : hErdos 216 ≤ 6 := by
  have h108p : IsPractical 108 := by
    simpa using two_mul_practical fiftyfour_practical
  have h : hErdos (2 * 108) ≤ hErdos 2 + hErdos 108 :=
    hErdos_mul_le two_practical h108p
  have hhalf := hErdos_onehundredeight_le
  rw [hErdos_two] at h
  have hm : hErdos 216 = hErdos (2 * 108) := by norm_num
  omega

/-- `hErdos 252 ≤ 5` — subadditivity at the practical split `252 = 2 · 126`. -/
theorem hErdos_twofiftytwo_le : hErdos 252 ≤ 5 := by
  have h : hErdos (2 * 126) ≤ hErdos 2 + hErdos 126 :=
    hErdos_mul_le two_practical onetwentysix_practical
  rw [hErdos_two, hErdos_onetwentysix] at h
  calc hErdos 252 = hErdos (2 * 126) := by norm_num
    _ ≤ 1 + 4 := h
    _ ≤ 5 := by norm_num

set_option maxRecDepth 40000 in
/-- `hErdos 140 ≤ 5` — sub-family engine: 140 = 2^2*5*7 has no practical split (70, 35, 28, 20, 10, 14 fail: 70 and 28 are not practical, the rest are odd or non-practical).
The kernel finds `≤ 5`-divisor representations of every `k < 140` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_oneforty_le : hErdos 140 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 5, 7, 20, 28, 35, 70} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 150 ≤ 5` — sub-family engine: 150 = 2*3*5^2 has no practical split (75, 50, 30-cofactor 5, 25, 15 all odd or non-practical).
The kernel finds `≤ 5`-divisor representations of every `k < 150` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_onefifty_le : hErdos 150 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 5, 6, 15, 25, 50, 75} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 156 ≤ 6` — sub-family engine: the split 156 = 2*78 only gives <= 1+6 = 7; the engine recovers the tight 6.
The kernel finds `≤ 6`-divisor representations of every `k < 156` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_onefiftysix_le : hErdos 156 ≤ 6 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 4, 6, 12, 26, 39, 78} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 160 ≤ 5` — sub-family engine: the split 160 = 2*80 only gives <= 1+6 = 7; the engine recovers the tight 5.
The kernel finds `≤ 5`-divisor representations of every `k < 160` inside the
10-element coin chain below (`2^10 = 1024` subsets searched). -/
theorem hErdos_onesixty_le : hErdos 160 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 5, 8, 10, 16, 32, 40, 80} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 162 ≤ 5` — sub-family engine: 162 = 2*3^4 has no practical split (81, 54, 27, 18-cofactor 9, all odd cofactors).
The kernel finds `≤ 5`-divisor representations of every `k < 162` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_onesixtytwo_le : hErdos 162 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 6, 9, 18, 27, 54, 81} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 176 ≤ 6` — sub-family engine: the split 176 = 2*88 only gives <= 1+6 = 7; the engine recovers the tight 6.
The kernel finds `≤ 6`-divisor representations of every `k < 176` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_oneseventysix_le : hErdos 176 ≤ 6 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 8, 11, 16, 22, 44, 88} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 196 ≤ 6` — sub-family engine: 196 = 2^2*7^2 has no practical split (98, 49, 28, 14 are not practical or odd).
The kernel finds `≤ 6`-divisor representations of every `k < 196` inside the
8-element coin chain below (`2^8 = 256` subsets searched). -/
theorem hErdos_oneninetysix_le : hErdos 196 ≤ 6 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 7, 14, 28, 49, 98} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 198 ≤ 5` — sub-family engine: 198 = 2*3^2*11 has no practical split (99, 66-cofactor 3, 33, 22-cofactor 9, 18-cofactor 11 all involve an odd or non-practical part).
The kernel finds `≤ 5`-divisor representations of every `k < 198` inside the
10-element coin chain below (`2^10 = 1024` subsets searched). -/
theorem hErdos_oneninetyeight_le : hErdos 198 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 6, 9, 11, 18, 33, 66, 99} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 200 ≤ 5` — sub-family engine: the split 200 = 2*100 only gives <= 1+6 = 7; the engine recovers the tight 5.
The kernel finds `≤ 5`-divisor representations of every `k < 200` inside the
10-element coin chain below (`2^10 = 1024` subsets searched). -/
theorem hErdos_twohundred_le : hErdos 200 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 5, 8, 10, 25, 40, 50, 100} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 204 ≤ 6` — sub-family engine: 204 = 2^2*3*17 has no practical split (102, 51, 34, 17 are not practical or odd).
The kernel finds `≤ 6`-divisor representations of every `k < 204` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_twohundredfour_le : hErdos 204 ≤ 6 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 6, 12, 17, 34, 51, 102} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 208 ≤ 6` — sub-family engine: the split 208 = 2*104 only gives <= 1+6 = 7; the engine recovers the tight 6.
The kernel finds `≤ 6`-divisor representations of every `k < 208` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_twohundredeight_le : hErdos 208 ≤ 6 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 8, 13, 16, 26, 52, 104} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 210 ≤ 5` — sub-family engine: 210 = 2*3*5*7 has no practical split (every cofactor pair contains an odd number); d(210) = 16 makes the full powerset infeasible -- the first genuine use of the sub-family engine.
The kernel finds `≤ 5`-divisor representations of every `k < 210` inside the
10-element coin chain below (`2^10 = 1024` subsets searched). -/
theorem hErdos_twohundredten_le : hErdos 210 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 7, 10, 15, 21, 42, 70, 105} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 220 ≤ 6` — sub-family engine: 220 = 2^2*5*11 has no practical split (110, 55, 44, 22, 20-cofactor 11 fail).
The kernel finds `≤ 6`-divisor representations of every `k < 220` inside the
10-element coin chain below (`2^10 = 1024` subsets searched). -/
theorem hErdos_twotwenty_le : hErdos 220 ≤ 6 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 5, 10, 11, 20, 44, 55, 110} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 800000 in
/-- `hErdos 224 ≤ 5` — sub-family engine: the split 224 = 2*112 only gives <= 1+6 = 7; the engine recovers the tight 5.
The kernel finds `≤ 5`-divisor representations of every `k < 224` inside the
11-element coin chain below (`2^11 = 2048` subsets searched — the heaviest
decide in the octave, hence the raised heartbeat budget; no 10-element
sub-family of the 11 proper divisors covers every target). -/
theorem hErdos_twotwentyfour_le : hErdos 224 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 7, 8, 14, 16, 28, 32, 56, 112} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 228 ≤ 6` — sub-family engine: 228 = 2^2*3*19 has no practical split (114, 57, 38, 19 are not practical or odd).
The kernel finds `≤ 6`-divisor representations of every `k < 228` inside the
9-element coin chain below (`2^9 = 512` subsets searched). -/
theorem hErdos_twotwentyeight_le : hErdos 228 ≤ 6 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 6, 12, 19, 38, 57, 114} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 234 ≤ 5` — sub-family engine: 234 = 2*3^2*13 has no practical split (117, 78-cofactor 3, 39, 26-cofactor 9, 18-cofactor 13 all involve an odd or non-practical part).
The kernel finds `≤ 5`-divisor representations of every `k < 234` inside the
10-element coin chain below (`2^10 = 1024` subsets searched). -/
theorem hErdos_twothirtyfour_le : hErdos 234 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 3, 6, 9, 13, 26, 39, 78, 117} ?_ ?_ <;> decide

set_option maxRecDepth 40000 in
/-- `hErdos 240 ≤ 5` — sub-family engine: the split 240 = 2*120 only gives <= 1+6 = 7; the engine recovers the tight 5 (d(240) = 20 rules out the full powerset).
The kernel finds `≤ 5`-divisor representations of every `k < 240` inside the
10-element coin chain below (`2^10 = 1024` subsets searched). -/
theorem hErdos_twoforty_le : hErdos 240 ≤ 5 := by
  refine hErdos_le_of_witnesses_from {1, 2, 4, 8, 16, 30, 40, 60, 80, 120} ?_ ?_ <;> decide

set_option maxRecDepth 200000 in
/-- **Every practical number below `256` other than `128` has index at most
`6`.**  Below `128` this is `hErdos_le_six_of_lt_onetwentyeight`; in the
octave `[128, 256)` the 24 practical numbers other than `128` are bounded by
the tight engine values and subadditive splits above (each non-practical
value excluded by a kernel `decide`).  This is strictly sharper than the
threshold `≤ 7` needed for the record-setter: it says `128` is the ONLY
index-`7` practical number in its octave — local uniqueness returns after
failing at `t = 6` (`record_index_six_not_locally_unique`). -/
theorem hErdos_le_six_of_lt_twofiftysix_of_ne {m : ℕ} (hm : IsPractical m)
    (hlt : m < 256) (hne : m ≠ 128) : hErdos m ≤ 6 := by
  by_cases h128 : m < 128
  · exact hErdos_le_six_of_lt_onetwentyeight hm h128
  · push Not at h128
    interval_cases m
    · exact absurd rfl hne
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onethirtytwo_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_oneforty_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onefortyfour_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onefifty_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onefiftysix_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onesixty_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact hErdos_onesixtytwo_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_onesixtyeight_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_oneseventysix_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_oneeighty_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_oneninetytwo_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_oneninetysix_le
    · exact absurd hm (by decide)
    · exact hErdos_oneninetyeight_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact hErdos_twohundred_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twohundredfour_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twohundredeight_le
    · exact absurd hm (by decide)
    · exact hErdos_twohundredten_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twosixteen_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twotwenty_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twotwentyfour_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twotwentyeight_le
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twothirtyfour_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twoforty_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact hErdos_twofiftytwo_le.trans (by norm_num)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)

/-- **Every practical number below `256` has index at most `7`.**  The octave
threshold feeding the `t = 8` record-setter. -/
theorem hErdos_le_seven_of_lt_twofiftysix {m : ℕ} (hm : IsPractical m)
    (hlt : m < 256) : hErdos m ≤ 7 := by
  by_cases h : m = 128
  · subst h
    simp [hErdos_onetwentyeight]
  · exact (hErdos_le_six_of_lt_twofiftysix_of_ne hm hlt h).trans (by omega)

/-- `256` is practical — the power-of-two family at `n = 8`. -/
theorem twofiftysix_practical : IsPractical 256 := by
  simpa using two_pow_practical 8

/-- `hErdos 256 = 8` — the power-of-two formula at `k = 8`. -/
theorem hErdos_twofiftysix : hErdos 256 = 8 := by
  have h := hErdos_two_pow 8
  norm_num at h
  exact h

/-- **Record-setter at `t = 8`: the least practical number with index `8` is
`256 = 2⁸`.**  The record-setter sequence for `t = 1, …, 8` is
`2, 4, 8, 16, 32, 64, 128, 256` — exactly the powers of two, now through five
doublings past the last octave (`[32, 64)`) where the record was locally
unique. -/
theorem minimal_hErdos_eight :
    IsLeast { m : ℕ | IsPractical m ∧ hErdos m = 8 } 256 := by
  constructor
  · exact ⟨twofiftysix_practical, hErdos_twofiftysix⟩
  · rintro m ⟨hpr, h8⟩
    by_contra hlt
    push Not at hlt
    have := hErdos_le_seven_of_lt_twofiftysix hpr hlt
    omega

/-- **Local uniqueness of the record RETURNS at `t = 7`**: `128` is the only
practical number below `256` with index `7`.  Contrast with `t = 6`, where
the record `64` shares its index with `78, 88, 100, 104`
(`record_index_six_not_locally_unique`).  The four index-`6` ties of the
previous octave all double into `[128, 256)` — `156, 176, 200, 208` — but
each doubling DROPS the index bound below the crude subadditive `1 + 6`: the
engine certifies `hErdos 156 ≤ 6`, `176 ≤ 6`, `200 ≤ 5`, `208 ≤ 6`, so none
of them reaches `7`.  Uniqueness is local: nothing here rules out an
index-`7` practical number above `256`. -/
theorem record_index_seven_locally_unique :
    ∀ m, IsPractical m → m < 256 → hErdos m = 7 → m = 128 := by
  intro m hm hlt h7
  by_contra hne
  have := hErdos_le_six_of_lt_twofiftysix_of_ne hm hlt hne
  omega

end Erdos18
