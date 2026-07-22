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
  obtain ⟨hm1, _⟩ := h
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

end Erdos18
