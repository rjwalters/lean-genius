/-
Erdős Problem #1054: Construction D — OQ-02

## A sharp boundary for divisor-partial-sum representability

The parent file `Erdos1054ConstructionD` (and its OQ-01 follow-up) prove that various
families of numbers are *representable* — `n` is representable if it occurs as a partial
sum of the increasingly-sorted divisor list of some `m ≥ 1`.  Those results only ever
exhibit numbers that **are** representable (e.g. `σ(m)`, the prime-power geometric sums
`1 + p + ⋯ + pᵏ`, the Mersenne numbers).

This file complements that one-sided picture with the **two opposite extremes**:

> **Lower boundary.** `2` is *not* representable: it is the smallest positive integer
> that never appears as a divisor partial sum.  (Indeed the only partial sum below `3`
> is the first one, which is always `1`.)
>
> **Upper boundary.** The set of representable numbers is nonetheless **infinite** — in
> fact unbounded above — because `p + 1 = σ(p)` is representable for every prime `p`.

Together these say representability is a *proper, infinite* subset of `ℕ`: not everything
is representable (`2` is a witness), yet representable numbers grow without bound.

The lower boundary rests on a small new monotonicity fact, `le_of_mem_scanl_add`: over `ℕ`
every entry of `scanl (·+·) b L` is `≥ b`, because addition only increases the running
total.  Combined with `1` being the smallest divisor and the second-smallest divisor being
`≥ 2`, this forces every partial sum to be `1` or `≥ 3`.

All results are `Lean.ofReduceBool`-free (no `native_decide`).

## Results
- `le_of_mem_scanl_add`        — every entry of `scanl (+) b L` over `ℕ` is `≥ b`  (new core)
- `two_not_representable`      — `¬ IsRepresentable 2`  (sharp lower boundary, headline)
- `succ_prime_representable`   — `p + 1 = σ(p)` is representable for every prime `p`
- `representable_unbounded`    — representable numbers are unbounded above
- `representable_infinite`     — `{n | IsRepresentable n}` is infinite  (headline)
- `one_representable`          — `1` is representable (the smallest such)
- `three_representable`, `four_representable` — concrete witnesses `σ(2)`, `σ(3)`
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos1054ConstructionDOQ02

-- ============================================================
-- Definitions (mirrored from `Erdos1054ConstructionD`; we avoid `native_decide`
-- throughout, keeping every result `Lean.ofReduceBool`-free).
-- ============================================================

/-- The divisors of `m`, listed in increasing order. -/
def sortedDivisors (m : ℕ) : List ℕ :=
  m.divisors.sort (· ≤ ·)

/-- The running (cumulative) sums of the sorted divisors of `m`. -/
def partialDivisorSums (m : ℕ) : List ℕ :=
  ((sortedDivisors m).scanl (· + ·) 0).tail

/-- `n` is *representable* if it occurs as a partial divisor sum of some `m ≥ 1`. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ n ∈ (partialDivisorSums m)

-- ============================================================
-- Part 0: List-folding / scanning helpers
-- ============================================================

/--
Folding addition over a list with an arbitrary starting accumulator `a`
just adds `a` to the list's sum.
-/
theorem foldl_add_acc (a : ℕ) (L : List ℕ) : L.foldl (· + ·) a = a + L.sum := by
  induction L generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.sum_cons]; ring

/--
**New core monotonicity lemma.** Over `ℕ`, every entry of the running-sum list
`scanl (·+·) b L` is at least the initial accumulator `b`: scanning by addition can
only increase the running total.
-/
theorem le_of_mem_scanl_add (b : ℕ) (L : List ℕ) :
    ∀ x ∈ List.scanl (· + ·) b L, b ≤ x := by
  induction L generalizing b with
  | nil => intro x hx; rw [List.scanl_nil, List.mem_singleton] at hx; omega
  | cons a as ih =>
    intro x hx
    rw [List.scanl_cons, List.mem_cons] at hx
    rcases hx with h | h
    · omega
    · have := ih (b + a) x h; omega

-- ============================================================
-- Part 1: The σ(m) machinery (ported, axiom-free) — gives the upper boundary
-- ============================================================

/-- The sum of the sorted divisor list of `m` is the sum-of-divisors function `σ(m)`. -/
theorem sortedDivisors_sum (m : ℕ) :
    (sortedDivisors m).sum = ∑ d ∈ m.divisors, d := by
  rw [sortedDivisors, (Finset.sort_perm_toList _ _).sum_eq, Finset.sum_toList]

/-- For every `m ≥ 1`, `σ(m)` occurs as the final divisor partial sum of `m`. -/
theorem sum_divisors_mem_partialSums (m : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ m.divisors, d) ∈ partialDivisorSums m := by
  rw [← sortedDivisors_sum]
  obtain ⟨a, l, hal⟩ : ∃ a l, sortedDivisors m = a :: l := by
    rcases h : sortedDivisors m with _ | ⟨a, l⟩
    · exfalso
      have hlen : (sortedDivisors m).length = m.divisors.card := by
        rw [sortedDivisors, Finset.length_sort]
      rw [h, List.length_nil] at hlen
      have h1 : (1 : ℕ) ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
      have := Finset.card_pos.mpr ⟨1, h1⟩
      omega
    · exact ⟨a, l, rfl⟩
  unfold partialDivisorSums
  rw [hal, List.scanl_cons, List.tail_cons]
  have hne : List.scanl (· + ·) (0 + a) l ≠ [] := List.scanl_ne_nil
  have hmem := List.getLast_mem hne
  rw [List.getLast_scanl hne] at hmem
  have hval : List.foldl (· + ·) (0 + a) l = (a :: l).sum := by
    rw [foldl_add_acc, List.sum_cons]; ring
  rwa [hval] at hmem

/-- **σ representability.** `σ(m)` is representable for every `m ≥ 1`. -/
theorem sum_divisors_representable (m : ℕ) (hm : 1 ≤ m) :
    IsRepresentable (∑ d ∈ m.divisors, d) :=
  ⟨m, hm, sum_divisors_mem_partialSums m hm⟩

/-- The geometric sum `∑_{i=0}^{k} p^i = σ(pᵏ)` is representable for every prime `p`. -/
theorem geom_sum_representable (p k : ℕ) (hp : p.Prime) :
    IsRepresentable (∑ i ∈ Finset.range (k + 1), p ^ i) := by
  have hpk : 1 ≤ p ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hp.pos.ne')
  have h := sum_divisors_representable (p ^ k) hpk
  rwa [Nat.sum_divisors_prime_pow (f := fun x => x) hp] at h

-- ============================================================
-- Part 2: Upper boundary — representable numbers are unbounded / infinite
-- ============================================================

/--
For every prime `p`, the successor `p + 1 = σ(p)` is representable.  This is the
`k = 1` instance of `geom_sum_representable` (`∑_{i=0}^{1} p^i = 1 + p`).
-/
theorem succ_prime_representable {p : ℕ} (hp : p.Prime) : IsRepresentable (p + 1) := by
  have h := geom_sum_representable p 1 hp
  have hval : (∑ i ∈ Finset.range (1 + 1), p ^ i) = p + 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]; ring
  rwa [hval] at h

/--
**Upper boundary.** The representable numbers are unbounded above: beyond any `N` there is
a representable number, namely `p + 1` for a prime `p > N`.
-/
theorem representable_unbounded (N : ℕ) : ∃ n, N < n ∧ IsRepresentable n := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨p + 1, by omega, succ_prime_representable hpp⟩

/--
**Headline (upper boundary).** The set of representable numbers is infinite: it cannot be
finite, since a finite set of naturals is bounded above but representable numbers are not.
-/
theorem representable_infinite : {n | IsRepresentable n}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨n, hn, hrep⟩ := representable_unbounded N
  have : n ≤ N := hN hrep
  omega

-- ============================================================
-- Part 3: Lower boundary — 2 is not representable
-- ============================================================

/--
**Headline (lower boundary).** `2` is *not* representable: it never appears as a divisor
partial sum.  The first partial sum of any `m` is its smallest divisor `1`; every later
partial sum already includes the second-smallest divisor `≥ 2`, hence is `≥ 1 + 2 = 3`.
So no partial sum equals `2`.
-/
theorem two_not_representable : ¬ IsRepresentable 2 := by
  rintro ⟨m, hm, hmem⟩
  -- Standing facts about the sorted divisor list of `m`.
  have h1S : (1 : ℕ) ∈ sortedDivisors m :=
    (Finset.mem_sort _).mpr (Nat.one_mem_divisors.mpr (by omega))
  have hsorted : List.Pairwise (· ≤ ·) (sortedDivisors m) := Finset.pairwise_sort m.divisors (· ≤ ·)
  have hnodup : (sortedDivisors m).Nodup := Finset.sort_nodup _ _
  have hmemS : ∀ x ∈ sortedDivisors m, x ∈ m.divisors :=
    fun x hx => (Finset.mem_sort _).mp hx
  -- Split on the shape of the sorted divisor list.
  rcases hS : sortedDivisors m with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · -- empty: there are no partial sums at all
    rw [hS] at h1S; simp at h1S
  · -- single divisor `[a]`: the only partial sum is `a`, and `a = 1`
    rw [hS] at h1S; rw [List.mem_singleton] at h1S
    unfold partialDivisorSums at hmem
    rw [hS, List.scanl_cons, List.tail_cons, List.scanl_nil, List.mem_singleton] at hmem
    omega
  · -- two or more divisors `a :: b :: rest`
    rw [hS] at h1S hsorted hnodup
    obtain ⟨hall, _⟩ := List.pairwise_cons.mp hsorted
    -- `a = 1`: `a` is a positive divisor and `a ≤ 1` since `1` is in the list
    have haDiv : a ∈ m.divisors := hmemS a (by rw [hS]; exact List.mem_cons_self)
    have hapos : 1 ≤ a := Nat.pos_of_mem_divisors haDiv
    have hle1 : a ≤ 1 := by
      rcases List.mem_cons.mp h1S with h | h
      · omega
      · exact hall 1 h
    have ha1 : a = 1 := by omega
    -- `b ≥ 2`: `a ≤ b` and `a ≠ b` (nodup), with `a = 1`
    have hab : a ≤ b := hall b (List.mem_cons_self)
    have hanb : a ≠ b := by
      intro h
      exact (List.nodup_cons.mp hnodup).1 (by rw [h]; exact List.mem_cons_self)
    have hb2 : 2 ≤ b := by omega
    -- The partial sums of `m` are exactly `scanl (+) (0+a) (b :: rest)`.
    unfold partialDivisorSums at hmem
    rw [hS, List.scanl_cons, List.tail_cons, List.scanl_cons, List.mem_cons] at hmem
    rcases hmem with h | h
    · omega
    · have := le_of_mem_scanl_add (0 + a + b) rest 2 h
      omega

-- ============================================================
-- Part 4: Concrete witnesses at the boundary
-- ============================================================

/-- `1 = σ(1)` is representable — the smallest representable number. -/
theorem one_representable : IsRepresentable 1 := by
  have h := sum_divisors_representable 1 (le_refl 1)
  simpa using h

/-- `3 = σ(2)` is representable (`1 + 2`). -/
theorem three_representable : IsRepresentable 3 := by
  have h := succ_prime_representable Nat.prime_two; norm_num at h; exact h

/-- `4 = σ(3)` is representable (`1 + 3`). -/
theorem four_representable : IsRepresentable 4 := by
  have h := succ_prime_representable (by norm_num : Nat.Prime 3); norm_num at h; exact h

end Erdos1054ConstructionDOQ02
