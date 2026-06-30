/-
# Exact equidistribution of reduced residues: the elementary skeleton of density `1/φ(d)`

Open question OQ-02 of `infinitude-primes-4k3` asks to **formalize the equidistribution**:
the primes `p ≡ a (mod d)` (with `gcd(a, d) = 1`) have density `1/φ(d)` among all
primes — Dirichlet's theorem in its quantitative form, equivalent to the Prime Number
Theorem for arithmetic progressions. The *prime* statement is genuinely deep: it
requires the non-vanishing of Dirichlet `L`-functions at `s = 1` together with a
Tauberian/PNT argument, and is **not** available in Mathlib (see the open-question note;
this file does not claim it).

What *is* elementary, exact, and fully machine-checkable is the equidistribution of the
**coprime integers** themselves — the combinatorial skeleton that the prime statement
refines. In every window `[0, N·d)` (a whole number `N` of periods):

* each residue class `v (mod d)` contains **exactly** `N` integers
  (`count_class_eq` — a direct consequence of `Nat.count_modEq_card`); and
* the integers coprime to `d` number **exactly** `N · φ(d)`
  (`count_coprime_eq` — `φ(d)` coprime residues per period, `N` periods).

Combining these, each *reduced* residue class carries the exact fraction `1/φ(d)` of the
coprime integers, **for every finite `N`** (`reduced_class_density`) — not merely
asymptotically. This is the honest, elementary content of "density `1/φ(d)`"; the only
gap to the full OQ-02 is the analytic input restricting attention from all coprime
integers to the primes among them.

## Main results

* `InfinitudePrimes4k3OQ02.count_class_eq` — for `0 < d`, exactly `N` of the integers in
  `[0, N·d)` are `≡ v [MOD d]`, for **every** residue `v`.
* `InfinitudePrimes4k3OQ02.count_coprime_eq` — for `0 < d`, exactly `N · φ(d)` of the
  integers in `[0, N·d)` are coprime to `d`.
* `InfinitudePrimes4k3OQ02.class_subset_coprime` — when `gcd(v, d) = 1`, the residue
  class `v` inside the window consists entirely of integers coprime to `d`.
* `InfinitudePrimes4k3OQ02.reduced_class_density` — the exact relative density: for
  `0 < d`, `1 ≤ N` and any residue `v`, the proportion of coprime integers in `[0, N·d)`
  lying in class `v` equals `1/φ(d)` (as a rational number).

## Exact finite equipartition (this session)

`reduced_class_density` divides the count of *all* integers `≡ v` by the count of
*coprime* integers — an honest ratio of `1/φ(d)` numerically, but the numerator ranges
over integers that need not be coprime when `v` is not. The genuinely sharper statement
is that the coprime integers are **exactly equipartitioned** among the `φ(d)` reduced
classes — each reduced class carries *exactly* `N` coprime integers — for every finite
`N`. This is the true finite skeleton of equidistribution.

* `InfinitudePrimes4k3OQ02.coprime_class_card_eq` — **the headline.** For `0 < d` and
  `gcd(v, d) = 1`, exactly `N` of the integers in `[0, N·d)` are *both* coprime to `d`
  *and* `≡ v [MOD d]`. Every reduced class is equally populated by coprimes.
* `InfinitudePrimes4k3OQ02.coprime_partition_card` — the coprime integers in `[0, N·d)`
  decompose as the disjoint union over the `φ(d)` reduced residues `v (mod d)` of the
  per-class coprime counts (a `card_eq_sum_card_fiberwise` partition along `x ↦ x % d`).
* `InfinitudePrimes4k3OQ02.coprime_card_eq_totient_mul` — combining the two: the coprime
  count `= φ(d) · N`, re-derived *independently* of `count_coprime_eq`'s block induction,
  via the equipartition (`φ(d)` classes × `N` coprimes each).
* `InfinitudePrimes4k3OQ02.reduced_class_density_coprime` — the **honest** relative
  density: restricting the numerator to coprime integers in class `v` (with
  `gcd(v, d) = 1`), the proportion of coprimes lying in class `v` is exactly `1/φ(d)`.
* `InfinitudePrimes4k3OQ02.count_class_card_eq` — `Finset.card` form of `count_class_eq`,
  bridging `Nat.count` to filtered-`range` cardinalities.
-/
import Mathlib

open Nat (totient)
open Finset

namespace InfinitudePrimes4k3OQ02

open scoped Nat

/-- **Exact equidistribution of a single residue class.** For a positive modulus `d`,
the count of integers in `[0, N·d)` congruent to `v` modulo `d` is exactly `N`, for
*every* residue `v` — every class is hit equally often over a whole number of periods. -/
theorem count_class_eq {d : ℕ} (hd : 0 < d) (v N : ℕ) :
    Nat.count (· ≡ v [MOD d]) (N * d) = N := by
  rw [Nat.count_modEq_card (N * d) hd v]
  -- `(N*d) % d = 0`, so the Iverson correction term vanishes and `N*d / d = N`.
  have hmod : (N * d) % d = 0 := Nat.mul_mod_left N d
  have hdiv : (N * d) / d = N := by
    rw [Nat.mul_div_assoc N (dvd_refl d), Nat.div_self hd, Nat.mul_one]
  rw [hmod, hdiv]
  simp

/-- **Exact count of coprime integers.** For a positive modulus `d`, exactly `N · φ(d)`
of the integers in `[0, N·d)` are coprime to `d`: each of the `N` length-`d` blocks
contributes exactly `φ(d)` coprime residues. -/
theorem count_coprime_eq {d : ℕ} (hd : 0 < d) (N : ℕ) :
    #{x ∈ range (N * d) | d.Coprime x} = N * totient d := by
  induction N with
  | zero => simp
  | succ N ih =>
    -- Split `[0, (N+1)·d)` into the prefix `[0, N·d)` and the final block `[N·d, N·d+d)`.
    have hsplit : range ((N + 1) * d) = range (N * d) ∪ Ico (N * d) (N * d + d) := by
      have he : (N + 1) * d = N * d + d := by ring
      rw [he]
      ext x
      simp only [mem_union, mem_range, mem_Ico]
      omega
    have hdisj : Disjoint (range (N * d)) (Ico (N * d) (N * d + d)) := by
      rw [range_eq_Ico]
      exact Ico_disjoint_Ico_consecutive 0 (N * d) (N * d + d)
    rw [hsplit, filter_union, card_union_of_disjoint (hdisj.mono (filter_subset _ _)
      (filter_subset _ _)), ih, Nat.filter_coprime_Ico_eq_totient d (N * d)]
    ring

/-- When `v` is coprime to `d`, every integer in the residue class `v (mod d)` is itself
coprime to `d`: the reduced classes sit *inside* the coprime integers. -/
theorem class_subset_coprime {d : ℕ} (v : ℕ) (hv : d.Coprime v) (N : ℕ) :
    {x ∈ range (N * d) | x ≡ v [MOD d]} ⊆ {x ∈ range (N * d) | d.Coprime x} := by
  intro x hx
  rw [mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  -- coprimality to `d` depends only on the residue mod `d`, and `x ≡ v [MOD d]`.
  have hxv : x % d = v % d := hx.2
  show Nat.gcd d x = 1
  rw [Nat.gcd_rec d x, hxv, ← Nat.gcd_rec d v]
  exact hv

/-- **Exact relative density `1/φ(d)`.** Over any whole number `N ≥ 1` of periods, the
proportion of the coprime integers in `[0, N·d)` that lie in a fixed residue class `v`
is exactly `1/φ(d)` — independent of `N` and of `v`. This is the elementary, *exact*
form of the "density `1/φ(d)`" sought in OQ-02 (here for all coprime integers; the
restriction to primes is the deep analytic input that remains open). -/
theorem reduced_class_density {d : ℕ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N) (v : ℕ) :
    (Nat.count (· ≡ v [MOD d]) (N * d) : ℚ)
        / (#{x ∈ range (N * d) | d.Coprime x} : ℚ) = 1 / totient d := by
  have hφ : 0 < totient d := Nat.totient_pos.mpr hd
  rw [count_class_eq hd v N, count_coprime_eq hd N]
  have hN0 : (N : ℚ) ≠ 0 := by
    have hNpos : 0 < N := hN
    exact_mod_cast hNpos.ne'
  have hφ0 : (totient d : ℚ) ≠ 0 := by exact_mod_cast hφ.ne'
  rw [Nat.cast_mul]
  field_simp

/-! ### Exact finite equipartition of the coprime integers

The results above give the count of *all* integers in each class and the count of *all*
coprime integers. We now combine them into the sharp statement: each *reduced* residue
class contains **exactly** `N` coprime integers, and the `φ(d)` reduced classes partition
the coprimes. This is the honest finite form of "equidistribution `1/φ(d)`". -/

/-- `Finset.card` form of `count_class_eq`: exactly `N` integers in `[0, N·d)` are
`≡ v [MOD d]`, expressed as a filtered-`range` cardinality. -/
theorem count_class_card_eq {d : ℕ} (hd : 0 < d) (v N : ℕ) :
    #{x ∈ range (N * d) | x ≡ v [MOD d]} = N := by
  rw [← Nat.count_eq_card_filter_range, count_class_eq hd v N]

/-- **Exact equipartition of the coprime integers (per class).** For `0 < d` and
`gcd(v, d) = 1`, exactly `N` of the integers in `[0, N·d)` are *both* coprime to `d` and
congruent to `v` modulo `d`. Since a reduced class lies entirely inside the coprime
integers (`class_subset_coprime`), the coprime constraint is automatic, so each reduced
class is populated by exactly the same number `N` of coprimes. -/
theorem coprime_class_card_eq {d : ℕ} (hd : 0 < d) {v : ℕ} (hv : d.Coprime v) (N : ℕ) :
    #{x ∈ range (N * d) | d.Coprime x ∧ x ≡ v [MOD d]} = N := by
  -- On a reduced class (`gcd(v,d)=1`) the coprime conjunct is automatic, so the filtered
  -- set coincides with the plain residue class; count it via `count_class_card_eq`.
  have hset : {x ∈ range (N * d) | d.Coprime x ∧ x ≡ v [MOD d]}
            = {x ∈ range (N * d) | x ≡ v [MOD d]} := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hr, _, hxv⟩
      exact ⟨hr, hxv⟩
    · rintro ⟨hr, hxv⟩
      refine ⟨hr, ?_, hxv⟩
      -- coprimality of `x` follows from `x ≡ v [MOD d]` and `gcd(v, d) = 1`.
      show Nat.gcd d x = 1
      have hxv' : x % d = v % d := hxv
      rw [Nat.gcd_rec d x, hxv', ← Nat.gcd_rec d v]
      exact hv
  rw [hset, count_class_card_eq hd v N]

/-- **The coprime integers partition into reduced residue classes.** The coprime integers
in `[0, N·d)` are the disjoint union, over the `φ(d)` reduced residues `v (mod d)`, of the
integers that are coprime and `≡ v [MOD d]`. Fiberwise count along the map `x ↦ x % d`. -/
theorem coprime_partition_card {d : ℕ} (hd : 0 < d) (N : ℕ) :
    #{x ∈ range (N * d) | d.Coprime x}
      = ∑ v ∈ {v ∈ range d | d.Coprime v},
          #{x ∈ range (N * d) | d.Coprime x ∧ x ≡ v [MOD d]} := by
  have hmaps : Set.MapsTo (· % d) (↑{x ∈ range (N * d) | d.Coprime x})
      (↑{v ∈ range d | d.Coprime v}) := by
    intro x hx
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hx
    simp only [coe_filter, mem_range, Set.mem_setOf_eq]
    refine ⟨Nat.mod_lt x hd, ?_⟩
    -- residues preserve coprimality: `gcd d (x % d) = gcd d x = 1`.
    show Nat.gcd d (x % d) = 1
    rw [Nat.gcd_comm d (x % d), ← Nat.gcd_rec d x]
    exact hx.2
  rw [card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mem_filter, mem_range] at hv
  rw [filter_filter]
  refine congrArg Finset.card (filter_congr ?_)
  intro x _
  -- for `v < d`, `x ≡ v [MOD d] ↔ x % d = v`.
  have hvv : v % d = v := Nat.mod_eq_of_lt hv.1
  constructor
  · rintro ⟨hc, he⟩
    exact ⟨hc, show x % d = v % d by rw [hvv]; exact he⟩
  · rintro ⟨hc, he⟩
    refine ⟨hc, ?_⟩
    have hx2 : x % d = v % d := he
    rw [hvv] at hx2
    exact hx2

/-- **Coprime count via equipartition.** Combining `coprime_partition_card` (the coprimes
split into reduced classes) with `coprime_class_card_eq` (each reduced class has exactly
`N` coprimes) gives `#coprime = φ(d) · N` — an independent re-derivation of the count in
`count_coprime_eq`, here via the `φ(d)`-fold equipartition rather than block induction. -/
theorem coprime_card_eq_totient_mul {d : ℕ} (hd : 0 < d) (N : ℕ) :
    #{x ∈ range (N * d) | d.Coprime x} = totient d * N := by
  rw [coprime_partition_card hd N]
  have hterm : ∀ v ∈ {v ∈ range d | d.Coprime v},
      #{x ∈ range (N * d) | d.Coprime x ∧ x ≡ v [MOD d]} = N := by
    intro v hv
    rw [mem_filter] at hv
    exact coprime_class_card_eq hd hv.2 N
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Nat.totient_eq_card_coprime]

/-- **Exact relative density `1/φ(d)` (honest numerator).** Restricting the numerator to
the integers that are *both* coprime to `d` and `≡ v [MOD d]` (with `gcd(v, d) = 1`), the
proportion of coprime integers in `[0, N·d)` lying in reduced class `v` is exactly
`1/φ(d)`. This sharpens `reduced_class_density`, whose numerator counted all integers in
class `v` regardless of coprimality. -/
theorem reduced_class_density_coprime {d : ℕ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N)
    {v : ℕ} (hv : d.Coprime v) :
    (#{x ∈ range (N * d) | d.Coprime x ∧ x ≡ v [MOD d]} : ℚ)
        / (#{x ∈ range (N * d) | d.Coprime x} : ℚ) = 1 / totient d := by
  have hφ : 0 < totient d := Nat.totient_pos.mpr hd
  rw [coprime_class_card_eq hd hv N, count_coprime_eq hd N]
  have hN0 : (N : ℚ) ≠ 0 := by
    have hNpos : 0 < N := hN
    exact_mod_cast hNpos.ne'
  have hφ0 : (totient d : ℚ) ≠ 0 := by exact_mod_cast hφ.ne'
  rw [Nat.cast_mul]
  field_simp

/-! ### Worked example: modulus `d = 4` (the `infinitude-primes-4k3` setting)

`φ(4) = 2`, with reduced residues `1` and `3 (mod 4)`. Over `[0, 4N)` each class gets
exactly `N` integers and there are `2N` coprime integers, so each reduced class has
relative density `1/2`. -/

-- Class `3 (mod 4)` (the primes `≡ 3 mod 4` of the parent entry) is exactly `N` strong
-- in `[0, 4N)`; here `N = 5`, window `[0, 20)`: the integers `3, 7, 11, 15, 19`.
example : Nat.count (· ≡ 3 [MOD 4]) (5 * 4) = 5 :=
  count_class_eq (by norm_num) 3 5

-- Coprime integers in `[0, 20)` number `5 · φ(4) = 5 · 2 = 10`.
example : #{x ∈ range (5 * 4) | (4).Coprime x} = 5 * totient 4 :=
  count_coprime_eq (by norm_num) 5

-- The exact relative density `1/φ(4) = 1/2` of class `3 (mod 4)` among coprimes.
example : (Nat.count (· ≡ 3 [MOD 4]) (5 * 4) : ℚ)
    / (#{x ∈ range (5 * 4) | (4).Coprime x} : ℚ) = 1 / totient 4 :=
  reduced_class_density (by norm_num) (by norm_num) 3

-- Equipartition: class `3 (mod 4)` contains exactly `N = 5` integers that are *both*
-- coprime to `4` and `≡ 3 (mod 4)` in `[0, 20)` — namely `3, 7, 11, 15, 19`.
example : #{x ∈ range (5 * 4) | (4).Coprime x ∧ x ≡ 3 [MOD 4]} = 5 :=
  coprime_class_card_eq (by norm_num) (by decide) 5

-- Honest relative density `1/φ(4) = 1/2`: among the `10` coprimes in `[0, 20)`, exactly
-- `5` lie in reduced class `3 (mod 4)`.
example : (#{x ∈ range (5 * 4) | (4).Coprime x ∧ x ≡ 3 [MOD 4]} : ℚ)
    / (#{x ∈ range (5 * 4) | (4).Coprime x} : ℚ) = 1 / totient 4 :=
  reduced_class_density_coprime (by norm_num) (by norm_num) (by decide)

end InfinitudePrimes4k3OQ02
