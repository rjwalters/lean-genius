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
  rw [Nat.count_modEq_card hd v]
  -- `(N*d) % d = 0`, so the Iverson correction term vanishes and `N*d / d = N`.
  have hmod : (N * d) % d = 0 := Nat.mul_mod_left N d
  rw [hmod, Nat.mul_div_cancel _ hd]
  simp [Nat.not_lt_zero]

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
      rw [range_eq_Ico, range_eq_Ico, Ico_union_Ico_eq_Ico (Nat.zero_le _)
        (by nlinarith)]
      congr 1; ring
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
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast Nat.pos_iff.mp hN |>.ne'
  have hφ0 : (totient d : ℚ) ≠ 0 := by exact_mod_cast hφ.ne'
  rw [Nat.cast_mul]
  field_simp
  ring

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

end InfinitudePrimes4k3OQ02
