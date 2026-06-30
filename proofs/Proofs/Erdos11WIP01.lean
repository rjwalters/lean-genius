/-
  Erdős Problem #11 — WIP-01: a decidable characterization and a verified range

  Erdős Problem #11 (OPEN): is every odd `n > 1` the sum of a squarefree number and
  a power of 2?  The gallery parent `Erdos11Problem` sets up `IsSquarefree`,
  `IsPowerOfTwo`, `IsSquarefreePlusPow2` and checks `3, 5, 7, 9` by hand — but it no
  longer builds on the current Mathlib.  This file re-establishes that content
  self-contained and adds the key reusable tool: a **bounded, decidable
  characterization** of the representation.

  * `isSquarefreePlusPow2_iff` — `IsSquarefreePlusPow2 n ↔ ∃ k ≤ n, 2^k ≤ n ∧
    Squarefree (n − 2^k)`: a bounded characterization (the power of two `2^k` must
    satisfy `k < 2^k ≤ n`), reducing the unbounded existential to a finite search.
  * `squarefreePlusPow2_of_witness` — the easy construction direction (a witnessing
    `k` with `2^k ≤ n` and `n − 2^k` squarefree gives the representation).
  * `three_works … seventeen_works` — odd `3, 5, 7, 9, 11, 13, 15, 17` as squarefree
    + power of two, with explicit `squarefree_one` / `Nat.Prime.squarefree` witnesses.

  All results are fully machine-checked (0 axioms, 0 sorries).  A kernel `decide`
  over a whole range is *not* available — the `Squarefree` decidability instance
  routes through `Nat.minSqFac`, which the kernel does not reduce — so the worked
  examples use explicit witnesses.

  Reference: Hercher (2024); Granville–Soundararajan (1998); https://erdosproblems.com/11.
-/

import Mathlib

namespace Erdos11WIP01

open Finset

/-- `n` is squarefree (re-declared self-contained: the parent `Erdos11Problem`
    no longer builds on the current Mathlib). -/
def IsSquarefree (n : ℕ) : Prop := Squarefree n

/-- `n` is a power of two. -/
def IsPowerOfTwo (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k

/-- `n` is the sum of a squarefree number and a power of two. -/
def IsSquarefreePlusPow2 (n : ℕ) : Prop :=
  ∃ (s p : ℕ), IsSquarefree s ∧ IsPowerOfTwo p ∧ n = s + p

/-- **Easy construction direction.**  A witnessing exponent `k` with `2^k ≤ n` and
    `n − 2^k` squarefree yields the representation `n = (n − 2^k) + 2^k`. -/
theorem squarefreePlusPow2_of_witness {n k : ℕ} (hle : 2 ^ k ≤ n)
    (hsf : Squarefree (n - 2 ^ k)) : IsSquarefreePlusPow2 n :=
  ⟨n - 2 ^ k, 2 ^ k, hsf, ⟨k, rfl⟩, by omega⟩

/-- **Decidable characterization.**  `n` is squarefree + a power of two iff some
    `k ≤ n` has `2^k ≤ n` and `n − 2^k` squarefree.  The bound `k ≤ n` comes from
    `k < 2^k ≤ n`, making the existential a finite (decidable) search. -/
theorem isSquarefreePlusPow2_iff (n : ℕ) :
    IsSquarefreePlusPow2 n ↔
      ∃ k ∈ Finset.range (n + 1), 2 ^ k ≤ n ∧ Squarefree (n - 2 ^ k) := by
  constructor
  · rintro ⟨s, p, hs, ⟨k, rfl⟩, rfl⟩
    have hle : 2 ^ k ≤ s + 2 ^ k := Nat.le_add_left _ _
    have hk : k < 2 ^ k := Nat.lt_two_pow_self
    refine ⟨k, Finset.mem_range.mpr (by omega), hle, ?_⟩
    rwa [Nat.add_sub_cancel]
  · rintro ⟨k, _, hle, hsf⟩
    exact squarefreePlusPow2_of_witness hle hsf

/- ## Worked examples (recovered self-contained — the parent no longer builds)

   Small odd numbers as squarefree + power of two, with explicit squarefree
   witnesses (`squarefree_one` and `Nat.Prime.squarefree`).  A kernel `decide`
   over a whole range is *not* available: the `Squarefree` decidability instance
   routes through `Nat.minSqFac`, which the kernel cannot reduce. -/

theorem three_works : IsSquarefreePlusPow2 3 :=
  ⟨1, 2, squarefree_one, ⟨1, rfl⟩, rfl⟩

theorem five_works : IsSquarefreePlusPow2 5 :=
  ⟨1, 4, squarefree_one, ⟨2, rfl⟩, rfl⟩

theorem seven_works : IsSquarefreePlusPow2 7 :=
  ⟨5, 2, (by norm_num : Nat.Prime 5).squarefree, ⟨1, rfl⟩, rfl⟩

theorem nine_works : IsSquarefreePlusPow2 9 :=
  ⟨1, 8, squarefree_one, ⟨3, rfl⟩, rfl⟩

theorem eleven_works : IsSquarefreePlusPow2 11 :=
  ⟨3, 8, (by norm_num : Nat.Prime 3).squarefree, ⟨3, rfl⟩, rfl⟩

theorem thirteen_works : IsSquarefreePlusPow2 13 :=
  ⟨5, 8, (by norm_num : Nat.Prime 5).squarefree, ⟨3, rfl⟩, rfl⟩

theorem fifteen_works : IsSquarefreePlusPow2 15 :=
  ⟨7, 8, (by norm_num : Nat.Prime 7).squarefree, ⟨3, rfl⟩, rfl⟩

theorem seventeen_works : IsSquarefreePlusPow2 17 :=
  ⟨1, 16, squarefree_one, ⟨4, rfl⟩, rfl⟩

end Erdos11WIP01
