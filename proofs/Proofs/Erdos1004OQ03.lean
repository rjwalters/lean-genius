import Mathlib

/-
# Erdős #1004 — An Unconditional, Axiom-Free Run-Length Bound via Totient Parity

## Background
A *distinct totient run* of length `K` starting at `n` is a block
`φ(n+1), φ(n+2), …, φ(n+K)` of pairwise-distinct totient values.  Erdős #1004
asks how long such runs can be.  The deep **Erdős–Pomerance–Sárközy (1987)**
theorem gives, for large `n`,

    K ≤ n / exp(c·(log n)^{1/3}),

an exponential improvement over the trivial `K ≤ n`.  In the parent gallery
entry this EPS bound is recorded as an **`axiom`** (it is far beyond elementary
methods), and it is the entry's only upper bound on run length.

## What this file adds
A **fully verified, 0-axiom, unconditional** upper bound:

    n ≥ 2  ⟹  every distinct totient run starting at n has length  K ≤ n − 1.

It does **not** improve EPS (EPS is asymptotically far stronger), but it is the
first *axiom-free* run-length bound for this problem, it holds for **all** `n ≥ 2`
with no threshold, and it is in fact **sharp** for small `n` (e.g. the maximal
run at `n = 3` is `φ(4), φ(5) = 2, 4`, of length `K = 2 = n − 1`).

## The idea
For every `m ≥ 3` the totient `φ(m)` is **even** (`Nat.totient_even`) and
satisfies `2 ≤ φ(m) ≤ m − 1`.  Inside a run starting at `n ≥ 2` every argument
`m = n+i ≥ 3`, so the `K` distinct totient values are `K` distinct **even**
numbers lying in `[2, n+K−1]`.  Halving gives `K` distinct integers in
`[1, (n+K−1)/2]`, whence `K ≤ (n+K−1)/2`, i.e. `K ≤ n − 1`.
-/

namespace Erdos1004OQ03

open Finset

/-- A distinct totient run of length `K` starting at `n`: the totient is
injective on the block of arguments `{n+1, …, n+K}`.  (Self-contained form of the
parent entry's `IsDistinctTotientRun`.) -/
def IsDistinctTotientRun (n K : ℕ) : Prop :=
  Set.InjOn Nat.totient (Finset.Icc (n + 1) (n + K) : Finset ℕ)

/-! ## Parity / size facts about totients of arguments `≥ 3` -/

/-- For `m ≥ 3` the totient is even and at least `2`. -/
theorem totient_even_ge_two {m : ℕ} (hm : 3 ≤ m) : Even (Nat.totient m) ∧ 2 ≤ Nat.totient m := by
  have hev : Even (Nat.totient m) := Nat.totient_even (by omega)
  refine ⟨hev, ?_⟩
  have hpos : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
  rcases hev with ⟨t, ht⟩
  omega

/-- `φ(m) ≤ m − 1` for `m ≥ 2`. -/
theorem totient_le_pred {m : ℕ} (hm : 2 ≤ m) : Nat.totient m ≤ m - 1 := by
  have := Nat.totient_lt m (by omega)
  omega

/-! ## The main unconditional bound -/

/-- **Unconditional run-length bound (0 axioms).**
If `n ≥ 2` and `φ` is injective on `{n+1, …, n+K}` (a distinct totient run),
then `K ≤ n − 1`.  Proof: the `K` distinct totient values are distinct even
numbers in `[2, n+K−1]`; halving embeds them into `[1, (n+K−1)/2]`. -/
theorem run_length_le_pred {n K : ℕ} (hn : 2 ≤ n) (hrun : IsDistinctTotientRun n K) :
    K ≤ n - 1 := by
  -- The halving map sends the run arguments injectively into `Icc 1 ((n+K-1)/2)`.
  have hmem : ∀ m ∈ Finset.Icc (n + 1) (n + K), Nat.totient m / 2 ∈ Finset.Icc 1 ((n + K - 1) / 2) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm3 : 3 ≤ m := by omega
    obtain ⟨_, hge2⟩ := totient_even_ge_two hm3
    have hle : Nat.totient m ≤ m - 1 := totient_le_pred (by omega)
    rw [Finset.mem_Icc]
    constructor
    · omega
    · calc Nat.totient m / 2 ≤ (m - 1) / 2 := Nat.div_le_div_right hle
        _ ≤ (n + K - 1) / 2 := Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun m => Nat.totient m / 2) (Finset.Icc (n + 1) (n + K) : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    have ha3 : 3 ≤ a := by omega
    have hb3 : 3 ≤ b := by omega
    obtain ⟨hea, _⟩ := totient_even_ge_two ha3
    obtain ⟨heb, _⟩ := totient_even_ge_two hb3
    -- equal halves of even numbers ⟹ equal totients
    have heq : Nat.totient a = Nat.totient b := by
      obtain ⟨s, hs⟩ := hea
      obtain ⟨t, ht⟩ := heb
      simp only at hab
      omega
    -- apply injectivity of φ on the run
    exact hrun (by simp [Finset.coe_Icc, Set.mem_Icc]; omega)
      (by simp [Finset.coe_Icc, Set.mem_Icc]; omega) heq
  -- card comparison
  have hcard : (Finset.Icc (n + 1) (n + K)).card ≤ (Finset.Icc 1 ((n + K - 1) / 2)).card :=
    Finset.card_le_card_of_injOn _ hmem hinj
  rw [Nat.card_Icc, Nat.card_Icc] at hcard
  -- |Icc (n+1) (n+K)| = K  and  |Icc 1 q| = q
  have hK : n + K + 1 - (n + 1) = K := by omega
  rw [hK] at hcard
  -- hcard : K ≤ (n+K-1)/2 + 1 - 1 = (n+K-1)/2
  omega

/-- Strict form: a distinct totient run starting at `n ≥ 2` has length `K < n`. -/
theorem run_length_lt {n K : ℕ} (hn : 2 ≤ n) (hrun : IsDistinctTotientRun n K) :
    K < n := by
  have := run_length_le_pred hn hrun
  omega

/-- Reformulation: there is **no** distinct totient run of length `n` starting at
`n ≥ 2` (the bound `K ≤ n − 1` cannot be met with equality at `K = n`). -/
theorem no_run_of_length_n {n : ℕ} (hn : 2 ≤ n) : ¬ IsDistinctTotientRun n n := by
  intro h
  have := run_length_lt hn h
  omega

/-! ## Sharpness at small `n` -/

/-- The bound is sharp at `n = 3`: `φ(4), φ(5) = 2, 4` is a distinct run of
length `K = 2 = n − 1`. -/
theorem run_sharp_at_three : IsDistinctTotientRun 3 2 := by
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  -- arguments lie in {4, 5}
  interval_cases a <;> interval_cases b <;> revert hab <;> decide

/-- And no run of length `3` starts at `n = 3` (consistent with `K ≤ n − 1 = 2`):
`φ(6) = 2 = φ(4)` breaks distinctness. -/
theorem no_run_three_three : ¬ IsDistinctTotientRun 3 3 := no_run_of_length_n (by norm_num)

end Erdos1004OQ03
