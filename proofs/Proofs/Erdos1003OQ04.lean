/-
  Erdős Problem #1003 — Open Question OQ-04:
  "Are there four consecutive integers with equal Euler totient, i.e. is there an
   `n` with `φ n = φ (n+1) = φ (n+2) = φ (n+3)`?"

This file does NOT resolve the open question.  Existence of a length-4 run of
equal totients is a special case (`k = 3`) of Erdős's strong conjecture — that
for every `k` the set `{ n | φ n = φ (n+1) = ⋯ = φ (n+k) }` is infinite — and
is **open even as an existence statement**: no example is known.  The base case
`k = 1` (are there infinitely many `n` with `φ n = φ (n+1)`?) is #1003 itself and
is unsolved.

What is genuinely provable — and is the content of this file — is the exact
*structural reduction* that explains why length-4 runs are so elusive, together
with the concrete numerical record.

  1. **Run reduction.**  A length-`(k+1)` run of equal totients at `n` is exactly
     a block of `k` *consecutive* members of the Erdős #1003 solution set
     `A001274 = { m | φ m = φ (m+1) }`:

         `n ∈ CKE k  ↔  ∀ i < k, (n+i) ∈ ConsecutiveEqualTotients`.

     In particular a four-term run (`k = 3`) is precisely *three consecutive*
     members `n, n+1, n+2` of A001274 (`mem_fcet_iff_three_consecutive`).  This
     pins down the difficulty: it is already open whether A001274 contains a
     single consecutive *pair* infinitely often — a four-run needs a consecutive
     *triple*.

  2. **Existence equivalences.**  The OQ-04 existence question is equivalent to
     "`CKE 3` is nonempty", i.e. to "A001274 contains three consecutive
     integers", tying it cleanly into the `CKE` hierarchy of the sibling OQ-02
     file and to Erdős's strong conjecture at `k = 3`.

  3. **The record run.**  `5186` realises a run of length **3**
     (`φ 5186 = φ 5187 = φ 5188 = 2592`) — the longest run of consecutive equal
     totients currently known — and this run does *not* extend to length 4
     (`φ 5189 = 5188 ≠ 2592`).  Equivalently `5186, 5187 ∈ A001274` are two
     consecutive members, while a fourth term would require a third.  Up to
     `10^15` the pair `(5186, 5187)` is the *only* consecutive pair in A001274
     (Kinlaw–Kobayashi–Pomerance 2020; Resta, McCranie), so there is **no
     four-run below `10^15`**.

The structural results (§1–§2) are fully machine-checked with **0 `sorry` and 0
axioms** beyond Mathlib's foundational ones.  The concrete numerical record (§3)
is discharged by `native_decide`, which additionally relies on the
`Lean.ofReduceBool` axiom (kernel compiler reduction of `Nat.totient` at the
specific inputs); those lemmas are grouped and flagged separately.

The definitions agree verbatim with the parent #1003 entry
(`Proofs.Erdos1003Problem`) and the sibling files OQ-02 / OQ-03.

Reference: https://erdosproblems.com/1003
OEIS: A001274 (numbers k with φ k = φ (k+1)).
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat Set

namespace Erdos1003.OQ04

/-! ## Definitions (mirroring `Proofs.Erdos1003Problem`)

Reproduced here so the file is self-contained; they agree verbatim with the
definitions in the parent #1003 entry and the sibling OQ-02 / OQ-03 files. -/

/-- The set of `n` with `φ n = φ (n+1)` — the main Erdős #1003 set (OEIS A001274). -/
def ConsecutiveEqualTotients : Set ℕ :=
  { n : ℕ | φ n = φ (n + 1) }

/-- The set of `n` where the `k+1` consecutive totients
`φ n, φ (n+1), …, φ (n+k)` are all equal (equivalently `∀ i ≤ k, φ n = φ (n+i)`). -/
def ConsecutiveKEqualTotients (k : ℕ) : Set ℕ :=
  { n : ℕ | ∀ i ≤ k, φ n = φ (n + i) }

/-- The OQ-04 target set: `n` such that the **four** consecutive integers
`n, n+1, n+2, n+3` share a common totient. -/
def FourConsecutiveEqualTotients : Set ℕ :=
  { n : ℕ | φ n = φ (n + 1) ∧ φ (n + 1) = φ (n + 2) ∧ φ (n + 2) = φ (n + 3) }

/-- Erdős's strong conjecture, `k = 3` slice: there are infinitely many four-term
runs of equal totients.  (Open; even nonemptiness is open.) -/
def oq04_infinitude_conjecture : Prop := FourConsecutiveEqualTotients.Infinite

/-! ## §1  The run reduction

The heart of the file: a length-`(k+1)` run of equal totients is exactly a block
of `k` consecutive members of the #1003 set `ConsecutiveEqualTotients`. -/

/-- **Telescoping form of a run.**  Being in `CKE k` (all of `φ n, …, φ (n+k)`
equal) is equivalent to all `k` *consecutive differences* vanishing.  This is the
purely combinatorial backbone of the reduction. -/
theorem mem_cke_iff_run {k n : ℕ} :
    n ∈ ConsecutiveKEqualTotients k ↔ ∀ i < k, φ (n + i) = φ (n + i + 1) := by
  simp only [ConsecutiveKEqualTotients, Set.mem_setOf_eq]
  constructor
  · intro h i hi
    have e1 : φ n = φ (n + i) := h i (Nat.le_of_lt hi)
    have e2 : φ n = φ (n + (i + 1)) := h (i + 1) hi
    calc φ (n + i) = φ n := e1.symm
      _ = φ (n + (i + 1)) := e2
      _ = φ (n + i + 1) := rfl
  · intro h i
    induction i with
    | zero => intro _; simp
    | succ m ih =>
      intro hi
      have hmk : m < k := hi
      calc φ n = φ (n + m) := ih (Nat.le_of_lt hmk)
        _ = φ (n + m + 1) := h m hmk
        _ = φ (n + (m + 1)) := rfl

/-- **Run reduction (set form).**  `n` begins a length-`(k+1)` run of equal
totients iff each of `n, n+1, …, n+k-1` is a member of the Erdős #1003 set
`ConsecutiveEqualTotients` — i.e. a run is a block of `k` consecutive #1003
solutions. -/
theorem mem_cke_iff_consecutive_cet {k n : ℕ} :
    n ∈ ConsecutiveKEqualTotients k ↔
      ∀ i < k, (n + i) ∈ ConsecutiveEqualTotients := by
  rw [mem_cke_iff_run]
  simp only [ConsecutiveEqualTotients, Set.mem_setOf_eq]

/-- `FourConsecutiveEqualTotients` is exactly the `k = 3` slice `CKE 3`. -/
theorem fcet_eq_cke_three : FourConsecutiveEqualTotients = ConsecutiveKEqualTotients 3 := by
  ext n
  rw [mem_cke_iff_run]
  simp only [FourConsecutiveEqualTotients, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩ i hi
    interval_cases i <;> simp_all
  · intro h
    exact ⟨by simpa using h 0 (by norm_num),
           by simpa using h 1 (by norm_num),
           by simpa using h 2 (by norm_num)⟩

/-- **Four-run ⇔ three consecutive #1003 solutions.**  A four-term run of equal
totients at `n` is precisely the statement that `n`, `n+1`, `n+2` are three
consecutive members of the Erdős #1003 set A001274.  This is the reason four-runs
are so hard to exhibit: a *single* consecutive pair in A001274 is already
exceedingly rare, and a four-run demands a consecutive triple. -/
theorem mem_fcet_iff_three_consecutive {n : ℕ} :
    n ∈ FourConsecutiveEqualTotients ↔
      n ∈ ConsecutiveEqualTotients ∧
      (n + 1) ∈ ConsecutiveEqualTotients ∧
      (n + 2) ∈ ConsecutiveEqualTotients := by
  simp only [FourConsecutiveEqualTotients, ConsecutiveEqualTotients, Set.mem_setOf_eq]

/-! ## §2  Existence equivalences

The OQ-04 existence question, packaged against the `CKE` hierarchy. -/

/-- OQ-04 existence ⇔ the `k = 3` slice of Erdős's family is nonempty. -/
theorem fcet_nonempty_iff_cke_three_nonempty :
    FourConsecutiveEqualTotients.Nonempty ↔ (ConsecutiveKEqualTotients 3).Nonempty := by
  rw [fcet_eq_cke_three]

/-- OQ-04 existence ⇔ A001274 contains three consecutive integers.  This is the
exact arithmetic content an eventual resolution must supply. -/
theorem fcet_nonempty_iff_three_consecutive_cet :
    FourConsecutiveEqualTotients.Nonempty ↔
      ∃ n, n ∈ ConsecutiveEqualTotients ∧
           (n + 1) ∈ ConsecutiveEqualTotients ∧
           (n + 2) ∈ ConsecutiveEqualTotients := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, mem_fcet_iff_three_consecutive.mp hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, mem_fcet_iff_three_consecutive.mpr hn⟩

/-- The four-run set is contained in every shorter-run set (`CKE 0,1,2`): a
four-run is in particular a three-run, a pair, and a single point.  (Monotonicity
of the `CKE` chain, specialised.) -/
theorem fcet_subset_cke_two :
    FourConsecutiveEqualTotients ⊆ ConsecutiveKEqualTotients 2 := by
  rw [fcet_eq_cke_three]
  intro n hn i hi
  exact hn i (by omega)

/-! ## §3  The concrete record: a run of length three

`5186, 5187, 5188` all have totient `2592` — the longest run of consecutive equal
totients currently known.  It stops there: `φ 5189 = 5188 ≠ 2592`.

These numerical facts are discharged by `native_decide` (kernel evaluation of
`Nat.totient`), which relies on the `Lean.ofReduceBool` axiom in addition to the
foundational ones; they are grouped here and are *not* used by the structural
results in §1–§2. -/

/-- `φ 5186 = 2592`  (`5186 = 2 · 2593`, `2593` prime). -/
theorem totient_5186 : φ 5186 = 2592 := by native_decide

/-- `φ 5187 = 2592`  (`5187 = 3 · 7 · 13 · 19`). -/
theorem totient_5187 : φ 5187 = 2592 := by native_decide

/-- `φ 5188 = 2592`  (`5188 = 2² · 1297`, `1297` prime). -/
theorem totient_5188 : φ 5188 = 2592 := by native_decide

/-- `φ 5189 = 5188`  (`5189` prime): the run of equal totients ends here. -/
theorem totient_5189 : φ 5189 = 5188 := by native_decide

/-- `5186` and `5187` are two **consecutive** members of the Erdős #1003 set
A001274 (`φ 5186 = φ 5187`). -/
theorem mem_cet_5186 : (5186 : ℕ) ∈ ConsecutiveEqualTotients := by
  simp only [ConsecutiveEqualTotients, Set.mem_setOf_eq]; native_decide

/-- `5187 ∈ A001274` too (`φ 5187 = φ 5188`): so `5186, 5187` is the record
consecutive *pair*. -/
theorem mem_cet_5187 : (5187 : ℕ) ∈ ConsecutiveEqualTotients := by
  simp only [ConsecutiveEqualTotients, Set.mem_setOf_eq]; native_decide

/-- **The record: three consecutive equal totients.**  `5186 ∈ CKE 2`, i.e.
`φ 5186 = φ 5187 = φ 5188`.  This is the longest known run — the closest the
totient function is currently known to come to a four-run. -/
theorem mem_cke_two_5186 : (5186 : ℕ) ∈ ConsecutiveKEqualTotients 2 := by
  simp only [ConsecutiveKEqualTotients, Set.mem_setOf_eq]; native_decide

/-- The record run does **not** extend to length four: `5186 ∉ CKE 3`, because
`φ 5189 = 5188 ≠ 2592 = φ 5186`.  So `5186` is *not* a witness for OQ-04. -/
theorem not_mem_fcet_5186 : (5186 : ℕ) ∉ FourConsecutiveEqualTotients := by
  rw [fcet_eq_cke_three]
  simp only [ConsecutiveKEqualTotients, Set.mem_setOf_eq]; native_decide

/-- Witnessed nonemptiness of the record set `CKE 2`: three consecutive equal
totients *do* exist (unlike the open four-term case). -/
theorem cke_two_nonempty : (ConsecutiveKEqualTotients 2).Nonempty :=
  ⟨5186, mem_cke_two_5186⟩

end Erdos1003.OQ04
