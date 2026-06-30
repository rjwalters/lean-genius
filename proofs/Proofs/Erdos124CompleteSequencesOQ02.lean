import Mathlib

/-
# Erdős Problem 124 — the exact boundary `∑ 1/(dᵢ-1) = 1`

## Background

The (weak version of the) Erdős–Burr–Graham–Li problem #124, solved and formally
verified by Harmonic's "Aristotle" in 2025 (see `Erdos124CompleteSequences.lean`),
states: given bases `d₁,…,d_k ≥ 2` with

    ∑ 1/(dᵢ - 1) ≥ 1,

every natural number is a sum `∑ aᵢ` where each `aᵢ` has only digits `0,1` in base
`dᵢ`. This file studies the open follow-up question **OQ-02: what happens exactly at
the boundary `∑ 1/(dᵢ - 1) = 1`?**

## What this file proves

The central observation is a clean structural identity. Writing `eᵢ = dᵢ - 1 ≥ 1`,
the boundary condition

    ∑ 1/(dᵢ - 1) = 1     ⟺     ∑ 1/eᵢ = 1,

i.e. **the boundary configurations of Erdős 124 are exactly the Egyptian-fraction
(unit-fraction) decompositions of `1`.** So the "technique needed at the boundary"
is the arithmetic of Egyptian fractions / the Sylvester splitting identity, not any
new completeness machinery — the parent theorem already covers the closed condition
`≥ 1`, and equality is its extreme face.

Concretely we prove, all `0`-axiom and machine checked:

* `reciSum_eq_egyptSum`  — the bridge `∑ 1/(dᵢ-1) = ∑ 1/eᵢ` with `eᵢ = dᵢ-1`.
* `egyptSum_split`       — Sylvester splitting `1/e = 1/(e+1) + 1/(e(e+1))`.
* `sylvester` / `sylvester_egyptSum` / `sylvester_length` — an explicit family of
  boundary Egyptian decompositions of length `k+1` for **every** `k`, i.e. Erdős-124
  boundary configurations exist with an arbitrary number of bases.
* `exists_boundary_config` — restated in base language: for every `k ≥ 1` there is a
  list of `k` bases `≥ 2` with `reciSum = 1`.
* `egypt_one_forces_singleton` / `base_two_forces_singleton` — the rigidity at the
  bottom: if a boundary configuration uses the base `d = 2` (equivalently the unit
  fraction `1/1`), then it is the singleton `[2]` (plain binary representation).
* concrete witnesses `[2]`, `[3,3]`, `[3,4,7]`, `[3,4,8,43]` (Sylvester's sequence).

These are elementary but genuinely characterize the boundary face; nothing here is in
Mathlib. The deep `≥ 1` completeness theorem is the parent file's contribution and is
not reproved.
-/

namespace Erdos124OQ02

open scoped BigOperators

/-- Sum of unit fractions `∑ 1/eᵢ` over a list of (positive) denominators. -/
def egyptSum (e : List ℕ) : ℚ := (e.map (fun x => (1 : ℚ) / x)).sum

/-- Erdős-124 reciprocal sum `∑ 1/(dᵢ - 1)` over a list of bases. -/
def reciSum (d : List ℕ) : ℚ := (d.map (fun x => (1 : ℚ) / ((x : ℚ) - 1))).sum

@[simp] theorem egyptSum_nil : egyptSum [] = 0 := rfl

@[simp] theorem egyptSum_cons (a : ℕ) (l : List ℕ) :
    egyptSum (a :: l) = (1 : ℚ) / a + egyptSum l := by
  simp [egyptSum]

@[simp] theorem reciSum_nil : reciSum [] = 0 := rfl

@[simp] theorem reciSum_cons (a : ℕ) (l : List ℕ) :
    reciSum (a :: l) = (1 : ℚ) / ((a : ℚ) - 1) + reciSum l := by
  simp [reciSum]

/-- **Bridge.** With `eᵢ = dᵢ - 1`, the Erdős-124 reciprocal sum is an Egyptian-fraction
sum.  Hence the boundary face `reciSum d = 1` is exactly a unit-fraction decomposition
of `1`. Requires the bases to be `≥ 1` so the natural subtraction casts correctly. -/
theorem reciSum_eq_egyptSum (d : List ℕ) (h : ∀ x ∈ d, 1 ≤ x) :
    reciSum d = egyptSum (d.map (fun x => x - 1)) := by
  induction d with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a := h a (List.mem_cons_self ..)
    have htl : ∀ x ∈ l, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem a hx)
    have hcast : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by
      rw [Nat.cast_sub ha]; simp
    simp only [reciSum_cons, List.map_cons, egyptSum_cons, hcast, ih htl]

/-- Each unit-fraction term is nonnegative, hence the whole Egyptian sum is. -/
theorem egyptSum_nonneg {l : List ℕ} : 0 ≤ egyptSum l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [egyptSum_cons]
    have : (0 : ℚ) ≤ 1 / a := by positivity
    linarith

/-- **Sylvester splitting identity** `1/e = 1/(e+1) + 1/(e·(e+1))`, the engine that
produces longer boundary configurations. Valid for `e ≥ 1`. -/
theorem egyptSum_split {e : ℕ} (he : 1 ≤ e) :
    (1 : ℚ) / (e + 1) + (1 : ℚ) / (e * (e + 1)) = 1 / e := by
  have he0 : (e : ℚ) ≠ 0 := by
    have : e ≠ 0 := by omega
    exact_mod_cast this
  have he1 : (e : ℚ) + 1 ≠ 0 := by positivity
  field_simp

/-- The explicit Sylvester construction in `e`-space: repeatedly split the head unit
fraction.  `sylvester 0 = [1]`, and each step replaces the head `e` by `e+1, e(e+1)`. -/
def sylvester : ℕ → List ℕ
  | 0 => [1]
  | (k + 1) =>
      match sylvester k with
      | [] => []                        -- unreachable; kept total
      | (e :: rest) => (e + 1) :: e * (e + 1) :: rest

/-- The construction is never empty. -/
theorem sylvester_ne_nil : ∀ k, sylvester k ≠ []
  | 0 => by simp [sylvester]
  | (k + 1) => by
      rw [sylvester]
      cases hk : sylvester k with
      | nil => exact (sylvester_ne_nil k hk).elim
      | cons e rest => simp

/-- Every denominator produced is `≥ 1`. -/
theorem sylvester_pos : ∀ k, ∀ x ∈ sylvester k, 1 ≤ x
  | 0 => by simp [sylvester]
  | (k + 1) => by
      have ih := sylvester_pos k
      rw [sylvester]
      cases hk : sylvester k with
      | nil => simp
      | cons e rest =>
          have he : 1 ≤ e := by
            have := ih; rw [hk] at this; exact this e (List.mem_cons_self ..)
          have hrest : ∀ x ∈ rest, 1 ≤ x := by
            intro x hx; have := ih; rw [hk] at this
            exact this x (List.mem_cons_of_mem e hx)
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with h | h | h
          · omega
          · subst h; nlinarith
          · exact hrest x h

/-- **Length.** The `k`-th Sylvester list has exactly `k + 1` denominators. -/
theorem sylvester_length : ∀ k, (sylvester k).length = k + 1
  | 0 => by simp [sylvester]
  | (k + 1) => by
      rw [sylvester]
      cases hk : sylvester k with
      | nil => exact (sylvester_ne_nil k hk).elim
      | cons e rest =>
          have hl := sylvester_length k
          rw [hk] at hl
          simp only [List.length_cons] at hl ⊢
          omega

/-- **Boundary invariant.** Every Sylvester list is an Egyptian decomposition of `1`. -/
theorem sylvester_egyptSum : ∀ k, egyptSum (sylvester k) = 1
  | 0 => by simp [sylvester, egyptSum]
  | (k + 1) => by
      have ih := sylvester_egyptSum k
      have hpos := sylvester_pos k
      rw [sylvester]
      cases hk : sylvester k with
      | nil => exact (sylvester_ne_nil k hk).elim
      | cons e rest =>
          have he : 1 ≤ e := by
            have := hpos; rw [hk] at this; exact this e (List.mem_cons_self ..)
          rw [hk] at ih
          rw [egyptSum_cons] at ih           -- 1/e + egyptSum rest = 1
          rw [egyptSum_cons, egyptSum_cons]   -- 1/(e+1) + (1/(e(e+1)) + egyptSum rest)
          have hsplit := egyptSum_split he
          push_cast
          push_cast at hsplit
          linarith [hsplit, ih]

/-- **Boundary configurations of every size, in base language.** For every `k ≥ 1`
there is a list of `k` bases, each `≥ 2`, lying exactly on the Erdős-124 boundary
`reciSum = 1`. (Take the Sylvester denominators `+ 1`.) -/
theorem exists_boundary_config :
    ∀ k : ℕ, 1 ≤ k → ∃ d : List ℕ, d.length = k ∧ (∀ x ∈ d, 2 ≤ x) ∧ reciSum d = 1 := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨(sylvester m).map (fun x => x + 1), ?_, ?_, ?_⟩
  · rw [List.length_map, sylvester_length]
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := sylvester_pos m y hy
    omega
  · -- reciSum (e+1 list) = egyptSum (e list) since (e+1) - 1 = e
    have hbridge : reciSum ((sylvester m).map (fun x => x + 1))
        = egyptSum (((sylvester m).map (fun x => x + 1)).map (fun x => x - 1)) := by
      apply reciSum_eq_egyptSum
      intro x hx
      rw [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; omega
    rw [hbridge]
    have hmap : ∀ l : List ℕ, (l.map (fun x => x + 1)).map (fun x => x - 1) = l := by
      intro l; induction l with
      | nil => rfl
      | cons a t ih => simp [ih]
    rw [hmap, sylvester_egyptSum]

/-- If the unit denominator `1` occurs, the Egyptian sum is already `≥ 1` (its term is
`1/1 = 1` and all other terms are nonnegative). -/
theorem egyptSum_ge_one_of_mem_one {l : List ℕ}
    (h1 : (1 : ℕ) ∈ l) (hpos : ∀ x ∈ l, 1 ≤ x) : (1 : ℚ) ≤ egyptSum l := by
  induction l with
  | nil => simp at h1
  | cons a t ih =>
    rw [egyptSum_cons]
    rcases List.mem_cons.mp h1 with h | h
    · -- head is the unit
      subst h
      simp only [Nat.cast_one, div_one]
      have : (0 : ℚ) ≤ egyptSum t := egyptSum_nonneg
      linarith
    · -- unit is further down the tail
      have htpos : ∀ x ∈ t, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
      have htail := ih h htpos
      have hhead : (0 : ℚ) ≤ 1 / (a : ℚ) := by positivity
      linarith

/-- If a denominator `1` (the unit fraction `1/1`) appears in an Egyptian decomposition
of `1` with all denominators `≥ 1`, then the list is exactly `[1]`: no other fraction
fits in the budget.  This is the rigidity that makes binary `(d = 2)` the only single
boundary base. -/
theorem egypt_one_forces_singleton (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hsum : egyptSum l = 1) (h1 : (1 : ℕ) ∈ l) :
    l = [1] := by
  cases l with
  | nil => exact absurd h1 (by simp)
  | cons a t =>
    rw [egyptSum_cons] at hsum
    have ha : 1 ≤ a := hpos a (List.mem_cons_self ..)
    by_cases hae : a = 1
    · -- head is the unit; the tail must vanish
      subst hae
      simp only [Nat.cast_one, div_one] at hsum      -- 1 + egyptSum t = 1
      have ht0 : egyptSum t = 0 := by linarith
      -- a nonempty tail of positive unit fractions has positive sum
      cases t with
      | nil => rfl
      | cons b s =>
        rw [egyptSum_cons] at ht0
        have hb : 1 ≤ b := hpos b (by simp)
        have hbq : (0 : ℚ) < 1 / b := by
          have : (0 : ℚ) < b := by exact_mod_cast hb
          positivity
        have hsn : 0 ≤ egyptSum s := egyptSum_nonneg
        linarith
    · -- head is ≥ 2, so the unit fraction sits in the tail and overflows the budget
      exfalso
      have ha2 : 2 ≤ a := by omega
      have h1t : (1 : ℕ) ∈ t := by
        rcases List.mem_cons.mp h1 with h | h
        · exact absurd h.symm hae
        · exact h
      have htpos : ∀ x ∈ t, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem a hx)
      -- the unit fraction `1/1` already saturates the tail's budget
      have hle : (1 : ℚ) ≤ egyptSum t := egyptSum_ge_one_of_mem_one h1t htpos
      have hapos : (0 : ℚ) < 1 / a := by
        have : (0 : ℚ) < a := by exact_mod_cast ha
        positivity
      linarith

/-- **Base-2 rigidity.** Any boundary configuration of Erdős 124 that uses the base
`d = 2` is the singleton `[2]` — i.e. plain base-2 (binary) representation. -/
theorem base_two_forces_singleton (d : List ℕ)
    (hpos : ∀ x ∈ d, 2 ≤ x) (hsum : reciSum d = 1) (h2 : (2 : ℕ) ∈ d) :
    d = [2] := by
  have h1pos : ∀ x ∈ d, 1 ≤ x := fun x hx => le_trans (by norm_num) (hpos x hx)
  have hsum' : egyptSum (d.map (fun x => x - 1)) = 1 := by
    rw [← reciSum_eq_egyptSum d h1pos]; exact hsum
  have hepos : ∀ x ∈ d.map (fun x => x - 1), 1 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := hpos y hy; omega
  have he1 : (1 : ℕ) ∈ d.map (fun x => x - 1) := by
    simpa using List.mem_map_of_mem (f := fun x : ℕ => x - 1) h2
  have hsingle := egypt_one_forces_singleton _ hepos hsum' he1
  -- d.map (·-1) = [1] forces d to be one element which subtracts to 1, i.e. 2
  rcases d with _ | ⟨a, t⟩
  · exact absurd h2 (by simp)
  · rw [List.map_cons] at hsingle
    obtain ⟨ha1, ht⟩ := List.cons_eq_cons.mp hsingle
    have ht' : t = [] := by simpa using ht
    subst ht'
    have ha : 2 ≤ a := hpos a (by simp)
    have : a = 2 := by omega
    rw [this]

/-! ## Concrete boundary witnesses (Egyptian decompositions of 1). -/

/-- Single base: `d = 2`, plain binary.  `1/(2-1) = 1`. -/
theorem witness_binary : reciSum [2] = 1 := by
  simp only [reciSum_cons, reciSum_nil]; norm_num

/-- Two bases: `d = 3, 3`.  `1/2 + 1/2 = 1`. -/
theorem witness_two : reciSum [3, 3] = 1 := by
  simp only [reciSum_cons, reciSum_nil]; norm_num

/-- Three bases: `d = 3, 4, 7`, the decomposition `1/2 + 1/3 + 1/6 = 1`. -/
theorem witness_three : reciSum [3, 4, 7] = 1 := by
  simp only [reciSum_cons, reciSum_nil]; norm_num

/-- Four bases: `d = 3, 4, 8, 43` — Sylvester's sequence `1/2 + 1/3 + 1/7 + 1/42 = 1`. -/
theorem witness_sylvester_four : reciSum [3, 4, 8, 43] = 1 := by
  simp only [reciSum_cons, reciSum_nil]; norm_num

/-- Sanity check of the recursion: `sylvester 3 = [4, 12, 6, 2]` in `e`-space, i.e. the
boundary configuration with bases `e + 1 = [5, 13, 7, 3]` (`1/4 + 1/12 + 1/6 + 1/2 = 1`).
This is a different length-4 Egyptian decomposition than `witness_sylvester_four`. -/
example : sylvester 3 = [4, 12, 6, 2] := by decide

end Erdos124OQ02
