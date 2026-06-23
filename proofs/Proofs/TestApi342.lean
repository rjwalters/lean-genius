/-
Test API for Erdős #342 - Ulam sequence computability
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open Nat

-- Count representations of m as list[i] + list[j] with i < j
def countReps (xs : List ℕ) (m : ℕ) : ℕ :=
  xs.enum.foldl (fun acc ⟨i, a⟩ =>
    acc + (xs.enum.foldl (fun acc2 ⟨j, b⟩ =>
      if i < j && a + b == m then acc2 + 1 else acc2) 0)) 0

-- Check if m has exactly one representation
def hasUniqueRep (xs : List ℕ) (m : ℕ) : Bool :=
  countReps xs m == 1

-- Find the next Ulam number after last, given current list
def nextUlam (xs : List ℕ) (last : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let candidate := last + 1
    if hasUniqueRep xs candidate then candidate
    else nextUlamFrom xs (candidate + 1) fuel
where
  nextUlamFrom (xs : List ℕ) (candidate : ℕ) : ℕ → ℕ
    | 0 => 0
    | fuel + 1 =>
      if hasUniqueRep xs candidate then candidate
      else nextUlamFrom xs (candidate + 1) fuel

-- Build first n terms of Ulam sequence
def buildUlam : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | n + 1 =>
    let prev := buildUlam n
    match prev.getLast? with
    | none => prev
    | some last =>
      let next := nextUlam prev last 1000
      prev ++ [next]

-- Test: first 12 terms should be [1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28]
#eval buildUlam 12

-- Can we prove initial values?
example : (buildUlam 12).get? 0 = some 1 := by native_decide
example : (buildUlam 12).get? 1 = some 2 := by native_decide
