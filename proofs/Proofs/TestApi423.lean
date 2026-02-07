/-
Test API for Erdős 423: computable consecutive-sum sequence
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Nat

-- Compute sum of elements arr[i..j] inclusive
def arrRangeSum (arr : Array ℕ) (i j : ℕ) : ℕ :=
  let mut s := 0
  for k in [i:j+1] do
    s := s + arr.getD k 0
  s

-- Find the smallest consecutive sum > threshold from an array of terms
-- Consecutive sum = sum of arr[i..j] where j > i (at least 2 terms)
def nextTerm (arr : Array ℕ) (threshold : ℕ) : ℕ :=
  let n := arr.size
  let mut best := 0  -- 0 means not found
  for i in [:n] do
    let mut s := arr.getD i 0
    for j in [i+1:n] do
      s := s + arr.getD j 0
      if s > threshold then
        if best == 0 || s < best then
          best := s
  best

-- Build the sequence up to n terms
def buildSeq (n : ℕ) : Array ℕ :=
  if n == 0 then #[]
  else if n == 1 then #[1]
  else
    let mut arr := #[1, 2]
    for _ in [2:n] do
      let last := arr.back!
      let next := nextTerm arr last
      if next > 0 then
        arr := arr.push next
      else
        arr := arr.push (last + 1)
    arr

-- Test: first 15 terms
-- Expected: 1, 2, 3, 5, 6, 8, 10, 11, 14, 16, 17, 18, 19, 21, 22
#eval buildSeq 15
#eval buildSeq 20
