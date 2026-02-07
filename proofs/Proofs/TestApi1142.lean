import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

-- Test: can we define the Erdős 1142 property and verify small cases?

/-- The list of powers of 2 that are > 1 and < n. -/
def powersOfTwoBelow (n : ℕ) : List ℕ :=
  (List.range n).filter (fun k => k ≥ 2 ∧ k.isPowerOfTwo)

/-- n satisfies the Erdős 1142 property if n - 2^k is prime for all 1 < 2^k < n. -/
def satisfiesE1142 (n : ℕ) : Bool :=
  let pows := powersOfTwoBelow n
  pows.length > 0 && pows.all (fun p => (n - p).Prime)

-- Test known values
#eval satisfiesE1142 4    -- should be true
#eval satisfiesE1142 7    -- should be true
#eval satisfiesE1142 15   -- should be true
#eval satisfiesE1142 21   -- should be true
#eval satisfiesE1142 45   -- should be true
#eval satisfiesE1142 75   -- should be true
#eval satisfiesE1142 105  -- should be true

-- Test non-values
#eval satisfiesE1142 6    -- should be false
#eval satisfiesE1142 10   -- should be false
#eval satisfiesE1142 106  -- should be false

-- Check: are there any other values up to 200?
#eval (List.range 200).filter satisfiesE1142
