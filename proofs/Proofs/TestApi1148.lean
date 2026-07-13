import Mathlib

open Nat

namespace Erdos1148Test

def HasConstRep (n : ℕ) : Prop :=
  ∃ x y z : ℕ, x ^ 2 + y ^ 2 = n + z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

-- n=23 DOES have a constrained representation: 4² + 4² = 32 = 23 + 3², with
-- 16, 16, 9 all ≤ 23. (The original `¬ HasConstRep 23` was false — witness 4,4,3.)
theorem hasConstRep_23 : HasConstRep 23 :=
  ⟨4, 4, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos1148Test
