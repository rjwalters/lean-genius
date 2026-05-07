/-
  Aristotle targets for SpernerFreudenthal (Freudenthal Triangulation)
  Routine supporting lemmas for automated proof search.
  See SpernerFreudenthal.lean for the main formalization.

  The sorry in SpernerFreudenthal.lean amenable to Aristotle:
  - finsetToNat_injective: the bitmap encoding of Finset (Fin n) is injective.

  Proof strategy:
  - finsetToNat s = ∑ i ∈ s, 2^i.val encodes s as a binary number
  - Key lemma: Nat.testBit (finsetToNat s) k.val = decide (k ∈ s)
  - Equal sums → equal testBits → equal membership → equal sets

  Criteria for inclusion:
  - NOT the pseudomanifold property (requires geometric insight)
  - NOT inline adj_symm/adj_vertex/adj_ne sorries (inside where-clause)
  - finsetToNat_injective is a standalone theorem about binary sums
  - The fact follows from: distinct powers of 2 are Z-linearly independent
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Mathlib

namespace SpernerFreudenthalAristotle

open Finset

/-- Encode a `Finset (Fin n)` as a natural number via bitmap representation.
    finsetToNat s = ∑ i ∈ s, 2^i.val -/
def finsetToNat {n : ℕ} (s : Finset (Fin n)) : ℕ :=
  s.sum (fun i => 2 ^ i.val)

-- Aristotle target: the k-th bit of finsetToNat s records membership of k.
-- Proof: finsetToNat is a sum of distinct powers of 2 (exponents are distinct
-- Fin n values), so standard binary decomposition applies.
-- Relevant Mathlib: Nat.testBit_sum_two_pow, Nat.testBit_two_pow,
-- Finset.sum_ite, Nat.sum_range_id_mul_two_pow.
theorem finsetToNat_testBit {n : ℕ} (s : Finset (Fin n)) (k : Fin n) :
    Nat.testBit (finsetToNat s) k.val = decide (k ∈ s) := by
  sorry

-- Aristotle target: the bitmap encoding is injective.
-- Proof: if finsetToNat s = finsetToNat t, then for each k, testBit agrees,
-- so membership in s and t coincide, giving s = t by ext.
theorem finsetToNat_injective (n : ℕ) : Function.Injective (@finsetToNat n) := by
  sorry

end SpernerFreudenthalAristotle
