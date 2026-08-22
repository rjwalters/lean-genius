import Mathlib

/-!
# Erdős 85: signed owner-mark telescope

This file formalizes the algebraic identity isolated in Sections 60--61 of
`SIZE_TWO_SIMULTANEOUS_ROUTING_PARTITION_AUDIT.md`.  If consecutive ports are
labelled by `p 0, ..., p (n+2)`, the alternating sum of the two-step owner
marks `p (i+2) - p i` has no interior contribution.  Only the two oriented
boundary differences remain, with a sign determined by the run length.
-/

namespace Erdos85

/-- Alternating two-step differences telescope to signed boundary differences. -/
theorem alternating_ownerMark_telescope (p : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (p (i + 2) - p i)) =
      (p 1 - p 0) + (-1 : ℤ) ^ n * (p (n + 2) - p (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf

end Erdos85
