/-
  Erdős Problem #11 — WIP-01 / OQ-01: a decidability instance, a sufficient
  family, and the n = 1 boundary

  Erdős Problem #11 (OPEN): is every odd `n > 1` the sum of a squarefree number
  and a power of two?  The parent file `Erdos11WIP01` builds the bounded
  characterization `isSquarefreePlusPow2_iff` and calls it a "decidable
  characterization", but it never actually registers the `Decidable` instance.
  This file completes that, and adds two structural results.

  * `decidableIsSquarefreePlusPow2` — the promised `DecidablePred` instance,
    obtained from the bounded characterization (a finite search over
    `k ∈ range (n+1)` with the decidable predicate `Squarefree (n − 2^k)`).
  * `works_of_pred_squarefree` — a clean sufficient condition / infinite family:
    if `n ≥ 1` and `n − 1` is squarefree then `n` is representable (take the
    power of two `2^0 = 1`).  In particular every `n` with `n − 1` squarefree —
    e.g. `n − 1 ∈ {1, 2, 3, 5, 6, 7, …}` squarefree — is a sum of a squarefree
    number and a power of two.
  * `one_not_works` — `1` is NOT squarefree + a power of two, so the hypothesis
    `n > 1` in the conjecture is genuinely needed at the boundary: the only
    candidate `2^0 = 1` would force the squarefree summand to be `0`, which is
    not squarefree.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: https://erdosproblems.com/11.
-/

import Proofs.Erdos11WIP01

namespace Erdos11WIP01

open Finset

/-- **The decidability instance promised by the parent's "decidable characterization".**
`IsSquarefreePlusPow2` is decidable: by `isSquarefreePlusPow2_iff` it is equivalent to a
bounded existential `∃ k ∈ range (n+1), 2^k ≤ n ∧ Squarefree (n − 2^k)`, a finite search whose
body is decidable (`Squarefree` on `ℕ` is decidable). (Kernel `decide` may still be slow because
the `Squarefree` instance routes through `Nat.minSqFac`; the instance is nonetheless valid.) -/
instance decidableIsSquarefreePlusPow2 : DecidablePred IsSquarefreePlusPow2 :=
  fun n => decidable_of_iff _ (isSquarefreePlusPow2_iff n).symm

/-- **Sufficient condition (the `k = 0` family).**  If `n ≥ 1` and `n − 1` is squarefree, then
`n = (n − 1) + 2^0` exhibits `n` as squarefree + a power of two.  This gives an infinite family of
representable numbers with no search at all. -/
theorem works_of_pred_squarefree {n : ℕ} (hn : 1 ≤ n) (h : Squarefree (n - 1)) :
    IsSquarefreePlusPow2 n := by
  have hle : (2 : ℕ) ^ 0 ≤ n := by simpa using hn
  have hsf : Squarefree (n - 2 ^ 0) := by simpa using h
  exact squarefreePlusPow2_of_witness hle hsf

/-- **The boundary case `n = 1` fails.**  `1` is not squarefree + a power of two: the only power
of two `≤ 1` is `2^0 = 1`, which would force the squarefree summand to be `1 − 1 = 0`, and `0` is
not squarefree.  This shows the conjecture's hypothesis `n > 1` is necessary. -/
theorem one_not_works : ¬ IsSquarefreePlusPow2 1 := by
  rw [isSquarefreePlusPow2_iff]
  rintro ⟨k, hk, hle, hsf⟩
  rw [Finset.mem_range] at hk
  interval_cases k
  · simp only [pow_zero, Nat.sub_self] at hsf
    exact not_squarefree_zero hsf
  · exact absurd hle (by norm_num)

end Erdos11WIP01

#print axioms Erdos11WIP01.decidableIsSquarefreePlusPow2
#print axioms Erdos11WIP01.works_of_pred_squarefree
#print axioms Erdos11WIP01.one_not_works
