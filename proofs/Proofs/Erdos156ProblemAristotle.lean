/-
  Aristotle targets for Erdős Problem #156 (Maximal Sidon Sets of Size O(N^{1/3}))
  Supporting lemmas for automated proof search.
  See Erdos156Problem.lean for the main formalization.

  Historical targets (now all discharged in the parent `Erdos156Problem`):
  - diffShadow_ncard_le: |diffShadow A| ≤ |A| * (|A|*(|A|+1)/2)
  - midShadow_ncard_le: |midShadow A| ≤ |A|*(|A|+1)/2
  - greedySidon_cube_lower_bound: N ≤ n + n*(n*(n+1)/2) + n*(n+1)/2

  These three lemmas are now declared and proven in `Proofs.Erdos156Problem`.
  Under v4.31, re-declaring them in this same-namespace companion (which imports
  the parent) is a hard error ("has already been declared"), so the companion is
  reduced to an import shim that re-exports the parent's results.

  Excluded:
  - The main O(N^{1/3}) conjecture (open problem)
-/
import Mathlib
import Proofs.Erdos156Problem

-- All Aristotle support targets for Erdős #156 now live in `Proofs.Erdos156Problem`
-- (diffShadow_ncard_le, midShadow_ncard_le, greedySidon_cube_lower_bound).
