import Proofs.Erdos85Problem14
import Proofs.Erdos85Problem21
import Proofs.Erdos85Ramsey
import Proofs.Erdos85PairedWitness
import Proofs.Erdos85TightWitness
import Proofs.Erdos85Polarity
import Proofs.Erdos85PolarityDegree
import Proofs.Erdos85PolarityFamily
import Proofs.Erdos85Relabel
import Proofs.Erdos85PrimeFamily
import Proofs.Erdos85PrimeSequence
import Proofs.Erdos85VertexDeletion
import Proofs.Erdos85ConsecutiveRamsey
import Proofs.Erdos85ProblemConflict
import Proofs.Erdos85PolarityDeletion
import Proofs.Erdos85PolarityAbsolute
import Proofs.Erdos85DeletePair
import Proofs.Erdos85RepairSet
import Proofs.Erdos85MinimalWitness
import Proofs.Erdos85OneDefectCore

/-!
# Headline results for Erdős Problem 85

This module collects the publication-facing statements proved by the detailed
development.  The main problem—eventual monotonicity of `minDegreeForC4`—remains
open.  We provide its exact Ramsey and witness-extension reformulations, a
complete checked table through order 21, one- and two-vertex attachment theory,
and the finite-field polarity construction underlying the classical infinite
family.  In particular, for every finite field of order `q`, the development
proves `minDegreeForC4 (q² + q + 1) = q + 1`.
Chevalley--Warning and deletion of an absolute point strengthen this to the
consecutive pair `f(q²+q) = f(q²+q+1) = q+1`.
-/

namespace Erdos85

/-- The checked small-value table, packaged as a single function. -/
def minDegreeForC4SmallTable (n : ℕ) : ℕ :=
  if n ≤ 3 then n
  else if n ≤ 4 then 2
  else if n ≤ 9 then 3
  else if n ≤ 14 then 4
  else 5

/-- **Exact table through 21.**  For every nonempty graph order at most 21,
`minDegreeForC4` agrees with `minDegreeForC4SmallTable`. -/
theorem minDegreeForC4_eq_smallTable {n : ℕ} (hpos : 1 ≤ n) (hle : n ≤ 21) :
    minDegreeForC4 n = minDegreeForC4SmallTable n := by
  interval_cases n <;>
    simp [minDegreeForC4SmallTable, minDegreeForC4_eq_self_of_le_three,
      minDegreeForC4_four, minDegreeForC4_five, minDegreeForC4_six,
      minDegreeForC4_seven, minDegreeForC4_eight, minDegreeForC4_nine,
      minDegreeForC4_ten, minDegreeForC4_eleven, minDegreeForC4_twelve,
      minDegreeForC4_thirteen, minDegreeForC4_fourteen,
      minDegreeForC4_fifteen, minDegreeForC4_sixteen,
      minDegreeForC4_seventeen, minDegreeForC4_eighteen,
      minDegreeForC4_nineteen, minDegreeForC4_twenty,
      minDegreeForC4_twentyone] at *

end Erdos85
