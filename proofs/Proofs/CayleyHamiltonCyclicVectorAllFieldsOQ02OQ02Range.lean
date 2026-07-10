/-
  The full Frobenius commutant range: `n ≤ dim_K C(M) ≤ n²` for every matrix
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02)

  The sibling development pins the two endpoints of the Frobenius commutant range
  and characterises the lower one:

    * `CyclicCommutantConverse.finrank_centralizer_ge` — the **lower bound**
      `n ≤ dim_K C(M)` for *every* `M` (Frobenius, 1878);
    * `...OQ02OQ02`  — the lower bound is **attained** exactly by the nonderogatory
      matrices, where `dim_K C(M) = n`;
    * `...OQ02OQ02Scalar` — the **upper** endpoint `n²` is attained by a scalar
      matrix `c • I`, whose commutant is the whole algebra `Mₙ(K)`.

  What was missing is the matching **general upper bound**: the docstrings
  repeatedly speak of "the Frobenius range `n ≤ dim_K C(M) ≤ n²`", but only the
  scalar *special case* `dim_K C(c • I) = n²` was recorded — the inequality
  `dim_K C(M) ≤ n²` for an *arbitrary* `M` was never stated.  This file supplies it
  and packages the complete two-sided range:

    * `finrank_centralizer_le` — `dim_K C(M) ≤ n²` for *every* `M`.  The commutant
      is a `K`-subspace of the matrix algebra `Mₙ(K)`, whose dimension is `n²`, so
      its dimension cannot exceed `n²`.  (No hypothesis on `M`.)
    * `frobenius_commutant_range` — the headline two-sided bound
      `n ≤ dim_K C(M) ≤ n²`, valid for every `n × n` matrix over any field, whose
      two endpoints are realised by the nonderogatory (`n`) and scalar (`n²`)
      matrices from the sibling files.

  All results are `0`-sorry / `0`-axiom on top of Mathlib and the sibling files.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ01

open Matrix Polynomial

noncomputable section

namespace CyclicCommutantRange

variable {K : Type*} [Field K] {n : ℕ}

/-- **General upper bound for the commutant dimension.**  For *any* `n × n` matrix
    `M` over a field `K`, the centralizer `C(M) = {N : NM = MN}` has `K`-dimension
    at most `n²`:

      `dim_K C(M) ≤ n²`.

    The commutant is a `K`-subalgebra — in particular a `K`-subspace — of the
    matrix algebra `Mₙ(K)`, and `dim_K Mₙ(K) = n²`, so its dimension cannot exceed
    `n²`.  This is the general form of the top of the Frobenius range; the scalar
    matrices `c • I` (`...OQ02OQ02Scalar`) show the bound is sharp. -/
theorem finrank_centralizer_le
    (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
      ≤ n * n := by
  have h := Submodule.finrank_le
    (Subalgebra.toSubmodule
      (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))))
  rw [Subalgebra.finrank_toSubmodule, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one] at h
  exact h

/-- **The full Frobenius commutant range.**  For every `n × n` matrix `M` over a
    field `K`, the commutant dimension lies in the closed interval `[n, n²]`:

      `n ≤ dim_K C(M) ≤ n²`.

    The lower bound is Frobenius' theorem
    (`CyclicCommutantConverse.finrank_centralizer_ge`); the upper bound is
    `finrank_centralizer_le`.  Both endpoints are attained: `n` by nonderogatory
    matrices (`...OQ02OQ02`) and `n²` by scalar matrices (`...OQ02OQ02Scalar`),
    so the interval is sharp on both sides. -/
theorem frobenius_commutant_range
    (M : Matrix (Fin n) (Fin n) K) :
    n ≤ Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
    ∧ Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
        ≤ n * n := by
  refine ⟨?_, finrank_centralizer_le M⟩
  have h := CyclicCommutantConverse.finrank_centralizer_ge M
  rwa [Fintype.card_fin] at h

end CyclicCommutantRange

end
