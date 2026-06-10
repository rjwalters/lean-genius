/-
Cyclic Vector Theorem — `ZMod 4` Counterexample (S3 ACT-1)

This file establishes the **negative answer** to the forward direction of the
cyclic-vector ↔ nonderogatory biconditional over a non-domain commutative
ring. With

  `M : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![0, 2; 0, 0]`

we show:

  1. `charpoly_eq_X_sq` — `M.charpoly = X^2` (proved, sorry-free).
  2. `M_pow_two_eq_zero` — `M^2 = 0` as a matrix over `ZMod 4` (proved).
  3. `minpoly_natDegree_eq_two` — `(minpoly (ZMod 4) M).natDegree = 2`
     (paste-ready with sorry — see proof outline; depends on bearer pins to
     be sharpened in S3 ACT-2).
  4. `no_cyclic_vector` — `¬ ∃ v, IsCyclicVector M v` (paste-ready with
     sorry — see proof outline; depends on small tactic adjustments to be
     verified in S3 ACT-2).

Companion to `CayleyHamiltonCyclicVectorCommRingOQ01.lean`, which proves the
backward direction `(∃ v, IsCyclicVector M v) → IsNonderogatory M` over any
nontrivial commutative ring. The pair settles the OQ extension of the
biconditional from `[Field K]` to `[CommRing R]`: backward extends, forward
fails on `ZMod 4`.

The S3 PREP-3 session memo
(`research/problems/<slug>/sessions/2026-06-02-s3-prep-3-minpoly-hazard-resolution.md`)
discovered that the more natural statement `minpoly (ZMod 4) M = X^2`
is **Lean-unprovable** because over `ZMod 4` both `X^2` and `X^2 + 2*X` are
monic degree-2 annihilators of `M`, and Mathlib's `minpoly` resolves the
tie via `Classical.choose`. The degree-form `minpoly_natDegree_eq_two`
sidesteps this by using `natDegree`, which is `2` for both candidates.

Bearer pins (Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
- `Matrix.charpoly_fin_two`
  (`LinearAlgebra/Matrix/Charpoly/Coeff.lean:226`, `[CommRing R]`)
- `Matrix.trace_fin_two_of`
  (`LinearAlgebra/Matrix/Trace.lean:232`)
- `Matrix.det_fin_two_of`
  (`LinearAlgebra/Matrix/Determinant/Basic.lean:816`)
- `Matrix.mul_apply`, `Fin.sum_univ_two` (for `M^2 = 0`)

Forward dependency: `Proofs.CayleyHamiltonCyclicVectorCommRingOQ01`
(S2 ACT, merged 2026-05-16) supplies the `GeneralCyclicVectorRing.IsCyclicVector`
predicate used in `no_cyclic_vector` below.
-/

import Mathlib
import Proofs.CayleyHamiltonCyclicVectorCommRingOQ01

noncomputable section

open Matrix Polynomial GeneralCyclicVectorRing

namespace CayleyHamiltonCyclicVectorZMod4Counterexample

/-- The witnessing matrix: `M = !![0, 2; 0, 0]` over `ZMod 4`. -/
def M : Matrix (Fin 2) (Fin 2) (ZMod 4) := !![0, 2; 0, 0]

/-- `Nontrivial (ZMod 4)` instance. Needed for `Matrix.charpoly_fin_two`
and `Matrix.charpoly_monic`. -/
private theorem nontrivial_zmod_four : Nontrivial (ZMod 4) :=
  ⟨0, 1, by decide⟩

/-- `M.charpoly = X^2`. The characteristic polynomial of `M = !![0, 2; 0, 0]`
in `(ZMod 4)[X]` is `X^2 - tr(M)·X + det(M) = X^2 - 0·X + 0 = X^2`. -/
theorem charpoly_eq_X_sq : M.charpoly = X ^ 2 := by
  haveI : Nontrivial (ZMod 4) := nontrivial_zmod_four
  rw [M.charpoly_fin_two]
  simp [M, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]

/-- `M^2 = 0` as a matrix over `ZMod 4`. Verified by direct entry-wise
computation using `Matrix.mul_apply` and `Fin.sum_univ_two`. -/
theorem M_pow_two_eq_zero : M ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, pow_two, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `2 • M = 0` over `ZMod 4`. Since `2 * 2 = 0` in `ZMod 4` and `M`'s
only nonzero entry is `M[0,1] = 2`. -/
theorem two_smul_M_eq_zero : (2 : ZMod 4) • M = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- `(minpoly (ZMod 4) M).natDegree = 2`. The natDegree of the minimal
polynomial is `2`, matching `M.charpoly.natDegree = 2`.

**Proof outline** (S3 PREP-3 §4.1; full discharge deferred to S3 ACT-2):

- Upper bound `≤ 2`: `X^2` is a monic annihilator of `M` (via
  `M_pow_two_eq_zero`), so `minpoly.min` gives
  `degree (minpoly M) ≤ degree (X^2) = 2`.
- Lower bound `≥ 2`: no monic polynomial of degree `≤ 1` annihilates `M`.
  Degree-0 monic = `1`, `aeval M 1 = I ≠ 0`. Degree-1 monic = `X + c`,
  `aeval M (X + c) = !![c, 2; 0, c]`, which is nonzero because the
  `[0,1]`-entry is `2 ≠ 0` in `ZMod 4`. -/
theorem minpoly_natDegree_eq_two :
    (minpoly (ZMod 4) M).natDegree = 2 := by
  sorry

/-- `M` has **no cyclic vector** over `ZMod 4`. For every `v : Fin 2 → ZMod 4`,
the nonzero polynomial `q = 2 * X` satisfies `q.natDegree = 1 < 2`,
`aeval M q = 2 • M = 0` (by `two_smul_M_eq_zero`), hence
`(aeval M q).mulVec v = 0`, witnessing `¬ IsCyclicVector M v`.

**Proof outline** (S3 PREP-3 §4.3; full discharge deferred to S3 ACT-2):

  ```
  rintro ⟨v, hcyc⟩
  -- aeval M (2 * X) · v = 0 because aeval M (2*X) = 2·M = 0.
  -- hcyc forces 2*X = 0, but coeff (2*X) 1 = 2 ≠ 0 in ZMod 4 ⇒ contradiction.
  ```

Reuses `IsCyclicVector` from `GeneralCyclicVectorRing` (S2 ACT). -/
theorem no_cyclic_vector :
    ¬ ∃ v : Fin 2 → ZMod 4, IsCyclicVector M v := by
  sorry

end CayleyHamiltonCyclicVectorZMod4Counterexample
