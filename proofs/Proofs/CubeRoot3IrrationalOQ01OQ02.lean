/-
# The explicit ℚ-basis `{1, ∛3, ∛9}` of `ℚ(∛3)`  (OQ-01 / OQ-02 of ∛3)

**Open Question OQ-02** of `cube-root-3-irrational-oq-01`:

  > Prove `ℚ(∛3)` has degree 3 and **exhibit its ℚ-basis `{1, ∛3, ∛9}`**,
  > linking to the parent's linear-independence open question.

The companion file `CubeRoot3IrrationalOQ02OQ01.lean` already established the bare
degree `[ℚ(∛3):ℚ] = 3` (as a corollary of the Eisenstein irreducibility of `X³-3`).
That settles the *dimension*, but it does not produce an **explicit ordered basis**.

This file supplies the missing certificate. From the integrality of `∛3` and the
already-proved degree, Mathlib's `IntermediateField.adjoin.powerBasis` yields the
power basis `1, ∛3, (∛3)²` of `ℚ(∛3)`. We:

1. build the power basis `cbrt3PowerBasis : PowerBasis ℚ ℚ⟮∛3⟯` and show `dim = 3`;
2. reindex it to an honest `Basis (Fin 3) ℚ ℚ⟮∛3⟯`;
3. compute the three basis vectors as real numbers: `1`, `∛3`, and `∛9`
   — the last via the arithmetic identity `(∛3)² = ∛9`;
4. give the **representation theorem**: every `x ∈ ℚ(∛3)` is the unique
   ℚ-combination `a·1 + b·∛3 + c·∛9`;
5. record that the basis is linearly independent and spanning.

This complements `CubeRoot3IrrationalOQ02OQ02.lean`, which proves the three *real
numbers* `1, ∛3, ∛3²` are ℚ-linearly independent. Linear independence alone is not
a basis: here we use the degree `[ℚ(∛3):ℚ] = 3` (companion `OQ02OQ01`) to upgrade
those three vectors to a genuine **basis** of the field extension, with spanning
and explicit coordinates — the structural content the parent's open question asks
for ("exhibit its ℚ-basis").

`∛9 = (∛3)²` is what makes `{1, ∛3, ∛9}` a *power* basis rather than an ad-hoc set:
the basis is genuinely `{1, ∛3, ∛3²}`, and `∛3² = 3^{2/3} = 9^{1/3} = ∛9`.

Zero axioms; builds on the Eisenstein degree corollary.
-/

import Proofs.CubeRoot2IrrationalOQ03

open Polynomial IntermediateField Module CubeRoot2IrrationalOQ03

namespace CubeRoot3IrrationalOQ01OQ02

/-- `∛3` as a real number, matching the form used throughout the ∛3 strand. -/
noncomputable abbrev cbrt3 : ℝ := (3 : ℝ) ^ ((1 : ℝ) / 3)

/-- `∛9` as a real number. -/
noncomputable abbrev cbrt9 : ℝ := (9 : ℝ) ^ ((1 : ℝ) / 3)

/-- `∛3` is integral over `ℚ` (root of the monic `X³ - 3`). -/
theorem cbrt3_isIntegral : IsIntegral ℚ cbrt3 :=
  isIntegral_nthRoot 3 3 (by norm_num)

/-- `[ℚ(∛3):ℚ] = 3`, specializing the general `adjoin_nthRoot_finrank` (n=m=p=3:
`3 ∣ 3` but `9 ∤ 3`). Re-derived here directly from `CubeRoot2IrrationalOQ03` so
this file does not depend on the (currently Mathlib-drifted) `OQ02OQ01` companion. -/
theorem cbrt3_fieldExtDegree : Module.finrank ℚ ℚ⟮cbrt3⟯ = 3 :=
  adjoin_nthRoot_finrank 3 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The defining arithmetic identity of the third basis vector: `(∛3)² = ∛9`,
since `(3^{1/3})² = 3^{2/3} = (3²)^{1/3} = 9^{1/3}`. -/
theorem cbrt3_sq_eq_cbrt9 : cbrt3 ^ 2 = cbrt9 := by
  show ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (9 : ℝ) ^ ((1 : ℝ) / 3)
  rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 3)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast (3 : ℝ) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-! ## The power basis `1, ∛3, (∛3)²` of `ℚ(∛3)` -/

/-- The power basis of `ℚ(∛3)` over `ℚ`, with generator `∛3` and vectors
`1, ∛3, (∛3)²`. -/
noncomputable def cbrt3PowerBasis : PowerBasis ℚ ℚ⟮cbrt3⟯ :=
  IntermediateField.adjoin.powerBasis cbrt3_isIntegral

/-- The power basis has dimension `3` — i.e. `[ℚ(∛3):ℚ] = 3`. -/
theorem cbrt3PowerBasis_dim : cbrt3PowerBasis.dim = 3 := by
  rw [← PowerBasis.finrank cbrt3PowerBasis]
  exact cbrt3_fieldExtDegree

/-- The generator of the power basis is `∛3` (as a real number). -/
theorem coe_gen : ((cbrt3PowerBasis.gen : ℚ⟮cbrt3⟯) : ℝ) = cbrt3 := by
  show ((IntermediateField.adjoin.powerBasis cbrt3_isIntegral).gen : ℝ) = cbrt3
  rw [adjoin.powerBasis_gen, IntermediateField.AdjoinSimple.coe_gen]

/-! ## The explicit ordered ℚ-basis `{1, ∛3, ∛9}` -/

/-- The ordered ℚ-basis `(1, ∛3, ∛9)` of `ℚ(∛3)`, indexed by `Fin 3`. -/
noncomputable def cbrt3Basis : Basis (Fin 3) ℚ ℚ⟮cbrt3⟯ :=
  cbrt3PowerBasis.basis.reindex (finCongr cbrt3PowerBasis_dim)

/-- The `i`-th basis vector is `(∛3)ⁱ` as a real number. -/
theorem cbrt3Basis_coe (i : Fin 3) :
    ((cbrt3Basis i : ℚ⟮cbrt3⟯) : ℝ) = cbrt3 ^ (i : ℕ) := by
  have hb : (cbrt3Basis i : ℚ⟮cbrt3⟯) = cbrt3PowerBasis.gen ^ (i : ℕ) := by
    show (cbrt3PowerBasis.basis.reindex (finCongr cbrt3PowerBasis_dim)) i
        = cbrt3PowerBasis.gen ^ (i : ℕ)
    rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
    congr 1
  rw [hb]
  push_cast
  rw [coe_gen]

/-- First basis vector: `1`. -/
theorem cbrt3Basis_zero : ((cbrt3Basis 0 : ℚ⟮cbrt3⟯) : ℝ) = 1 := by
  rw [cbrt3Basis_coe 0, (by decide : ((0 : Fin 3) : ℕ) = 0), pow_zero]

/-- Second basis vector: `∛3`. -/
theorem cbrt3Basis_one : ((cbrt3Basis 1 : ℚ⟮cbrt3⟯) : ℝ) = cbrt3 := by
  rw [cbrt3Basis_coe 1, (by decide : ((1 : Fin 3) : ℕ) = 1), pow_one]

/-- Third basis vector: `∛9 = (∛3)²`. -/
theorem cbrt3Basis_two : ((cbrt3Basis 2 : ℚ⟮cbrt3⟯) : ℝ) = cbrt9 := by
  rw [cbrt3Basis_coe 2, (by decide : ((2 : Fin 3) : ℕ) = 2), cbrt3_sq_eq_cbrt9]

/-! ## Representation and linear independence -/

/-- **Representation theorem.** Every element of `ℚ(∛3)` is the ℚ-combination
`a·1 + b·∛3 + c·∛9` of the basis, with coordinates `a, b, c` read off by
`cbrt3Basis.repr`. Uniqueness is automatic from `cbrt3Basis` being a basis. -/
theorem cbrt3_repr (x : ℚ⟮cbrt3⟯) :
    cbrt3Basis.repr x (0 : Fin 3) • cbrt3Basis (0 : Fin 3)
      + cbrt3Basis.repr x (1 : Fin 3) • cbrt3Basis (1 : Fin 3)
      + cbrt3Basis.repr x (2 : Fin 3) • cbrt3Basis (2 : Fin 3) = x := by
  have h := cbrt3Basis.sum_repr x
  rwa [Fin.sum_univ_three] at h

/-- The basis `{1, ∛3, ∛9}` is ℚ-linearly independent (inside `ℚ(∛3)`). -/
theorem cbrt3Basis_linearIndependent : LinearIndependent ℚ cbrt3Basis :=
  cbrt3Basis.linearIndependent

/-- The basis spans all of `ℚ(∛3)`. -/
theorem cbrt3Basis_span : Submodule.span ℚ (Set.range cbrt3Basis) = ⊤ :=
  cbrt3Basis.span_eq

end CubeRoot3IrrationalOQ01OQ02
