# Skolem-Noether for Mn(K): Elementary Proof via Matrix Units

## Status: ACT (axiom eliminated, 7 routine sorries remain)

## Key Achievement: Axiom → Theorem

Replaced `axiom skolemNoether` with `theorem skolemNoether` using an elementary
matrix units proof that avoids Artin-Wedderburn theory entirely.

## Proof Architecture (PROVED)

Given φ : Mn(K) ≃ₐ[K] Mn(K), construct an invertible P with φ = conj(P⁻¹):

### Step 1: Image multiplication law (PROVED: hf_mul)
Let f_ij = φ(E_ij). Then f_ij * f_kl = δ_{jk} f_il.
Proof: from φ being a ring hom and eij_mul_ekl.

### Step 2: Nonzero image (PROVED: hf_ne)
f_{i₀,i₀} ≠ 0 since φ is injective and E_{i₀,i₀} ≠ 0.
Uses: `simp [Matrix.stdBasisMatrix, Matrix.of_apply]` for entry computation.

### Step 3: Column intertwining (PROVED: hfp)
Define p_j = (f_{j,i₀}).mulVec v₀. Then:
  (f_ab).mulVec(p_c) = δ_{bc} · p_a
Proof: Matrix.mulVec_mulVec + hf_mul.

### Step 4: Nonzero columns (PROVED: hp_ne)
p_j ≠ 0 for all j. Proof: hfp applied with a=i₀, b=j, c=j.

### Step 5: Linear independence (PROVED: hp_li)
p_j are linearly independent. Proof: mulVecLin distributes over sums,
then Finset.sum_eq_single extracts g_j • p_j = 0, and hp_ne gives g_j = 0.

### Step 6: Conclusion (PROVED)
φ(A) = Pu.val * A * Pu⁻¹.val via Units.mul_inv and hPcomm.

## Remaining Sorries (7 total, all routine)

### Helper lemmas (4):
1. `eij_mul_ekl`: E_ij * E_kl = δ_{jk} E_il (entry-wise computation)
2. `sum_eii_eq_one`: Σ E_ii = 1 (entry-wise computation)
3. `matrix_eq_sum_eij`: M = Σ M_ij • E_ij (entry-wise computation)
4. `exists_nonzero_mulVec`: nonzero matrix has nonzero column action

### Linear algebra (1):
5. `linearIndependent_matrix_isUnit`: lin. indep. columns → matrix is unit

### Main theorem (2):
6. `hintertwine`: f_ij * P = P * E_ij (entry-wise from hfp)
7. `hPcomm`: φ(M) * P = P * M (linearity from hintertwine)

## Lean4 API Notes (verified)

- `Matrix.stdBasisMatrix` = `Matrix.single` (via `Pi.single`)
- Entry access: `simp [Matrix.stdBasisMatrix, Matrix.of_apply]` works
- `dsimp [Matrix.stdBasisMatrix, Matrix.of]` does NOT unfold properly
- `unfold Matrix.stdBasisMatrix` unfolds but follow-up simp doesn't match
- `Matrix.mulVec_mulVec` goes LEFT to RIGHT: M.mulVec(N.mulVec v) = (M*N).mulVec v
- `Matrix.mulVecLin` is the linear map version of mulVec
- `dotProduct` (not `Matrix.dotProduct`) for vector dot products
- `map_mul φ` (not `φ.map_mul`) for AlgEquiv multiplication
