
## Session 2026-07-08 (researcher-1) — counterexample: diagonalizable M,N, non-diagonalizable product

Executed nextStep #2 (necessity of the common-diagonalizer hypothesis in
mul_of_commonDiagonalizer). Added to Proofs/MinpolyCharpolyOQ02Incomplete01.lean
(VERIFIED 0 axioms / 0 sorries, host lake env lean):
- exists_diagonalizable_mul_not_diagonalizable : ∃ M N : Matrix (Fin 2)(Fin 2) ℚ,
  M.IsDiagonalizable ∧ N.IsDiagonalizable ∧ ¬(M*N).IsDiagonalizable.
  Witnesses: M=!![0,1;1,0] (swap, eigenvalues ±1, diagonalized by P=!![1,1;1,-1],
  P⁻¹=!![1/2,1/2;1/2,-1/2]), N=!![1,0;0,-1] (diagonal → of_isDiag). M*N=!![0,-1;1,0]
  (90° rotation, eigenvalues ±i∉ℚ) not diagonalizable. First NEGATIVE result in this
  all-positive-closure-law file.
  Non-diag proof (no eigenvalue theory): rintro ⟨P,hP,hdiag⟩; trace/det similarity-
  invariant via Matrix.trace_conj'/det_conj' (h:IsUnit M)(N):tr/det(M⁻¹NM)=tr/det N;
  D:=P⁻¹(MN)P diagonal ⟹ trace_fin_two D=D00+D11=0, det_fin_two D=D00·D11=1 (off-diag
  h01/h10 via hdiag(by decide)); D11=-D00 ⟹ D00·(-D00)=1 ⟹ D00²=-1, nlinarith[sq_nonneg].

★Lean recipe for concrete 2×2 ℚ matrix proofs: `Matrix.isUnit_iff_isUnit_det`+
`Matrix.det_fin_two_of`+norm_num for IsUnit; `Matrix.inv_eq_right_inv (by rw[Matrix.
one_fin_two];norm_num[Matrix.mul_fin_two])` to pin P⁻¹ (rw one_fin_two FIRST — norm_num
won't rewrite RHS `1`); product equalities `norm_num [Matrix.mul_fin_two]`; IsDiag goals
`intro i j hij; fin_cases i <;> fin_cases j <;> simp_all`; trace/det_fin_two(_of).
★Host-verify needs local deps built first: `lake env lean -o .lake/build/lib/lean/Proofs/
MinpolyCharpoly.olean Proofs/MinpolyCharpoly.lean` then OQ02 then the file (imports local
Proofs.* not just Mathlib). No gallery meta on this research file. File 332→380, 18 thms.

REMAINING: nextStep #1 (HARD half: commuting diagonalizable ⟹ common diagonalizer, needs
eigenspace decomposition) genuinely hard, not session-sized.

## Session 2026-07-09 (researcher-1) — additive counterexample sibling

Added exists_diagonalizable_add_not_diagonalizable (the ADD analogue of the existing
exists_diagonalizable_mul_not_diagonalizable): diagonalizable summands need not have a
diagonalizable sum, so the common-diagonalizer hypothesis in add_of_commonDiagonalizer is
genuinely necessary (not merely for products). Witnesses over ℚ:
- M = !![-2,-1;1,1/2], distinct rational eigenvalues 0 and -3/2, diagonalized by
  P = !![1,2;-2,-1] (columns = eigenvectors), P⁻¹ = !![-1/3,-2/3;2/3,1/3],
  P⁻¹MP = !![0,0;0,-3/2]. Chosen so N is DIAGONAL and M+N reuses the rotation.
- N = !![2,0;0,-1/2] diagonal → of_isDiag.
- M+N = !![0,-1;1,0] = rational 90° rotation, eigenvalues ±i∉ℚ, not diagonalizable.

Non-diag proof is a byte-for-byte reuse of the mul counterexample's trace/det-invariant
argument (D₀₀+D₁₁=0, D₀₀·D₁₁=1 ⟹ D₀₀²=-1, nlinarith[sq_nonneg]). Only new plumbing:
`hsum : M+N=!![0,-1;1,0]` via `ext i j; fin_cases<;>fin_cases<;>simp[Matrix.add_apply]<;>
norm_num`, then rw at hdiag before the shared set-D block.

★UNVERIFIED (env): 5 docker builds, ALL env failures — SIGBUS-135/139 at olean-WRITE with
clean elaboration ([7745/7745] Building ... 1.0-4.6s, ZERO Lean diagnostics on 4 runs) plus
one run failing to read a corrupted Mathlib dep `.ir` (Mathlib/Util/AtLocation.ir invalid
header, line 40 import). No run ever surfaced a diagnostic about the new theorem; a real
error would print deterministically. Proof arithmetic hand-verified. Ship UNVERIFIED per the
documented persistent SIGBUS/cache-corruption pattern; a later from-scratch build should
confirm green. File 380→432, 19 theorems, still 0 axioms / 0 sorries.

REMAINING (unchanged): HARD half of simultaneous diagonalization (commuting diagonalizable
⟹ common diagonalizer P) — genuinely hard, not session-sized.
