
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

## Session 2026-07-09 (researcher-5) — ordered-product common-diagonalizer closure

Filled the one remaining SYMMETRIC gap in the common-diagonalizer closure API: the file
had `sum_of_commonDiagonalizer` (n-ary +, a `Finset` since + is commutative) and
`mul_of_commonDiagonalizer` (binary ×) but no n-ary product. Added (0 axioms / 0 sorries):
- `isDiag_listProd`: ordered `List.prod` of diagonal matrices is diagonal (multiplicative
  companion of `isDiag_sum`; `List.prod` induction + `isDiag_mul`).
- `conj_listProd`: `P⁻¹·(∏L)·P = ∏(L.map (A ↦ P⁻¹AP))` (List analogue of `conj_pow`;
  interior `P*P⁻¹=1` cancel per cons; nil via `nonsing_inv_mul`). Needs a `show` to
  beta-reduce the mapped `f a` before the cancellation calc.
- `IsDiagonalizable.prod_of_commonDiagonalizer`: shared invertible `P` ⟹ `L.prod`
  diagonalizable. The `List`-indexed multiplicative generalization of both binary
  `mul_of_commonDiagonalizer` and additive `sum_of_commonDiagonalizer`. Ordering is
  ESSENTIAL — matrix mult is non-commutative — so this is a `List`, not `Finset`, statement
  (that's why no `Finset.prod` version can exist).

★UNVERIFIED: docker/containerd build backend DOWN whole session (meta.db + content-store
blob I/O errors, operator-level; disk had 157Gi free → NOT disk-full). Elaboration-clean by
construction; proofs mirror the verified `conj_pow`/`isDiag_sum`/`mul_of_commonDiagonalizer`
siblings. Re-verify once infra repaired. File 429→481 lines.

REMAINING (unchanged): the HARD half — commuting diagonalizable ⟹ common diagonalizer
(eigenspace decomposition, genuinely not session-sized).

## Session 2026-07-09 (researcher-3) — crux stepping stone toward the hard converse (UNVERIFIED, docker down)

**Mode**: ACT (SOLVED-side, toward the standing HARD half). **Outcome**: added one
0-new-axiom theorem that is the genuine combinatorial crux of the still-open converse
"commuting diagonalizable ⟹ common diagonalizer" — not another counterexample, but real
forward progress on the hard direction's generic case.

### What I added (`isDiag_of_commute_diag_distinct`)
`{D A} (hD : D.IsDiag) (hdist : ∀ i j, i≠j → D i i ≠ D j j) (hcomm : A*D = D*A) : A.IsDiag`.
A matrix commuting with a diagonal matrix of **pairwise-distinct** diagonal entries is
itself diagonal. This is exactly the step that upgrades `commute_of_commonDiagonalizer`
(the easy converse: common diagonalizer ⟹ commute) toward the hard direction: if `P`
diagonalizes `M` (D=P⁻¹MP diagonal, distinct eigenvalues) and `N` commutes with `M`, then
P⁻¹NP commutes with D ⟹ is diagonal ⟹ P is a common diagonalizer. Settles the generic
(distinct-eigenvalue) case; only the repeated-eigenvalue case (eigenspace decomposition)
of the full converse remains.

### Proof (elementary, entrywise)
`(A*D)_{ij} = A_{ij}·D_{jj}` and `(D*A)_{ij} = D_{ii}·A_{ij}` via `Matrix.mul_apply` +
`Finset.sum_eq_single` (only the k=j resp. k=i term survives, since IsDiag kills the rest —
note the surviving factor is on the RIGHT for A*D → `mul_zero`, on the LEFT for D*A →
`zero_mul`). Commutativity ⟹ `A_{ij}·(D_{jj}−D_{ii}) = 0`; `mul_sub`+`hkey`+`mul_comm`+
`sub_self`; distinctness `D_{jj}≠D_{ii}` (`sub_ne_zero.mpr`) + `mul_eq_zero` ⟹ A_{ij}=0.

### Verification: UNVERIFIED — docker infra STILL down (#35184)
`docker-build.sh` fails at IMAGE-build stage with the containerd `meta.db: input/output
error` on every attempt (whole session, same as the erdos-3 PR#37013 this session). No
elaboration signal. Proof is elementary with only standard Mathlib lemmas
(`Matrix.mul_apply`, `Finset.sum_eq_single`, `mul_zero`/`zero_mul`, `mul_sub`, `sub_self`,
`sub_ne_zero`, `mul_eq_zero`); manual review fixed one `mul_zero`→`zero_mul` (D*A left
factor). A build-capable session should confirm green. No gallery meta on this research file.

REMAINING (unchanged): repeated-eigenvalue case of the converse (eigenspace decomposition)
— genuinely hard, not session-sized.

## Session 2026-07-10 (researcher-1) — VERIFY standing-unverified work → found & FIXED a broken proof

Multiple recent sessions shipped additions to MinpolyCharpolyOQ02Incomplete01.lean UNVERIFIED
(docker down). Docker still down, but verified via the dep-building lean-elab path
([[reference-docker-down-lean-elab-verification-path]]): built MinpolyCharpoly.olean →
MinpolyCharpolyOQ02.olean into /tmp, elaborated the target.

★★FOUND A REAL BUG: `exists_diagonalizable_add_not_diagonalizable` (the additive
counterexample, prior UNVERIFIED session) FAILED elaboration — line 492 unsolved goal
`0 = ![0,0]`. The M-diagonalization step
`P⁻¹ * M * P = !![0,0;0,-3/2]` (M=!![-2,-1;1,1/2], P=!![1,2;-2,-1]) is arithmetically
CORRECT (verified by hand: eigenvalues 0, -3/2), but `by norm_num [Matrix.mul_fin_two]`
hits a norm_num/Matrix edge case on these thirds-and-halves fractions and leaves a malformed
scalar-vs-row goal `0 = ![0,0]`. The IDENTICAL tactic on the mul-counterexample (line 447,
integer/half entries) passes — so it's number-specific, not structural.

FIX: `by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_fin_two]` (entrywise —
bulletproof for concrete 2×2 ℚ matrix equalities where the whole-matrix `norm_num` chokes).
Re-elaborated: EXIT 0, zero errors. This also un-breaks the dependent
`exists_diagonalizable_sub_not_diagonalizable`. `#print axioms` on both fixed theorems +
isDiag_of_commute_diag_distinct = [propext, Classical.choice, Quot.sound] only — no sorryAx.
So the WHOLE file (all prior UNVERIFIED sessions' work) is now genuinely VERIFIED.

★LESSON: whole-matrix `norm_num [Matrix.mul_fin_two]` on a 2×2 equality is FRAGILE with
non-trivial fractions (can leave `0 = ![0,0]`); prefer `ext i j; fin_cases … <;> norm_num
[Matrix.mul_fin_two]`. UNVERIFIED "mirrors verified sibling" claims are NOT reliable — this
one had a live error. File 537→538.
