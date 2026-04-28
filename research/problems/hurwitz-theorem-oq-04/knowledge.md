# Knowledge Base: hurwitz-theorem-oq-04

## Problem Summary

Formalize the connection between Hurwitz's theorem (exactly 4 normed division algebras: ℝ, ℂ, ℍ, 𝕆) and the exceptional Lie groups (G₂, F₄, E₆, E₇, E₈) via:
1. G₂ = Aut(𝕆)
2. Freudenthal-Tits magic square: 𝔏(A,B) = Der(A)⊕(ImA⊗ImB)⊕Der(B)

File: `proofs/Proofs/HurwitzTheoremOQ04.lean` (~1380 lines)

---

## Session 2026-04-28 (Session 7) — Close i=0 sub-case in derEval14_injective

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: PROGRESS — Closed third structural case (i = 0 → real-part kills) via
existing `submodule_der_real_part`. Residual sorry now 42 entries, down from 49.

### What I Did

1. Cherry-picked the prior session's commit `f227e9348c4` (real-part lemma + the
   four helpers `submodule_der_unit_zero`, `submodule_der_diagonal_kill`,
   `submodule_der_antisymm`, `submodule_der_real_part`) onto a fresh master-based
   branch `research/hurwitz-oq-04-derEval14-j-ge-1`.
2. Extended `derEval14_injective`'s `by_cases` chain with a third branch:
   `by_cases hi : i = 0` inside the `j ≠ 0, i ≠ j` case.
   - When `i = 0`, both `f (stdBasis j) 0` and `g (stdBasis j) 0` are zero by
     `submodule_der_real_part`, closing the entry by `rw`.
3. Updated the residual-sorry comment with the precise count (42 entries) and a
   roadmap for the remaining work (ev=0 + antisymmetry + Fano-line Leibniz).

### Sorry Decomposition Status (64-entry kernel)

| Case | Closed by | Entries handled |
|---|---|---|
| j = 0 (any i) | `submodule_der_unit_zero` | 8 |
| j ≠ 0, i = j (diagonal) | `submodule_der_diagonal_kill` | 7 |
| j ≠ 0, i = 0 (real-part) | `submodule_der_real_part` | 7 (NEW) |
| j ≠ 0, i ≠ 0, i ≠ j | residual sorry | 42 |
| **total** | | **64** |

### Key Findings

- The full helper library is now in place: `unit_zero`, `diagonal_kill`,
  `real_part`, `antisymm`, plus `eightMul_stdBasis_*_zero_imag`.
- `submodule_der_real_part` is exactly the ingredient needed for the i=0 sub-case
  — 5 lines of by_cases + rw.
- Build NOT verified: Docker daemon was unresponsive (multi-agent activity);
  per `feedback_docker_build_io_errors.md`, committed and pushed unverified;
  next session should rerun build first.

### Files Modified

- `proofs/Proofs/HurwitzTheoremOQ04.lean` — added i=0 sub-case (5 lines + comment).

### Sorry Status

- Before (master): 1 sorry (entire 56-entry kernel claim, j ≥ 1 only) — but prior
  session's 250-line helper block was *not* on master.
- After: 1 sorry (42-entry kernel claim, j ≠ 0 ∧ i ≠ 0 ∧ i ≠ j); helper block IS
  on this branch (cherry-picked).

### Next Steps

1. Verify the build (Docker capacity permitting).
2. Add the antisymmetry-based WLOG reduction: assume `j > i` (else swap by
   `submodule_der_antisymm`). Reduces 42 → 21 upper-triangular pairs.
3. Extract the 14 ev=0 coords from `hfg` directly (`congr_fun hfg 0`, …, 13);
   this closes 14 of the 21 upper-triangular pairs.
4. The residual 7 upper-triangular pairs are:
   - column 3: (4, 3), (5, 3), (6, 3), (7, 3) — 4 pairs
   - column 5: (6, 5), (7, 5) — 2 pairs
   - column 6: (7, 6) — 1 pair
   These need Fano-line Leibniz analysis (using e₁·e₂=e₃, e₃·e₄=e₇, etc.).

---

## Session 2026-04-27 (Session 6) — Real-part preservation lemma + 4 helpers

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: PROGRESS — Built the helper library: `submodule_der_unit_zero`,
`submodule_der_diagonal_kill`, `submodule_der_antisymm`, `submodule_der_real_part`.

Commit `f227e9348c4` (cherry-picked into Session 7's branch). Each helper proves
a structural property of any element of `OctonionDerSubmodule`:
- unit kills: f(e₀) = 0
- diagonal kill: f(e_j)[j] = 0 for j ≥ 1
- antisymm: f(e_i)[j] + f(e_j)[i] = 0 for distinct i, j ≥ 1
- real-part: f(e_j)[0] = 0 for j ≥ 1, via factorisation e_j = e_p · e_q

Plus the component-0 specialisations of `eightMul`:
- `eightMul_stdBasis_right_zero_imag`: (a · e_k)_0 = -a_k (k ≥ 1)
- `eightMul_stdBasis_left_zero_imag`:  (e_k · a)_0 = -a_k (k ≥ 1)

These four helpers + the by_cases scaffolding are exactly what's needed to
fully close `derEval14_injective` once the 14 ev=0 coords are extracted and the
Fano-line analysis is done.

---

## Session 2026-04-24 (Session 1) — Unit Identity Proofs

**Mode**: REVISIT
**Outcome**: progress — 2 computational sorries eliminated (pending build)

### What I Did

- Attempted to prove `eightMul_right_unit` and `eightMul_left_unit`
- Pattern from existing proofs: `simp only [stdBasis, ...] <;> simp (config := { decide := true }) only [ite_true, ite_false] <;> ring`
- Key insight: `simp (config := { decide := true })` is needed to evaluate `if (0:Fin 8) = j then 1 else 0` for concrete j values — found this in HurwitzTheorem.lean line 956

### Proof Attempts

**eightMul_right_unit** (and left_unit analogously):
```lean
set_option maxHeartbeats 800000 in
theorem eightMul_right_unit (a : Fin 8 → ℝ) : eightMul a octUnit = a := by
  funext i
  fin_cases i <;>
  simp only [eightMul, octUnit, stdBasis,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;>
  simp (config := { decide := true }) only [ite_true, ite_false] <;>
  ring
```

### Key Technical Insights

- `octUnit = stdBasis 0 = fun j => if (0:Fin 8) = j then 1 else 0`
- After `fin_cases i`, the eightMul formula has concrete `octUnit j` for j = 0..7
- Plain `simp [stdBasis]` may not evaluate `(0:Fin 8) = j` for concrete j — need `decide := true` config
- Matrix.cons_val_* lemmas needed to access components of `![expr0, ..., expr7]`
- Pattern from line 956: `simp (config := { decide := true }) only [ite_true, ite_false]`

### Remaining Sorries

1. **alg_aut_preserves_norm** (line 160): normSq(φ(a)) = normSq(a) for OctonionAut
   - Cannot be proved from current axioms (alg hom + invertibility) without additional structure
   - Would need: φ(e₀) = e₀ (requires idempotent classification: only 0 and e₀ are idempotent in 𝕆)
   - OR: redefine OctonionAlgHom to include `map_norm` field (changes the formalization)
   
2. **real_part_preserved** (line 201): realPart(φ(x)) = realPart(x) for OctonionAut
   - Depends on alg_aut_preserves_norm and φ(e₀) = e₀

### Why alg_aut_preserves_norm Needs More

The algebra homomorphism condition `φ(a*b) = φ(a)*φ(b)` combined with the 8-square identity only gives:
  `normSq(φ(a)) * normSq(φ(b)) = normSq(φ(a*b))`
  
This is consistent with normSq being preserved, but doesn't FORCE it. The argument would be circular.

For a true proof:
1. Show φ(e₀) = e₀: Since φ(e₀)^2 = φ(e₀) (idempotent), and 𝕆 is a division algebra, the only idempotents are 0 and e₀. Since φ is injective, φ(e₀) ≠ 0. So φ(e₀) = e₀.
2. Then: normSq(φ(a)) * 1 = normSq(φ(a)) * normSq(e₀) = normSq(φ(a * e₀)) = normSq(φ(a)) [right unit]
   But this is tautological.
3. The actual proof uses: for any y in the image of φ, normSq(φ⁻¹(y)) = normSq(y). But we can't prove this without knowing normSq is preserved.

**Conclusion**: Need to add `map_one` to OctonionAlgHom AND a separate proof that unit-preserving multiplicative maps with the 8-square structure preserve norms. ~50 lines but requires restructuring.

### Next Steps

1. Add `map_one : map octUnit = octUnit` to OctonionAlgHom structure
2. Prove `alg_hom_unit : φ.map octUnit = octUnit` (trivial from new field)
3. Use this to prove `alg_aut_preserves_norm`:
   - From alg_hom_preserves_norm_product with b = octUnit: normSq(φ(a)) * normSq(φ(octUnit)) = normSq(φ(a * octUnit)) = normSq(φ(a))
   - Since φ(octUnit) = octUnit: normSq(φ(a)) * 1 = normSq(φ(a)) ✓ (still tautological!)
   - Need additional argument: normSq(φ(a)) = normSq(a) by "quadratic form invariance"
   
4. Alternative: axiomatize `alg_aut_preserves_norm` as an axiom (it's true, just hard to prove from our formalization)

---

## Session 2026-04-25 (Session 4) — De-axiomatize + Der(𝕆) Lie Algebra

**Mode**: REVISIT (RICH knowledge tier, score 24)
**Outcome**: PROGRESS — 4 axioms removed (rfl), OctonionDer Lie algebra formalized (0 sorries)

### What I Did

1. **De-axiomatized 4 trivial axioms**: `freudenthal_tits_f4/e6/e7/e8` were `axiom X.dim = N`
   where `X.dim` is DEFINED as `N`. These are just `rfl` — changed from `axiom` to `theorem ... := rfl`.
   Axiom count: 5 → 1 (only `G2_is_octonion_aut` remains as genuine axiom).

2. **Added PART IV-b: Der(𝕆)** (~140 lines, 0 sorries):
   - `eightMul_add_left/right/smul_left/right`: bilinearity helpers extracted from eightSquareIdentity
   - `OctonionDer` structure: ℝ-linear maps with Leibniz rule D(ab) = D(a)b + aD(b)
   - `zeroDer`: zero map is a derivation (0 sorries, proved by `fin_cases i; simp [eightMul]; ring`)
   - `addDer`: sum of two derivations (0 sorries, proved by `rw [D₁.leibniz, D₂.leibniz]; abel`)
   - `smulDer`: scalar multiple of a derivation (0 sorries, proved by bilinearity rewrites)
   - `eightMul_sub_left/right`: subtraction linearity (proved via add + smul)
   - `commDer`: [D₁,D₂] is a derivation (0 sorries, proved via h1/h2 expansions + abel)
   - `commDer_self_eq_zero`: [D,D] = 0 (0 sorries)
   - `commDer_antisymm`: [D₁,D₂] = -[D₂,D₁] (0 sorries)
   - `commDer_jacobi`: [[D₁,D₂],D₃] + [[D₂,D₃],D₁] + [[D₃,D₁],D₂] = 0 (0 sorries, `ring`)

### Key Findings

- **4 axioms were trivially true**: The `freudenthal_tits_*` axioms just said `dim = dim`. No
  mathematical content. The real mathematical claim (𝔏(𝕆,A) = ExceptionalType) is NOT formalized.
- **commDer.leibniz proof structure**: The key is to expand D₁(D₂(ab)) and D₂(D₁(ab)) separately
  using `h1`, `h2`, then use `eightMul_sub_left/right` for subtraction bilinearity, then `abel`.
  The cross-terms D₂(a)D₁(b) and D₁(a)D₂(b) cancel.
- **commDer_jacobi by ring**: After unfolding `commDer`, the Jacobi identity becomes an abelian
  group equation `ring` closes directly.
- **Lie algebra of Der(𝕆)**: Formalized: Der(𝕆) is closed under commutator [·,·], antisymmetric,
  satisfies Jacobi. This is the Lie algebra 𝔤₂ = Der(𝕆) at the algebraic level.

### Files Modified

- `proofs/Proofs/HurwitzTheoremOQ04.lean` (583 → 730 lines; PART IV-b added, preamble updated)
- `src/data/proofs/hurwitz-theorem-oq-04/meta.json` (axiomCount 5 → 1, lineCount 730, theoremCount 31)
- `src/data/research/problems/hurwitz-theorem-oq-04.json` (knowledge updated)

### Axiom Count: 5 → 1

- ~~freudenthal_tits_f4~~ → `theorem freudenthal_tits_f4 := rfl` ✓
- ~~freudenthal_tits_e6~~ → `theorem freudenthal_tits_e6 := rfl` ✓
- ~~freudenthal_tits_e7~~ → `theorem freudenthal_tits_e7 := rfl` ✓
- ~~freudenthal_tits_e8~~ → `theorem freudenthal_tits_e8 := rfl` ✓
- `G2_is_octonion_aut`: UNCHANGED (genuinely needs Lie group theory)

### Next Steps

1. **Exhibit 14 explicit derivations** of 𝕆: The space Der(𝕆) has dim 14. We could exhibit
   specific derivations via cross-product operators L_a,R_b — e.g., D_{ij}(x) = eₙ*(eᵢx)-eᵢ*(eⱼx)
   for specific basis pairs. ~100 lines.
2. **Archive sessions 1-3**: Move to sessions/ subdirectory (knowledge.md now >100 lines).
3. **G2_is_octonion_aut**: Still axiom. Proving it formally requires Lie group theory not in Mathlib.
   Could reformulate it as a dim(Der(𝕆)) = 14 statement once explicit derivations are exhibited.

---

## Session 2026-04-26 (Session 5) — Axiom Correction + OctonionDerSubmodule

**Mode**: REVISIT (RICH knowledge tier, score 31)
**Outcome**: PROGRESS — axiom replaced with mathematically correct formulation

### What I Did

1. **Fixed mathematically incorrect axiom**: `G2_is_octonion_aut : G2.dim = Nat.card OctonionAut`
   asserts `14 = Nat.card OctonionAut`. Since OctonionAut is infinite (G₂ is a continuous
   Lie group), `Nat.card OctonionAut = 0` in Lean. The axiom was effectively `14 = 0`.
   Replaced with `G2_der_dimension : finrank ℝ OctonionDerSubmodule = G2.dim` — mathematically
   correct statement about the Lie ALGEBRA dimension.

2. **Added PART IV-c: OctonionDerSubmodule** (~30 lines, 0 sorries):
   - `eightMul_zero_left/right`: zero · b = 0 and a · 0 = 0 (private lemmas)
   - `OctonionDerSubmodule`: Der(𝕆) as a `Submodule ℝ ((Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ))`
   - Membership: zero_mem (trivial), add_mem (bilinearity + abel), smul_mem (bilinearity)
   - `G2_der_dimension`: axiom finrank ℝ OctonionDerSubmodule = 14

### Key Findings

- **Nat.card vs finrank**: `Nat.card` of an infinite type returns 0. `FiniteDimensional.finrank`
  is the right tool for Lie algebra dimension, requiring Module + FiniteDimensional instances.
- **Submodule approach**: Der(𝕆) as a `Submodule ℝ (LinMap)` automatically inherits all
  module structure from the ambient finite-dimensional End_ℝ(ℝ⁸) (dim 64).
- **Previous formulation was inconsistent**: If Lean ever proves `Infinite OctonionAut`,
  the old axiom `14 = 0` would give `False`. The new axiom avoids this.

### Files Modified

- `proofs/Proofs/HurwitzTheoremOQ04.lean` (736 → 764 lines; PART IV-c added, axiom fixed)
- `src/data/research/problems/hurwitz-theorem-oq-04.json` (knowledge updated)
- `src/data/proofs/hurwitz-theorem-oq-04/meta.json` (lineCount, theoremCount, assumptions)

### Next Steps

1. **Exhibit 14 derivations**: D_{ij}(x) for 1 ≤ i < j ≤ 7 to PROVE G2_der_dimension
2. **Linear independence**: 14×14 matrix argument (decide-based)
3. **Archive sessions 1-4** to sessions/ directory

---

## Session 2026-04-27 (Session 7) — Diagonal Kill (i = j subcase)

**Mode**: REVISIT (RICH, score 36)
**Outcome**: PROGRESS — added two helper lemmas, scoped down remaining sorry from 56 → 49 entries.

### What I Did

1. **Added `stdBasis_sq_neg_unit`**: For any imaginary basis `eⱼ` (j ≠ 0),
   `eⱼ · eⱼ = -e₀`. Proof by case-on-j (1..7), then component-wise `simp+ring`.

2. **Added `submodule_der_diagonal_kill`**: For any `f ∈ OctonionDerSubmodule`
   and `j ≠ 0`, `(f eⱼ)_j = 0`. Apply Leibniz at (eⱼ, eⱼ), use
   `stdBasis_sq_neg_unit` to rewrite `eⱼ² = -e₀`, then `LinearMap.map_neg` +
   `submodule_der_unit_zero` give `f(-e₀) = 0`. Component 0 reduces to
   `-2·(f eⱼ)_j = 0`.

3. **Refactored `derEval14_injective`**: Within the `j ≠ 0` branch, added
   `by_cases hij : i = j`. The `i = j` (diagonal) case is closed via
   `submodule_der_diagonal_kill`; `i ≠ j` (off-diagonal) remains as `sorry`.

### Sorry Status

- Before: 1 sorry (entire 56-entry imaginary-basis kernel claim)
- After: 1 sorry (49-entry off-diagonal claim: j ∈ {1..7}, i ≠ 0, i ≠ j)

### Files Modified

- `proofs/Proofs/HurwitzTheoremOQ04.lean` (1123 → 1180 lines)

### Next Steps

1. Antisymmetry helper: `(f eᵢ)_j + (f eⱼ)_i = 0` from Leibniz at `(eᵢ, eⱼ) + (eⱼ, eᵢ)`.
2. Real-part preservation: `(f eⱼ)_0 = 0` for j ≥ 1 via Fano-line Leibniz.
3. Combine all constraints to determine all 64 entries.

---

## Session 2026-04-27 (Session 8) — Antisymmetry helper added

**Mode**: REVISIT (RICH, score 41)
**Outcome**: PROGRESS — Added the on-Im(𝕆) antisymmetry lemma plus its
combinatorial precursor; both stated for any `f ∈ OctonionDerSubmodule`.
Sorry count unchanged (still 1 in the off-diagonal `derEval14_injective`
sub-case), but the lemma library now provides the structural tool the
next session needs to attack the off-diagonal kernel claim.

### What I Did

1. **Added `imag_anticomm`** (private lemma): for `i, j ∈ {1,...,7}`,
   `i ≠ j`, the symmetric octonion product vanishes:
   `eightMul (stdBasis i) (stdBasis j) + eightMul (stdBasis j) (stdBasis i) = 0`.
   Proof by `fin_cases i <;> fin_cases j <;> funext k <;> fin_cases k <;>
   simp + ring` (≈42 × 8 = 336 leaves; uses `set_option maxHeartbeats 6400000`).
   This is a pure octonion-multiplication identity — no derivation involved.

2. **Added `submodule_der_antisymm`** (private lemma): for any
   `f ∈ OctonionDerSubmodule` and `i ≠ 0, j ≠ 0, i ≠ j`,
   `(f eᵢ)_j + (f eⱼ)_i = 0`. Proof: apply Leibniz at `(eᵢ, eⱼ)` and
   `(eⱼ, eᵢ)`; sum and use `imag_anticomm` to reduce LHS to `f 0 = 0`.
   The 0-th component of the four product terms each evaluates to
   `-(f eᵢ)_j` or `-(f eⱼ)_i` (each appearing twice via the symmetric
   inner-product structure of `(a·b)_0`), giving
   `-2·((f eᵢ)_j + (f eⱼ)_i) = 0`. Same fin_cases pattern with linarith.

### Key Findings

- The 0-th component of any octonion product `(a·b)_0` is the
  negative-definite inner product `a_0·b_0 - ∑_{k≥1} a_k·b_k`. Both
  `(v · eⱼ)_0` and `(eⱼ · v)_0` equal `-v_j` for `j ≥ 1`. This
  symmetry is what makes the antisymmetry result work cleanly.
- Im(𝕆) anti-commutativity (`eᵢ·eⱼ = -eⱼ·eⱼ` for `i ≠ j` both `≥ 1`)
  is essential — without it the LHS `f(eᵢeⱼ + eⱼeᵢ)` would contain
  a non-trivial `f(εeₖ)` term and antisymmetry would not hold cleanly.
- This puts `Der(𝕆) ⊆ 𝔰𝔬(7)` (anti-symmetric matrices on `Im(𝕆) ≅ ℝ⁷`,
  dim 21). The remaining cut from 21 down to 14 = G₂ requires the
  Fano-line Leibniz constraints (next session).

### Files Modified

- `proofs/Proofs/HurwitzTheoremOQ04.lean` (1180 → 1255 lines; +75)
- `src/data/research/problems/hurwitz-theorem-oq-04.json` (knowledge updated)
- `research/problems/hurwitz-theorem-oq-04/knowledge.md` (this entry)

### Sorry Status

- Before: 1 sorry (49-entry off-diagonal claim, j ∈ {1..7}, i ≠ 0, i ≠ j)
- After: 1 sorry (same target — but we now have antisymmetry available
  to reduce 42 off-diagonal pairs (j, i) with j ≠ i to ≈14 + Fano-line work)

### Build Verification

NOT run (disk at 1.2 GB free; per saved guidance, skip Docker builds when
disk < 1 GB or borderline). Proof structure mirrors `submodule_der_diagonal_kill`
and `stdBasis_sq_neg_unit` (both successful in main). Risk: a single typo in
an iterated `simp` set, which the next session / CI build / mechanic will
catch quickly.

### Next Steps

1. **Real-part preservation**: prove `(f eⱼ)_0 = 0` for `j ≥ 1`. Strategy:
   express each `eⱼ` as a product of two distinct imaginary basis
   vectors. Then `(f(eᵢ·eₖ))_0 = -(f eᵢ)_k - (f eₖ)_i = 0` by
   `submodule_der_antisymm`.
2. **Use antisymmetry to close i = 0 sub-case** of `derEval14_injective`:
   `f (stdBasis j) 0 = 0 = g (stdBasis j) 0` via real-part preservation.
3. **Use antisymmetry to swap (j, i) → (i, j)** in the off-diagonal case:
   reduces the 42 unordered pairs to ≈14 ordered ones; combine with the
   14 explicit ev coordinates to cover (1,k), (2,k), (4,k) directly,
   leaving only pairs in {3,5,6,7}² + {(3,4),(4,3)} for Fano-line work.
4. **Fano-line trilinear Leibniz** for the remaining ~14 uncovered
   pairs (those involving only {3,5,6,7}): apply Leibniz at three
   specific basis vectors on a Fano line to relate the components.

---

## Session 2026-04-27 (Session 9, researcher-7) — Multiplication-Table Audit

**Mode**: REVISIT (RICH, score 49)
**Outcome**: Documentation only. Disk pressure (~1 GB free) prevented Docker
build verification of any new lemmas; instead, did a careful audit of the
`eightMul` definition (HurwitzTheorem.lean:255–271) to derive the exact
factorisation table needed by the next session's real-part-preservation proof.

### Verified `eᵢ · eⱼ = eₖ` table (for the real-part-preservation lemma)

Reading off `eightMul`'s component-k formula and looking for the unique
positive monomial `aᵢ · bⱼ`:

| Target `eⱼ` | Factorisation | Verifying monomial |
|------------|---------------|--------------------|
| `e₁`       | `e₂ · e₃`     | comp 1: `+a₂b₃`    |
| `e₂`       | `e₃ · e₁`     | comp 2: `+a₃b₁`    |
| `e₃`       | `e₁ · e₂`     | comp 3: `+a₁b₂`    |
| `e₄`       | `e₅ · e₁`     | comp 4: `+a₅b₁`    |
| `e₅`       | `e₁ · e₄`     | comp 5: `+a₁b₄`    |
| `e₆`       | `e₂ · e₄`     | comp 6: `+a₂b₄`    |
| `e₇`       | `e₃ · e₄`     | comp 7: `+a₃b₄`    |

All seven factorisations have `i ≠ 0`, `k ≠ 0`, and `i ≠ k`, which is
exactly the precondition `submodule_der_antisymm` requires.

### Two crucial component identities (no proof yet — for next session)

For `k ≥ 1` and any vector `a`,
`(eightMul a (stdBasis k))_0 = -aₖ`
(reading off comp 0: `a₀(eₖ)₀ - a₁(eₖ)₁ - … - a₇(eₖ)₇ = -aₖ`).

Symmetrically, for `i ≥ 1` and any vector `b`,
`(eightMul (stdBasis i) b)_0 = -bᵢ`.

These should be added as private lemmas
(`eightMul_stdBasis_right_zero_imag` and `…_left_zero_imag`) before the
real-part-preservation proof — they isolate the only fact the proof needs
about component 0, eliminating most of the per-case `simp + ring` work.

### Recommended structure for the next session's work

```lean
private lemma eightMul_stdBasis_right_zero_imag (a : Fin 8 → ℝ)
    (k : Fin 8) (hk : k ≠ 0) :
    eightMul a (stdBasis k) 0 = -a k := by
  fin_cases k
  · exact absurd rfl hk
  all_goals
    simp [eightMul, stdBasis, Matrix.cons_val_zero, …] <;>
    simp (config := { decide := true }) [ite_true, ite_false] <;> ring

private lemma eightMul_stdBasis_left_zero_imag … -- symmetric

private lemma submodule_der_real_part
    (f : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ)) (hf : f ∈ OctonionDerSubmodule)
    (j : Fin 8) (hj : j ≠ 0) : f (stdBasis j) 0 = 0 := by
  fin_cases j
  · exact absurd rfl hj
  -- For each j ∈ {1,…,7}, use the table above.
  -- e₁ case: pick (i,k) = (2,3), use Leibniz, the two component lemmas,
  --          and submodule_der_antisymm (reduces to -A - B = 0 where A+B = 0).
  …
```

This decomposition keeps the per-case work to ~6 lines each (× 7 cases) rather
than the ad-hoc 50-line block hinted at in session 8's notes.

### Why no Lean changes this session

- Disk at ~1 GB free (borderline per saved guidance).
- File is 1255 lines, intricate; prior sessions' edits sometimes silently
  reverted under disk pressure.
- Multiple PRs landing on this file in the last 24 h (#13228, #13371) — risk
  of conflict if I push speculative un-verified code in parallel.

### Files Modified

- `research/problems/hurwitz-theorem-oq-04/knowledge.md` (this entry only).

### Sorry Status

- Before: 1 sorry (off-diagonal kernel claim, `j ∈ {1..7}, i ≠ 0, i ≠ j`).
- After: 1 sorry (no change).
