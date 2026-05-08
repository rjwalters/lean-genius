# Knowledge Base: law-of-cosines-oq-01-oq-01-oq-03

**Problem**: Polar triangle construction and dual spherical law of cosines

## Problem Summary

Formalize the polar triangle construction on S² and derive the dual spherical law of cosines:
`cos(γ) = -cos(α)cos(β) + sin(α)sin(β)cos(c)`

Parent: `law-of-cosines-oq-01-oq-01` (proved dual law via Gram determinants)

---

## Session 2026-05-06 (Session 1) — Polar triangle formalized, dual law axiomatized

**Mode**: FRESH
**Outcome**: progress (0 sorries, 2 axioms, PR #16220 open)

### What I Did

1. Read `SphericalLawOfSines.lean` for the `Fin 3 → ℝ` framework with `dot`, `normSq`, `IsUnit3`, `arcLen`, `projPerp`, `dihedralAngle`
2. Identified the key algebraic identity: `dot(B×C, C×A) = -dot(projPerp A C, projPerp B C)` for unit C
3. Proved `normSq(B×C) = normSq(projPerp B C)` from Lagrange identity
4. Proved the **main theorem** `polar_side_eq_pi_minus_angle` (0 sorries):
   - `arcLen(normalize(B×C), normalize(C×A)) = π - dihedralAngle(C, A, B)`
5. Created gallery entry `Proofs/LawOfCosinesOQ01OQ01OQ03.lean` (310 lines, 12 theorems, 2 axioms)
6. Created gallery meta.json

### Key Findings

**Polar triangle vertices**: A' = normalize(B×C), B' = normalize(C×A), C' = normalize(A×B)
where normalize(v) = v/‖v‖.

**Key identity (proved)**: `dot(B×C, C×A) = -dot(projPerp A C, projPerp B C)` for unit C.
Proof: Both equal `-(dot A B - dot A C · dot B C)` by component expansion via `linear_combination`.

**Cross product norms (proved)**: `normSq(B×C) = normSq(projPerp B C) = 1 - (dot B C)²` for unit B, C.
Via `lagrange_identity` from SphericalLawOfSines.

**Polar side formula (PROVED, 0 sorries)**:
```
arcLen(A', B') = arccos(-cos(γ)) = π - γ
```
Since `dot(A', B') = dot(B×C, C×A)/(|B×C||C×A|) = -cos(γ)` exactly.

### Files Created

- `proofs/Proofs/LawOfCosinesOQ01OQ01OQ03.lean` (310 lines)
- `src/data/proofs/law-of-cosines-oq-01-oq-01-oq-03/meta.json`

### Remaining Axioms (to eliminate in future sessions)

1. **polar_angle_eq**: `dihedralAngle(C', A', B') = π - arcLen A B`
   - Proof: analogous to side formula, applying `cross_dot_eq_neg_projperp` to polar triangle projections
   - The computation would show `dot(projPerp A' C') (projPerp B' C') = -dot(A,B)`... 

2. **projperp_dot_sinsincos**: `dot(projPerp A C) (projPerp B C) = sin(arcLen A C) * sin(arcLen B C) * cos(dihedralAngle C A B)`
   - This is the definition of dihedral angle rearranged
   - Proof: cos(arccos(x/y)) * y = x using Cauchy-Schwarz bounds

### Next Steps

- Prove `projperp_dot_sinsincos` using `cos_arccos` + Cauchy-Schwarz (≤ 30 lines)
- Prove `polar_angle_eq` by applying `cross_dot_eq_neg_projperp` to polar vertices (≤ 40 lines)
- Both axioms are mathematically routine — the paths are clear

---

## Session 2026-05-07 (Session 2, Enrichment) — Annotations and cross-references (PR #16667, MERGED)

**Mode**: ENRICHMENT (run by enricher agent, not researcher; logged here for continuity)
**Outcome**: gallery entry made browseable, no Lean changes

### What changed

- Created `src/data/proofs/law-of-cosines-oq-01-oq-01-oq-03/index.ts` (was missing — without it
  the page rendered "proof not found" on the live site).
- Annotations: 0 → 10 with `mathContext` LaTeX, `significance`, `relatedConcepts`, `prerequisites`.
- `meta.json`: expanded `historicalContext` (Napier 1614, Todhunter 1859, projective duality);
  added `mathematicalSignificance`, `prerequisites`, two `openQuestions`
  ($S^n$ generalization via $\Lambda^{n-1}\mathbb{R}^{n+1}$; deriving spherical law of sines from
  polar duality), and 5 `crossReferences` (parent `law-of-cosines-oq-01-oq-01`, grandparent
  `law-of-cosines-oq-01`, planar limit `law-of-cosines`, two siblings).

### Implication for research

None directly — this was a pedagogical/discoverability pass. The Lean proof state was
unchanged: 0 sorries, 2 axioms.

---

## Session 2026-05-08 (Session 3) — `projperp_dot_sinsincos` axiom eliminated + Mathlib drift repair (PR #16788, MERGED)

**Mode**: AXIOM_REDUCTION
**Outcome**: progress (0 sorries, axioms 2 → 1, theorems 12 → 13, lines 271 → 321)

### What I Did

1. Proved `projperp_dot_sinsincos` (~50 lines) via:
   - `sqrt(normSq(projPerp u w)) = sin(arcLen u w)` for unit `u, w` (from
     `normSq_projPerp_unit` + `Real.sin_arccos ≥ 0` on `[0, π]`).
   - Cauchy–Schwarz `(dot pA pB)² ≤ normSq pA · normSq pB` (from `lagrange_identity` +
     `normSq_cross_nonneg`) for the `[-1, 1]` bound feeding `Real.cos_arccos`.
   - `dihedralAngle C A B = arccos(dot(pA, pB) / (|pA|·|pB|))` by definition.
2. Repaired ~9 sites of pre-existing Mathlib API drift that prevented PR #16220's file from
   compiling against current Mathlib (see PR #16788 body for full list — `cross_anticomm`
   parens with `×₃`, `field_simp` no longer needs `ring`, `simp only [crossProduct]` no longer
   beta-reduces, `linear_combination` sign fix, `set_option maxHeartbeats 400000 in` placement
   before the docstring of the next decl, etc.).
3. Synced `meta.json` + `leanFile`: axioms 2→1, theorems 12→13, lineCount.

### Key Lessons (also captured in user memory)

- `set_option foo in` must precede the **docstring** of the next decl, not be sandwiched
  between docstring and decl — else parse error "expected 'lemma'".
- `Real.arccos_neg` matches `arccos(-x)`, not `arccos((-a)/b)`. Add `neg_div` to the rewrite
  chain to convert `(-a)/b → -(a/b)`.
- `simp only [crossProduct]` unfolds the head occurrence of `crossProduct` but does not
  beta-reduce the resulting `LinearMap.mk₂` application; switch to plain `simp [crossProduct]`
  or use `.toFun` patterns explicitly.

### Remaining axiom

**polar_angle_eq**: `dihedralAngle(C', A', B') = π - arcLen A B`
where `A' = normalize(B×C), B' = normalize(C×A), C' = normalize(A×B)`.

Proof sketch (deferred, ~80–100 lines):

1. Cross-cross identities (auxiliary lemmas):
   - `(C×A) ×₃ (A×B) = tripleProduct A B C • A`
   - `(B×C) ×₃ (A×B) = tripleProduct A B C • B`
2. Non-degeneracy: `tripleProduct A B C ≠ 0` follows from
   `normSq(B×C) ≠ 0 ∧ normSq(C×A) ≠ 0 ∧ normSq(A×B) ≠ 0` (the existing hypotheses) +
   the identity `(tripleProduct A B C)² = det(Gram(A,B,C))` (Lagrange).
3. Sign analysis: `normalize3 (k • v) = sign(k) • normalize3 v` for `k ≠ 0`, applied
   to the cross-cross expansions.
4. The final `dot(projPerp(A', C'), projPerp(B', C')) = ±dot(A, B)` reduction then
   gives `arccos(±dot(A,B) / …) = arccos(-dot(A,B)/…) = π - arcLen A B`.

The structural skeleton mirrors `polar_side_eq_pi_minus_angle` (already proved), but with
one additional `tripleProduct ≠ 0` hypothesis threading through.

