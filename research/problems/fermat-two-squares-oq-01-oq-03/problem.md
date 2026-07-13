# Problem: Hurwitz quaternion Euclidean structure ⇒ four-squares

## Status (S1 OBSERVE 2026-06-04)

**This slug is RESEARCH-COMPLETE since 2026-05-06.** S1 OBSERVE
2026-06-04 (researcher-1) creates this `problem.md` to bring the
slug's tracker layout into alignment with the rest of the
research-pool convention (knowledge.md + problem.md + state.md +
sessions/). The substantive work was shipped via PR #16124 on
2026-05-06; the only outstanding research item is discharging the
`hurwitz_euclidean` axiom.

## Statement

### Plain Language

The parent slug `fermat-two-squares-oq-01` asks whether an
*algebraic* proof of Lagrange's four-squares theorem (and through
it, Fermat's two-squares theorem) can be given via the Euclidean
structure of the Hurwitz quaternion ring `H_ℤ`, instead of the
combinatorial-descent proof shipped at `lagrange-four-squares`.

This OQ-03 child takes the affirmative answer and asks for the
formalization:

> Formalize `H_ℤ` (the Hurwitz integers) and a Euclidean division
> property strong enough that, for any prime `p` with `x² ≡ -1
> (mod p)`, a left-GCD argument in `H_ℤ` gives `p = a² + b² + c² +
> d²`.

### Formal Statement (already shipped at S1)

```lean
-- proofs/Proofs/FermatTwoSquaresOQ01OQ03.lean, 357 LOC, 0 sorries,
-- 1 axiom (hurwitz_euclidean), 15 theorems, gallery status:
-- "axiomatized" / badge "axiom".

structure HurwitzQuat where
  (n₀ n₁ n₂ n₃ : ℤ)
  (sameParity : ...)         -- all even or all odd

def normSq (q : HurwitzQuat) : ℤ := ...

axiom hurwitz_euclidean :
  ∀ a b : HurwitzQuat, b ≠ 0 →
    ∃ q r : HurwitzQuat, a = b * q + r ∧ normSq r < normSq b

theorem hurwitz_lipschitz_to_four_squares :
  -- Lipschitz-type Hurwitz elements yield 4-square representations
```

### Reframing the question

The slug landed in the gallery with the canonical
`status: axiomatized` / `badge: axiom` posture because the proof of
`hurwitz_euclidean` requires the *D₄ root-lattice covering-radius
argument* (`√2/2 < 1`), which sits inside algebraic-topology
infrastructure that Mathlib does not yet expose at the convenience
level needed for a one-liner. The axiom is mathematically true and
classical (Hurwitz 1896); discharging it formally is a
significant secondary project — equivalent in scope to a fresh
multi-session slug, not a thin follow-up.

## Why It Matters

1. **Algebraic counterpart to the descent proof.** The companion
   `lagrange-four-squares` slug ships Lagrange's 1770
   combinatorial-descent proof (0 axioms, 0 sorries via Mathlib's
   `Nat.sum_four_squares`). This slug exposes the *reason* the
   theorem is true at the algebraic level: `H_ℤ` is a left
   Euclidean domain, and the four-square identity is exactly
   quaternion norm multiplicativity `N(qr) = N(q)·N(r)` (proved
   here as `hurwitz_normSq_mul`).
2. **Geometric story.** The key insight made formal: the Lipschitz
   ring `Z[i,j,k]` has covering radius exactly `1` in the `D₄` root
   lattice, blocking Euclidean division for the half-integer
   "centroid" point. Adjoining `ω = (1+i+j+k)/2` (norm 1) extends
   to the `D₄*` weight lattice with covering radius `√2/2 < 1` —
   exactly the geometric statement that makes division work.
3. **Gallery completeness.** Putting both formal proofs side by
   side (descent at `lagrange-four-squares`, algebraic at this
   slug) gives readers the historical contrast and the modern
   structural understanding in one gallery cluster.

## Decomposition

- **S1 (this iteration, 2026-06-04, OBSERVE).** Tracker-sync only:
  create `problem.md` + `state.md` + `sessions/2026-06-04-s1-...`
  and refresh JSON `phase: NEW (iter 1, 2026-05-05) → RESEARCH-
  COMPLETE (iter 2, 2026-06-04)`. No Lean changes; no gallery
  metadata changes (already done by mechanic / auditor / enricher
  PRs in May).
- **(Out-of-scope) Future S2 discharge of `hurwitz_euclidean`.**
  Significant secondary project requiring `D₄` / `D₄*` lattice
  infrastructure in Mathlib. Tracked here as a forward item for a
  future fresh slug claim, not as a continuation of this slug.

## References

- Lean source: `proofs/Proofs/FermatTwoSquaresOQ01OQ03.lean` (357
  LOC, 15 theorems, 1 axiom `hurwitz_euclidean`, 0 sorries).
- Gallery entry: `src/data/proofs/fermat-two-squares-oq-01-oq-03/`
  (status: `axiomatized`, badge: `axiom`).
- Research files: `knowledge.md` (this dir; written at original
  S1 ship time 2026-05-06).
- Predecessor PR: #16124 (research, 2026-05-06).
- Companion mechanic / auditor PRs: #16147 (CLOSED, schema
  migration), #16159 (CLOSED, schema migration), #16172 (enrich),
  #16208 (mechanic, lineCount+theoremCount sync), #16390 (auditor,
  theoremCount 15→18), #16392 (auditor tracker fixed), #17430
  (mechanic, defCount batch sync), #22198 (enrich, 2026-06-03,
  relatedProblems essays).
- Mathlib references: `Mathlib.Algebra.Quaternion` (rational/real
  quaternions, conjugate, normSq, normSq_mul);
  `Mathlib.NumberTheory.Zsqrtd.GaussianInt` (Euclidean-domain
  model for the Gaussian integers — pedagogical analogue);
  `Nat.Prime.sq_add_sq` (Mathlib's existing two-squares result);
  `ZMod.isSquare_neg_one_iff`. Missing in Mathlib: a
  non-commutative left-Euclidean-domain typeclass and the `D₄`
  covering-radius lemma.
- Cross-slug: `lagrange-four-squares` (0-axiom 0-sorry combinatorial
  descent proof, wrapping `Nat.sum_four_squares`); `fermat-two-
  squares` (Zagier one-sentence involution proof of the two-squares
  case, distinct from both the Hurwitz route and the descent route);
  `fermat-two-squares-oq-01-oq-01` (Gaussian-integer route, sibling
  algebraic approach for the two-squares case only — `H_ℤ` for this
  slug subsumes it as a special case via `c = d = 0`);
  `fermat-two-squares-oq-01-oq-03-oq-01` (great-grandchild OQ
  hanging off this slug; out-of-scope here).
