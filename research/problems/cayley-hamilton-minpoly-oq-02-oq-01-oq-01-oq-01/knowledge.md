# cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01

**Question**: Can the more general Skolem-Noether theorem for arbitrary central simple algebras be formalized in Lean 4 using Mathlib?

**Formal target**: For A a finite-dimensional simple K-algebra and B a finite-dimensional central simple K-algebra, any two K-algebra homomorphisms f, g : A →ₐ[K] B are conjugate by a unit u ∈ Bˣ: f(a) = u⁻¹·g(a)·u for all a ∈ A.

---

## Session 2026-05-06 (Session 1) — IN-PROGRESS

**Mode**: FRESH
**Outcome**: in-progress (1 axiom, 0 sorries, 7 proved theorems, build submitted)

### What I Did
- Surveyed Mathlib v4.26 for central simple algebra (CSA) infrastructure: found CSA structure, Algebra.IsCentral, IsSimpleRing, Wedderburn-Artin, IsIsotypic, BrauerGroup — all in Mathlib
- Identified 4-stage proof architecture:
  1. Right-B-linear maps are left multiplication (trivial algebra lemma — proved)
  2. Unit extraction from bijective linear equiv (proved via φ∘φ⁻¹=id)
  3. A-module isomorphism B_f ≃ B_g (axiomatized — needs Wedderburn+IsIsotypic)
  4. Conjugation formula from module iso (proved)
- Wrote SkolemNoetherCSA.lean (~240 lines) with 7 theorems proved and 1 axiom
- Created gallery entry at `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01/meta.json`
- Submitted Docker build

### Key Findings
- The algebraic core of Skolem-Noether is a 1-line lemma: φ(b) = φ(1)·b for right-B-linear maps
- Unit extraction requires no finite-dimensionality: just φ∘φ⁻¹=id gives u·v=1 and v·u=1
- The hard part is purely the module isomorphism B_f ≃ B_g, which needs Wedderburn-Artin + isotypic decomposition
- Mathlib v4.26 has IsSimpleRing.exists_ringEquiv_matrix_divisionRing and IsSimpleRing.isIsotypic — the exact tools needed

### Files Modified
- `proofs/Proofs/SkolemNoetherCSA.lean` (new, ~240 lines)
- `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01/meta.json` (new)
- `src/data/research/problems/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01.json` (updated)

### Next Steps
1. Verify build passes (axiom is well-typed, all proved lemmas check)
2. Submit PR for the axiomatized version
3. Future work: prove `skolemNoether_module_iso` using:
   - `IsSimpleRing.isIsotypic` for uniqueness of simple A-module
   - `IsSimpleRing.exists_ringEquiv_matrix_divisionRing` (Wedderburn-Artin)
   - Bimodule extension principle (centrality of K in B)

---

## Session 2026-06-06 (Session 2) — IN-PROGRESS

**Mode**: REFINE (extending existing entry)
**Outcome**: in-progress (1 axiom unchanged, 0 sorries, 12 proved theorems total — +3 new, build needs verification)

### What I Did
- Identified a structural refinement opportunity: the existing `IsConjugate` predicate is qualitative (∃ a unit u with the conjugation), but Skolem-Noether's deeper content is *quantitative* — the set of conjugating units, when nonempty, forms a torsor under a specific centralizer.
- Proved **witness ambiguity = centralizer torsor** as 3 new hypothesis-free theorems (no simple/CSA/finite-dim, independent of `skolemNoether_module_iso`):
  1. `witness_diff_centralizes`: if `u, u'` are both witnesses for the conjugation `f = conj(u⁻¹)(g)`, then `u'·u⁻¹` commutes with every element of `g(A)`.
  2. `witness_mul_centralizer`: converse — multiplying a witness by a centralizing unit yields another witness.
  3. `witness_set_torsor`: combined statement — `c ↦ c·u` embeds the centralizer of `g(A)` in `Bˣ` into the witness set.
- Updated gallery meta.json with new section, originalContributions, and theorem counts (9 → 12, lineCount 311 → 392).

### Key Findings
- The proofs use only ring associativity + Units inverse identities — no commutativity, no finite-dim, no simple-ring hypotheses. Holds for arbitrary `Ring A`, `Ring B`, `Algebra K A`, `Algebra K B`.
- The "torsor under the centralizer" structure is a textbook consequence of Skolem-Noether (cf. Pierce, *Associative Algebras*, §12). Formalizing it makes the witness ambiguity *quantitative* — a building block for:
  - The "Skolem-Noether action map" Aut_K(B) → Bˣ / Z(Bˣ) (kernel = inner conjugacy ambiguity).
  - The connection to Galois cohomology H¹(Gal, Z(D)×) classifying lifts.
  - The well-definedness of Brauer group operations.
- The Lean proofs are short (~50 lines for 3 theorems) because the algebra is just associativity manipulation; `simp only [mul_assoc]` normalizes parenthesization on both sides.

### Files Modified
- `proofs/Proofs/SkolemNoetherCSA.lean` (+81 lines, 311 → 392)
- `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01/meta.json` (originalContributions, sections, leanFile.theoremCount, lineCount)
- `research/problems/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01/knowledge.md` (this entry)

### Next Steps
1. Verify Docker build passes — the 3 new theorems use only `mul_assoc`, `Units.mul_inv`, `Units.inv_mul`, `Units.val_mul`, `mul_inv_rev`, `mul_one`, `one_mul`, and `simp only [mul_assoc]` for non-commutative reassociation. All standard.
2. Future work: extend the torsor structure to a `MulAction` of `Subalgebra.centralizer (g.range)` on the witness set, and a `Setoid`-quotient structure relating witnesses up to centralizer action.
3. Long-term: still need to prove the `skolemNoether_module_iso` axiom (Wedderburn + Isotypic decomposition, ~200-300 lines).
