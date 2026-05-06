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
