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

---

## Session 2026-06-13 (Session 3) — AUDIT (build blackout)

**Mode**: AUDIT / STATE-SYNC (no Lean change — Docker verification infra down)
**Outcome**: corrected stale gallery counts; flagged OQ blocked pending Docker.

### What I Did
- Audited `proofs/Proofs/SkolemNoetherCSA.lean` against its gallery `meta.json`.
- Found the published `theoremCount` was **stale at 12** while the source proves
  **14** theorems by the canonical `^(theorem|lemma) ` convention used in
  `scripts/research/enrich-research.ts`. Both counting conventions (column-0 and
  include-namespaced) agree on 14 — there are no indented/private theorems — so 12
  matched neither convention and was simply wrong.
- Root cause: the Session-2 narrative recorded "theorem counts (9 → 12)" but the
  actual delta was 11 → 14 (the 3 `IsConjugate.refl/symm/trans` equivalence-relation
  theorems were not counted, even though they are listed in `originalContributions`).
- Fixed `meta.json` in both the `meta` block and the `leanFile` block:
  `theoremCount` 12 → 14, `lineCount` 392 → 394 (`lines.length` = 393 newlines + 1).
  `axiomCount` (1), `definitionCount` (2), `sorries` (0) were already correct.

### The 14 theorems
rightBLinear_is_leftMul, rightBLinear_symm_is_leftMul, isUnit_of_rightBLinear_equiv,
skolemNoether_general, aut_is_inner, conjugate_iff_same_image, IsConjugate.refl,
IsConjugate.symm, IsConjugate.trans, skolemNoether_isConjugate,
conjugateSetoid_single_class, witness_diff_centralizes, witness_mul_centralizer,
witness_set_torsor.

### Status of the open question
The sole remaining gap is discharging the axiom `skolemNoether_module_iso`
(the two A-module structures on B, via f and g, are isomorphic by a right-B-linear
K-linear bijection). This is BLOCKED during the 2026-06-13 verification blackout:
- **Research-hard** (~200-300 lines): needs Wedderburn-Artin
  (`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`, B ≅ Mₙ(D)) + isotypic
  decomposition (`IsSimpleRing.isIsotypic`, forcing B_f ≅ B_g as A-modules) +
  a bimodule-extension argument using centrality of K in B.
- **Build-gated**: Docker build infra is down; unverifiable Lean should not be
  shipped. Resume the axiom discharge once Docker is restored.

### Files Modified
- `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01/meta.json`
  (theoremCount 12 → 14, lineCount 392 → 394, in both blocks)
- `research/problems/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01/state.md`
  (phase → BLOCKED, iteration 3)
- `research/problems/cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01/knowledge.md`
  (this entry)

---

## Session 2026-06-15 — concrete finite-field certificate of the conjugator torsor

The REFINE deliverable pinned the conjugator set `S = {u ∈ Bˣ : g = u·f·u⁻¹}` as a
**torsor** under `(C_B(f(A)))ˣ` (free + transitive coset), the abstract target for the
Lean `MulAction` formalization. This session grounds that structure with an exact,
exhaustive certificate on finite-field matrix instances — `K = 𝔽_q`, `A = M_m(𝔽_q) ↪
B = M_n(𝔽_q)` (`n = m·k`) via `f(a) = a ⊗ I_k`, second embedding `g = c·f(·)·c⁻¹`.

`verify_skolem_noether_torsor.py` (pure stdlib, exact GF(q), full enumeration) confirms:

| instance | C_B(f(A)) dim | \|S\| | \|(C_B)ˣ\| | torsor `u₀⁻¹·S = (C_B)ˣ` |
|----------|---------------|-------|------------|--------------------------|
| A=M₂↪B=M₄ /𝔽₂ (genuine CSA) | 4 = k² | 6 | \|GL₂(𝔽₂)\|=6 | ✓ |
| A=K↪B=M₂ /𝔽₂ (A central) | 4 | 6 | 6 | ✓ |
| A=B=M₂ /𝔽₂ (A=B) | 1 | 1 | 1 | ✓ |
| A=B=M₂ /𝔽₃ (A=B) | 1 | 2 | 2 | ✓ |

All checks pass: (T1) `S` nonempty (Skolem–Noether), (T2) `dim C_B(f(A)) = k² =
dim B / dim A` (double centralizer), (T3) `|S| = |(C_B(f(A)))ˣ| = |GL_k(𝔽_q)|`,
(T4) `u₀⁻¹·S = (C_B(f(A)))ˣ` exactly (free + transitive coset), and (T5) the A=B case
gives `|S| = q − 1`, recovering `Aut_K(M_m) ≅ M_m(𝔽_q)ˣ/𝔽_qˣ`.

This is a concrete instance of the structure the build-gated Lean `MulAction` must
encode (the free+transitive action is exactly the coset equality T4), de-risking the
formalization while Docker is down. It does not discharge the open module-iso axiom
(that needs Wedderburn–Artin / `IsSimpleRing.isIsotypic` in Lean), but it validates the
torsor formulation that is independent of that axiom.

### Files (this session)
- `research/problems/.../verify_skolem_noether_torsor.py` (new)
