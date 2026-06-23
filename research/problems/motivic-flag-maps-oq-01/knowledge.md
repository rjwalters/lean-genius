# Knowledge Base: motivic-flag-maps-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Parent**: `motivic-flag-maps` formalizes the motivic identity `[Ω²_β(Fl_{n+1})] = [GL_n × A^a]` in K₀(Var), proved by Bryan–Elek–Manners–Salafatinos–Vakil (BEMSV) 2025 (arXiv:2601.07222). The proof relies on:
- A definition of `K₀(Var)` (axiomatized via `GrothendieckRingVar` structure at `MotivicFlagMaps.lean:66`).
- A definition of `motivicClassBasedMaps` — the motivic class of the moduli space of based rational maps to flag varieties.
- The BEMSV theorem itself as an axiom.

**OQ-01**: Can the 2 axioms in `MotivicFlagMaps.lean` be removed by formalizing moduli space theory in Mathlib?

---

## Axiom map (`MotivicFlagMaps.lean`, primary file scope)

| # | Name | Line | Type |
|---|---|---|---|
| 1 | `motivicClassBasedMaps` | 309 | `(n : ℕ) (β : HomologyClass n) : K.carrier` |
| 2 | `motivic_class_flag_maps` | 320 | `[Ω²_β(Fl_{n+1})] = [GL_n × A^a]` (BEMSV 2025 main theorem) |

Out-of-scope axioms (in `MotivicFlagMapsPartialFlags.lean`):
- `motivicClassPartialFlagMaps` (L527)
- `partial_flag_extension` (L563) — the open extension conjecture for partial flags.

---

## Mathlib bearer audit (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

**Existing infrastructure** (foundation only):
- `Mathlib/AlgebraicGeometry/*` — schemes, projective spectrum, morphisms (~30 files).
- `Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean` — generic group completion.
- `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` — sole occurrence of "moduli" (j-invariant level).

**Missing in Mathlib at pinned SHA**:
- ❌ `K₀(Var)` — Grothendieck ring of varieties.
- ❌ Flag varieties / Grassmannians as schemes.
- ❌ Moduli spaces of stable maps `M̄_{g,n}(X, β)`.
- ❌ Hilbert schemes, Quot schemes.
- ❌ Spaces of based rational maps `Ω²_β(X)`.
- ❌ Any "motivic" terminology.

---

## Insights

### Insight 1: Axiom #1 cannot be removed without the actual moduli space
`motivicClassBasedMaps` is a *value* in `K.carrier` (the Grothendieck ring). Removing this axiom requires either (a) defining the moduli space concretely as a scheme and pushing it forward to K₀(Var), or (b) refining `GrothendieckRingVar` so that the class can be derived from a constructive description (cell decomposition, F_q point counts, etc.). Both are multi-month projects.

### Insight 2: Axiom #2 IS the BEMSV theorem
`motivic_class_flag_maps` axiomatizes the 2025 paper's main theorem. Removing it means formalizing the BEMSV proof, which uses cell decomposition of `Ω²_β(Fl_{n+1})` and tableaux combinatorics. Research-level.

### Insight 3: Mathlib has no motivic infrastructure at pinned SHA
GitHub code search at the pinned SHA returns ZERO files in Mathlib mentioning "motivic", "K_0(Var)", "stable map moduli", or "Quot scheme". The OQ-03 thread has already established this; OQ-01 inherits the same blocker.

### Insight 4: Sibling OQ-03 thread provides a template
`motivic-flag-maps-oq-03` is actively building a `MotivicMeasure` structure (PR #18457 + #18744) that abstracts the motivic-measure interface. This pattern — replace raw axioms with a structure that bundles assumptions — is the **template for sub-goal A** here: bundle the 2 axioms into a `BEMSVTheoremAxioms` structure.

### Insight 5: Structure-encoded refinement doesn't reduce assumption count
Per CLAUDE.md's Axiom Integrity Policy: moving axioms into a structure does **not** reduce the assumption count. It only changes where they are declared. Sub-goal A's value is **architectural** (cleaner interface, single point of dependency), not assumption-eliminating.

### Insight 6: F_q realization is a tractable falsifiability route
The BEMSV identity in K₀(Var) implies, via the realization homomorphism `K₀(Var) → ℤ[q]`, an exact F_q point count for `Ω²_β(Fl_{n+1})(F_q)`. The F_q count for fixed `(n, β)` is verifiable by combinatorial methods independent of moduli space theory. This is **sub-goal B**: replace the K₀(Var) identity with the (weaker) F_q-count identity.

### Insight 7: GrothendieckRingVar structure already exists in the parent file
`MotivicFlagMaps.lean:66` defines `GrothendieckRingVar` as a structure with `carrier`, `L` (Lefschetz motive), and ring operations. The 2 axioms in this file consume `K : GrothendieckRingVar` — so any future K₀(Var) implementation can be plugged in directly without changing the parent file's signatures.

### Insight 8: Out-of-scope axioms in PartialFlags.lean are genuinely open
The `partial_flag_extension` axiom in `MotivicFlagMapsPartialFlags.lean:563` is the **extension conjecture** for partial flags — it is open mathematically, not just unformalized. Even a perfect Mathlib formalization of BEMSV 2025 would not remove that axiom; it would still be an open conjecture.

---

## Cross-references

- `motivic-flag-maps`: parent gallery proof.
- `motivic-flag-maps-oq-03`: actively-researched sibling; established the "structure-encoded `MotivicMeasure`" pattern. PRs: #18299 #18401 #18457 #18524 #18744.
- arXiv:2601.07222 (BEMSV 2025): the source of axiom #2.

---

## Sub-goals

See `state.md` § "Sub-goal decomposition" for full details:
- **Sub-goal A** (tractable, 30–60 LOC): `BEMSVTheoremAxioms` structure refactor — pure architectural improvement. Axiom count → 0 in this file, but assumption count unchanged.
- **Sub-goal B** (harder, 100–200 LOC + sorries): F_q realization route — replace BEMSV identity with weaker F_q-count identity for small `(n, β)`.
- **Sub-goal C** (blocked on Mathlib, multi-month): full K₀(Var) + flag variety + BEMSV formalization.

---

## Dead Ends

None yet — this is the OBSERVE session.

Likely future dead ends (based on Mathlib audit):
- Searching for an existing K₀(Var) or stable-maps moduli library in Mathlib (does not exist at pinned SHA).
- Trying to derive `motivicClassBasedMaps` from elliptic-curve moduli infrastructure (`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` is too specialized).
- Replacing axioms via `derive`/`decide` tactics — these are propositional/categorical, not computational.

---

## References

- Bryan, J., Elek, B., Manners, F., Salafatinos, G., Vakil, R. (2025). *Motivic class of based maps to flag varieties*. arXiv:2601.07222.
- Kontsevich, M. (1995). *Enumeration of rational curves via torus actions*. (Moduli of stable maps.)
- Bittner, F. (2004). *The universal Euler characteristic for varieties of characteristic zero*. Compositio Math. (K₀(Var) foundations.)
- Mathlib `GrothendieckGroup.lean` (Yaël Dillies et al.): the only existing K₀-like primitive.
