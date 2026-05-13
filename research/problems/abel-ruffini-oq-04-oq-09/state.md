# Current State

**Phase**: S2 PREP complete (per-row Mathlib API path sketches; doc-only)
**Since**: 2026-05-13T23:15:00Z
**Iteration**: 2 (S1 OBSERVE, S2 PREP per-row API sketches)
**Researcher**: researcher-3 (S1); researcher-10 (S2 PREP)

## Current Focus

S1 OBSERVE — scope-narrowed framing of OQ-04-OQ-09 as the "constructive
finite-explicit slice" of Shafarevich's theorem for solvable subgroups of
$S_n$ with $n \leq 4$, distinguishing this slug from siblings
`abel-ruffini-galois-extensions-oq-05` (full Shafarevich axiom) and
`abel-ruffini-galois-extensions-oq-05-oq-01` (cyclic + coprime abelian
proved).

## Active Approach

**S1 deliverable** (this PR): documentation-only OBSERVE scaffold.
- `problem.md`: full statement, classification, scope.
- `knowledge.md`: Mathlib API survey + per-row realization menu.
- `state.md`: this file.
- `src/data/research/problems/abel-ruffini-oq-04-oq-09.json`: registry
  updates (phase OBSERVE, problem statement, knownResults, related proofs).

**No Lean changes.** First Lean work is deferred to S2.

## Findings (S1)

1. **The OQ-04-OQ-09 slug is NOT a duplicate of OQ-05.** OQ-05 axiomatizes
   the full theorem; OQ-04-OQ-09 carves out the axiom-free $n \leq 4$ slice
   that closes the parent's threshold theorem constructively.

2. **9 distinct group structures** appear as transitive Galois groups of
   irreducible polynomials of degree $\leq 4$ over ℚ:
   $\{e\}, \mathbb{Z}/2, \mathbb{Z}/3, \mathbb{Z}/4, V_4, S_3, D_4, A_4, S_4$.
   All 9 are solvable (matches parent's threshold theorem) and all 9 admit
   explicit ℚ-realizations using Mathlib's cyclotomic + splitting-field
   infrastructure.

3. **Mathlib gaps**: none for the cyclic + V₄ rows; the S₃/D₄/A₄/S₄ rows
   require ~100 lines of polynomial-Galois-group identification per case
   (no missing infrastructure, just no pre-packaged lemma).

4. **Sibling reuse**: OQ-05-OQ-01's `cyclic_realizable` already handles
   $\mathbb{Z}/n$ for $n \in \{2, 3, 4\}$. The new gallery entry can
   import that lemma and add the 4 non-abelian cases.

## Blockers

None for S1. For S2+:
- Broken `proofs/.lake` symlink → ~45 min cold-build cycles (see
  `feedback_researcher_lake_symlink_broken.md`). Plan build budget
  accordingly.

### Risks

- **Sibling drift**: if a parallel session updates
  `AbelRuffiniGaloisExtensionsOQ05` to remove the Shafarevich axiom (e.g.
  by importing a Mathlib PR), OQ-04-OQ-09's "axiom-free $n \leq 4$ slice"
  framing becomes less novel. Re-check at S2 start.
- **Polynomial-Galois identification difficulty**: the S₄ case (e.g.
  $X^4 - X - 1$) requires proving the resolvent cubic is irreducible AND
  its discriminant is non-square; the discriminant computation in Lean
  may be longer than expected. Fallback: postpone S₄, deliver
  $\{e, \mathbb{Z}/2, \mathbb{Z}/3, \mathbb{Z}/4, V_4, S_3, D_4, A_4\}$
  (8 of 9 groups) as a first ACT cut.

## Next Action

**S2 (any researcher)** — Choose ONE of:

**Option A — Lean API probe (low-risk, ~30 lines)**:
Create `proofs/Proofs/AbelRuffiniOQ04OQ09Probe.lean` with `#check`s for:
- `Polynomial.SplittingField`
- `Polynomial.Gal.galActionHom`
- `IsCyclotomicExtension.Rat.aut_equiv_pow`
- `Polynomial.Monic.eisensteinAt`
- the parent's `symmetric_solvable_iff_le_four`

Run `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniOQ04OQ09Probe`,
report which names exist, delete the probe file, proceed to S3.
Estimate: 1 Docker cycle (~45 min cold + 5 min compile).

**Option B — Expand knowledge.md menu (~300 lines, no build)**:
For each of the 9 group rows in `knowledge.md` §2, add:
1. Explicit polynomial / cyclotomic-subfield realization.
2. Proof sketch: discriminant computation + irreducibility argument.
3. Specific Mathlib lemma names anticipated.

This is the lower-risk path; it leaves a complete recipe for S3 (the
actual Lean file) without burning a build cycle.

**Recommended**: Option B for S2 — markdown menu completion.

## Attempt Counts

- Total attempts: 0 (S1 is documentation-only)
- Current approach attempts: 0
- Approaches tried: 0

## Session Log

- **S1 (2026-05-12)** — researcher-3 — OBSERVE scaffold. Identified the
  three sibling gallery entries (OQ-05, OQ-05-OQ-01, InverseGalois) that
  already touch Shafarevich and narrowed OQ-04-OQ-09's scope to the
  axiom-free $n \leq 4$ slice. Surveyed Mathlib API surface for cyclotomic
  Galois groups, splitting fields, and `Polynomial.Gal`. Catalogued the
  9 target group structures. **No Lean code; no build.** PR pending.
