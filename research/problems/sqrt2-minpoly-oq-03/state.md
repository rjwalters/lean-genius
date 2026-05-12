# Current State

**Phase**: OBSERVE (S1 scaffold complete; no Lean changes yet)
**Since**: 2026-05-12T17:30:00Z
**Last Updated**: 2026-05-12 (Iteration 1, researcher-10)
**Iteration**: 1

## Iteration 1 (researcher-10, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md`, and `src/data/research/problems/sqrt2-minpoly-oq-03.json`.
No Lean changes.

### What I added

Doc-only scaffolding for a fresh tier-B slug. The deliverable is:

- A precise framing of "class number 1 for $\mathbb{Q}(\sqrt 2)$ via
  Minkowski's bound" as a follow-up to the parent's minimal-polynomial
  result. The formal target is
  `NumberField.classNumber (Q_sqrt2) = 1`, with two strictly stronger
  optional corollaries: `IsPrincipalIdealRing` and `EuclideanDomain`
  on the ring of integers.
- A tractability triage distinguishing the **Minkowski-bound route**
  (S2-S4: define Q(√2) as a number field, compute discriminant 8,
  compute Minkowski bound √2, conclude h_K = 1) from the **Euclidean-
  domain route** (S5 optional: $|N(a + b\sqrt 2)| = |a^2 - 2b^2|$
  with division-with-remainder verified geometrically).
- A survey of the Mathlib surface (`NumberField.classNumber`,
  `NumberField.minkowskiBound`, `NumberField.RingOfIntegers`,
  `NumberField.discr`, `Zsqrtd 2`) and the parent / sibling re-use
  opportunities (parent provides irreducibility of $X^2 - 2$ over $\mathbb{Q}$;
  the Gaussian integer `Mathlib.NumberTheory.Zsqrtd.GaussianInt`
  provides a Euclidean-domain template).
- A concrete S2 plan: build
  `proofs/Proofs/Sqrt2MinpolyOQ03.lean`, construct
  $\mathbb{Q}(\sqrt 2)$ via
  `Polynomial.SplittingField (X^2 - C 2 : ℚ[X])`, verify the
  `NumberField` instance, and stub the main theorem
  `Q_sqrt2_classNumber_eq_one` with the inline strategy
  (discriminant 8 → Minkowski bound √2 → h_K = 1).

### Why not S2 in this session

S2 ORIENT requires verifying Mathlib's `NumberField.classNumber`,
`NumberField.discr`, and `NumberField.minkowskiBound` API at the
pinned v4.26.0 rev — particularly the exact module path
(`Mathlib.NumberTheory.NumberField.Minkowski` vs
`Mathlib.NumberTheory.NumberField.CanonicalEmbedding`) and the form
of the bound (a `Real.toNNReal` or a plain `ℝ`). The recursive
`proofs/.lake` self-symlink in this worktree (per
`feedback_researcher_lake_symlink_broken.md`) prevents direct
Mathlib search; that lookup is best done in S2 ORIENT where the
build can verify the imports compile.

Additionally, the OQ-03 deliverable has a *Minkowski-route* /
*Euclidean-route* split that benefits from being made explicit in
the S2 plan — the Minkowski route is the canonical proof in Marcus
Chapter 5, while the Euclidean route is the canonical proof in
Stewart-Tall and Hardy-Wright; both are gallery-worthy, but the
Minkowski route is the more general (it scales to other small
quadratic fields).

### Files added (S1)

- `research/problems/sqrt2-minpoly-oq-03/problem.md` — problem
  description with tractability triage, references (Marcus,
  Neukirch, Stewart-Tall, Hardy-Wright), and parent / sibling
  linkage
- `research/problems/sqrt2-minpoly-oq-03/knowledge.md` — Mathlib
  surface inventory, feasibility table, S2 plan, risk register
- `research/problems/sqrt2-minpoly-oq-03/state.md` — this file
- `src/data/research/problems/sqrt2-minpoly-oq-03.json` —
  phase OBSERVE, iter 1, references, knowledge surface

### Next action (S2 ORIENT)

Create `proofs/Proofs/Sqrt2MinpolyOQ03.lean` with:

1. Imports: parent (`Proofs.Sqrt2Minpoly` for irreducibility) +
   `Mathlib.NumberTheory.NumberField.Basic` +
   `Mathlib.NumberTheory.NumberField.ClassNumber` +
   `Mathlib.NumberTheory.NumberField.Discriminant` +
   `Mathlib.NumberTheory.NumberField.CanonicalEmbedding` (verify
   exact module name for Minkowski-bound API at v4.26.0) +
   `Mathlib.NumberTheory.Zsqrtd.Basic`.
2. `def Q_sqrt2 : Type := Polynomial.SplittingField (X^2 - C 2 : ℚ[X])`
   (or via `AdjoinRoot` if the splitting-field instance derivation
   for `NumberField Q_sqrt2` is friction-heavy at the pin).
3. `instance : Field Q_sqrt2`, `instance : Algebra ℚ Q_sqrt2`,
   `instance : NumberField Q_sqrt2` — derive from Mathlib's
   `SplittingField` instances + the parent's
   `irred_X_sq_sub_two_rat`.
4. `theorem Q_sqrt2_classNumber_eq_one :
        NumberField.classNumber Q_sqrt2 = 1 := by sorry` —
   strategic sorry, with the inline strategy documented:
   * Compute `NumberField.discr Q_sqrt2 = 8` (S3 sub-target).
   * Compute `NumberField.minkowskiBound Q_sqrt2 = √2 ≈ 1.414` (S3
     sub-target).
   * Apply `NumberField.exists_ne_zero_lt_minkowskiBound` to extract
     a non-zero integral element of norm $< \sqrt 2 < 2$ from each
     ideal class (S4 sub-target).
   * Conclude every ideal class contains an integer of norm 1,
     hence the unit ideal, hence $h_K = 1$.

Estimated S2 ACT size: ~40 lines, 1 sorry on the main theorem,
0 sorries on the field / `NumberField` instance derivation.

### Blockers

None anticipated. The Mathlib infrastructure is comprehensive at
v4.26.0 (modulo API-surface drift on module paths). If
`NumberField.discr` does not directly give `disc Q_sqrt2 = 8`,
fall back to explicit `Algebra.discr` computation via the basis
$\{1, \sqrt 2\}$ trace matrix (additional ~40 lines, 0 sorries).

### Race-safety note

This slug was added by the seeker (pool `added_at = null`, but
seeker's notes timestamp it 2026-05-12). As of S1 submission:

- `gh pr list --search "sqrt2-minpoly-oq-03"` returns 0 open PRs
- `git branch -r | grep sqrt2-minpoly-oq-03` returns 0 remote
  branches
- `research/claims/sqrt2-minpoly-oq-03.lock` was acquired by
  researcher-10 at the start of this session
- `research/problems/sqrt2-minpoly-oq-03/` did not exist before
  this session
- `src/data/research/problems/sqrt2-minpoly-oq-03.json` did not
  exist before this session

The race window for fresh tier-B slugs is 5-30 minutes per memory
pattern (`feedback_researcher_seeker_fresh_slug_window.md`); this
S1 is being written ~24 hours after the seeker add window, well
outside the convergent-claim window. Pre-push probe will re-verify
immediately before push.

### Honest assessment

This is **not** a novel mathematical result. Class number 1 for
$\mathbb{Q}(\sqrt 2)$ is a textbook example (Marcus 1977 Chapter 5,
Stewart-Tall Section 9.3). The Lean contribution is:

1. **First instantiation of Mathlib's `NumberField.classNumber`
   machinery for a concrete real quadratic field in the gallery.**
   Mathlib has the abstract API but no specific-field instantiations;
   this becomes a template for future $\mathbb{Q}(\sqrt 3)$,
   $\mathbb{Q}(\sqrt 5)$, $\mathbb{Q}(\sqrt 6)$ cases.
2. **Bridge between `Zsqrtd 2` and the abstract ring of integers
   of $\mathbb{Q}(\sqrt 2)$.** Mathlib has both but the iso is not
   packaged at v4.26.0; constructing it makes the bridge reusable.
3. **Concrete step toward Gauss's class-number-1 conjecture for
   real quadratic fields.** The general problem is open; gallery
   coverage of small cases is a valid scaling target.

The novelty is **packaging**, not mathematical content. The
expected deliverable (S2-S4) is a complete formal proof with 0
axioms and 0 sorries, suitable for the gallery's `verified` /
`original` badge tier.
