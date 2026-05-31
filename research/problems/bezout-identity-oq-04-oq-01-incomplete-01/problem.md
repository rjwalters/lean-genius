# Problem: Constructive Discharge of `snf_exists` in `BezoutIdentityOQ04OQ01.lean`

**Slug**: `bezout-identity-oq-04-oq-01-incomplete-01`
**Created**: 2026-04-03 (scaffold); **S2 ORIENT rewrite**: 2026-05-31 (researcher-1)
**Status**: Active — ORIENT phase
**Source**: gallery-gap (axiom in parent `Proofs/BezoutIdentityOQ04OQ01.lean`)

## Lineage recovery (S2 ORIENT, 2026-05-31)

The slug was originally created on 2026-04-03 as a scaffold with placeholder
text (`"[Explain what we're trying to prove in accessible terms]"`,
`"[LaTeX formulation of the theorem/conjecture]"`). The originating
problem statement was never recorded; both the local `problem.md` and the
slug JSON record this as a known blocker. The slug name's `incomplete-01`
suffix and the parent gallery entry's two declared axioms together pin
down the intended scope: **discharge the existence axiom of Smith
Normal Form** declared at
`proofs/Proofs/BezoutIdentityOQ04OQ01.lean:146`.

This S2 ORIENT rewrites `problem.md` (this file), `knowledge.md`, and the
slug JSON to record the recovered statement; no `*.lean` files are modified.

## Problem Statement

### Formal Statement

In `proofs/Proofs/BezoutIdentityOQ04OQ01.lean` at line 146, the parent
gallery axiomatises Smith Normal Form existence:

```lean
axiom snf_exists (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ snf : SmithNormalForm m n, snf.isDecompOf A
```

where `SmithNormalForm m n` is the structure declared at line 103 with
fields `U, D, V` plus invariant-factor divisibility chain, and
`isDecompOf snf A` is the proposition `A = snf.U * snf.D * snf.V`
(line 122).

**Goal**: replace the axiom with a `theorem snf_exists … := by …` that
constructs a Smith Normal Form for every integer matrix, using only
Mathlib and the parent file's existing infrastructure (`IsUnimodular`,
`isUnimodular_one`, `IsUnimodular.mul`, `IsUnimodular.transpose`,
`isUnimodular_iff_abs_det`).

### Plain Language

Every integer matrix `A` admits a decomposition `A = U · D · V` where
`U` and `V` have integer entries and determinant `±1` (unimodular) and
`D` is "diagonal with divisibility chain" — i.e., off-diagonal entries
are zero and consecutive diagonal entries divide one another. The
parent file currently *asserts* this without proof; we want to *prove*
it constructively in Lean 4.

The standard algorithmic proof (folklore / Smith 1861 / textbook):

1. Find the matrix entry of smallest nonzero absolute value.
2. Row/column-swap it to position `(0,0)`.
3. Use the Euclidean algorithm on row 0 and column 0 to reduce all other
   entries in row 0 and column 0 modulo `D[0,0]`.
4. If any entry in the `(1..,1..)` submatrix is not divisible by
   `D[0,0]`, add that row to row 0 (which introduces a non-multiple)
   and restart from step 1.
5. Recurse on the `(1..,1..)` submatrix.

Termination: the absolute value of `D[0,0]` strictly decreases each time
step 4 triggers, and `ℕ` is well-ordered.

### Why This Matters

1. **Discharges an axiom** in the verified-with-axioms gallery entry
   `bezout-identity-oq-04-oq-01` (`Linear Diophantine Systems via Smith
   Normal Form`, badge `axiom`, status `axiomatized`). Per the project's
   axiom-integrity policy, a successful discharge changes the parent's
   status from `axiomatized` to `verified` (or, if `snf_solvability_criterion`
   is also axiomatised, brings the parent halfway to `verified`).
2. **No Mathlib SNF** (as of v4.26.0, lake-manifest pin `2df2f015…`):
   Mathlib has `Matrix.IsDiag`, `Matrix.det_one`, `Matrix.det_mul`,
   `Int.gcd_eq_gcd_ab`, and unimodular-related infrastructure, but **no
   `Matrix.SmithNormalForm` or top-level `snf_exists` theorem**. A
   successful constructive proof is therefore an upstream Mathlib
   contribution candidate as well.
3. **Unlocks downstream solvability**: once `snf_exists` is a theorem,
   the companion axiom `snf_solvability_criterion` (line 196) becomes
   the natural next target — together they form the foundation of the
   `bezout-identity-oq-04-oq-01` gallery entry. Discharging both would
   convert the entry from `axiom`-badged to `verified`.

## Known Results

### What's Already Proven (parent file infrastructure)

* `IsUnimodular`, `IsUnimodular.mul`, `IsUnimodular.transpose`,
  `IsUnimodular.det_ne_zero`, `isUnimodular_iff_abs_det`,
  `isUnimodular_one` — lines 49–90.
* `SmithNormalForm` structure — lines 103–120.
* `SmithNormalForm.isDecompOf` — line 122.
* **`snf_exists_zero`** — lines 153–167 (the zero matrix case, fully
  constructive, ~14 LOC; the only non-axiomatic existence case in the
  parent file).
* `SmithNormalForm.invariantFactor`, `SmithNormalForm.rank` — lines
  173–183.
* `bezout_from_snf` (classical 1×2 reduction to gcd) — discharged
  from `snf_exists` + Mathlib's `Int.gcd_eq_gcd_ab`.

### What's Still Open (this slug)

1. **`snf_exists`** for general `(m, n)` matrices — the main goal.
2. **`snf_solvability_criterion`** — out of scope for this slug; track
   as a follow-on (sibling slug `bezout-identity-oq-04-oq-01-incomplete-02`
   if needed).

### Our Goal

Discharge `axiom snf_exists` (line 146 of
`proofs/Proofs/BezoutIdentityOQ04OQ01.lean`) with a constructive proof.
Estimated LOC budget per the parent file's own docstring: **~500 lines**
for a full Euclidean-algorithm reduction. This breaks naturally into:

* Elementary row/column operations as unimodular matrices (~100 LOC).
* `Matrix.swap_rows`, `Matrix.swap_cols`, `Matrix.add_row`,
  `Matrix.add_col` (~50 LOC each; some may exist in Mathlib).
* The reduction algorithm + termination on `Σ |entries|` or
  `lex (min nonzero abs, # nonzero entries)` (~150 LOC).
* Divisibility-chain invariant maintenance (~100 LOC).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `bezout-identity-oq-04-oq-01` (`BezoutIdentityOQ04OQ01.lean`) | direct parent — axiom lives here | unimodular matrices, SNF structure |
| `bezout-identity` (root, `Proofs/BezoutIdentity.lean`) | classical scalar Bezout — base case `(m,n) = (1,2)` | `Int.gcd_eq_gcd_ab`, `Mathlib.RingTheory.Coprime.Basic` |
| `bezout-identity-oq-04-oq-01-oq-01` (sibling, OBSERVE phase) | "Smith Normal Form gcd characterization for PIDs via Mathlib" — likely complementary | generalisation of SNF to PIDs |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Constructive Euclidean reduction in Lean 4** (~500 LOC)
   - Why it might work: standard algorithmic proof; well-documented in
     every algebra textbook (Lang *Algebra*, Jacobson *Basic Algebra I*,
     Newman *Integral Matrices*); the algorithm is decidable and
     terminating.
   - Risk: Mathlib has limited elementary-row-operation API for ℤ
     matrices; substantial scaffolding required. LOC budget may need
     to grow.

2. **Approach B — Lift from Mathlib's PID structure theorem** (~150-200 LOC)
   - Why it might work: Mathlib has `Module.equiv_directSum_of_pid`
     and related results for finitely-generated modules over a PID.
     Smith Normal Form is the matrix shadow of this; ℤ is a PID. A
     Mathlib-bridge approach could compress the proof significantly.
   - Risk: bridging from `Submodule.IsPrincipal`-style results back to
     `Matrix (Fin m) (Fin n) ℤ` may require non-trivial unfolding;
     constructive vs classical witnesses may diverge.

3. **Approach C — Defer to upstream Mathlib SNF** (potential ~50 LOC bridge)
   - Why it might work: there are draft Mathlib PRs for SNF (track at
     `leanprover-community/mathlib4` search "Smith Normal Form"). If
     one merges, this slug becomes a bridge.
   - Risk: pure dependency; only viable if an upstream version exists
     at the lake-manifest pin `2df2f015…`. Per the parent file's
     `mathlibDependencies` (no `SmithNormalForm` listed), no such
     upstream version exists today at v4.26.0.

**Recommended**: Approach B first (smaller LOC budget, leverages Mathlib's
PID infrastructure); fall back to Approach A if B's framework bridge
proves intractable.

### Key Difficulties

* **Algorithm complexity**: the Euclidean reduction maintains multiple
  invariants (divisibility chain, unimodularity of accumulated U/V,
  zero off-diagonal); tracking these through Lean's term-level machinery
  is error-prone.
* **Termination measure**: the "smallest nonzero entry strictly
  decreases" measure works, but Lean 4's `termination_by` requires
  carefully chosen `WellFoundedRelation` instances. A
  `Σ |entries|` measure may be cleaner.
* **No direct Mathlib SNF**: the proof is genuinely new content in
  Lean 4 (Mathlib v4.26.0); no off-the-shelf API.

### What Would a Proof Need?

* **Elementary-row-operation infrastructure** for ℤ matrices, packaged
  as unimodular-matrix-left-multiplication (and column ops as
  right-multiplication).
* **Single-step reduction lemma**: given a non-SNF matrix `A`, produce
  a "smaller" matrix `A'` and unimodular `U, V` with `A' = U·A·V`.
* **Termination lemma**: each non-trivial reduction strictly decreases
  the chosen measure.
* **Recursive composition**: the iterated reduction produces a SNF.

## Tractability Assessment

**Difficulty**: High (substantial Lean 4 development; comparable in
scope to the `szemeredi-core-oq-04` Part 8 cascade, ~190 LOC).

**Justification**:
- Standard classical proof, no mathematical novelty (Smith 1861 +
  textbook).
- Lean 4 development is the cost; Mathlib lacks SNF API.
- Comparable in spirit to other axiom-discharge projects in the gallery
  (e.g., `cantor-bendixson-axiom-discharge` style), but heavier on
  matrix-algebra plumbing.

**Estimated Effort**:
- S2 ORIENT (this iteration): **0 LOC Lean** — recover problem statement,
  survey Mathlib, pick approach. Doc-only.
- S3 PREP: ~50 LOC scaffold — declare `SmithNormalForm_exists` as
  `theorem … := by sorry`, identify Mathlib bearer cluster.
- S4 ACT iterations: 5–10 ACT cycles, ~50–80 LOC per cycle, totalling
  ~500 LOC for Approach A or ~200 LOC for Approach B.
- Upstream Mathlib contribution (optional): ~+50 LOC for the bridge
  to `Matrix.SmithNormalForm` once approach lands.

## References

### Papers / Books
- Smith, H.J.S. (1861). "On systems of linear indeterminate equations
  and congruences." *Philosophical Transactions of the Royal Society of
  London*, 151, 293–326. — original SNF.
- Jacobson, N. (1985). *Basic Algebra I*, 2nd ed., chapter 3 (Smith
  Normal Form).
- Newman, M. (1972). *Integral Matrices*, chapter 2 (constructive
  reduction algorithm). — recommended algorithmic reference.
- Lang, S. (2002). *Algebra*, revised 3rd ed., chapter III §7. —
  Mathlib-style structure-theorem viewpoint.

### Online Resources
- Wikipedia: "Smith normal form"
  (https://en.wikipedia.org/wiki/Smith_normal_form) — concise statement
  + algorithm.
- nLab: "Smith normal form" — categorical viewpoint, mostly for
  Approach B framing.

### Mathlib (v4.26.0 / lake-manifest pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
- `Mathlib.Data.Matrix.Basic` — matrix scaffold.
- `Mathlib.LinearAlgebra.Matrix.Diagonal` — diagonal predicates.
- `Mathlib.LinearAlgebra.Matrix.IsDiag` — `Matrix.IsDiag`.
- `Mathlib.Data.Int.GCD` — `Int.gcd_eq_gcd_ab` (1×2 base case).
- `Mathlib.RingTheory.Coprime.Basic` — coprime infrastructure.
- **Missing**: `Matrix.SmithNormalForm`, `Matrix.snf_exists`,
  `Matrix.invariantFactors` — confirmed via parent file's
  `mathlibDependencies` list (no `SmithNormalForm` entry) and absence
  of a direct API at v4.26.0.

## Metadata

```yaml
tags:
  - number-theory
  - linear-algebra
  - smith-normal-form
  - axiom-discharge
  - constructive
related_proofs:
  - bezout-identity-oq-04-oq-01
  - bezout-identity
  - bezout-identity-oq-04-oq-01-oq-01
difficulty: high
source: gallery-gap
created: 2026-04-03T01:04:41-07:00
recovered: 2026-05-31 (S2 ORIENT, researcher-1)
```

**Significance**: 6/10 (closes a real axiom; not a millennium-class result).
**Tractability**: 4/10 (heavy Lean 4 plumbing, no Mathlib SNF API).

(Note: the original scaffold listed both at 6/10. This S2 ORIENT
re-calibrates tractability down to 4/10 reflecting the absence of a
Mathlib SNF and the ~500 LOC budget.)
