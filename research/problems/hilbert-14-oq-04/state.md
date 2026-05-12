# Current State

**Phase**: OBSERVE (S1 closed — Mathlib-gap audit + shortlist of Lean-formalizable adjacent targets)
**Since**: 2026-05-12T19:30:00Z
**Iteration**: 1

## Current Focus

S1 OBSERVE — **Algorithmic landscape for non-reductive invariant theory
surveyed**. OQ-04 (effective algorithms for finite generation of
non-reductive invariant rings) is a meta-mathematical conjecture about
the existence of uniform algorithms; it cannot be formalized as a single
Lean theorem. Identified the tractable adjacent target hierarchy and
selected the S2 entry point.

## Active Approach

**S2 target: Noether's degree bound (1916) — algorithmic refinement.**

For a finite group `G` acting linearly on `k[V] = k[x_1, …, x_n]` over a
field `k` with `char k ∤ |G|`, the invariant ring `k[V]^G` is generated,
as a `k`-algebra, by invariants of **degree at most `|G|`**. Noether's
bound is the *quantitative* refinement of the OQ-01-side qualitative
finiteness statement; it converts the existence theorem into an explicit
algorithm (enumerate monomials of degree `≤ |G|`, apply Reynolds, perform
Gauss elimination).

Crucially, the sibling slug `hilbert-14-oq-01` already provides the
**structural** infrastructure (`InvariantSubset`, `ReynoldsOperator`,
`invariantSubring`, `reynoldsSum` plus seven basic properties) but has
**no degree-bound machinery**. OQ-04's S2 ACT therefore picks up where
OQ-01 leaves off, with no duplication.

**Proof outline (5 steps)**:
1. For each `v ∈ V`, the orbit polynomial
   `P_v(T) = ∏_{w ∈ Orbit(v)} (T - w)` is `G`-invariant; its coefficients
   live in `k[V]^G` and have degree `≤ |G|`.
2. Each `v ∈ V` is integral over `k[V]^G` of degree `|Orbit(v)| ≤ |G|`.
3. Hence `k[V]` is integral over the subalgebra
   `S := k[ \text{orbit-polynomial coefficients} ] ⊆ k[V]^G_{≤ |G|}`.
4. Atiyah-Macdonald 5.1 (integral + finitely-generated-as-algebra ⇒
   finitely-generated-as-module): `k[V]` is f.g. as an `S`-module.
5. Hence `k[V]^G` is sandwiched between `S` and `k[V]`, and Noetherian
   intersection arguments give `S ⊆ k[V]^G` is the full degree-bounded
   generator set.

## Blockers

None firm. The Mathlib prerequisites for the degree-bound proof are:
- `IsIntegral` / `Algebra.IsIntegral` (present);
- `Polynomial` and root-product factorizations (`Polynomial.prod_X_sub`,
  present);
- `Algebra.adjoin` (present);
- `Subalgebra.FG ↔ Algebra.FiniteType` (present in
  `Mathlib.RingTheory.FiniteType`).

The deeper non-reductive program (Weitzenboeck, LND theory, Nagata's
counterexample) is *bounded by Mathlib's absence of any locally
nilpotent derivation framework*. Deferred to S5+ once
`IsLocallyNilpotent` is introduced.

## Next Action

**S2 ACT**: Scaffold `proofs/Proofs/Hilbert14OQ04.lean` with:

1. **Setup**:
   ```lean
   variable {k : Type*} [Field k] {n : ℕ} {G : Type*}
     [Group G] [Fintype G] [MulAction G (MvPolynomial (Fin n) k)]
     [Invertible (Fintype.card G : k)]
   ```

2. **Orbit-polynomial definition** (the algorithmic primitive):
   ```lean
   noncomputable def orbitPolynomial (v : MvPolynomial (Fin n) k) :
       Polynomial (MvPolynomial (Fin n) k) :=
     ∏ g : G, (Polynomial.X - Polynomial.C (g • v))
   ```

3. **Key lemmas** (scaffolded):
   - `orbit_polynomial_invariant`: each coefficient of `orbitPolynomial v`
     lies in `MulAction.fixedPoints G (MvPolynomial (Fin n) k)`.
   - `orbit_polynomial_degree`: `(orbitPolynomial v).natDegree ≤ |G|`.
   - `vanishes_at_v`: `(orbitPolynomial v).eval v = 0`, so `v` is
     integral over `k[V]^G` of degree `≤ |G|`.

4. **Main theorem (statement, sorried)**:
   ```lean
   theorem noether_degree_bound :
       (MulAction.fixedPoints G (MvPolynomial (Fin n) k) :
           Subalgebra k (MvPolynomial (Fin n) k)) =
       Algebra.adjoin k
         { f : MulAction.fixedPoints G (MvPolynomial (Fin n) k) |
           (f : MvPolynomial (Fin n) k).totalDegree ≤ Fintype.card G }
     := sorry
   ```
   (The discharge of this `sorry` is the deeper S3 ACT step.)

5. **Cross-reference**: Re-export OQ-01's `reynoldsSum` and
   `InvariantSubset` via Lean `open Hilbert14.NonReductive` for use in
   the S2 file. (No duplicate definitions.)

6. **Gallery entry**: `src/data/research/problems/hilbert-14-oq-04.json`
   describing the algorithmic refinement, citing the parent `hilbert-14`
   and sibling `hilbert-14-oq-01`.

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE).
- Current approach attempts: 1.
- Approaches tried:
  - S1: classical-resolution survey, Mathlib-gap audit, shortlist of
    Lean-formalizable adjacent targets.

## Key Files

- `research/problems/hilbert-14-oq-04/problem.md` — **created in S1**
  (problem statement, sub-problem decomposition, decision: S2 target =
  Hilbert-Noether for finite groups).
- `research/problems/hilbert-14-oq-04/knowledge.md` — **created in S1**
  (algorithmic landscape, Reynolds operator background, LND background,
  counterexamples, Mathlib API gap inventory).
- `research/problems/hilbert-14-oq-04/state.md` — **this file**.
- `src/data/research/problems/hilbert-14-oq-04.json` — **created in S1**
  (gallery entry for the open question).
- `proofs/Proofs/Hilbert14OQ04.lean` — **planned for S2**.
- `src/data/proofs/hilbert-14/meta.json` — parent gallery entry; not
  modified in S1.

## Pedagogical anchor: parent gallery entry's openQuestions

The parent `hilbert-14/meta.json` lists three open questions in its
`openQuestions` field:
1. "Can we characterize exactly which non-reductive groups have finitely
   generated invariants?"
2. "What is the optimal bound on degrees of generators for reductive
   groups?"
3. "Are there effective algorithms to decide finite generation for
   specific non-reductive groups?"

OQ-04 = the *algorithmic* version of #1 ∩ #3. The S2 ACT positive-result
baseline (Hilbert-Noether) gives us the affirmative answer in the
finite-group case (the simplest reductive setting), against which both
the optimal-bound question (#2: Noether 1916: `≤ |G|`) and the
non-reductive failure questions (#1, #3) acquire force.

## Tactic A (S2 target): Reynolds-operator scaffold

A scaffold of the Reynolds operator + statement of Hilbert-Noether
finiteness. Discharge of the Noether-bound proof of finiteness deferred
to S3.

## Tactic B (followup S3-S5): Noether bound + degree-stable algorithm

After S2 ACT lands the Reynolds operator and the finiteness statement,
S3 ACT proves the **Noether degree bound**:
`generators(k[V]^G) ⊆ k[V]^G_{≤ |G|}` — every minimal generating set of
the invariant ring lies in degrees bounded by `|G|`. This makes the
algorithm explicit: enumerate monomials up to degree `|G|`, average each
via Reynolds, perform Gauss elimination.

## Tactic C (much later, possibly out of scope): LND framework + Weitzenboeck

S5+ would introduce `IsLocallyNilpotent` and the slice theorem,
formalizing the simplest case of Weitzenboeck (`G_a` on `k[x, y]` via
`D = ∂/∂y`) and stating the general Weitzenboeck theorem as an axiom
pending the van-den-Essen algorithm.

## Tactic D (out of scope for Lean): Nagata's counterexample

Axiom-only statement for pedagogical completeness; full Lean proof is
many thousands of lines (would require formalizing Nagata's symbolic
blow-up of a smooth surface).

## Build status (S1)

S1 deliverable is **documentation-only**: four files (`problem.md`,
`knowledge.md`, `state.md`, `src/data/research/problems/hilbert-14-oq-04.json`).
No Lean changes. Per the seeker-fresh-slug S1 OBSERVE precedent (e.g.
`cube-root-3-irrational-oq-04` PR #17718, `birthday-problem-oq-01-oq-02`
PR #17735), this is the conventional S1 ACT-deferred deliverable.

Build verification not applicable.
