# hilbert-14-oq-04 — Effective algorithms for finite generation of non-reductive invariant rings

**Parent**: `hilbert-14` — Hilbert's Fourteenth Problem (Finiteness of Invariant Systems)
**Tier**: B (significance 6, tractability 4)
**Status**: open
**Seeker note (2026-05-12)**: Weitzenboeck-style result or Nagata counterexample template.

## Precise statement (the open question)

Let `k` be a field of characteristic zero, `V = k^n` a finite-dimensional
representation of an algebraic group `G`, and `k[V] = k[x_1, …, x_n]` the
coordinate ring. The invariant ring is

```
  k[V]^G  =  { f ∈ k[V] | g · f = f  for all g ∈ G }.
```

For **reductive** `G` (e.g. finite groups, tori, semisimple groups, `GL_n`,
`SL_n`), Hilbert (1890) and Mumford (1965) proved `k[V]^G` is always finitely
generated as a `k`-algebra, and Derksen (1999) gave an effective algorithm
to compute a generating set.

For **non-reductive** `G`, the situation is dramatically different:

- **Weitzenboeck (1932)**: For `G = G_a` (the additive group) acting
  linearly on a polynomial ring over a field of characteristic zero, the
  invariant ring is finitely generated. The action corresponds to a single
  locally nilpotent derivation `D : k[V] → k[V]`, and `k[V]^{G_a} = ker D`.

- **Nagata (1959)**: There exist linear actions of `G_a^13` on `k^32`
  whose invariant ring is **not** finitely generated. This refuted the
  natural generalization of Hilbert's positive result.

- **Roberts (1990)**: A 7-dimensional non-finitely-generated counterexample
  with `G_a^6` acting on `k^7`, simpler than Nagata's.

- **Derksen-Kemper, Freudenburg, Daigle-Freudenburg, Kuroda, van den Essen**:
  Extensive partial results on (i) effective computation of `ker D` for a
  single locally nilpotent derivation when finite generation holds, and
  (ii) constructing new families of counterexamples.

**OQ-04 (this slug)**: *Does there exist a uniform effective algorithm that,
given an algebraic group `G`, a representation `V`, and a finite presentation
of the action, decides whether `k[V]^G` is finitely generated as a `k`-algebra,
and (when the answer is positive) outputs a finite generating set?*

A constructive answer is known to be impossible for **arbitrary** algebraic
groups (one can encode undecidable instances via wild-type unipotent groups).
The open part is the **boundary**: characterize the largest class `C` of
algebraic groups such that finite generation **and** computability of a
generating set both hold uniformly for actions on finite-dimensional
representations.

## Source / pedagogical framing

The parent gallery entry `hilbert-14` presents the **classical resolution**
(Mumford-Hilbert positive case + Nagata counterexample) as a four-part
narrative: reductive case → counterexample → modern classification
(Hochster-Roberts, Noether bound). OQ-04 zooms into the gap between cases
2 (Nagata: NO) and 4 (Modern Classification): can we draw the boundary
**algorithmically**, not just structurally?

## Why this is interesting for the gallery

1. Connects classical invariant theory (Hilbert, Weyl) to modern
   computational algebra (Derksen's algorithm, Gröbner bases).
2. Touches the boundary between decidable and undecidable algorithmic
   problems in commutative algebra.
3. Provides a natural setting for formalizing **locally nilpotent
   derivations** (LNDs), a topic with no current Mathlib coverage.
4. Adjacent to the well-known **Jacobian conjecture** (which is equivalent
   to a statement about `G_a` actions on polynomial rings).

## Relation to sibling slug `hilbert-14-oq-01`

The neighbouring open-question slug `hilbert-14-oq-01`
("Can we characterize exactly which non-reductive groups have finitely
generated invariants?") focuses on the **structural / qualitative**
characterization: *for which groups* does finite generation hold? Its
current Lean development (`proofs/Proofs/Hilbert14NonReductive.lean`,
`proofs/Proofs/Hilbert14InvariantsOQ01.lean`) covers:

- `InvariantSubset`, `ReynoldsOperator` structure, `invariantSubring`;
- `reynoldsSum : R → R` for finite `G` and its seven basic properties
  (additivity, invariance, idempotence on `R^G`, etc.);
- The **Grosshans criterion** stated as `axiom`
  (`grosshans_characterization`) plus the derived
  `finite_group_grosshans` and `reductive_subgroup_grosshans`.

OQ-04 (this slug) is **complementary and orthogonal**: its focus is the
**effective / algorithmic** refinement — given that finite generation
holds, *how do we compute generators?*, and *can we decide* finite
generation algorithmically? The two natural algorithmic anchor points,
both absent from OQ-01's development, are:

- **Noether's degree bound (1916)**: for finite `G` and `char k ∤ |G|`,
  generators of `k[V]^G` have degree `≤ |G|`. This is the quantitative
  refinement of the existence theorem, and it converts the abstract
  finiteness into an explicit enumeration-and-Reynolds-averaging
  algorithm.
- **Locally nilpotent derivations (LNDs)**: the algorithmic dual of the
  `G_a`-action picture, with its own van-den-Essen-Tan computational
  procedure for `ker D`.

This division of labour — OQ-01 for the *characterization* axis, OQ-04
for the *algorithmic* axis — keeps the two sibling slugs from
duplicating effort.

## Sub-problem decomposition

A direct Lean formalization of OQ-04 is beyond present scope — it is a
**meta-mathematical** problem about the existence of algorithms across an
infinite class of inputs, not a single theorem. The pedagogical-Lean program
must instead formalize **anchor points** in the landscape:

**Tier-1 (most tractable, S2-reachable in Mathlib)**:
- **(A) Hilbert-Noether (1916) for finite groups**: For `G` a finite group
  acting linearly on `k[V]`, the invariant ring `k[V]^G` is finitely
  generated. Provable via the Reynolds operator
  `R(f) = (1/|G|) ∑_{g ∈ G} g · f` and degree-bounded reduction. Mathlib
  has `MulAction`, `Polynomial.algebra`, but no Reynolds operator or
  Noether-bound theorem.

- **(B) Locally nilpotent derivation (LND) framework**: Define
  `IsLocallyNilpotent (D : R →+ R)` for a derivation `D`, and prove the
  basic facts: `ker D` is a subalgebra; if `D = 0` then `ker D = R`; if
  `D` is non-zero with `D x = 1` for some `x` (a "slice"), then
  `R = (ker D)[x]` (the slice theorem, a foundational tool for `G_a`
  actions).

**Tier-2 (intermediate)**:
- **(C) Weitzenboeck's theorem** (axiom-form): State as an `axiom` the
  finite generation of `ker D` for a single LND on `k[x_1, …, x_n]` over a
  characteristic-zero field. Lean proof would require the
  van-den-Essen/Tan algorithm, which is substantial.

- **(D) Slice theorem**: If `D x = 1`, then `R = (ker D)[x]` (concrete
  slice). One-page algebraic identity, Lean-provable.

**Tier-3 (counterexamples, axiom-only)**:
- **(E) Nagata's counterexample**: State as `axiom` the existence of a
  non-finitely-generated invariant ring for some `G_a^13` action.
- **(F) Roberts' 7-dim counterexample**: Similarly axiom-only.

**Tier-4 (the OQ-04 conjecture itself)**:
- **(G) Existence/non-existence of uniform algorithm**: A meta-statement
  about the family of all algebraic group actions. Not formalizable in a
  single Lean theorem without an explicit complexity-theoretic encoding.

## Recommended S2 entry point

**Noether's degree bound (1916)** is the highest-leverage S2 target for
OQ-04 specifically: it provides the *quantitative / algorithmic*
refinement of the OQ-01 finite-group finiteness result, has a
self-contained 1-page proof (orbit-product trick + integral-extension
argument), and is **not** present in the OQ-01 Lean development.

**Statement** (informal). Let `G` be a finite group acting linearly on
`V = k^n` over a field `k` with `char k ∤ |G|`. Then the invariant ring
`k[V]^G` is generated, as a `k`-algebra, by invariants of degree at most
`|G|`. (Noether 1916; for `char k ∣ |G|` the bound is `≥ |G|` and the
sharp value is known only up to `(|G|, n)`-dependent constants.)

**Proof outline** (5 steps):
1. For each `v ∈ V` and each orbit `O_v = {g v : g ∈ G}`, the orbit
   polynomial `P_v(T) = ∏_{w ∈ O_v} (T - w)` is `G`-invariant in the
   coefficient ring `k[V]^G[T]`.
2. Each `v ∈ V` is integral over `k[V]^G` of degree exactly `|O_v| ≤ |G|`
   (via `P_v(v) = 0`).
3. Hence `k[V]` is integral over the sub-`k`-algebra generated by the
   coefficients of all orbit polynomials, all of which have degree
   `≤ |G|`.
4. By the integral-extension finiteness theorem (Atiyah-Macdonald 5.1):
   if `B ⊇ A` is integral and `B` is f.g. as an `A`-algebra, then `B` is
   f.g. as an `A`-module.
5. Apply to `B = k[V]`, `A = (k[V]^G)_{≤ |G|}`-subalgebra: `B` is f.g. as
   an `A`-module and hence `A = k[V]^G` (using `A ⊆ k[V]^G ⊆ B` and the
   fact that `k[V]^G` shares the `A`-module structure on `B`).

The proof connects naturally to the OQ-01 Reynolds-operator
infrastructure: the orbit polynomials of step (1) are the building
blocks of the **elementary symmetric invariants**, which `reynoldsSum`
recovers via averaging.

This S2 ACT establishes the **algorithmic baseline** against which
OQ-04's non-reductive failure (Nagata, Roberts) — where no such
universal degree bound exists — becomes the dramatic open question.

### Alternative S2 entry point: `IsLocallyNilpotent` framework

If the Mathlib API for `MvPolynomial`-module finite generation proves
too thin for the degree-bound proof, the alternative S2 ACT is to
introduce `IsLocallyNilpotent` for derivations, establish `ker D` as a
`k`-subalgebra, and state the **slice theorem** as a Lean lemma. This
opens the door to a tier-3 axiom statement of Weitzenboeck's theorem,
which would be the natural mid-iteration pivot once Reynolds-side
groundwork is mature.

## Mathlib API gap inventory

| Concept                                  | Mathlib status | Gap                                 |
|------------------------------------------|----------------|-------------------------------------|
| `MulAction G R` with `R` ring            | ✅ present      | —                                   |
| `Polynomial.algebra` action by aut. group | ⚠️ partial     | No `MvPolynomial`-level action API  |
| `Subalgebra` finite-generation `Algebra.FG` | ✅ present  | —                                   |
| Reynolds operator (char-0, finite `G`)   | ❌ absent       | Must define + prove averaging facts |
| Noether degree bound (`deg ≤ |G|`)       | ❌ absent       | Must define + prove                 |
| Locally nilpotent derivation             | ❌ absent       | Must define `IsLocallyNilpotent`    |
| Hilbert-Noether finiteness               | ❌ absent       | The S2 target                       |
| Weitzenboeck finiteness for `G_a`        | ❌ absent       | Tier-2 axiom                        |
| Nagata counterexample                    | ❌ absent       | Tier-3 axiom                        |

## Open questions for future iterations

1. After S2 ACT (Hilbert-Noether), can we formalize the **Reynolds-operator
   exactness sequence** to expose the reductive-vs-non-reductive boundary?
2. Is there a Lean-tractable special case of Weitzenboeck's theorem (e.g.
   `G_a` on `k[x, y]` via `D = ∂/∂y`, giving `ker D = k[x]`) that we can
   prove from scratch as a tier-2 anchor?
3. Can we state the **Hilbert-Mumford criterion** for reductive
   semistability in a Mathlib-compatible way, even if we cannot yet prove
   it?

## References

- Hilbert, D. (1890). "Ueber die Theorie der algebraischen Formen."
  *Math. Ann.* 36, 473–534. (Finiteness for `SL_n` invariants.)
- Hilbert, D. (1893). "Ueber die vollen Invariantensysteme."
  *Math. Ann.* 42, 313–373. (Second proof, more constructive.)
- Noether, E. (1916). "Der Endlichkeitssatz der Invarianten endlicher
  Gruppen." *Math. Ann.* 77, 89–92. (Finiteness for finite groups, degree
  bound `|G|`.)
- Weitzenboeck, R. (1932). "Über die Invarianten von linearen Gruppen."
  *Acta Math.* 58, 230–250. (Finiteness for `G_a`.)
- Nagata, M. (1959). "On the 14th problem of Hilbert." *Amer. J. Math.*
  81(3), 766–772. (Counterexample.)
- Mumford, D. (1965). *Geometric Invariant Theory.* Springer. (Finiteness
  for reductive groups.)
- Haboush, W. J. (1975). "Reductive groups are geometrically reductive."
  *Ann. of Math.* 102, 67–83. (Extension to positive characteristic.)
- Roberts, P. (1990). "An infinitely generated symbolic blow-up in a power
  series ring and a new counterexample to Hilbert's fourteenth problem."
  *J. Algebra* 132, 461–473. (Dimension 7 counterexample.)
- Derksen, H. (1999). "Computation of invariants for reductive groups."
  *Adv. Math.* 141, 366–384. (Algorithm for reductive case.)
- van den Essen, A. (2000). *Polynomial Automorphisms and the Jacobian
  Conjecture.* Birkhäuser. (LND algorithms, ch. 1–2.)
- Freudenburg, G. (2006/2017). *Algebraic Theory of Locally Nilpotent
  Derivations.* Springer EMS. (Comprehensive LND reference.)
- Kuroda, S. (2003). "A condition for finite generation of the kernel of a
  derivation." *J. Algebra* 262, 391–407. (Refined finiteness criteria.)
