# Problem: Orbit–Stabilizer Without Finiteness — The Bijection and its Cardinal Corollary

**Slug**: lagrange-theorem-oq-02-oq-03
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $G$ be an *arbitrary* group (no finiteness hypothesis) acting on a set $X$,
and fix $x \in X$. The orbit–stabilizer correspondence is the natural bijection

$$
\operatorname{Orb}_G(x) \;\simeq\; G \,/\, \operatorname{Stab}_G(x),
\qquad
g \cdot x \;\longmapsto\; g\,\operatorname{Stab}_G(x),
$$

between the orbit of $x$ and the *left coset space* of the stabilizer. This map
is a well-defined bijection with **no** cardinality assumption on $G$, $X$, or the
orbit: $g_1 \cdot x = g_2 \cdot x \iff g_1^{-1} g_2 \in \operatorname{Stab}_G(x)
\iff g_1 \operatorname{Stab}_G(x) = g_2 \operatorname{Stab}_G(x)$.

Taking cardinalities of both sides yields the *infinite-general* cardinal identity

$$
\#\,\operatorname{Orb}_G(x)
   \;=\;
   \#\bigl(G / \operatorname{Stab}_G(x)\bigr)
   \;=\;
   [\,G : \operatorname{Stab}_G(x)\,]
$$

as `Cardinal.mk`, where the index $[G : H]$ is read as the cardinal $\#(G/H)$.
Restricting to a finite group recovers the multiplicative form
$\#\operatorname{Orb}_G(x)\cdot\#\operatorname{Stab}_G(x) = \#G$ as natural
numbers.

A concrete target theorem signature (Lean 4 / Mathlib):

```lean
/-- Orbit–stabilizer bijection, no finiteness hypothesis. -/
theorem orbit_equiv_quotient_stabilizer_general
    {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
    MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

/-- Cardinal orbit–stabilizer: `#(orbit) = #(G ⧸ Stab)` as cardinals,
    for an arbitrary (possibly infinite) group. -/
theorem mk_orbit_eq_mk_quotient_stabilizer_general
    {G : Type*} [Group G] {X : Type*} [MulAction G X] (x : X) :
    Cardinal.mk (MulAction.orbit G x)
      = Cardinal.mk (G ⧸ MulAction.stabilizer G x) :=
  Cardinal.mk_congr (MulAction.orbitEquivQuotientStabilizer G x)

/-- Finite specialization: the product form as natural numbers,
    needing only local finiteness of the stabilizer. -/
theorem card_orbit_mul_card_stabilizer_general
    {G : Type*} [Group G] [Finite G] {X : Type*} [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x)
      = Nat.card G := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x), mul_comm]
  exact Subgroup.card_mul_index (MulAction.stabilizer G x)
```

### Plain Language

The orbit–stabilizer theorem is usually stated for *finite* groups:
"orbit size times stabilizer size equals group order." But the *reason* it is
true has nothing to do with finiteness — it is a genuine one-to-one
correspondence between the points you can reach from $x$ (the orbit) and the
cosets of the subgroup that pins $x$ in place (the stabilizer). The parent
gallery entry proved the finite version. This child asks: state and package the
correspondence itself, valid for *any* group — infinite groups included — and
then read off the size statement as an equation of **cardinals**, so that
"orbit size $=$ stabilizer index" makes sense even when everything in sight is
infinite. The finite product formula then drops out as a corollary.

### Why This Matters

The finite orbit–stabilizer theorem is the workhorse of finite group theory, but
its structural core — the bijection $\operatorname{Orb}(x) \simeq G/\operatorname{Stab}(x)$ —
is a statement about *arbitrary* group actions and is exactly how Mathlib already
packages it. Making the infinite-general statement explicit in the gallery does
three things: (1) it separates the *bijective content* (finiteness-free) from the
*arithmetic content* (a corollary needing only local finiteness), which is the
honest conceptual decomposition; (2) it exhibits the correct home for the size
statement in the infinite case — the cardinal $\#(G/\operatorname{Stab})$, i.e.
the subgroup *index* as a cardinal — rather than a natural-number product; and
(3) it directly answers the parent's own open question about extending
orbit–stabilizer beyond finite groups. This is the same move that upgrades
Lagrange's theorem from "$|H|$ divides $|G|$" to "$|G| = |H|\cdot[G:H]$ as
cardinals," and it is the natural launching point for infinite-index arguments
(e.g. finitely generated groups acting on trees, transitive actions on infinite
sets).

## Known Results

### What's Already Proven

- **Orbit–Stabilizer for finite groups** ($\#\operatorname{Orb}(x)\cdot\#\operatorname{Stab}(x)=\#G$,
  plus divisibility, Lagrange recovery, $p$-group corollaries; $0$ axioms,
  $0$ sorries) — parent gallery entry `lagrange-theorem-oq-02`.
- **Lagrange's theorem** — grandparent gallery entry `lagrange-theorem`:
  $\#H \mid \#G$ for a subgroup $H$ of a finite group.
- **The orbit–stabilizer bijection is already fully general in Mathlib.**
  `MulAction.orbitEquivQuotientStabilizer G x : orbit G x ≃ G ⧸ stabilizer G x`
  carries *no* finiteness typeclass — it is the honest infinite-general
  equivalence. The genuine content of this child is *exposing* it without
  finiteness and deriving the cardinal corollary, not re-deriving the map.
- **Index as a cardinal / product formula.** Mathlib's `Subgroup.index` and the
  relations `Subgroup.card_mul_index`, `Subgroup.index_eq_card`, together with
  `Cardinal.mk_congr` and `Nat.card_congr`, connect the equivalence to both the
  cardinal and the finite natural-number statements.

### What's Still Open

- No gallery entry states the orbit–stabilizer *bijection* and its *cardinal*
  corollary in full generality (no `Fintype`/`Finite` on $G$ or $X$).
- The clean packaging "$\#\operatorname{Orb}(x) = [G:\operatorname{Stab}(x)]$
  as `Cardinal.mk`" — the infinite-general size statement — is not presented,
  even though every ingredient exists in Mathlib.
- The precise *minimal* finiteness hypotheses for the natural-number product form
  (`Finite (stabilizer G x)` combined with `Finite (orbit G x)`, versus the usual
  blanket `Finite G`) deserve to be stated and separated cleanly.

### Our Goal

Present, in a self-contained verified file, the finiteness-free backbone:

1. The bijection $\operatorname{Orb}_G(x) \simeq G/\operatorname{Stab}_G(x)$ for
   an arbitrary group $G$ acting on an arbitrary set $X$ (restating
   `MulAction.orbitEquivQuotientStabilizer`).
2. The cardinal identity $\#\operatorname{Orb}_G(x) = \#(G/\operatorname{Stab}_G(x))
   = [G:\operatorname{Stab}_G(x)]$ via `Cardinal.mk_congr`, with the index read as
   a cardinal.
3. The finite-group corollary $\#\operatorname{Orb}(x)\cdot\#\operatorname{Stab}(x)=\#G$
   recovered from (1) under a finiteness hypothesis, so the parent's headline
   theorem becomes a *special case*.
4. Structural corollaries that survive to the infinite setting: transitive
   actions give $\operatorname{Orb}(x) = X$ hence $\#X = \#(G/\operatorname{Stab}(x))$;
   a free/faithful transitive (regular) action gives $\#X = \#G$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lagrange-theorem-oq-02 | Direct parent: the finite orbit–stabilizer theorem this generalizes; its headline becomes our finite corollary | `MulAction.orbitEquivQuotientStabilizer`, `Subgroup.card_mul_index`, `Nat.card_congr` |
| lagrange-theorem | Grandparent: $\#H \mid \#G$; the transitive $G$-action on $G/H$ is the model example, now stated as cardinals | Coset partition, index formula |
| lagrange-theorem-oq-03 | Sibling: Hall/converse-flavored subgroup existence; shares the coset/index machinery | `Subgroup.index`, coset spaces |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Restate the Mathlib equivalence, then push through cardinals (recommended).**
   The map is `MulAction.orbitEquivQuotientStabilizer G x`, which is already
   finiteness-free. Apply `Cardinal.mk_congr` to obtain
   $\#\operatorname{Orb}(x) = \#(G/\operatorname{Stab}(x))$. Identify the RHS with
   the index either definitionally (Mathlib's `Subgroup.index H` is
   `Nat.card (G ⧸ H)`; for the cardinal version use `Cardinal.mk (G ⧸ H)` directly,
   or a lemma of the form bridging index and coset cardinality). For the finite
   corollary, feed the equivalence to `Nat.card_congr` and combine with
   `Subgroup.card_mul_index`.
   - Why it works: it is the exact architecture of the verified parent with the
     `[Fintype G] [Fintype X]` instances *removed* from the bijection and confined
     to the corollary; a near-mechanical, low-risk port.
   - Risk: minimal. The only care needed is choosing the honest home for the index
     in the infinite case (`Cardinal.mk (G ⧸ H)` vs. the `Nat`-valued
     `Subgroup.index`, which is `0` when the coset space is infinite).

2. **Approach B — Work directly with `Cardinal.mk` and cardinal coset decomposition.**
   Build the cardinal statement from the ground up: $\#(G/H) \cdot \#H = \#G$ as a
   cardinal product (the cardinal Lagrange, of the form
   `Cardinal.mk_eq_mk_mul …` for the coset partition), then substitute
   $H = \operatorname{Stab}(x)$ and $\#(G/H) = \#\operatorname{Orb}(x)$.
   - Why it might help: gives the fully infinite multiplicative identity
     $\#\operatorname{Orb}(x)\cdot\#\operatorname{Stab}(x) = \#G$ as cardinals,
     stronger than the `Nat` corollary.
   - Risk: cardinal multiplication lemmas for coset decompositions may need to be
     assembled by hand; more moving parts than Approach A, though still
     finiteness-free.

### Key Difficulties

- **Where does the index live in the infinite case?** `Subgroup.index` is
  `Nat`-valued and *collapses to `0`* for infinite coset spaces, so the honest
  infinite statement must use `Cardinal.mk (G ⧸ stabilizer G x)` (or a cardinal
  index), not `Subgroup.index`. Stating the corollary with the right object is the
  main conceptual choice.
- **Separating hypotheses cleanly.** The bijection needs nothing; the `Nat` product
  needs finiteness. Exposing the *minimal* hypothesis for the product corollary
  (finiteness of the coset space / stabilizer via `Subgroup.card_mul_index`, rather
  than a blanket `Fintype G`) is a small but worthwhile piece of hygiene.
- **Honesty about novelty.** The core equivalence is a one-line wrapper around an
  existing Mathlib lemma; the *value added* is the finiteness-free framing, the
  cardinal corollary, and the clean exhibition of the parent's theorem as a special
  case. The file should say so plainly.

### What Would a Proof Need?

- Key lemma 1: the equivalence `orbit G x ≃ G ⧸ stabilizer G x` with no finiteness
  instances (restate `MulAction.orbitEquivQuotientStabilizer`).
- Key lemma 2: `Cardinal.mk (orbit G x) = Cardinal.mk (G ⧸ stabilizer G x)` via
  `Cardinal.mk_congr` applied to Key lemma 1.
- Key lemma 3: finite corollary
  `Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G` via
  `Nat.card_congr` + `Subgroup.card_mul_index`, under a finiteness hypothesis.
- Key lemma 4 (structural): transitive action $\Rightarrow$ `orbit G x = Set.univ`
  (`MulAction.orbit_eq_univ`) hence $\#X = \#(G/\operatorname{Stab}(x))$; regular
  action $\Rightarrow \#X = \#G$.
- Technical requirements: `MulAction.orbitEquivQuotientStabilizer`,
  `Cardinal.mk_congr`, `Nat.card_congr`, `Subgroup.card_mul_index`,
  `Subgroup.index_eq_card`, and the `Subgroup.index` / `Cardinal.mk` bridging — all
  present in current Mathlib.

## Tractability Assessment

**Difficulty**: Low–Medium (High tractability)

**Justification**:
- The **bijection is already infinite-general in Mathlib**
  (`MulAction.orbitEquivQuotientStabilizer` carries no finiteness typeclass), so
  Key lemma 1 is a one-line restatement and Key lemma 2 is a single
  `Cardinal.mk_congr`. This is very likely to close with $0$ axioms.
- The **finite corollary is a verbatim port of the parent's headline theorem**
  (`Nat.card_congr` + `Subgroup.card_mul_index`), already known to compile in
  `lagrange-theorem-oq-02`.
- The only genuine design decision is the **honest home for the index in the
  infinite case** (`Cardinal.mk (G ⧸ H)` vs. the `Nat`-collapsing
  `Subgroup.index`), which is a framing choice, not a proof obstacle.
- Techniques available in Mathlib: `MulAction.orbitEquivQuotientStabilizer`,
  `Cardinal.mk_congr`, `Nat.card_congr`, `Subgroup.card_mul_index`,
  `MulAction.orbit_eq_univ`.

**Estimated Effort**:
- Exploration: a few hours (confirm the cardinal-index framing and lemma names).
- If tractable (backbone + finite corollary + structural corollaries): 1–2 days
  for a $0$-axiom file of roughly 100–160 lines.
- Stretch (fully infinite cardinal product $\#\operatorname{Orb}\cdot\#\operatorname{Stab}=\#G$
  via Approach B): additional 1–2 days assembling cardinal coset-decomposition lemmas.

## References

### Papers / Books

- Dummit, D. S. and Foote, R. M., *Abstract Algebra*, 3rd ed., Wiley, 2004 —
  Section 4.1 develops the orbit–stabilizer theorem via the coset bijection; the
  argument is stated without essential use of finiteness.
- Rotman, J. J., *An Introduction to the Theory of Groups*, 4th ed., Springer
  (GTM 148), 1995 — Chapter 3 presents group actions, orbits, stabilizers, and the
  orbit–stabilizer correspondence as a bijection of coset spaces, the natural home
  for the infinite-general statement.
- Lang, S., *Algebra*, 3rd ed., Springer, 2002 — Chapter I.5 on group actions,
  orbits, and the counting formula.

### Online Resources

- https://en.wikipedia.org/wiki/Group_action — the orbit–stabilizer bijection and
  its cardinal (index) form.

### Mathlib

- `Mathlib.GroupTheory.GroupAction.Basic` — `MulAction.orbit`,
  `MulAction.stabilizer`, `MulAction.orbit_eq_univ` (transitive actions).
- `Mathlib.GroupTheory.GroupAction.Quotient` —
  `MulAction.orbitEquivQuotientStabilizer` (the finiteness-free bijection at the
  heart of this problem).
- `Mathlib.GroupTheory.Index` — `Subgroup.index`, `Subgroup.card_mul_index`,
  `Subgroup.index_eq_card` (index as coset cardinality; the finite product form).
- `Mathlib.SetTheory.Cardinal.Finite` — `Nat.card`, `Nat.card_congr` (transporting
  cardinalities along `Equiv`, for the finite corollary).
- `Mathlib.SetTheory.Cardinal.Basic` — `Cardinal.mk`, `Cardinal.mk_congr` (the
  infinite-general cardinal identity).

## Metadata

```yaml
tags:
  - group-theory
  - group-actions
  - algebra
  - cardinal-arithmetic
  - orbit-stabilizer
related_proofs:
  - lagrange-theorem-oq-02
  - lagrange-theorem
  - lagrange-theorem-oq-03
difficulty: low
source: gallery-gap
created: 2026-06-30
```
