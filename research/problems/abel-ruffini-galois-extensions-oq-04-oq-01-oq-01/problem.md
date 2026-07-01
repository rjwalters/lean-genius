# Problem: Relativize the simple-quotient / maximal-normal bridge to an arbitrary subgroup K via `H.subgroupOf K`

**Slug**: abel-ruffini-galois-extensions-oq-04-oq-01-oq-01
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $G$ be a group, let $K \le G$ be a subgroup, and let $H \le G$ be a subgroup
with $H \le K$ and $H \trianglelefteq K$ (i.e. $H$ is normal *in* $K$; in Lean this
is `(H.subgroupOf K).Normal`, where `H.subgroupOf K = H.comap K.subtype` is the
image of $H$ inside the subtype group $\uparrow K$). Prove:

$$
\mathrm{IsSimpleGroup}\bigl(\, \uparrow K \,/\, (H.\mathrm{subgroupOf}\ K)\,\bigr)
\quad\Longleftrightarrow\quad
H.\mathrm{subgroupOf}\ K \ \text{is a maximal normal subgroup of}\ \uparrow K .
$$

Unfolded, the right-hand side reads: $H.\mathrm{subgroupOf}\ K \ne \top$ and for
every $M \le \uparrow K$ with $H.\mathrm{subgroupOf}\ K \le M$ and $M$ normal in
$\uparrow K$, either $M = H.\mathrm{subgroupOf}\ K$ or $M = \top$. Equivalently,
in terms of subgroups of $G$ sitting between $H$ and $K$: $K/H$ (as a quotient of
the subtype group) is simple iff $H$ is proper in $K$ and no normal subgroup of
$K$ lies strictly between $H$ and $K$.

The parent entry proved exactly this statement in the special case $K = \top$
(so $\uparrow K \cong G$ and `H.subgroupOf ⊤ = H`), giving
`IsSimpleGroup (G ⧸ N) ↔ IsMaximalNormal N`. This child removes the $K = \top$
restriction.

### Plain Language

The parent showed that "the quotient $G/N$ is simple" is the same as "$N$ is a
maximal normal subgroup of $G$." Composition series, however, do not work with
one fixed ambient group: at each step of a chain
$\{1\} = H_0 \trianglelefteq H_1 \trianglelefteq \cdots \trianglelefteq H_n = G$
one asks whether $H_{i+1}/H_i$ is simple, i.e. whether $H_i$ is maximal normal
*inside $H_{i+1}$*, not inside all of $G$. So we need the bridge relativized: fix
an ambient subgroup $K$ and a subgroup $H$ normal in $K$, and prove the same
"simple quotient ⇔ maximal normal" equivalence for the pair $(H, K)$.

Mathematically this is the *same theorem* — just applied with the group $\uparrow K$
playing the role of $G$ and `H.subgroupOf K` playing the role of $N$. The genuine
work, and the thing the open question explicitly flags, is Lean's subtype-group /
quotient typeclass bookkeeping: making $\uparrow K$ a group, arranging the
`Normal` instance for `H.subgroupOf K`, and forming the quotient
`↥K ⧸ H.subgroupOf K` with all the instances the parent proof consumed.

### Why This Matters

The Jordan–Hölder theorem is about *composition series*: maximal chains of normal
subgroups whose successive quotients are simple. The link "maximal step ⇔ simple
quotient" is needed at **every rung** of such a chain, and every rung after the
first is relativized — $H_i$ maximal normal in $H_{i+1}$, an arbitrary subgroup,
not in $G$. The parent's $K = \top$ result covers only the top rung. The
relativized bridge here is what a `JordanHolderLattice (Subgroup G)` instance
(the target of the grandparent open question oq-01) actually consumes, and it is
the direct prerequisite for the Abel–Ruffini application (solvability ⇔ all
composition factors abelian).

## Known Results

### What's Already Proven

- **Parent (`abel-ruffini-galois-extensions-oq-04-oq-01`)**: the $K = \top$
  bridge, `IsSimpleGroup (G ⧸ N) ↔ IsMaximalNormal N`, axiom-free, routed through
  the correspondence theorem `QuotientGroup.comapMk'OrderIso`. Also the two
  directions as dot-notation lemmas and the packaged `IsMaximalNormal` predicate.
- **Grandparent (`abel-ruffini-galois-extensions-oq-04`)**: defines the
  combinatorial `IsMaxNorm H K` predicate and *asserts* (in a comment) its
  equivalence to `IsSimpleGroup (K ⧸ H.subgroupOf K)` "by the correspondence
  theorem, but avoids quotient typeclass issues."
- **Mathlib** provides the pieces:
  - `Subgroup.subgroupOf` — `H.subgroupOf K = H.comap K.subtype : Subgroup ↥K`.
  - `Subgroup.subgroupOf_normal` (verify exact name; cf. `Subgroup.Normal.subgroupOf`)
    — transports normality between `H ⊓ K`/`H` and `H.subgroupOf K`.
  - `QuotientGroup.comapMk'OrderIso` — the fourth isomorphism / correspondence
    theorem (used verbatim in the parent proof).
  - `QuotientGroup.comap_map_mk'`, `QuotientGroup.ker_mk'`,
    `QuotientGroup.le_comap_mk'`, `Subgroup.comap_top`, `MonoidHom.comap_bot`,
    `isSimpleGroup_iff`, `subsingleton_quotient_top`,
    `subgroup_eq_top_of_subsingleton` — the exact lemmas the parent forward/reverse
    directions consume.
  - `Subgroup.toGroup` / the `Group ↥K` instance — makes the subtype a group.

### What's Still Open

- The relativized statement above (this problem) — proving it inside `↥K`.
- Actually contributing `JordanHolderLattice (Subgroup G)` and this bridge
  upstream to Mathlib (tracked by the grandparent oq-01; out of scope here).

### Our Goal

Prove the boxed equivalence for arbitrary `K : Subgroup G` and
`H.subgroupOf K` normal in `↥K`, ideally by **reusing the parent theorem**
applied to the group `↥K`, and discharging the subtype-group / quotient typeclass
obligations. Deliverable: a self-contained Lean file with the relativized
`isSimpleGroup_quotient_iff` and an `IsMaxNorm ↔ IsSimpleGroup (K ⧸ ·)` corollary,
0 sorries, 0 axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-galois-extensions-oq-04-oq-01 | Direct parent: the $K=\top$ bridge to be relativized | correspondence theorem, `comapMk'OrderIso`, quotient groups |
| abel-ruffini-galois-extensions-oq-04 | Grandparent: defines `IsMaxNorm`, asserts the target equivalence | Jordan–Hölder lattice, `subgroupOf` |

## Initial Thoughts

### Potential Approaches

1. **(Recommended) Instantiate the parent at `↥K`.** The parent theorem
   `isSimpleGroup_quotient_iff (N : Subgroup G') [N.Normal]` is stated for a
   *generic* group `G'`. Apply it with `G' := ↥K` and `N := H.subgroupOf K`.
   Then the entire proof reduces to (a) supplying the `Group ↥K` instance
   (Mathlib: `Subgroup.toGroup`), (b) supplying `(H.subgroupOf K).Normal`, and
   (c) translating the abstract conclusion "$N$ maximal normal in `↥K`" back into
   statements about subgroups of $G$ between $H$ and $K$ if a $G$-level corollary
   is desired. Why it might work: the mathematical content is *identical*; the
   parent was deliberately written for an arbitrary group, so no re-proof is
   needed. Risk: the parent lives in a namespace/file; we must import it (add a
   dependency) or restate the generic theorem here. Also the $G$-level
   translation in (c) needs `subgroupOf` lattice lemmas.

2. **Re-run the parent proof directly inside `↥K`.** Copy the parent's
   forward/reverse argument with `mk' (H.subgroupOf K)` and
   `comapMk'OrderIso (H.subgroupOf K)`. Why it might work: no cross-file
   dependency. Risk: pure duplication; still hits every typeclass obligation of
   approach 1, so it is strictly more work.

3. **Prove `IsMaxNorm H K ↔ IsSimpleGroup (K ⧸ H.subgroupOf K)` end-to-end**
   using the `subgroupOf` correspondence (subgroups of `↥K` ↔ subgroups of `G`
   between `⊥.subgroupOf` and `⊤`). Why it might work: directly answers the
   grandparent's asserted equivalence in $G$-terms. Risk: the `subgroupOf`
   Galois-connection lemmas (`subgroupOf_le`, `comap`/`map` under `K.subtype`)
   add a second layer of lattice bookkeeping on top of the quotient one.

**Recommendation: Approach 1** — it isolates exactly the "quotient typeclass
issues" the open question names and reuses the already-verified mathematics.

### Key Difficulties

- **Making `↥K` a group and forming the quotient.** `↥K ⧸ H.subgroupOf K`
  requires the `Group ↥K` instance and a `(H.subgroupOf K).Normal` instance in
  scope simultaneously; instance resolution here is exactly what the OQ flags.
- **Normality transport.** From `H.Normal` (or "H normal in K") to
  `(H.subgroupOf K).Normal` via `Subgroup.subgroupOf_normal` /
  `Subgroup.Normal.subgroupOf` (verify precise statement/direction). If only
  `H ⊴ G` is assumed, `H.subgroupOf K` is automatically normal in `↥K`; if only
  `H ⊴ K`, one supplies it as a hypothesis.
- **Def-eq / instance diamonds** between `Subgroup.toGroup`-derived structure and
  the `QuotientGroup` machinery — the classic subtype-group friction.
- **Correspondence theorem inside the subtype.** `comapMk'OrderIso` must be
  applied to `H.subgroupOf K : Subgroup ↥K`; the objects it manipulates are now
  subgroups of `↥K`, and translating them back to subgroups of `G` between `H`
  and `K` (for a `G`-facing corollary) uses the `subgroupOf` correspondence.

### What Would a Proof Need?

- The parent theorem in scope (import `Proofs.AbelRuffiniGaloisExtensionsOQ04OQ01`
  or restate its generic form).
- `Group ↥K` instance (`Subgroup.toGroup`) and the `(H.subgroupOf K).Normal`
  instance/hypothesis.
- The relativized predicate: `IsMaximalNormal (H.subgroupOf K)` in `↥K`, and a
  bridge lemma relating it to the grandparent's `IsMaxNorm H K` (via
  `subgroupOf` order lemmas).
- Optional $G$-level corollary using `Subgroup.subgroupOf` Galois-connection
  lemmas to phrase "maximal among normal subgroups of $K$ containing $H$."

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is *routine*: it is the parent theorem re-read for the
  group `↥K`, and the parent is already stated for an arbitrary group. No new
  mathematical idea is required.
- The genuine cost is precisely the Lean subtype-group / quotient typeclass
  navigation that the open question itself names as "the main obstacle" — group
  instance on `↥K`, normality transport for `subgroupOf`, quotient instances, and
  possible def-eq/diamond friction.
- All required Mathlib lemmas already exist (the parent consumed the quotient
  ones; `subgroupOf`, `subgroupOf_normal`, `toGroup` cover the subtype side).
- Comparable relativization arguments (working inside `↥K`) appear throughout
  Mathlib's group-theory library, so the pattern is well-trodden.

**Estimated Effort**:
- Exploration: 0.5–1 day (confirm exact `subgroupOf`/normality lemma names and
  instance paths).
- If tractable: 1–3 days.
- If hard (instance diamonds bite): up to a week of typeclass wrangling.

## References

### Papers/Texts
- D. Dummit & R. Foote, *Abstract Algebra*, 3rd ed. — §3.3 (isomorphism theorems,
  lattice/correspondence theorem), §3.4 (composition series, Jordan–Hölder).
- I. M. Isaacs, *Finite Group Theory* — composition series and chief factors.
- C. Jordan (1870), O. Hölder (1889) — original Jordan–Hölder theorem.

### Online Resources
- Mathlib docs: `Mathlib.GroupTheory.QuotientGroup.Basic` (correspondence theorem).
- Mathlib docs: `Mathlib.Algebra.Group.Subgroup.Basic` (`subgroupOf`, normality).

### Mathlib
- `Subgroup.subgroupOf` — `H.subgroupOf K = H.comap K.subtype : Subgroup ↥K`.
- `Subgroup.subgroupOf_normal` / `Subgroup.Normal.subgroupOf` (verify) —
  normality transport for `subgroupOf`.
- `Subgroup.toGroup` — the `Group ↥K` instance on a subgroup.
- `QuotientGroup.comapMk'OrderIso` — correspondence (fourth isomorphism) theorem.
- `QuotientGroup.comap_map_mk'`, `QuotientGroup.ker_mk'`,
  `QuotientGroup.le_comap_mk'`, `MonoidHom.comap_bot`, `Subgroup.comap_top`,
  `isSimpleGroup_iff`, `subsingleton_quotient_top`,
  `subgroup_eq_top_of_subsingleton` — parent-proof machinery to reuse.
- `QuotientGroup.quotientInfEquivProdNormalQuotient` (verify; second iso theorem)
  — likely *not* needed, listed only to rule out.

## Metadata

```yaml
tags:
  - group-theory
  - jordan-holder
  - simple-group
  - maximal-normal-subgroup
related_proofs:
  - abel-ruffini-galois-extensions-oq-04-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-30
```
