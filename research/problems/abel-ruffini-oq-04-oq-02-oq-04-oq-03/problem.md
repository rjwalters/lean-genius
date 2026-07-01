# Problem: Metacyclic Groups Are Solvable — Cyclic-by-Cyclic Extensions

**Slug**: `abel-ruffini-oq-04-oq-02-oq-04-oq-03`
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap (open-question child of `abel-ruffini-oq-04-oq-02-oq-04`)

## Problem Statement

The parent entry `abel-ruffini-oq-04-oq-02-oq-04` ("Dihedral Groups Are Solvable")
proves `IsSolvable (DihedralGroup n)` for every `n` by exhibiting `Dₙ` as **metabelian**:
a cyclic normal rotation subgroup `⟨r⟩ ≅ ℤ/n` of index `2` with abelian quotient `ℤ/2`.
The concrete proof builds a parity homomorphism `parity : Dₙ →* ℤ/2` whose kernel equals
the range of a rotation inclusion `ℤ/n →* Dₙ`, then feeds this into Mathlib's
`solvable_of_ker_le_range`.

The parent's third open question asks:

> "Generalize to the metacyclic and, more broadly, supersolvable families: is every group
> with a cyclic normal subgroup of prime index solvable by the same parity/character
> argument? Concretely: if `G` has a normal subgroup `N` that is cyclic with `G/N` cyclic
> (a metacyclic group), then `G` is solvable; more generally supersolvable ⇒ solvable."

This child abstracts the dihedral proof to its structural core: the ad-hoc parity character
is a special case of the general **extension-closure** fact that a group built as an
abelian-by-abelian (indeed cyclic-by-cyclic) tower is automatically solvable. The dihedral
case is `N = ⟨r⟩` cyclic of index 2; here we drop all ties to the dihedral multiplication
table and state the clean, reusable theorem.

### Formal Statement

Let `G` be a group and `N : Subgroup G` a normal subgroup.

**(1) Cyclic-by-cyclic (metacyclic) ⇒ solvable.** If `N` is cyclic and the quotient `G ⧸ N`
is cyclic, then `G` is solvable:

```lean
theorem isSolvable_of_cyclic_by_cyclic {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [IsCyclic N] [IsCyclic (G ⧸ N)] :
    IsSolvable G := by
  -- cyclic ⇒ commutative ⇒ solvable, on both layers
  haveI : CommGroup N := IsCyclic.commGroup
  haveI : CommGroup (G ⧸ N) := IsCyclic.commGroup
  -- solvability is closed under the extension 1 → N → G → G ⧸ N → 1
  exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
```

The key identity is `(QuotientGroup.mk' N).ker = N = N.subtype.range` (from
`QuotientGroup.ker_mk'` and `Subgroup.range_subtype`), so the hypothesis
`g.ker ≤ f.range` of `solvable_of_ker_le_range` holds with equality. Since `N` and `G ⧸ N`
are abelian they are solvable (`CommGroup.isSolvable`), and the lemma delivers
`IsSolvable G`.

**(1′) Abelian-by-abelian (metabelian) ⇒ solvable.** The same proof works verbatim if
`IsCyclic` is weakened to `CommGroup`/abelian on both layers — this is the direct
generalization the dihedral proof instantiates:

```lean
theorem isSolvable_of_abelian_by_abelian {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [IsSolvable N] [IsSolvable (G ⧸ N)] :
    IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
```

**(2) Specialization — cyclic normal subgroup of prime index.** If `N ⊴ G` is cyclic and
`[G : N] = p` is prime, then `G ⧸ N` has prime order, hence is cyclic
(`isCyclic_of_prime_card` / `ZMod p`-type argument), so (1) applies:

```lean
theorem isSolvable_of_cyclic_normal_prime_index {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [IsCyclic N] {p : ℕ} (hp : p.Prime)
    (hindex : N.index = p) : IsSolvable G := by
  haveI : IsCyclic (G ⧸ N) := by
    -- Nat.card (G ⧸ N) = N.index = p prime ⇒ cyclic of prime order
    sorry
  exact isSolvable_of_cyclic_by_cyclic N
```

The dihedral entry is exactly `p = 2`.

**(3) Supersolvable ⇒ solvable (stretch goal).** A supersolvable group has a normal
series `1 = G₀ ◁ G₁ ◁ ... ◁ Gₖ = G` with each `Gᵢ ◁ G` (normal in the whole group) and each
factor `Gᵢ₊₁ / Gᵢ` cyclic. Every factor abelian ⇒ solvable by induction along the series
using (1′) at each step. **Caveat:** Mathlib (checked at version 4.26.0) has **no**
`Supersolvable` predicate, so part (3) requires first *defining* the notion (or an ad-hoc
finite chain hypothesis) — it is not a one-liner. Parts (1), (1′), (2) are the core, fully
supported by existing Mathlib API; (3) is optional and heavier.

## Plain Language

A group is **solvable** when it can be built up out of abelian (commutative) pieces stacked
in layers — formally, a chain of subgroups whose successive quotients are all abelian.
"Solvable" is the group-theoretic condition behind Abel–Ruffini: a polynomial is solvable by
radicals exactly when its Galois group is solvable.

A **metacyclic** group is the simplest non-trivial case: just **two** layers, a cyclic
normal subgroup `N` on the bottom and a cyclic quotient `G/N` on top. Two abelian layers is
already a solvable tower, so *every metacyclic group is automatically solvable* — no clever
argument required. The dihedral group `Dₙ` (rotations `⟨r⟩` on the bottom, the flip `ℤ/2` on
top) is the textbook example, and the parent entry proved that case by hand. The point of
this problem is to prove the *general* statement once, so the dihedral proof becomes a
one-line corollary rather than a bespoke computation.

**Supersolvable** groups extend this to a full *normal cyclic tower* (each layer cyclic and
normal in the whole group). Stacking cyclic-hence-abelian layers still gives a solvable
group, so supersolvable ⇒ solvable as well.

## Why This Matters

The parent proves solvability of a *specific* family (dihedral) with a hand-crafted parity
character and a four-case check against the dihedral multiplication table. That argument is
correct but non-reusable: it is glued to `DihedralGroup`. This problem extracts the
**structural** statement — solvability is closed under (abelian, and in particular cyclic)
extensions — which is:

- **The clean, reusable Mathlib fact.** `solvable_of_ker_le_range` already encodes
  extension-closure; the metacyclic theorem is the natural named consequence and would let
  the dihedral proof (and any future split/metacyclic family) be discharged in one line via
  `isSolvable_of_cyclic_by_cyclic`.
- **Directly relevant to Abel–Ruffini-style Galois arguments.** Solvable-by-radicals
  reasoning repeatedly needs "this Galois group is an extension of abelian layers, hence
  solvable." Metacyclic groups arise as Galois groups of many concrete radical extensions
  (e.g. `xⁿ − a` over a field containing `n`-th roots of unity has metacyclic Galois group),
  so the general lemma is a genuine workhorse.
- **Isolates what makes Sₙ special.** The parent contrasts solvable `Dₙ` with non-solvable
  `S₅`. Making the metacyclic direction structural sharpens the point: solvability fails for
  `Sₙ` (`n ≥ 5`) precisely because `Sₙ` is *not* an iterated abelian extension, whereas every
  metacyclic/supersolvable group is by construction.

## Known Results

Everything needed for parts (1), (1′), (2) is present in Mathlib
(`Mathlib/GroupTheory/Solvable.lean`, `.../SpecificGroups/Cyclic.lean`,
`.../QuotientGroup/Defs.lean`), verified against version 4.26.0:

- `class IsSolvable (G) : Prop` — solvability via the derived series.
- `instance CommGroup.isSolvable {G} [CommGroup G] : IsSolvable G` — **abelian ⇒ solvable.**
- `def IsCyclic.commGroup [Group α] [IsCyclic α] : CommGroup α` — **cyclic ⇒ abelian**
  (so cyclic ⇒ solvable by composing with the above).
- `theorem solvable_of_ker_le_range (f : G' →* G) (g : G →* G'') (hfg : g.ker ≤ f.range)`
  `[IsSolvable G'] [IsSolvable G''] : IsSolvable G` — **the extension-closure lemma** (this
  is exactly what the parent dihedral proof uses).
- `theorem QuotientGroup.ker_mk' (N : Subgroup G) [N.Normal] :`
  `(QuotientGroup.mk' N).ker = N` — kernel of the quotient map is `N`.
- `theorem Subgroup.range_subtype (H : Subgroup G) : H.subtype.range = H` — range of the
  inclusion is `N`. Together with `ker_mk'` this gives `g.ker = f.range`, discharging the
  `≤` hypothesis of `solvable_of_ker_le_range`.
- Supporting closure instances confirming the picture:
  `instance subgroup_solvable_of_solvable (H : Subgroup G) [IsSolvable G] : IsSolvable H`,
  `instance solvable_quotient_of_solvable (H : Subgroup G) [H.Normal] [IsSolvable G] :`
  `IsSolvable (G ⧸ H)`, and `solvable_of_surjective` / `solvable_of_solvable_injective`.
- For part (2): `isCyclic_of_prime_card` (a group of prime order is cyclic) plus
  `Subgroup.index` / `Nat.card (G ⧸ N) = N.index` to see the prime-index quotient is cyclic.

**Not in Mathlib:** there is no `Supersolvable` class or `supersolvable` predicate (searched,
none found), so part (3) must either define the notion or take a concrete finite normal
cyclic series as a hypothesis and induct.

**Parent's specific argument:** `abel-ruffini-oq-04-oq-02-oq-04` proves the `Dₙ` instance via
`parity : Dₙ →* ℤ/2`, `rotation : ℤ/n →* Dₙ`, and
`parity_ker_eq_rotation_range`, then `solvable_of_ker_le_range rotation parity ...`. The
present problem is that same final step made hypothesis-free / general.

## Suggested Approach

**Core (parts 1, 1′).** Follow the Lean sketches above.

1. Get `IsSolvable N`: from `[IsCyclic N]` obtain `CommGroup N` via `IsCyclic.commGroup`
   (`haveI`), then `CommGroup.isSolvable` fires the instance. (For part (1′) take
   `[IsSolvable N]` directly as hypothesis.)
2. Get `IsSolvable (G ⧸ N)` the same way from `[IsCyclic (G ⧸ N)]`.
3. Apply `solvable_of_ker_le_range` with `f := N.subtype` and `g := QuotientGroup.mk' N`;
   discharge `g.ker ≤ f.range` by rewriting with `QuotientGroup.ker_mk'` and
   `Subgroup.range_subtype` (they give equality, so `.le` / `le_of_eq`).

**Specialization (part 2).** Show `IsCyclic (G ⧸ N)` from a prime index: relate
`Nat.card (G ⧸ N)` to `N.index`, then use `isCyclic_of_prime_card`. Then invoke
`isSolvable_of_cyclic_by_cyclic`. Provide `DihedralGroup n` (`p = 2`) as a sanity-check
corollary, re-deriving the parent result in one line.

**Stretch (part 3).** Either (a) add a lightweight definition of a supersolvable group as a
`List`/`Fin`-indexed normal series with cyclic factors and induct along it applying (1′) at
each extension step, or (b) state a concrete instance (e.g. any group with a subnormal series
of cyclic factors) and prove solvability by the same induction. Flag this as the harder,
possibly-out-of-scope part since Mathlib provides no supersolvable scaffolding.

**Caution / uncertainty to verify during formalization:**
- Confirm `IsCyclic.commGroup` is usable as a local instance via `haveI` (it is a `def`, not
  an `instance`); alternatively there may be a direct `IsCyclic → IsSolvable` path worth
  checking.
- The exact spelling `Nat.card (G ⧸ N) = N.index` vs `Subgroup.index` API should be
  double-checked (`Subgroup.card_quotient_eq_index` or similar) when doing part (2).
- Keep the theorem `axiom`-free: `solvable_of_ker_le_range` and the cyclic/abelian instances
  are all `decide`/`native_decide`-free, matching the parent's 0-axiom status.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - group-theory
  - solvable-groups
  - metacyclic
  - dihedral-group
  - galois-theory
  - abel-ruffini
```

Parts (1), (1′), (2) are genuinely tractable — the extension-closure route reduces to three
short applications of existing Mathlib lemmas and mirrors the parent almost exactly. Part (3)
(supersolvable) is a natural but heavier stretch because Mathlib lacks a supersolvable
predicate.

## Related Gallery Proofs

- **`abel-ruffini-oq-04-oq-02-oq-04`** (parent) — "Dihedral Groups Are Solvable"; proves the
  metabelian `Dₙ` instance via `solvable_of_ker_le_range`. This problem generalizes its final
  step to arbitrary cyclic-by-cyclic (metacyclic) groups.
- **`abel-ruffini-oq-04-oq-02`** (grandparent) — "S₂, S₃, S₄ Are Solvable"; classifies
  solvability of symmetric groups (`Sₙ` solvable iff `n ≤ 4`), the origin of the
  "other infinite families" open question.
- **`abel-ruffini-oq-04-oq-02-oq-02`** — "Aₙ solvable iff n ≤ 4"; the `A₅` obstruction,
  contrasting with the always-solvable metacyclic/dihedral families here.
- **`abel-ruffini-oq-04`** / **`abel-ruffini`** (root) — the Abel–Ruffini impossibility
  theorem, whose Galois-solvability machinery is exactly where metacyclic solvability feeds in.
- Any Sylow / p-group / solvable-group gallery entries — Sylow theory and supersolvability
  are the natural next structural layer above metacyclic.
