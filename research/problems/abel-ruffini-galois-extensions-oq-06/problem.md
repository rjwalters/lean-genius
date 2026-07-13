# abel-ruffini-galois-extensions-oq-06

## Problem Description

**Primitive solvable permutation groups of prime degree.** While
`abel-ruffini-galois-extensions` proves the qualitative threshold
"$S_n$ is solvable iff $n \leq 4$", it leaves open the *quantitative*
characterization of maximal solvable subgroups of $S_p$ for prime $p$.

Galois (1832) proved: for prime degree $p$, the only **primitive
solvable** permutation groups of degree $p$ are the affine groups
$\mathrm{AGL}(1, p) = (\mathbb{Z}/p\mathbb{Z}) \rtimes
(\mathbb{Z}/p\mathbb{Z})^\times$ of order $p(p-1)$.

These are the Frobenius groups of order $p(p-1)$ arising as the
splitting fields' Galois groups of irreducible degree-$p$ polynomials
that factor over their splitting field as a product of a $p$-cycle and
a $(p-1)$-cycle (or as a single $p$-cycle, in which case the Galois
group is cyclic of order $p$).

## Formal target

Two complementary statements package this open question. The
"forward" direction is the existence/solvability of the affine groups;
the "Galois direction" is the converse — that primitivity plus
solvability forces the affine form.

**Forward (easy in Lean once AGL is defined).** For every prime $p$,
the affine group $\mathrm{AGL}(1, p)$ acts faithfully and primitively on
$\mathbb{Z}/p\mathbb{Z}$; the action is solvable; and the order is
$p(p-1)$.

```
theorem agl1_primitive_solvable :
    ∀ (p : ℕ) [hp : Fact p.Prime],
      ∃ (G : Type) [Group G] [MulAction G (ZMod p)],
        IsSolvable G ∧
        MulAction.IsPrimitive G (ZMod p) ∧
        Nat.card G = p * (p - 1)
```

**Galois direction (HARD; Mathlib has no `IsPrimitive` for permutation
groups of prime degree).** Every primitive solvable subgroup of
$S_p$ embeds into $\mathrm{AGL}(1, p)$:

```
theorem primitive_solvable_subgroup_of_S_p :
    ∀ (p : ℕ) [hp : Fact p.Prime] (H : Subgroup (Equiv.Perm (ZMod p))),
      MulAction.IsPrimitive H (ZMod p) → IsSolvable H →
      ∃ (φ : H →* AGL1Z p), Function.Injective φ
```

(where `AGL1Z p` is the affine group of $\mathbb{Z}/p\mathbb{Z}$.)

## Metadata

- **Category**: extension (Galois quantitative refinement of the parent
  qualitative threshold)
- **Source proof**: `abel-ruffini-galois-extensions`
  (`Proofs/AbelRuffiniGaloisExtensions.lean`, 534 lines, 0 axioms,
  status: verified)
- **Tier**: B
- **Selected by**: seeker, 2026-05-12T09:56:28Z
- **Significance**: 7 (Galois 1832 classical result; concrete sharpening
  of the parent threshold; new infrastructure for primitive permutation
  groups in Mathlib)
- **Tractability**: 5 (forward direction tractable in 1-2 sessions; Galois
  direction requires substantial new infrastructure — primitive
  permutation group theory, Frobenius-group classification)

## Related gallery work

- **Parent**: `abel-ruffini-galois-extensions` — proves $S_n$ is
  solvable iff $n \leq 4$ qualitatively.
- **Sibling OQ-01**: explicit $S_5$-Galois-group for a specific
  degree-5 polynomial.
- **Sibling OQ-04**: Jordan-Hölder uniqueness for finite groups
  (instantiates Mathlib `JordanHolderLattice` for `Subgroup G`).
- **Sibling OQ-07**: Burnside's $p^a q^b$ theorem (every group of order
  $p^a q^b$ is solvable). This OQ and OQ-07 sharpen the parent threshold
  in *complementary* directions: OQ-07 says "few enough primes ⇒
  solvable"; OQ-06 says "for prime degree, solvable + primitive ⇒
  affine, order $p(p-1)$".

## Tractability triage (what's feasible in Lean)

**Feasible (forward direction, S2-S3 work)**:

- **Define $\mathrm{AGL}(1, p)$.** The affine group of
  $\mathbb{Z}/p\mathbb{Z}$ is the semidirect product
  $(\mathbb{Z}/p\mathbb{Z}) \rtimes (\mathbb{Z}/p\mathbb{Z})^\times$
  where the units act on the additive group by multiplication.
  Mathlib has `SemidirectProduct` (in
  `Mathlib.GroupTheory.SemidirectProduct`); the construction is direct.
- **Solvability of $\mathrm{AGL}(1, p)$.** Since both factors of the
  semidirect product are abelian (hence solvable) and the extension
  $\mathrm{AGL}(1, p) \twoheadrightarrow (\mathbb{Z}/p\mathbb{Z})^\times$
  has abelian kernel, $\mathrm{AGL}(1, p)$ is solvable of derived length
  at most 2. Mathlib's `IsSolvable.of_solvable_quotient` or
  `solvable_of_ker_le_range` gives this directly.
- **Faithful action on $\mathbb{Z}/p\mathbb{Z}$.** The natural action
  $(a, u) \cdot x = a + u \cdot x$ is faithful (any $(a, u)$ fixing
  every $x$ forces $a = 0, u = 1$).
- **Order calculation.** $|\mathrm{AGL}(1, p)| = p \cdot (p - 1)$, by
  the product structure of the underlying set.

**Feasible but heavier (primitivity, S3-S4 work)**:

- **Primitivity of the $\mathrm{AGL}(1, p)$ action.** No non-trivial
  block exists: any non-trivial block $B \subseteq \mathbb{Z}/p\mathbb{Z}$
  with $|B| > 1$ would have to be a union of $\mathrm{AGL}(1, p)$-orbits
  of subsets, but the action is doubly transitive (sharp 2-transitivity
  is folklore for $\mathrm{AGL}(1, p)$). Mathlib has `MulAction.IsBlock`
  and `MulAction.IsPrimitive` (`Mathlib.Dynamics.MeasurableEquiv.Group`
  / `Mathlib.GroupTheory.GroupAction.Primitive`); the proof is several
  Mathlib lemmas chained together.
- **Faithful primitive action ⟹ transitive action.** Standard
  reduction.

**Hard (Galois direction, S5+ work)**:

- **Every primitive solvable subgroup of $S_p$ is conjugate in
  $S_p$ to a subgroup of $\mathrm{AGL}(1, p)$.** This is the deep half
  of Galois 1832 and requires:
  1. A primitive transitive permutation group of prime degree $p$ has
     a unique Sylow-$p$ subgroup, which is normal (cyclic of order $p$).
  2. The normalizer of this Sylow-$p$ in $S_p$ is $\mathrm{AGL}(1, p)$
     of order $p(p-1)$.
  3. A solvable transitive subgroup of $S_p$ with normal Sylow-$p$
     must be contained in the normalizer.
- Each step requires non-trivial group theory not currently in Mathlib's
  `IsSolvable` / `IsPrimitive` API: in particular, the structure theorem
  for transitive groups of prime degree.

**NOT feasible without major infrastructure**:

- **Quantitative ratio $p! / [p(p-1)] = (p-2)!$ as the
  "distance from solvability".** This requires (a) defining maximal
  solvable subgroup, (b) showing $\mathrm{AGL}(1, p)$ is maximal solvable
  in $S_p$, (c) the index $[S_p : \mathrm{AGL}(1, p)] = (p-2)!$. Step
  (b) needs the Galois direction above.

## Suggested first steps (S2+ ACT phase)

1. **S2 — Define $\mathrm{AGL}(1, p)$.** Create
   `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (~80 lines).
   Use `SemidirectProduct` to define `AGL1Z p`, the natural map to
   `Equiv.Perm (ZMod p)`, and the order calculation
   $|\mathrm{AGL}(1, p)| = p(p-1)$. 0 sorries expected.
2. **S3 — Solvability and faithfulness.** Add ~50 lines: prove
   `IsSolvable (AGL1Z p)` (via the abelian-by-abelian extension) and
   `Function.Injective (toPerm : AGL1Z p → Equiv.Perm (ZMod p))`.
3. **S4 — Primitivity.** Prove the action on $\mathbb{Z}/p\mathbb{Z}$
   is primitive (~120 lines, the bulk of the forward direction).
4. **S5+ — Galois direction.** Define primitive permutation group of
   prime degree, set up the Sylow-$p$ uniqueness argument. May need to
   carve into a sub-OQ slug if the infrastructure exceeds ~500 lines.

A finished OQ-06 deliverable can be the forward direction (S2-S4),
leaving the Galois direction explicitly to a sub-OQ. The forward
direction alone is a substantial gallery contribution: an explicit
formalization of $\mathrm{AGL}(1, p)$ as a Lean-verified primitive
solvable group action of prime degree, complementing the parent's
qualitative threshold theorem.

## References

- Galois, É. (1832). *Lettre à Auguste Chevalier*. Posthumously
  published; contains the classification of primitive solvable groups
  of prime degree as $\mathrm{AGL}(1, p)$. Reproduced in:
  Bourgne, R.; Azra, J.-P. (1962). *Écrits et mémoires mathématiques
  d'Évariste Galois*. Gauthier-Villars.
- Rotman, J. J. (1995). *An Introduction to the Theory of Groups*,
  4th ed. Springer GTM 148. Theorem 9.11 (Galois): primitive solvable
  group of prime degree is affine.
- Robinson, D. J. S. (1996). *A Course in the Theory of Groups*, 2nd ed.
  Springer GTM 80. Section 7.3 (Frobenius groups, with $\mathrm{AGL}(1,
  p)$ as the canonical example of a Frobenius group with abelian Frobenius
  kernel).
- Cameron, P. J. (1999). *Permutation Groups*. London Math. Soc. Student
  Texts 45. Chapter 4 (primitive groups of prime degree).
- Wielandt, H. (1964). *Finite Permutation Groups*. Academic Press.
  §11 (Frobenius groups), §13 (primitive groups of prime degree).

## Provenance

- Selected by seeker, 2026-05-12T09:56:28Z
- Parent gallery: `src/data/proofs/abel-ruffini-galois-extensions/`
- Parent Lean: `proofs/Proofs/AbelRuffiniGaloisExtensions.lean`
- Sibling OQ-04: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ04.lean`
  (Jordan-Hölder; instantiates `JordanHolderLattice (Subgroup G)`)
- Sibling OQ-07: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`
  (Burnside $p^a q^b$; currently 1 axiom + 1 sorry)
