# Problem: Shafarevich realizability for solvable subgroups of S_n (n ≤ 4)

**Slug**: `abel-ruffini-oq-04-oq-09`
**Parent**: `abel-ruffini-oq-04` (threshold theorem: S_n is solvable ⇔ n ≤ 4)
**Tier**: B  **Significance**: 6  **Tractability**: 5

## Statement

### Plain language

For every $n \leq 4$, every subgroup of $S_n$ — in particular every group of
order dividing $n!$ that arises as $\mathrm{Gal}(K/\mathbb{Q})$ for some
degree-$n$ extension — is realizable as a Galois group over $\mathbb{Q}$ by
an *explicit* construction. This gives the constructive converse to the
parent entry's threshold theorem:

$$
\text{for } n \leq 4: \quad
\text{Gal}(f/\mathbb{Q}) \subseteq S_n \ \Longrightarrow\ \text{Gal}(f/\mathbb{Q})
\text{ is solvable AND realizable over } \mathbb{Q}.
$$

The full Shafarevich theorem (1954, with corrections by Iwasawa) says every
finite solvable group is realizable over $\mathbb{Q}$. We carve out a
**finite, explicit, $S_n$-bounded** slice that requires no embedding-problem
theory and connects directly to the threshold theorem.

### Formal statement (Lean-side)

```lean
/-- For each `n ≤ 4` and each finite group `G` that embeds into `Equiv.Perm (Fin n)`,
    `G` is realizable as a Galois group over `ℚ`. -/
theorem solvable_realizable_le_four
    (n : ℕ) (hn : n ≤ 4)
    {G : Type*} [Group G] [Fintype G]
    (φ : G →* Equiv.Perm (Fin n)) (hφ : Function.Injective φ) :
    ∃ (L : Type*) [Field L] [Algebra ℚ L] [IsGalois ℚ L],
      Nonempty (G ≃* (L ≃ₐ[ℚ] L))
```

Together with the parent's `symmetric_solvable_iff_le_four`, this packages
the *finite-explicit* side of Shafarevich:

```lean
/-- For solvable subgroups of `S_n` with `n ≤ 4`, no axiom is needed —
    every such group has an explicit realization. -/
theorem oq04_oq09_full :
    ∀ n ≤ 4, ∀ G : Subgroup (Equiv.Perm (Fin n)), ∃ (L : ...) ...
```

The general statement (arbitrary finite solvable G) reduces to OQ-05
(`shafarevich_inverse_galois` axiom) and OQ-05-OQ-01 (cyclic + coprime
abelian PROVED via Dirichlet, full Shafarevich pending embedding theory).

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - gallery-extracted
  - inverse-galois
  - shafarevich
  - radical-solvability
```

**Significance 6/10**: Closes the constructive direction of OQ-04's
threshold theorem with *no axioms* (for the $n \leq 4$ slice).
Distinguished from sibling OQ-05/OQ-05-OQ-01 which axiomatize the full
solvable case.

**Tractability 5/10**: The $n \leq 4$ slice is bounded by a finite menu
of explicit realizations:
- $\mathbb{Z}/2 \cong \mathrm{Gal}(\mathbb{Q}(\sqrt{2})/\mathbb{Q})$
- $\mathbb{Z}/3 \cong \mathrm{Gal}(\mathbb{Q}(\zeta_7)^{(\mathbb{Z}/2)}/\mathbb{Q})$ — order-3 subfield of $\mathbb{Q}(\zeta_7)$
- $\mathbb{Z}/4 \cong \mathrm{Gal}(\mathbb{Q}(\zeta_5)/\mathbb{Q})$ — since $(\mathbb{Z}/5)^\times \cong \mathbb{Z}/4$
- $V_4 \cong \mathrm{Gal}(\mathbb{Q}(\sqrt{2},\sqrt{3})/\mathbb{Q})$
- $S_3 \cong \mathrm{Gal}(f/\mathbb{Q})$ for $f$ an irreducible cubic with non-square discriminant (e.g. $X^3 - 2$)
- $A_4, S_4$ via explicit quartics (e.g. resolvent-cubic-driven examples)

Each is constructible from existing Mathlib (cyclotomic Galois groups,
`Polynomial.SplittingField`, `IsCyclotomicExtension`).

## Why this matters

1. **Closes the threshold theorem constructively** — pairs with
   `symmetric_solvable_iff_le_four` to give:
   > *radical formulas exist for degrees $\leq 4$ because every
   > occurring solvable Galois group is constructible explicitly.*

2. **Axiom reduction** — OQ-05 axiomatizes Shafarevich. For the $n \leq 4$
   slice, all targets can be proved via Mathlib's existing cyclotomic +
   splitting-field theory, **with zero axioms beyond `Classical.choice`**.

3. **Pedagogical bridge** — Gives readers concrete number-field examples
   matching each row of OQ-04's threshold table (Sn solvable ⇔ n ≤ 4).

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `abel-ruffini-oq-04` | Parent: the threshold theorem this OQ closes constructively |
| `abel-ruffini-galois-extensions-oq-05` | Sibling: full Shafarevich (axiomatized) |
| `abel-ruffini-galois-extensions-oq-05-oq-01` | Sibling: cyclic + abelian feasibility (1 axiom for compositum) |
| `inverse-galois` | Cousin: general IGP framing |
| `abel-ruffini-oq-04-oq-01` | Cousin: companion explicit-solvable-quintic examples |

## Out of scope (for this slug)

- Full Shafarevich for arbitrary solvable G — handled by OQ-05/OQ-05-OQ-01.
- Hilbert irreducibility (OQ-08) — handled in `oq-04-oq-07`.
- Effective Galois-group computation (OQ-10) — separate slug.
- General inverse Galois (non-solvable case, e.g. A₅) — Open conjecture.
