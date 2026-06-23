# Problem: Borsuk-Ulam for Non-Cyclic Groups (Dihedral, Symmetric)

## Statement

### Plain Language
Extend the equivariant Borsuk-Ulam dimension framework from cyclic groups Z/n
to non-cyclic finite groups, specifically dihedral groups D_n and symmetric groups S_n.

The parent `BorsukUlamOQ02OQ01.lean` axiomatizes `buDim(n, d)` for cyclic groups and
proves monotonicity via prime divisors. The open question: what is `buDim(G, d)` for
non-cyclic G, and can similar monotonicity results be derived?

### Formal Statement

```lean
-- Extend buDim to arbitrary finite groups
-- For dihedral group D_n = ⟨r, s | r^n = s² = e, srs = r⁻¹⟩:
-- buDim(D_n, d) ≥ buDim(Z/2, d) = d-1  (since Z/2 ≤ D_n)

-- For symmetric group S_n:
-- buDim(S_n, d) ≥ buDim(Z/2, d) via the sign representation

-- Key conjecture: buDim(G, d) = max over prime p | |G| of buDim(Z/p, d)
-- (same formula as for cyclic groups, but now over ALL prime divisors of |G|)
```

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - topology
  - borsuk-ulam
  - equivariant-topology
  - dihedral-groups
  - symmetric-groups
```

**Significance**: 6/10 — Extends the equivariant Borsuk-Ulam framework beyond cyclic
groups; connects to representation theory and the Fadell-Husseini index. Meaningful
but unlikely to resolve the deepest open problems.

**Tractability**: 5/10 — The monotonicity approach (subgroup monotonicity) is tractable
via axiomatization. Full proofs for dihedral/symmetric groups likely require additional
group-theoretic infrastructure. A partial formalization (axiomatized) is very feasible.

## Why This Matters

1. **Extension of existing framework**: `BorsukUlamOQ02OQ01.lean` provides the
   cyclic group case; extending to non-cyclic groups fills a natural gap.
2. **Subgroup monotonicity**: If H ≤ G, then buDim(G, d) ≥ buDim(H, d). For D_n
   (which contains Z/2 and Z/n), this gives immediate lower bounds.
3. **Representation theory connection**: Non-cyclic groups have irreducible
   representations beyond the cyclic ones; the BU dimension depends on the
   G-representation structure.
4. **Dold's theorem generalization**: The Dold index (formalized in `borsuk-ulam-oq-02-oq-03`)
   applies to free G-spaces for any finite group G — connecting to the oq-03 entry.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `borsuk-ulam-oq-02-oq-01` | Parent: cyclic group Z/n framework (axiomatized) |
| `borsuk-ulam-oq-02-oq-01-oq-01` | Sibling: dimension formula for composite n |
| `borsuk-ulam-oq-02-oq-01-oq-02` | Sibling: exotic representations for composite groups |
| `borsuk-ulam-oq-02-oq-03` | Dold's theorem (Dold index for free G-spaces) |
| `borsuk-ulam-oq-02-oq-01-oq-04` | Sibling: Fadell-Husseini index formalization |

## Lean Files

- `proofs/Proofs/BorsukUlamOQ02OQ01.lean` — Parent cyclic group framework to extend
- No dedicated OQ01-OQ03 file exists yet — new file needed

Key existing infrastructure:
- `buDim : ℕ → ℕ → ℕ` axiom (for cyclic groups, by group order)
- Monotonicity lemma: `prime_monotonicity` (p | n → buDim(p,d) ≤ buDim(n,d))
- Extension needed: `buDimG : Type* → ℕ → ℕ` parametrized by group type

## Suggested Approach

1. **OBSERVE**: Read `BorsukUlamOQ02OQ01.lean` fully. Note the `buDim` axiom
   takes `ℕ × ℕ` (cyclic group order + dimension). Understand `BorsukUlamOQ02OQ03.lean`
   (Dold index) for the general G-space framework.
2. **ORIENT**: Determine whether to:
   (a) Generalize `buDim` to `Type*` (general groups), or
   (b) Add axioms for specific cases: `buDim_dihedral`, `buDim_symmetric`
   Option (b) is much more tractable for axiomatization.
3. **DECIDE**: Use subgroup monotonicity axiom + specific dihedral/symmetric axioms.
   Key fact: D_n contains Z/2 and Z/n as subgroups, so
   `buDim_dihedral(n, d) ≥ max(buDim(2, d), buDim(n, d))`.
4. **ACT**: Create `BorsukUlamOQ02OQ01OQ03.lean` with:
   - Axioms for dihedral/symmetric BU dimensions
   - Subgroup monotonicity theorem
   - Lower bounds via Z/2 inclusion

## Mathematical Context

The dihedral group D_n = ⟨r, s | r^n = s² = 1, srs⁻¹ = r⁻¹⟩ has order 2n and:
- Contains Z/n = ⟨r⟩ as a normal subgroup
- Contains Z/2 = ⟨s⟩ as a subgroup (many copies)
- Is non-cyclic for n ≥ 3

By subgroup monotonicity for the Dold/Yang-Borsuk framework:
- buDim(D_n, d) ≥ buDim(Z/2, d) = d-1
- buDim(D_n, d) ≥ buDim(Z/n, d) (from cyclic subgroup)

The conjectured formula (from Matousek): buDim(G, d) = max_{p prime, p||G|} buDim(Z/p, d)
holds for cyclic groups by the parent proof. For non-cyclic groups it remains open
whether equality holds or whether non-abelian structure provides stronger constraints.
