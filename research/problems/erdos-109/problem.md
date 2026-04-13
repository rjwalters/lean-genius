# Problem: Erdős #109: The Erdős Sumset Conjecture

## Statement

### Plain Language
Any subset A of the natural numbers with positive upper density contains a sumset
B + C = {b + c : b ∈ B, c ∈ C} where both B and C are infinite.

**Status**: SOLVED (Moreira, Richter, Robertson — Annals of Mathematics, 2019)

### Formal Statement
```lean
def ErdosSumsetConjecture : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ A

-- Currently axiomatized as:
axiom moreira_richter_robertson : ErdosSumsetConjecture
```

where `HasPositiveUpperDensity A` means `0 < Filter.limsup (fun N => |A ∩ {1..N}| / N) atTop`.

## Classification

```yaml
tier: A
significance: 8
tractability: 7
tags:
  - erdos
  - solved
  - additive-combinatorics
  - density
  - sumsets
  - ergodic-theory
```

**Significance**: 8/10 — Major result proved in Annals of Math; foundational in additive combinatorics
**Tractability**: 7/10 — Main theorem deep but Lean infrastructure already exists; OQ variants tractable

## Why This Matters

1. **Density forces additive structure** — positive density implies existence of B+C ⊆ A with B, C infinite
2. **Parallel to Szemerédi** — as Szemerédi gives arithmetic progressions, this gives infinite sumsets
3. **Ergodic proof technique** — Furstenberg correspondence translates combinatorics to measure theory
4. **Connects to Erdős #656** — extended by Kra-Moreira-Richter-Robertson (2024) to density-Hindman theorem

## Current Lean Proof (gallery)

File: `proofs/Proofs/Erdos109Problem.lean` (438 lines)
- 1 axiom: `moreira_richter_robertson : ErdosSumsetConjecture`
- Complete density framework (upper density via `Filter.limsup`)
- Custom sumset definition with commutativity
- Derived consequences: positive density → infinite set
- Example: even numbers have density 1/2

## Research Goal

**Primary**: Attempt to prove or reduce `moreira_richter_robertson`. The Lean proof in the gallery
axiomatizes this theorem. Research should explore whether Mathlib's ergodic theory / measure
theory tools allow formalizing the Furstenberg correspondence principle step.

**Secondary**: Explore open questions from the conclusion:
1. Strengthened versions: B, C with specific gap conditions (e.g., B = C)?
2. Minimal density threshold for various sumset structures
3. More elementary proof (avoiding ergodic theory)?

## Proof Approach (actual MRR proof)

1. **Furstenberg correspondence**: Convert density condition to measure-preserving system
2. **IP-sets and polynomial recurrence**: Use polynomial ergodic recurrence theorems
3. **Structured return times**: Construct B, C from return times to sets of positive measure

Key tool: Bergelson-Leibman (1996) polynomial van der Waerden theorem.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-656` | Density version of Hindman's theorem — direct extension by same team (2024) |
| `erdos-139` | Szemerédi's theorem — same density-forces-structure paradigm |
| `erdos-3` | Arithmetic progressions in divergent-reciprocal-sum sets — companion problem |
| `erdos-31` | Additive complements — complementary sumset covering question |
| `erdos-245` | Sumset growth ratio — finite sumset theory (Plünnecke-Ruzsa) |
| `szemeredi-theorem` | Roth's theorem in Lean — shares density framework and limsup definitions |

## Key References

- Moreira, Richter, Robertson (2019). "A proof of a sumset conjecture of Erdős." *Ann. Math.* 189(2):605–652.
- Kra, Moreira, Richter, Robertson (2024). "Infinite sumsets in sets with positive density." *JEMS* 26(10):3709–3735.
- Furstenberg (1977). "Ergodic behavior of diagonal measures." *J. d'Analyse Math.* 31:204–256.
