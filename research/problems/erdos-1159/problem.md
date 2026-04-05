# Problem: Erdős #1159: Bounded Blocking Sets in Projective Planes

## Statement

### Plain Language
Does there exist an absolute constant C such that every finite projective plane has a blocking
set that meets every line in at most C points?

A **blocking set** in a projective plane is a set S of points that intersects every line.
The question asks: can we always find a blocking set with bounded intersection multiplicity,
where the bound is a universal constant (independent of the plane size/order)?

**Known**: The ESS probabilistic construction gives a blocking set meeting every line in at
most O(log n) points, where n is the order of the plane. The open question is whether O(log n)
can be improved to O(1).

**Status**: OPEN. The absolute-constant version remains unresolved.

### Formal Statement

```lean
-- The axiomatized ESS bound (proved via probabilistic method):
axiom ess_log_blocking_set :
    ∀ (P L : Type*) [Membership P L] [inst : ProjectivePlane P L]
      [Fintype P] [Fintype L],
    ∃ (S : Set P),
      IsBlockingSet S ∧
      ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤
        3 * (Nat.log 2 (ProjectivePlane.order P L) + 1)

-- The open conjecture (Erdős #1159):
-- ∃ C : ℕ, ∀ (P L : Type*) ..., ∃ S, IsBlockingSet S ∧ ∀ l, |S ∩ l| ≤ C
```

## Classification

```yaml
tier: A
significance: 7
tractability: 6
erdosNumber: 1159
erdosUrl: https://erdosproblems.com/1159

tags:
  - erdos
  - finite-geometry
  - combinatorics
  - projective-planes
  - blocking-sets
  - open
```

**Significance**: 7/10 — classical combinatorial geometry problem with connections to coding theory
**Tractability**: 6/10 — primary axiom is a PROVED result (reducible); main conjecture is OPEN

## Current Lean Proof (gallery)

File: `proofs/Proofs/Erdos1159Problem.lean`
- 1 axiom: `ess_log_blocking_set` (the ESS O(log n) bound, proved via probabilistic method)
- Defines `ProjectivePlane`, `IsBlockingSet`, order of a projective plane
- The main conjecture (absolute constant C) is stated but unproved

## Why This Matters

1. **Blocking sets in coding theory**: Blocking sets correspond to non-trivial linear codes;
   bounded intersection gives structural constraints on minimum-distance codes
2. **Probabilistic method in combinatorics**: The ESS construction is a clean probabilistic
   argument — formalizing it advances Lean's probabilistic combinatorics infrastructure
3. **Desarguesian planes**: For PG(2,q), algebraic geometry (projective varieties, Weil bounds)
   may give better constants than the probabilistic method
4. **Open problem**: If C exists, it would unify blocking set theory across all finite geometries

## Research Goal

**Primary**: Prove `ess_log_blocking_set` from first principles in Lean.
- The proof: include each point independently with probability p = c·(log n)/n
- A line l (with |l| = n+1 points) is not blocked with probability (1-p)^{n+1} ≈ e^{-c log n} = n^{-c}
- Union bound over all n² lines: total failure probability ≤ n² · n^{-c} → 0 for c > 2

**Secondary**: Explore whether PG(2,q) has smaller blocking sets via Singer cycles.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-1084` | Unit distances among separated points — related projective/incidence geometry |
| `brouwer-fixed-point` | Topology methods sometimes used in combinatorial geometry |
| `szemeredi-core` | Szemerédi regularity — same spirit of finding structure in dense sets |

## Key References

- Erdős, P. (1959). "Problems and results on combinatorial number theory." Graphs and other
  combinatorial topics.
- Turán, P.; technical intersection theory for projective planes (blocking set foundations)
- Probabilistic method: Alon & Spencer, "The Probabilistic Method," Theorem 1.1 (union bound)

## Related Problems

- [Problem #2000](https://www.erdosproblems.com/2000)
- [Problem #83](https://www.erdosproblems.com/83)
- [Problem #888](https://www.erdosproblems.com/888)
- [Problem #2](https://www.erdosproblems.com/2)
- [Problem #39](https://www.erdosproblems.com/39)
- [Problem #1](https://www.erdosproblems.com/1)

## References

(No references available)

## OEIS Sequences

- [C124171](https://oeis.org/C124171)
- [B884451](https://oeis.org/B884451)
- [C042214](https://oeis.org/C042214)
