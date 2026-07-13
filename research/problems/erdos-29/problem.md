# Problem: Erdos #29

## Statement

### Plain Language
Is there an explicit construction of a set A ⊆ ℕ such that A + A = ℕ (additive basis) but the representation function r_A(n) = o(n^ε) for every ε > 0 (economical)?

### Formal Statement
$$
\exists A \subset \mathbb{N} \text{ explicit}: A + A = \mathbb{N} \land \forall \varepsilon > 0, r_A(n) = o(n^\varepsilon)
$$

where $r_A(n) = \#\{(a,b) \in A^2 : a + b = n\}$ is the representation count.

## Classification

```yaml
tier: B
significance: 8
tractability: 10
erdosNumber: 29
erdosUrl: https://erdosproblems.com/29
prize: $100

tags:
  - erdos
  - additive-combinatorics
  - additive-bases
  - representation-function
  - solved
```

**Significance**: 8/10 (90+ year old problem, explicit vs probabilistic construction)
**Tractability**: 10/10 (SOLVED by Jain-Pham-Sawhney-Zakharov 2024)
**Prize**: $100

## Why This Matters

1. **Historical Significance** - Sidon asked Erdős this in 1932
2. **Constructive vs Existence** - Erdős proved existence probabilistically; JPSZ gave explicit construction
3. **Optimal Bounds** - JPSZ construction achieves essentially optimal size √N · √(log N)
4. **90+ Year Journey** - From question to complete answer took over 90 years

## Key Results

- **Erdős (~1950s)**: Proved existence using probabilistic methods (non-constructive)
- **JPSZ (2024)**: Explicit construction with r_A(n) ≤ exp(C√(log n))

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| Erdos29Problem.lean | Full formalization with JPSZ solution |

## References

- Jain, Pham, Sawhney, Zakharov (2024): arXiv:2405.08650 "An explicit economical additive basis"
- Erdős: Original probabilistic proof
- Sidon (1932): Original question

---

*Last updated: 2026-01-14*
