# Erdős #1178 - Knowledge Base

## Problem Statement

For r ≥ 3, let d_r(e) be the minimal d such that ex_r(n, F) = o(n²), where F is the family of r-uniform hypergraphs on d vertices with e edges. Conjecture: d_r(e) = (r-2)e + 3 for all r, e ≥ 3.

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 6/10
**Aristotle Suitable**: Partially (for the norm_num lemmas and connection theorems)

## Tags

- erdos
- extremal-combinatorics
- hypergraphs
- open-conjecture
- turán-type

## Known Results

- **Lower bound** (proved): d_r(e) ≥ (r-2)e + 3 [BES73]
- **Upper bound**: d_r(e) ≤ (r-2)e + 2 + ⌊log₂ e⌋ [SaSe05]
- **Case e=3**: d_r(3) = (r-2)·3 + 3 for all r ≥ 3 [EFR86]
- **Case r=3**: d_3(e) ≤ e + O(log e / log log e) [CGLS23]
- **d_3(3) = 6**: The (6,3)-problem [RuSz78]
- **d_3(10) ≤ 14**: [SoSo17]

## Related Problems

- [Problem #716](https://www.erdosproblems.com/716) - The Ruzsa-Szemerédi (6,3)-problem
- [Problem #1076](https://www.erdosproblems.com/1076) - F_k extremal numbers
- [Problem #1157](https://www.erdosproblems.com/1157) - General case

## References

- [BES73] Brown-Erdős-Sós, "Some extremal problems on r-graphs" (1973)
- [Er75b] Erdős, "Problems and results on graphs and hypergraphs" (1975)
- [Er81] Erdős, "On the combinatorial problems..." (1981)
- [EFR86] Erdős-Frankl-Rödl (1986)
- [RuSz78] Ruzsa-Szemerédi (1978)
- [SaSe05] Sárközy-Selkow (2005)
- [CGLS23] Conlon-Gishboliner-Levanzov-Shapira (2023)
- [SoSo17] Solymosi-Solymosi (2017)

## Sessions

### Session 1 (2026-03-28, researcher-8)
- Created full formalization: Erdos1178Problem.lean (185 lines)
- Defined r-uniform hypergraphs, family F(r,d,e), extremal numbers, threshold d_r(e)
- Formalized BES lower bound, Sárközy-Selkow upper bound, solved cases
- Created gallery entry with meta.json, annotations.json, index.ts
- 7 axioms, 3 sorries (bes_lower_bound, ruzsa_szemeredi_d3_3, efr_e3)
- Cross-referenced with #716 and #1076

---

*Generated from erdosproblems.com on 2026-01-15*
*Updated 2026-03-28 by researcher-8*
