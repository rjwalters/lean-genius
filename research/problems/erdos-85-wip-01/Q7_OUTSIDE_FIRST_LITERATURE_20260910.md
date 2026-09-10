# q=7 outside-first literature audit — 2026-09-10

Owner: codex-sol-2. Goal48 / board38 Phase A. Status: source pass complete;
peer review pending. No external exclusion of the four remaining profiles was
established. This is a bounded audit, not a claim that no relevant theorem exists.
No solver, certificate replay, cloud spend, or Lean proof was run for this audit.

## Exact question and disposition

We seek a simple C4-free graph on 49 vertices with minimum degree at least 7.
The squad's reductions leave degree sequences 7^(49-h) 8^h for h=1,3,5,7.
Those reductions are inputs here, not new literature conclusions.

| Source / restriction | h=1 | h=3 | h=5 | h=7 |
| --- | --- | --- | --- | --- |
| Boza's published Ramsey bounds | unresolved | unresolved | unresolved | unresolved |
| Afzaly–McKay six published n=49 examples | none is a witness | none is a witness | none is a witness | none is a witness |
| Girth >=5 / (7,5)-cage bounds | excludes only triangle-free subclass | same | same | same |
| ABL polarity constructions (abstract checked) | no exclusion established | same | same | same |
| ABD large-girth constructions (full text checked) | wrong forbidden-cycle class for general exclusion | same | same | same |

## Ramsey translation: Boza

Write r(s)=R(C4,K1,s), avoiding the paper's f notation, which conflicts with
Erdős85's threshold function. Boza's v2 (12 June 2026), §3 table, gives
r(41)=49 and r(42)<=50. Ramsey monotonicity supplies r(42)>=49.
On 49 vertices, a complement avoids K1,42 exactly when the original graph
has minimum degree at least 7. Thus a target witness selects r(42)=50;
nonexistence selects r(42)=49. The table does not decide this case.
Theorem4 requires m>=8 and m=2 mod6; it cannot be invoked at q=7 merely
by substituting the degree parameter.
[Primary paper](https://arxiv.org/html/2409.12770v2).

## Afzaly–McKay records: revalidated, not exhaustive

The maintainers' C4 table labels n=49 with ne>=174 and ng>=6. Their legend
explicitly treats this combination as best examples, with larger edge counts
not ruled out. Freshly downloaded sparse6 data contain six graphs; every graph
has 49 vertices, 174 edges, minimum degree 6 and maximum pairwise common-neighbor
count 1. Degree multisets, each occurring twice, are
6^4 7^36 8^9, 6^5 7^34 8^10, and 6^7 7^30 8^12.
This independently reproduces the existing
[August audit](manuscript/FIRST_DROP_LITERATURE_CHECK.md); it is not a new kill.
[Maintainer table and legend](https://users.cecs.anu.edu.au/~bdm/data/extremal.html),
[actual data](https://users.cecs.anu.edu.au/~bdm/data/extremal/c4_n49e174.maybe.s6).

Downloaded bytes SHA256:
`2b3254d03d5ab980d03b673d7fab4aa69e99c1d97736f5ac29b3ea2dde7f280a`.
Check used NetworkX3.6.1 sparse6 decoding and direct neighborhood intersections.
Machine-readable results: local evidence directory below, `records_check.json`.
No exhaustive graph generation is asserted.

## Cages and Hoffman–Singleton: triangle-free hypothesis is essential

Hoffman–Singleton's original paper proves uniqueness of the Moore graph of
degree7 and diameter2 (Theorem11). This is the 50-vertex girth5 example.
[Original paper, pp.497–504](https://people.orie.cornell.edu/dpw/orie6334/HoffmanS60.pdf).

Elementary applicability check: in a triangle-free, C4-free graph of minimum
degree7, the root, its at least7 neighbors, and their at least6 other neighbors
are distinct, giving at least 1+7+7*6=50 vertices. Hence the triangle-free
49-vertex subclass is impossible. With triangles allowed, second-step vertices
can lie in the first neighborhood; that count is unavailable. Neither
regularity nor girth5 follows from the target hypotheses. In fact 7-regularity
on 49 vertices already violates the handshaking parity condition, whereas all
four mixed-degree profiles have even degree sum. A table of regular cages
therefore cannot itself settle them.

## Abreu–Balbuena–Labbate (2010): polarity construction scope

*Adjacency matrices of polarity graphs and of other C4-free graphs of large
size*, Designs, Codes and Cryptography55,221–233,
[DOI](https://doi.org/10.1007/s10623-010-9364-1).
The [institutional record](https://upcommons.upc.edu/entities/publication/635cb854-810e-4754-a1e9-87f7b44a6451)
was downloaded and its abstract read. It describes polarity adjacency matrices
and lower bounds on ex(n,C4) obtained by constructions. The displayed special
family has order q²-sqrt(q), requiring a square prime power q; q=7 does not meet
that condition. The general polarity order at q=7 is57, so reaching49 would
also require a deletion/construction argument preserving minimum degree7.
No such argument was established here. The institutional full text is marked
restricted; no full-text nonexistence theorem or complete regular-graph table
has been checked. Keep this access gap explicit.

## Abajo–Balbuena–Diánez (2010): full text checked

*New families of graphs without short cycles and large size*, Discrete Applied
Mathematics158,1127–1135,
[DOI](https://doi.org/10.1016/j.dam.2010.03.007),
[institutional PDF](https://idus.us.es/server/api/core/bitstreams/606c1f82-6503-4060-86f4-8d9736481dfe/content).
The paper's f_s(n) forbids every cycle C3 through Cs. Theorem1 starts from a
regular graph of girth at least6; Theorem2(i) supplies a lower bound for
f_4(2q²+q), which at q=7 is order105, not49. Theorems3–4 concern still larger
girth, and Theorem5 supplies asymptotic bounds. These statements do not give
an upper bound for the triangle-allowing target. The paper itself distinguishes
cages from edge-extremal graphs. Its use of regular inputs must not be
misreported as an exhaustive C4-only classification.

PDF SHA256: `1a06c99d53b457e73b8a52fe2a0404b8718c554c02589fc9f94876b3de6310a8`.

## Related titles checked for scope

The same authors' 2012 *Girth of {C3,...,Cs}-free extremal graphs*
([primary PDF abstract](https://idus.us.es/bitstreams/0c030ca4-67c1-4fcd-bcc2-c71320db8aaa/download))
concerns when an edge-extremal graph in that forbidden family must contain
Cs+1. It does not remove the triangle-free hypothesis at s>=4.
The 2019 *Improving bounds on the order of regular graphs of girth5*, by
Abajo–Balbuena–Bendala–Marcote, is a different author list
([primary PDF abstract/introduction](https://idus.us.es/bitstreams/89054962-efb0-477b-b075-63fee8b5d5ad/download)).
It constructs smaller regular girth5 graphs, improving upper bounds on cage
orders. This is not a table of all triangle-allowing C4-free mixed-degree graphs.
Only the cited abstract/introduction material was checked for these two titles.

## Evidence and next handoff

Local retrieval/check evidence is under
`/Users/rwalters/lean-genius-q7-outside-first-20260910/`:
`abd.pdf`, extracted `abd.txt`, `abl.html`, `n49.s6`, `records_check.json`.
The cited primary URLs and hashes allow independent retrieval. No third-party
claim of a solved Ramsey value has been promoted to a theorem.

Phase A should retain all h=1,3,5,7 until the algebraic owners establish a
profile-specific contradiction or leave it unresolved. Integrate the table
above into Q7_SQUEEZE_20260910.md after review. Certificate preparation remains
postponed; this audit supplies no authorization or readiness claim for a launch.
