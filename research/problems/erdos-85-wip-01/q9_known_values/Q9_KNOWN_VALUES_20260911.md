# Erdős 85: q=9 literature audit, 2026-09-11

Owner: codex-sol-2. Prepared for squad board39, the zero-spend q=9 existence experiment. This is the literature component, not a solver verdict or a Lean proof.

**Search consequence:** degree at least 9 on 79 vertices is already excluded by a published exact Ramsey value. The consulted results leave the 78- and 80-vertex existence decisions unresolved. Several other entries reported as exact in Boza v2 have a citation gap described below; this audit does not assert those entries are false or globally unknown.

## Notation and conversion

Write `r(n)=R(C4,K1,n)` and reserve `f(N)` for the Erdős threshold: `f(N)=1+max δ(G)` over C4-free graphs on N vertices. Boza calls the Ramsey function f; silently copying that notation would give the wrong table.

The exact bridge is

`f(N) >= d+1  iff  r(N-d) > N`.

Indeed the complement of a graph of minimum degree at least d on N vertices has maximum degree at most N-1-d, and hence contains no star K1,N-d. A Ramsey witness of larger order restricts to N vertices with the same complement-degree bound. Conversely, any such N-vertex graph is a Ramsey counterexample. Thus an upper bound `r(N-d)<=N` proves `f(N)<=d`.

## Threshold table

“Traced” uses only the formulas and short deductions below. “Reported” translates Boza v2's table without repairing its citations. An interval in the traced column is a limit of this audit; it is not a claim that no other theorem settles it.

| N | f(N), traced bounds | f(N), from reported table | Assessment |
|---:|:---:|:---:|---|
| 73 | 9 | 9 | Exact |
| 74 | 9 | 9 | Exact |
| 75 | 8–9 | 9 | Reported exact; lower endpoint needs citation repair |
| 76 | 9 | 9 | Exact; Boza Theorem 4 gives the needed upper bound |
| 77 | 9 | 9 | Exact |
| 78 | 9–10 | 9–10 | Degree-9 existence unresolved in consulted results |
| 79 | 9 | 9 | Exact; skip degree-9 search |
| 80 | 9–10 | 9–10 | Degree-9 existence unresolved in consulted results |
| 81 | 9–10 | 9–10 | Degree-9 existence unresolved in consulted results |
| 82 | 9–10 | 10 | Reported exact; citation unresolved |
| 83 | 9–10 | 10 | Reported exact; citation unresolved |
| 84 | 10 | 10 | Exact |
| 85 | 9–10 | 10 | Reported exact; citation unresolved |
| 86 | 10 | 10 | Exact |
| 87 | 10 | 10 | Exact |
| 88 | 10 | 10 | Exact |
| 89 | 10 | 10 | Exact |
| 90 | 10 | 10 | Exact |
| 91 | 10 | 10 | Exact |

The companion `verify_table.py` checks every conversion and writes explicit lower/upper bridge witnesses in `table-results.json`. It verifies arithmetic, not the literature proofs. It never assumes monotonicity of the Erdős threshold.

## Source premises and deductions

[Parsons, *Ramsey Graphs and Block Designs, I* (1975)](https://doi.org/10.1090/S0002-9947-1975-0396317-X) gives `r(q²)=q²+q+1`, `r(q²+1)=q²+q+2`, and the upper bound `r(n)<=n+ceil(sqrt(n-1))+1`. The original AMS PDF returned 403. These statements were cross-checked in the full Wu et al. paper and the [2025 account by Chen, Zhang and Zhang](https://ccj.pku.edu.cn/article/info?id=679227200979013), Theorems 2.1–2.2. At q=8 and 9 they give r64=73, r65=74, r81=91, r82=92.

[Zhang–Chen–Cheng, *Some values of Ramsey numbers for C4 versus stars* (2017)](https://research.polyu.edu.hk/en/publications/some-values-of-ramsey-numbers-for-csub4subversus-stars/) proves `r(q(q-1)-t)=q²-t` for odd prime powers q>=5 and even t from 2 through `2ceil(q/4)`. Substituting q=9 and t=6,4,2 gives **r66=75, r68=77, r70=79**. In particular an N=79, δ>=9 witness would require r70>79 and is impossible.

[Zhang–Chen–Cheng, *Polarity graphs and Ramsey numbers for C4 versus stars* (2017)](https://research.polyu.edu.hk/en/publications/polarity-graphs-and-ramsey-numbers-for-csub4subversus-stars/) proves `r(q²-t)=q²+q-t+1` for odd prime powers q, `1<=t<=2ceil(q/4)`, **excluding** `t=2ceil(q/4)-1`. For q=9 this permits t=1,2,3,4,6 and gives **r80=90, r79=89, r78=88, r77=87, r75=85**. The authors' 2025 account, Theorems 2.3–2.6, corroborates both 2017 formulas and records Parsons1976's earlier even-t version. The q=8 even-prime-power Parsons1976 formula also gives the neighboring r55–r63 seeds except n56.

[Boza v2 (12 June 2026)](https://arxiv.org/html/2409.12770v2) has an independently applicable Theorem 4 yielding **r67<=76** at m=8. Its Corollary 7, `r(2n+1-r(n))>=n`, applied to the traced exact values r78=88, r80=90, r81=91 and r82=92 yields **r69>=78, r71>=80, r72>=81 and r73>=82**, respectively. [Chen (1997)](https://doi.org/10.1016/0012-365X(95)00340-3) gives `r(n-1)>=r(n)-2`, hence r74>=83 and r76>=85. Monotonicity of r gives r67>=75. These statements do not require the contested exact entries.

Consequently the traced Ramsey bounds needed here are:

| n | r(n) |
|---:|:---:|
| 64 | 73 |
| 65 | 74 |
| 66 | 75 |
| 67 | 75–76 |
| 68 | 77 |
| 69 | 78–79 |
| 70 | 79 |
| 71 | 80–81 |
| 72 | 81–82 |
| 73 | 82–83 |
| 74 | 83–84 |
| 75 | 85 |
| 76 | 85–86 |
| 77 | 87 |
| 78 | 88 |
| 79 | 89 |
| 80 | 90 |
| 81 | 91 |
| 82 | 92 |

## Citation gap requiring independent review

Boza v2 reports r73=83, r74=84 and r76=86 within a larger interval citing [Wu–Sun–Zhang–Radziszowski, *Ramsey Numbers of C4 versus Wheels and Stars* (2015)](https://cs.rit.edu/~spr/PUBL/cws14.pdf). The full paper's Theorem 3(a) supplies r(q²-2) for prime powers. Its interval theorem 3(b) explicitly requires **even q**. It cannot be instantiated at q=9. The other traced odd-q formulas do not fill these three positions: t=8 and 7 are outside their range, while t=5 is explicitly excluded. Boza's proof of r67=76 then uses r76=86 for its lower bound; the upper bound remains separately supported by Theorem 4.

This is a source-traceability finding, not a refutation. A separate construction or theorem could repair the entries. Pending that repair, do not use them as independently verified exclusion/existence premises. The N=79 exclusion and the bounds at N=78,80,81 do not depend on the gap.

## ANU check and experiment handoff

The [ANU extremal graph data page](https://users.cecs.anu.edu.au/~bdm/data/extremal.html), under H={C4}, ends at order 49. It supplies no N=73–91 entry. Other girth/bipartite sections have different constraints; edge counts alone also do not certify the needed minimum degree.

The literature stage launches no solver and spends no money. Continue the separately authorized semiregular existence experiment at N=80 and then N=78, subject to its controls, caps and ledger. N=79 should be recorded as a literature exclusion. A SAT witness requires independent graph validation; a class-restricted UNSAT result excludes only that action class. Neither class misses nor this table prove that the proposed q=7 drop is sporadic, and no global Erdős85 or Lean completion is claimed.

This file is intended as an input to `Q9_EXISTENCE_DECISION_20260911.md`; controls, seeds, per-class outcomes and the final experiment verdict belong to the solver ledger when available.
