# Literature correction: the two remaining Ramsey choices

Checked 2026-09-15 by codex-sol-2. Write r(s) = R(C₄,K₁,ₛ), distinct from the graph-order extremal function in Erdős 85.

## Result

The checked theorems imply **r(109) ∈ {120,121}** and **r(155) ∈ {168,169}**. This improves the lower endpoints 119 and 167 in the September 13 fallback note. These are deductions, not new exact values or a claim of novelty.

## Inputs and derivation

[Zhang–Chen–Cheng, *Polarity graphs and Ramsey numbers for C₄ versus stars*, Discrete Mathematics 340 (2017), 655–660](https://doi.org/10.1016/j.disc.2016.12.005) proves r(q²−t)=q²+q−t+1 for odd prime powers q, 1≤t≤2⌈q/4⌉, except t=2⌈q/4⌉−1. The [authors' institutional abstract](https://research.polyu.edu.hk/en/publications/polarity-graphs-and-ramsey-numbers-for-csub4subversus-stars/) states the formula; it is also reproduced as Theorem 2.4, p.296, in the 2025 survey below. Setting t=1 is valid for q=11,13 and gives r(120)=132 and r(168)=182.

[Boza, *Exact values and bounds for Ramsey numbers of C₄ versus a star graph*, arXiv:2409.12770v2, 12 June 2026](https://arxiv.org/html/2409.12770v2) gives r(2n+1−r(n))≥n (Corollary 7) and r(s)≤s+⌈√(s−1)⌉+1 (Corollary 3). Substitute the preceding exact values:

| n | r(n) | 2n+1−r(n) | Lower bound | Upper bound |
|---:|---:|---:|---:|---:|
| 120 | 132 | 109 | r(109)≥120 | 109+11+1=121 |
| 168 | 182 | 155 | r(155)≥168 | 155+13+1=169 |

More generally, the same substitution gives q²−1≤r(q²−q−1)≤q² for every odd prime power q≥5. The upper bound uses (q−1)²<q²−q−2<q².

## Exact meaning for the census

Directly from the Ramsey definition, a C₄-free graph of order N and minimum degree at least d exists iff r(N−d)>N: its complement has maximum degree at most N−d−1 and therefore avoids K₁,ₙ₋d. Thus:

- An 11-regular C₄-free graph on 120 vertices exists iff r(109)=121.
- A 13-regular C₄-free graph on 168 vertices exists iff r(155)=169.
- Unrestricted nonexistence would give the lower choice, 120 or 168 respectively.

Regularity needs no symmetry assumption. At a vertex v of degree k in a C₄-free graph of minimum degree d, each neighbor has at least d−2 neighbors outside the closed neighborhood of v; these sets are disjoint. Hence N≥1+k+k(d−2)=1+k(d−1). If k≥d+1 then N≥d². Therefore every graph with N<d² and minimum degree d is d-regular.

A Cayley-only UNSAT census cannot select either unrestricted Ramsey value. Nor would an isolated drop settle the eventual-monotonicity question without the additional argument required by Erdős 85.

## Literature search scope

I checked the relevant results and bibliography in [Chen–Zhang–Zhang, *Star-quadrilateral Ramsey Number and Beyond*, Advances in Mathematics (China) 54 (2025), 292–314](https://ccj.pku.edu.cn/Article/DownLoad?id=679227200979013&type=ArticleFile), especially Theorems 2.4 and 2.6; Boza v2; and sections 3.3 and 5.5 of [Radziszowski, *Small Ramsey Numbers*, DS1.18 (2026)](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/0). Targeted searches for the two star indices found no exact-value result. The 2025 survey's Theorem 2.6 gives r(108)=119 and r(154)=167, but its even-t hypothesis does not settle the adjacent indices.

**Publication wording:** “The cited results leave r(109) between 120 and 121, and r(155) between 168 and 169. We found no determination of either exact value in the literature checked on 15 September 2026.” Do not strengthen this into an exhaustive certification that no result exists.

Validation: theorem hypotheses and all four numerical substitutions checked; prose mathematics only, no new Lean theorem or solver verdict asserted.
