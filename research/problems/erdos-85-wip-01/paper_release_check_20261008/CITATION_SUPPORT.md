# Follow-up to the v9 citation-support obligations

Checked 2026-10-08 against primary texts for existing bibliography entries.
This is a focused follow-up, not a new full citation audit or a literature
novelty search. No bibliography, manuscript, or completed critic was edited.
Page numbers below are the source's printed page labels unless specified.

| Existing key / manuscript claim | Finding and primary location |
|---|---|
| `tan2021cakelpr`: HOL4/CakeML correctness includes parsing and reaches machine code | **SUPPORTED.** Tan, Heule and Myreen, TACAS 2021, pp. 224–225 and §4.1, p. 231: the refinement adds parsing and file I/O, verifies the source implementation, and composes with compiler correctness. Acceptance relates to the parsed DIMACS formula under the stated FFI model. This supports the paper's description, not an unconditional guarantee about arbitrary builds, hardware, or our emitter. [Publisher PDF](https://link.springer.com/content/pdf/10.1007/978-3-030-72013-1_12.pdf). |
| `heule2024hexagon`: empty-hexagon result, cube partitioning, cake_lpr checks | **SUPPORTED.** Heule and Scheucher, author preprint §6.3, p. 15, and §7.1, p. 17: 312,418 subproblems, LRAT production and validation, and concurrent CaDiCaL-to-cakeLPR checking through a pipe. [Primary preprint](https://arxiv.org/pdf/2403.00737). |
| `subercaseaux2024hexagonlean`: Lean encoding verification combined with external cake_lpr checks | **SUPPORTED WITH THE STATED TRUST BOUNDARY.** §2 describes the geometric reduction; §6.1, p. 35:15, describes the generated CNF, checked subproblems and coverage check. §7, p. 35:17, explicitly says UNSAT is asserted as a Lean axiom and CNF identity is trusted. Thus the cited work supports the reduction-plus-external-check description, not kernel admission of all SAT proofs. [Publisher PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.35/LIPIcs.ITP.2024.35.pdf). |
| `zhang2017polarity` and `boza2024ramsey`: `r(109) ∈ {120,121}`, `r(155) ∈ {168,169}` | **SUPPORTED AS A DEDUCTION FROM THE STATED RESULTS.** The polarity article's author-institution abstract supplies the needed exact values; Boza v2, Corollaries 7 and 3, supplies the transfer and upper bounds. Derivation and access limits follow. |

Write `r(n) = R(C4,K_{1,n})` (Boza calls this function `f`). The
[PolyU record for Zhang–Chen–Cheng](https://research.polyu.edu.hk/en/publications/polarity-graphs-and-ramsey-numbers-for-csub4subversus-stars/)
states `r(q²−t) = q²+q−(t−1)` for odd prime powers `q`, with
`1 ≤ t ≤ 2 ceil(q/4)` and `t ≠ 2 ceil(q/4)−1`. At `t=1`, both
`q=11` and `q=13` qualify: the respective ceilings are 3 and 4, so the
excluded values of `t` are 5 and 7. Thus `r(120)=132` and `r(168)=182`.
This is theorem-statement support from the institutional abstract; the full
2017 proof text was not accessible. The web text extraction flattens the
fraction `q/4` to `q4`.

[Boza v2, Corollary 7](https://arxiv.org/html/2409.12770v2#S2) gives
`r(2n+1−r(n)) ≥ n`. Our substitutions are:

| `n` | Known `r(n)` | `2n+1−r(n)` | Deduced lower bound |
|---|---|---|---|
| 120 | 132 | 109 | `r(109) ≥ 120` |
| 168 | 182 | 155 | `r(155) ≥ 168` |

[Boza v2, Corollary 3](https://arxiv.org/html/2409.12770v2#S1) gives
`r(n) ≤ n + ceil(sqrt(n−1)) + 1` for `n ≥ 2`.
Since `10² < 108 ≤ 11²`, the first upper bound is `109+11+1=121`;
since `12² < 154 ≤ 13²`, the second is `155+13+1=169`.
Together these prove the two stated intervals, using the cited results.
They are deductions, not entries in Boza's small-value tables. This note does
not refresh the earlier literature search for an exact value or audit the
full proof of the polarity theorem.

Source access: the publisher cake_lpr and ITP PDFs, the Heule–Scheucher arXiv
PDF, Boza v2 PDF/HTML, and the PolyU polarity abstract were read directly.
Access to the full 2017 polarity article failed. No full publisher text is
redistributed here; links and section/page locations identify the support.
