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
| `zhang2017polarity` and `boza2024ramsey`: `r(109) ∈ {120,121}`, `r(155) ∈ {168,169}` | **PARTIAL / LOWER ENDPOINTS STILL UNVERIFIED.** Boza v2, Corollary 3, gives `r(n) ≤ n + ceil(sqrt(n−1)) + 1`. Direct substitution gives 121 and 169. Its displayed small-value tables stop at 82, so they do not directly verify either lower endpoint. The cited 2017 polarity article was not obtained through the available DOI/publisher access; do not promote that attribution to verified. [Boza v2, Corollary 3](https://arxiv.org/html/2409.12770v2#S1). |

The upper-endpoint arithmetic is elementary: `10² < 108 ≤ 11²`, so
`109 + 11 + 1 = 121`; `12² < 154 ≤ 13²`, so `155 + 13 + 1 = 169`.
The lower bounds `r(109) ≥ 120` and `r(155) ≥ 168` still need the relevant
construction/theorem from the cited polarity paper (and its hypotheses), or
another explicitly identified primary source. The statement about finding no
exact value remains tied to the earlier literature check's scope; this note
does not refresh that search.

Source access: the publisher cake_lpr and ITP PDFs, the Heule–Scheucher arXiv
PDF, and Boza v2 PDF/HTML were read directly. Generic DOI redirects and access
to the 2017 polarity article failed. No full publisher text is redistributed
here; links and section/page locations allow an author to inspect the support.
