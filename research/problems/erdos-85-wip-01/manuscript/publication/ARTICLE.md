<!--
DRAFT for Robb Walters. Not published. Every number is taken from paper v12
(manuscript/anvil/erdos85-drop.12/main.tex, 12 October 2026; to be copied into manuscript/paper/ at
release) or the pinned receipts it links, unless marked as coming from CHECKING.md.

Site format (rjwalters.info, matched from drafts/*/post.md and src/blog/posts/posts.ts):
  - Draft location:   drafts/erdos85-drop.1/post.md   (+ _progress.json; the blog skill's
                      draft -> review -> revise loop runs on it there)
  - Published as:     src/blog/posts/YYYY-MM-DD-erdos85-drop.tsx (markdown converted to JSX
                      <section>/<h2>/<p>), plus an entry in src/blog/posts/posts.ts and an
                      import line in src/blog/posts/index.ts.
  - The site has no YAML front matter; post metadata lives in posts.ts. Proposed entry:
      id:          "YYYY-MM-DD-erdos85-drop"
      title:       "A Drop at Forty-Nine"
      description: "We did not solve Erdős Problem 85. We found a strict drop, f(48) = 8 and
                    f(49) = 7, whose upper side Lean derives from two explicit families of
                    unsatisfiable formulas checked by a formally verified checker, plus a
                    Lean-verified proof that one open proposition would imply a negative
                    answer to the problem. What that means, what it does not, and how to
                    check it yourself."
      date:        "YYYY-MM-DD"
      author:      "RJ Walters"
      category:    "Essay"   (or "Research"; the existing Erdős posts use "Essay")
      tags:        ["mathematics", "Lean", "SAT", "Erdős problems", "AI", "agents"]
      readingTime: "13 min read"
  - Alternative placement: the paper itself can also get an entry in
    src/research/papers/papers.ts (fields: id, title, authors, venue "Preprint", year,
    date, abstract, tags, links {pdf, doi, github}); see ZENODO.md.
  - Style: STYLE_GUIDE.md (no em-dashes; no "honest/candid/genuine"); internal links use
    /blog/<id> and /rooms/erdos-85.

Title options:
  1. A Drop at Forty-Nine
  2. What We Found About Erdős 85, and What We Did Not
  3. One Step Down, and What It Rests On

Placeholders: [DOI], [GitHub release], [CHECKING.md]
-->

# A Drop at Forty-Nine

## The question

Take a graph on n vertices and ask how large every vertex's degree has to be before a four-cycle becomes unavoidable: four vertices a, b, c, d with edges ab, bc, cd and da. Call the answer f(n). Precisely, f(n) is the least d such that every simple graph on n vertices with minimum degree at least d contains a four-cycle. As n grows, f(n) grows too, roughly like the square root of n.

[Erdős Problem 85](https://www.erdosproblems.com/85) asks whether f is eventually nondecreasing: is f(n+1) ≥ f(n) for all sufficiently large n? It sounds like it should be obvious. Adding a vertex should never make the property easier to force. But f is defined by a minimum degree, and one extra vertex changes the arithmetic of who can be adjacent to whom, so nothing rules out a small step down. The problem is open, and the maintained record on erdosproblems.com lists no partial result.

For several months a team of frontier AI models and I worked on it in [a shared room](/rooms/erdos-85), formalizing in Lean 4 and running SAT solvers on rented machines. We did not solve it. This piece describes what we did establish, which is two things: a strict drop between two adjacent orders, f(48) = 8 and f(49) = 7, at a level of evidence I will spell out carefully; and a Lean-verified proof that one open proposition about regular graphs would imply a negative answer to the whole problem. The paper is at [DOI]; the code, Lean sources and receipts are at [GitHub release].

There is also a Ramsey-theory way to say the same thing. Write r(s) for the Ramsey number R(C4, K1,s), as in Luis Boza's table of these numbers. Then r(s) ≤ N exactly when f(N) ≤ N − s, so a plateau r(s) = r(s+1) = N is the same as a drop f(N) < f(N−1). Boza's table gives r(41) = 49 and leaves r(42) open between 49 and 50. Our upper side selects r(42) = 49, which is exactly f(49) = 7 < 8 = f(48).

## The drop

A drop has two halves. The lower sides say f(48) ≥ 8 and f(49) ≥ 7, and each needs only one example: a four-cycle-free graph on 48 vertices where every vertex has degree 7, and a four-cycle-free graph on 49 vertices with minimum degree 6. We have both as explicit graphs (the 48-vertex one is 7-regular with 168 edges) and Lean checks them. The check runs through `native_decide`, which trusts Lean's compiled evaluator rather than its kernel alone; a cold rebuild lists three such trust points per graph by name. From these two graphs Lean proves f(48) = 8 and f(49) ≥ 7. Our 48-vertex graph is not isomorphic to any of the ten 48-vertex, 168-edge graphs in the Afzaly–McKay records.

The upper side is the hard part. f(49) ≤ 7 is a statement about every graph on 49 vertices: none of them is four-cycle-free with minimum degree 7. You cannot exhibit that. You have to exclude it.

The exclusion starts with a short counting argument. If two vertices share at most one neighbour, then the walks of length two out of any vertex land on distinct vertices, and a graph with 49 vertices does not have room for many of them. That forces every degree to be 7 or 8, and the number h of degree-8 ("high") vertices to be odd and at most 9. Lean proves this case split and refutes h = 9, checking 18 certificates through `native_decide`. What remains are four strata, H1, H3, H5 and H7, named by the number of high vertices, and Lean has a theorem that takes the four stratum exclusions as inputs and returns the nonexistence statement. The case split is part of the formal statement, so the evidence that follows is evidence for exactly those four propositions.

Here is where each stratum stands:

- **H3 and H5** are excluded in Lean. Each is reduced to a few canonical cases (two for H3, three for H5), and Lean excludes every case by exhaustive finite search: 408 search parts for H3, and 40 search parts plus 18 cover and cardinality checks for H5, all run through `native_decide`. Reviewed paper arguments had excluded both strata earlier and agree with the Lean proofs.
- **H7** splits by the number t of degree-7 vertices adjacent to three high vertices. Lean proves that every H7 graph matches one of fourteen canonical patterns. The thirteen with t ≥ 1 are excluded by LRAT certificates checked inside Lean through `native_decide`. The last one, t = 0, Lean reduces to 28 "cover" formulas and 377,776 "leaf" formulas: if all are unsatisfiable, the stratum is excluded.
- **H1** Lean reduces to 13,351 formulas, described next.

So Lean derives f(49) ≤ 7, and with the lower sides the drop, from exactly two hypotheses: that the 13,351 H1 formulas are unsatisfiable, and that the 377,804 H7 (t = 0) formulas are. Both hypotheses are about formulas defined in Lean. Neither is proved in Lean. They are supported by external checks, and the rest of this piece is about those checks and what they cover.

The derivation's printed axioms are the three standard ones and 598 `native_decide` axioms, 601 in all, with no `sorry`; the two corollaries that add the witness graphs print 607 and 604.

H1, the stratum with one high vertex, carries most of the computation. The eight neighbours of the high vertex are paired off, every other vertex hangs off exactly one of them, and the remaining 40 vertices form a 6-regular four-cycle-free graph whose attachment pattern can be summarized in a small table of counts. Symmetries of the eight neighbours act on these tables, and Lean proves that every H1 graph can be relabelled so its table is one stored representative per orbit. After a capacity inequality (also proved in Lean) removes 190 of the 13,541 stored representatives, 13,351 orbits remain. Each one becomes a SAT formula; the hardest has 42,160 variables and 613,228 clauses. Lean then proves: if all 13,351 formulas are unsatisfiable, H1 is excluded. That theorem uses `native_decide` for its finite enumeration checks, and its printed axioms include 23 of those alongside the three standard ones, with no `sorry`.

## How H1 was checked

A SAT solver that says UNSAT is reporting that it searched and found nothing. That is a claim, and solvers have bugs. The standard remedy is proof logging: the solver writes down every clause it learned, in a format (DRAT, or LRAT, which adds hints so each step can be replayed quickly) that a much smaller program can check independently. We used `cake_lpr`, an LRAT checker by Tan, Heule and Myreen whose correctness, including parsing the input files, is proved in the HOL4 theorem prover and carried down to machine code by the verified CakeML compiler. Once `cake_lpr` accepts a proof of a formula, you no longer need to trust the solver.

The catch is size. These proofs record every step of a search; our largest single proof was 36.2 GB, and across all of H1 they come to about 28 TB. We did not keep them. For each orbit the pipeline did three things:

1. **Pin the formula.** Regenerate the formula from the orbit's table with `v2cnf`, which is the compiled form of the Lean function that the Lean reduction quantifies over, and require its sha256 to match the hash recorded when the orbit was first solved.
2. **Check the proof as it streams.** Pipe the proof, fresh from the solver or read from an archive, through a hashing relay into `cake_lpr`. An orbit counts only when `cake_lpr` prints `s VERIFIED UNSAT`. (`cake_lpr` exits with status 0 even when a check fails, so that printed line is the only success signal.)
3. **Discard.** Keep the proof's hash and length, not the proof. With the identical solver binary the proofs reproduce byte for byte, so anyone can regenerate one and compare.

The 13,351 orbits fell into four sets:

| Set | Orbits | Proofs | Checked by |
|---|---:|---|---|
| August 2026 bank | 12,094 | archived proofs, 22.55 TB of LRAT, largest 26.5 GB | `cake_lpr`, 8 GB heap |
| Fresh census | 1,160 | CaDiCaL 3.0.1 proofs, streamed; 5.64 TB, largest 36.2 GB | `cake_lpr`, 4–16 GB heap |
| Historical | 96 | archived DRAT, converted to LRAT; 0.10 TB | `cake_lpr` |
| Hardest orbit | 1 | 36 cube proofs, 47.1 GB in all | `cake_lpr`, composed by a Lean lemma |
| **Total** | **13,351** | **about 28 TB** | |

No proof was rejected and no orbit was satisfiable.

One orbit beat every whole-instance solve we tried, with time limits up to 24 hours. We split it by cube-and-conquer into 36 sub-problems ("cubes") that together partition the original formula, solved and checked each cube, and proved in Lean that the orbit's formula is unsatisfiable if all 36 cube formulas are. That composition lemma uses only standard axioms.

The bank set deserves a word, because it is where we nearly overclaimed. Those 12,094 proofs came from a production run in August and had been checked at the time only by drat-trim, a standard checker that is not itself formally verified. A review caught that our description of the result implied more than that. So we re-checked all of them with `cake_lpr`: regenerate each formula, stream the archived proof through decompression and two hash checks into the checker, and accept only if everything matches. That took 408 hours of summed check time and verified all 12,094.

A detail that made all this practical: `cake_lpr` checks a proof within a heap fixed in advance, however long the proof is. Four gigabytes was enough for 1,075 of the 1,160 fresh proofs, and none needed more than 16. Checking cost about 6% of the solver's CPU time. Before the run we had planned to cube every hard orbit to keep proofs small, and the bounded memory meant we did not have to. The census and the bank re-check together cost about $225 of cloud compute, by our controllers' estimates.

## How H7 was checked

The t = 0 case of H7 went through the same kind of pipeline. Lean works from the graph on the seven degree-7 vertices with no high neighbour. That graph has 43 possible shapes up to isomorphism; Lean rules out 15 by a counting argument checked with kernel `decide`, leaving 28. For each, the formula is extended by symmetry-breaking clauses, and Lean proves the extension sound. A cover formula then splits each extended formula into leaves, 377,776 in all.

Each cover and leaf formula was solved by CaDiCaL 3.0.1 with LRAT logging and checked as it streamed by `cake_lpr`, with both binaries pinned by hash; the leaf proofs were discarded after the check. One leaf that exceeded the solver time cap was split into 256 sub-leaves plus a sub-cover, and Lean proves that the leaf is unsatisfiable if all of those are, so the tool that made the split does not need to be trusted. Every formula verified, with no satisfiable formula and no rejected proof. The verified leaf and split checks took 4,269 solver and 706 checker CPU-hours on about 20.2 TB of LRAT. A collector recomputes every formula hash from the pinned inputs and requires a verified receipt for each cover and leaf; a second AI author re-ran it independently with the same result.

## What "certificate-checked" means, and what it does not

For each of the 13,351 H1 orbits, a formally verified checker has accepted a refutation of a formula file whose hash matches what the compiled Lean emitter produces for that orbit. The same holds for the 377,804 H7 (t = 0) formulas, with one difference in the emitter described below. That is the claim. It removes the solvers from the trusted base entirely.

What remains trusted is smaller but not empty. The first piece is `cake_lpr` itself: its guarantee is a HOL4 theorem about its compiled binary, not a check by Lean's kernel. The second is the link between each checked file and the Lean formula. For H1 that link rests on the fact that the file was printed by a compiled Lean program, not on a Lean proof that the printing is faithful. For H7 the base files were printed by the Lean term, and the symmetry-breaking and cover lines by a separate generator whose output was compared byte for byte with the Lean definitions. The third is `native_decide`, which the Lean derivation uses for its finite checks.

The closest precedent is Heule and Scheucher's empty-hexagon theorem, with its Lean verification by Subercaseaux and coauthors. Both that work and ours reduce the mathematical statement, in Lean, to the unsatisfiability of a formula defined in Lean, and both rely on `cake_lpr` for the unsatisfiability check. On the faithfulness of the encoding we claim no advantage: our reduction uses `native_decide`, and our checked files are tied to the Lean formulas only through emitters. What our work adds is of a different kind: Lean reductions of two strata to 13,351 and 377,804 formulas, all checked by `cake_lpr`; a check-then-discard method that keeps only hashes; and a public checker for H1.

So the drop is not a Lean theorem. Lean derives it from two explicit hypotheses. The external checks that support them are not admitted into Lean, the file-to-formula identity runs through the emitters, and the derivation depends on `native_decide`. The paper lists every one of these gaps in a single table. Closing them would mean admitting the checks into Lean and proving that the checked files are the Lean formulas; replaying the proofs inside Lean would do both, at a cost we have not attempted.

The build itself was repeated from scratch. The whole Lean project, 893 modules, was compiled from source on a fresh build volume and printed exactly the axiom lists above; an audit of the output checked every source hash, object hash and compile log. Our first attempt at this failed partway through, because of a defect in the build runner, and its record is published next to the successful one. A second rebuild, starting without the H7 certificate files and downloading them with the published script, produced byte-identical compiled objects for all 893 modules.

And one drop decides nothing about Erdős 85. The problem asks about all sufficiently large n. Lean proves that a negative answer is equivalent to arbitrarily late strict drops, so a single drop at 48 to 49 is compatible with either answer. What it does give is the first data point a negative answer would need. To our knowledge it is the first strict drop of f established on the problem's domain at this level of evidence.

## The reduction

The second result is about the infinite problem, and it is fully inside Lean, using only the standard axioms.

The idea is that drops come in pairs of adjacent orders with two halves. If there is a q-regular four-cycle-free graph on q² − 1 vertices, and no four-cycle-free graph of minimum degree q on q² vertices, then f drops from q² − 1 to q². Do that for infinitely many q and the answer to Erdős 85 is no. For q a power of two, at least 8, the first half comes for free: a construction from finite geometry (the even-characteristic polarity graph with its absolute nucleus deleted) supplies the witness, uniformly in q, and Lean checks it. That leaves only the nonexistence half.

Lean proves, from the standard axioms alone, that the nonexistence half follows from one proposition, which we call A-REG: for no k ≥ 3 is there a four-cycle-free 2^k-regular graph on 4^k vertices. If A-REG is true, Erdős 85 has a negative answer. Every link in that chain was compiled and axiom-audited from source.

A-REG is open, and we do not claim it. The evidence is mixed. In its favour, the existence half is uniform, and a defect calculus proved in Lean rules out several kinds of hypothetical counterexample. Against it, the q = 4 analogue is false: Lean proves f(15) = f(16) = 5, so there is no drop from 15 to 16, and exhibits a four-cycle-free 4-regular graph on 16 vertices. Every generic attack we tried on what remains (determinants, spectra, sign patterns of inverses, structured families, packing relaxations) failed, and the paper records why each one fails, because the failures say what a proof would have to use. The rival reading, that special plane orders organize both the constructions and the obstructions with no uniform rule for powers of two, is live.

What remains beneath A-REG has a sharp one-component form: for powers of two q ≥ 8, every loopless q-regular four-cycle-free adjacency matrix of order q² should be singular. Singularity cannot follow from regularity or the spectrum alone. If someone wants a concrete target, that is it.

## Check it yourself

You do not have to trust our receipts. For H1 we published a machine image and the proofs so that anyone with an AWS account can repeat any part of the check without downloading anything to their own computer. The guide is [CHECKING.md]; in outline:

1. Launch the public image `ami-05697724475f2e748` in us-east-1 (Amazon Linux 2023, arm64) on a Graviton instance. It contains the pinned emitter, solver, `cake_lpr`, and a tool called `e85-check`.
2. Give the instance read access to the certificate bucket, which is Requester Pays: you pay your own transfer, which is free within the region.
3. Run `e85-check bank --sample 100` to stream a random sample of our bank proofs into `cake_lpr`, `e85-check census --sample 5` to re-solve census orbits and confirm your proof is byte-identical to ours, or `e85-check cube` to rebuild and check the cubes of the hardest orbit.
4. Read the tally from `e85-check summary`. Anything other than a pass is a real discrepancy, and we would like to hear about it.

By the guide's estimates, a 100-orbit bank sample takes minutes; the whole bank is about 400 checker-hours, around $20 on spot instances; the hardest orbit's cubes take about 8 CPU-hours. Every check regenerates the formula from the orbit's table first and refuses to proceed if its hash does not match.

There is no public checker image for H7. The thirteen H7 certificate files that Lean checks (about 2.57 GB) are in the same Requester Pays bucket, and the script `proofs/scripts/fetch-h7-certificates.sh` in the repository downloads them and verifies each against a committed hash manifest; with them the Lean project builds from source. So far that script has been run end to end only with credentials from the bucket owner's account. The H7 (t = 0) receipts and the collector that checks them are in the repository.

## What is open

- **Making the drop a Lean theorem.** Admit the H1 and H7 checks into Lean and prove that the checked files are the Lean formulas. Even then the axiom list would include the `native_decide` trust points.
- **A-REG**, and beneath it the singularity statement above.
- **Other candidate drops.** At order 64 (q = 8) several cases are closed in Lean but others are open, so 63 to 64 is not established as a drop. For the odd plane orders 9, 11 and 13, an order-80 SAT search ended UNKNOWN and a census of Cayley graphs found no witness (which excludes only those families); with published values this leaves r(109) between 120 and 121 and r(155) between 168 and 169.
- **Erdős 85 itself.**

The paper is "A Drop at Forty-Nine in Erdős Problem 85," by Claude Fable, GPT Sol, Astra, Claude Opus and me. It is at [DOI], and the full repository is at [GitHub release]. The day-by-day record of the room where the work happened is at [/rooms/erdos-85](/rooms/erdos-85).
