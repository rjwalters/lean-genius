# Draft note for erdosproblems.com, Problem 85

**Status.** DRAFT for Robb Walters. Not posted. Robb posts. Replaces, in content, the outdated
`../ERDOSPROBLEMS_POST_DRAFT.md` (written before the H1 certificate check, when 1,161 H1
instances were verdict-only); that file is kept for history. Every number below is from paper v13
(`../anvil/erdos85-drop.13/main.tex`, 12 October 2026; now the manuscript of record in `../paper/`) or
the pinned receipts it links. Links (Robb, 2026-10-12): only the Zenodo paper; no GitHub, CHECKING.md or rjwalters.info links. Robb posts.

Conventions. F(N) is the function of the problem: the least d such that every simple graph on N
vertices with minimum degree at least d contains a C_4. Boza's Ramsey function is
r(s) = R(C_4, K_{1,s}). The note quotes both and says which is which.

---

## Text to post

> We report two results on this problem. Neither settles it.
>
> **1. A strict drop, F(48) = 8 and F(49) = 7, as a computational result.**
>
> *Conversion to Boza's table.* r(s) ≤ N exactly when F(N) ≤ N − s, so
> r(s) = min{N : F(N) ≤ N − s}, and a plateau r(s) = r(s+1) = N is the same as a drop
> F(N) < F(N−1). Boza's table (arXiv:2409.12770, v2) gives r(41) = 49 and leaves
> r(42) ∈ {49, 50} open. Our upper side selects r(42) = 49, which is exactly
> F(49) = 7 < 8 = F(48).
>
> *Lower sides.* Explicit C_4-free graphs: a 7-regular graph on 48 vertices (168 edges; not
> isomorphic to any of the ten 48-vertex, 168-edge graphs in the Afzaly–McKay records) and a
> graph on 49 vertices with minimum degree 6. Both are checked in Lean 4 via `native_decide`,
> so they rely on Lean's compiled evaluator, not on the kernel alone.
>
> *Upper side, F(49) ≤ 7.* Lean proves that a C_4-free graph on 49 vertices with minimum degree
> at least 7 has all degrees in {7, 8} and h ∈ {1, 3, 5, 7, 9} vertices of degree 8; it refutes
> h = 9 and reduces the claim to excluding four strata H1, H3, H5, H7. Lean excludes H3 and H5
> by exhaustive finite searches (408 parts for H3; 40 parts and 18 cover and cardinality checks
> for H5). In H7, the 13 canonical cases with t ≥ 1 (t the number of degree-7 vertices with
> three degree-8 neighbours) are excluded by LRAT certificates checked inside Lean. That leaves
> two families of formulas defined in Lean:
>
> - H1: 13,351 symmetry-reduced CNF formulas, the hardest split into 36 cubes whose composition
>   is a standard-axiom Lean lemma;
> - H7 with t = 0: 28 cover and 377,776 leaf formulas, one leaf split 256 ways with the
>   composition proved in Lean.
>
> Lean derives F(49) ≤ 7 from exactly two hypotheses: that every formula in these two families
> is unsatisfiable. Every one of those formulas has an unsatisfiability proof accepted by the
> CakeML-verified LRAT checker `cake_lpr` (Tan, Heule and Myreen, TACAS 2021): about 28 TB of
> LRAT for H1 and about 20 TB for H7, checked as it streamed. The H1 proofs and the H7 leaf
> proofs were then discarded, keeping only their hashes. No proof was rejected and no formula was
> satisfiable. Each checked CNF file is tied to its Lean formula by emitters: for H1, the
> compiled Lean emitter, whose output must match a recorded sha256; for H7, files printed by the
> Lean term plus a generator whose output was compared byte for byte with the Lean definitions.
>
> *Evidence level.* This is not a Lean theorem. Lean derives the upper side from the two
> unsatisfiability hypotheses above; the `cake_lpr` checks that support them run outside Lean
> and are not admitted into Lean, and the identity of each checked file with its Lean formula
> rests on the emitters, not a kernel proof. The Lean derivation uses `native_decide` (Lean's
> compiled evaluator) and prints the three standard axioms and 598 `native_decide` axioms,
> with no `sorry`. The whole 893-module Lean project was rebuilt from source on a fresh volume
> and audited (a first attempt failed in the build runner; its record is published), and a
> second rebuild that downloaded the H7 certificate files with the published script produced
> byte-identical compiled objects. The paper lists every remaining gap in one table. To our
> knowledge this is the first strict drop of F on the problem's domain N ≥ 4 established at
> this level of evidence; we found no consecutive equality yielding one in Boza's decided
> entries, though some entries there are still ranges.
>
> *Checking it yourself.* The H1 check can be repeated on one's own AWS account with a public
> machine image (ami-05697724475f2e748, us-east-1) and the published proofs in a Requester Pays
> S3 bucket; the tool `e85-check` streams a published proof into `cake_lpr`, or re-solves an
> instance and compares the proof's sha256 with ours; the paper's Availability section links the guide. There is no public
> checker image for H7; the 13 H7 certificate files that Lean checks (about 2.57 GB) are in the
> same bucket, with a download script that verifies them against a committed hash manifest.
>
> **2. A Lean-verified reduction to one proposition.** Let A-REG be the statement that for no
> k ≥ 3 is there a C_4-free 2^k-regular graph on 4^k vertices. Lean 4 verifies, using only the
> standard axioms (propext, Classical.choice, Quot.sound), that A-REG implies a negative answer
> to this problem. A-REG is open and we do not assert it. Its k = 2 analogue is false: Lean
> exhibits a C_4-free 4-regular graph on 16 vertices, and proves F(15) = F(16) = 5. The paper
> also records the approaches to the remaining case that fail and why.
>
> **What this does not do.** The problem asks about all sufficiently large N, and Lean proves
> that a negative answer is equivalent to arbitrarily late strict drops. A single drop at
> 48 → 49 is compatible with either answer. We make no claim about the problem itself.
>
> Paper: https://doi.org/10.5281/zenodo.23325806
> Authors: Claude Fable, GPT Sol, Astra, Claude Opus (AI models from Anthropic and OpenAI) and
> Robb Walters, who directed the work; details of who did what are in the paper.

---

## Notes for Robb (not for posting)

- The `r(s) = min{N : F(N) ≤ N − s}` conversion and the r(41)/r(42) values are from the paper's
  introduction and `../FIRST_DROP_LITERATURE_CHECK.md` (2026-09-28 correction section).
- "We found no consecutive equality yielding one in Boza's decided entries, though some entries
  there are still ranges" paraphrases the paper's "What is new" paragraph. Drop it if the post
  should stay shorter.
- If the forum prefers shorter posts, item 1's *Evidence level* and *Checking it yourself*
  paragraphs are the ones to keep; the conversion paragraph can be cut to one sentence.
- "t" in the H7 sentence is the paper's cell index (low vertices with three high neighbours).
  The paper's "What is not claimed" paragraph is the source for the evidence-level wording;
  keep "Lean derives the upper side from two hypotheses" and do not shorten it to "proved in Lean".
- The H7 download script has been exercised end to end only with the bucket owner's credentials
  (paper, Availability). If someone reports a download failure from another account, that is
  the known untested path.
