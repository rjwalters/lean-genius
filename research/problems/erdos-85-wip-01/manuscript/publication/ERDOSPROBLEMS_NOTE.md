# Draft note for erdosproblems.com, Problem 85

**Status.** DRAFT for Robb Walters. Not posted. Robb posts. Replaces, in content, the outdated
`../ERDOSPROBLEMS_POST_DRAFT.md` (written before the H1 certificate check, when 1,161 H1
instances were verdict-only); that file is kept for history. Every number below is from the
audited paper (`../paper/main.tex`, 7 October 2026). Fill [DOI], [GitHub release] and
[CHECKING.md] at release, and re-check the bracketed [CHECK vs final paper] sentence against the
final wording of the paper's H3 paragraph before posting.

Conventions. F(N) is the function of the problem: the least d such that every simple graph on N
vertices with minimum degree at least d contains a C_4. Boza's Ramsey function is
r(s) = R(C_4, K_{1,s}). The note quotes both and says which is which.

---

## Text to post

> We report two results on this problem. Neither settles it.
>
> **1. A strict drop, F(48) = 8 and F(49) = 7, as a certificate-checked computational result.**
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
> h = 9 directly and reduces the claim to excluding four strata H1, H3, H5, H7. The three
> smaller strata are closed by a combination of checked certificates and reviewed arguments.
> [CHECK vs final paper] For H1, Lean reduces the stratum (using `native_decide` for a finite
> enumeration) to the unsatisfiability of 13,351 symmetry-reduced CNF formulas. Every one of
> them has an unsatisfiability proof accepted by the CakeML-verified LRAT checker `cake_lpr`
> (Tan, Heule and Myreen, TACAS 2021): about 28 TB of LRAT in all, checked as it streamed and
> then discarded, with only hashes kept. The hardest instance was split into 36 cubes whose
> composition is a standard-axiom Lean lemma. No proof was rejected and no instance was
> satisfiable. Each checked CNF is regenerated from the orbit's table by a compiled Lean
> emitter and must match a recorded sha256.
>
> *Evidence level.* This is not a Lean theorem. The `cake_lpr` checks run outside Lean and are
> not admitted into Lean; the identity of each checked file with its Lean formula rests on the
> compiled emitter, not a kernel proof; and some steps for the smaller strata remain open in
> Lean and rest on reviewed arguments. The paper lists every such step in one table. To our
> knowledge this is the first strict drop of F on the problem's domain N ≥ 4 established at
> this level of evidence; we found no consecutive equality yielding one in Boza's decided
> entries, though some entries there are still ranges.
>
> *Checking it yourself.* The H1 check can be repeated on one's own AWS account with a public
> machine image (ami-05697724475f2e748, us-east-1) and the published proofs in a Requester Pays
> S3 bucket; the tool `e85-check` streams a published proof into `cake_lpr`, or re-solves an
> instance and compares the proof's sha256 with ours. Guide: [CHECKING.md].
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
> Paper: [DOI]. Lean sources, receipts and checker: [GitHub release].
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
