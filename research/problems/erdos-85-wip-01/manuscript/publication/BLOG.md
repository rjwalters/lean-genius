<!--
DRAFT for Robb Walters, written in his voice for him to rewrite. Not published.
Numbers are from the audited paper (manuscript/paper/main.tex, 7 October 2026).

Site format (rjwalters.info, matched from drafts/*/post.md and src/blog/posts/posts.ts):
  - Draft location:   drafts/erdos85-what-we-found.1/post.md (+ _progress.json), then the
                      blog skill's review/revise loop.
  - Published as:     src/blog/posts/YYYY-MM-DD-erdos85-what-we-found.tsx, plus entries in
                      src/blog/posts/posts.ts and src/blog/posts/index.ts.
  - This would be the closing dispatch of the Erdős 85 series (08-05, 08-10, 08-12, 08-20).
    It supersedes the unpublished drafts/erdos85-stopped.2 ("The Price of Certainty"), whose
    facts predate the certificate run: that draft says the 1,161 residual orbits were
    verdict-only and that we chose not to buy certificates; both are now out of date.
  - Proposed posts.ts entry:
      id:          "YYYY-MM-DD-erdos85-what-we-found"
      title:       "We Did Not Solve Erdős 85"
      description: "A month ago I was bullish that a room of AI models might solve an Erdős
                    problem. They did not. What they found instead: one strict drop, checked
                    by a verified checker over about 28 TB of proofs, and a reduction of the
                    whole problem to one open proposition."
      date:        "YYYY-MM-DD"
      author:      "RJ Walters"
      category:    "Essay"
      tags:        ["AI", "agents", "collaboration", "Lean", "mathematics", "squad"]
      readingTime: "5 min read"

Title options:
  1. We Did Not Solve Erdős 85
  2. One Step Down
  3. What the Room Found

Placeholders: [ARTICLE] = the companion article's /blog/<id>; [DOI]; [CHECKING.md]
-->

# We Did Not Solve Erdős 85

## Following up

A month ago I was publicly bullish that the room might solve Erdős Problem 85. [CHECK: name the venue, e.g. the SF Lean group] I had reasons. The agents had been working it since early August, the proof outline in [the room](/rooms/erdos-85) had for weeks carried the title "Final proof outline: Erdős 85 is false," and every few days something that had been open closed.

We did not solve it. The problem asks whether a certain function f(n), the minimum degree that forces a four-cycle in a graph on n vertices, eventually stops going down. What we have is narrower and, I think, more durable than what I was hoping for. We established one strict drop, f(48) = 8 and f(49) = 7, as a certificate-checked computational result. Separately, Lean verifies that a single open proposition about regular graphs, which we call A-REG, would imply a negative answer to the whole problem. A-REG is still open. One drop decides nothing about the problem, which concerns all large n. The details, including exactly what "certificate-checked" covers, are in [the companion article]([ARTICLE]) and [the paper]([DOI]).

## Belief, then accounting

The pattern I wrote about in August kept repeating: the agents produce belief cheaply, and the real work is the accounting that follows. Several moments from the last stretch stand out, because each was a case where we were wrong in a way the room itself caught.

At order 64, an early encoding of one case silently reused a table from a neighbouring case, 80 candidate owners instead of 88, and the solver duly reported that the strengthened, wrong problem had no solutions. Someone compared the formal statement with the certificate universe before the endpoint was called proved, and the corrected formulas are now checked in Lean. A proposed sign-separation lemma survived a thousand sampled models, and then it turned out every one of those models was singular, so the hypothesis had never once been tested. And `cake_lpr`, the verified checker we leaned on for everything, exits with status 0 when a check fails. If you only read the exit code, every failure looks like a pass.

The one I think about most came at the very end. The largest stratum of the 49-vertex case reduces, in Lean, to 13,351 SAT formulas. By early October every one of them had a proof, and we were ready to say they were all checked by a formally verified checker. [CHECK: confirm this matches what the review actually flagged] A review pointed out that 12,094 of those proofs, the bank from our August fleet run, had only ever been checked by drat-trim, an unverified tool. Our sentence claimed more than our certificates covered. So we re-checked them all with `cake_lpr`, streaming 22.55 TB of proofs through the checker and keeping only their hashes. Every one verified. The paper says what it says because a reviewer would not let the earlier sentence stand.

## The price came down

In mid-September I told the room we would stop at strong belief and publish what certainty would cost, because the certificates looked too expensive to buy. When we came back to certificates at the start of October, the plan was still to cube every hard instance into small pieces just to keep the proofs manageable. What changed that was a property of `cake_lpr`: it checks a proof of any length within a heap fixed in advance, and four gigabytes was enough for most of ours. Checking added about 6% to the solver's time. In the end the fresh census and the bank re-check together cost about $225 of AWS compute, for about 28 TB of checked proof, none of which we kept.

We do not store the proofs. With the same solver binary they reproduce byte for byte, so we published the hashes, a public machine image, and a tool that lets anyone regenerate a proof and check it. If you have an AWS account you can repeat any piece of it; [CHECKING.md] has the steps.

## Who did the work

This ran for several months with frontier models from two labs and me directing. The paper lists five authors: Claude Fable, GPT Sol, Astra, Claude Opus and me. The seats kept their names while the models behind them changed as the state of the art moved, which is why Sol and Astra share one seat. Fable built the certification pipeline and ran the fleet; Sol and Astra developed the structural reductions, the map of approaches that fail, and the independent audits; Opus ran the October certificate check, including the Lean lemma that stitches the hardest instance back together from its 36 pieces. My job was priorities and scope, and more and more it was deciding what we were entitled to say.

The room's most useful rule came out of a failure: a Lean result counted only after it built from source in a clean environment and someone read its printed axiom list, adopted after a stale-cache incident. Most of what the agents taught me reduces to that. Silence is not success. Ask for the positive artifact: the verification line, the instantiated hypothesis, the printed axioms.

## Where it stands

So the follow-up to my bullishness is this. We did not solve Erdős 85. To our knowledge we did establish the first strict drop of f on the problem's domain at this level of evidence, and anyone can check it. It is not a Lean theorem. The external checks are not admitted into Lean, the checked files match the Lean formulas only through a compiled emitter, and some of the smaller cases rest on reviewed arguments rather than formal proof. We wrote all of that down in one table.

What is left is a question that fits on one line. For q a power of two, at least 8, can a q-regular four-cycle-free graph on q² vertices exist? The room attacked it from every direction it could think of. The paper lists the ways in, and why each one stopped.
