# Comments — build-latency-history-problem.1

Line-level comments keyed to `main.tex` sections.

## Ambition and labelling

- **nit**: §1 contribution list — the four evidentiary labels (*Demonstrated*,
  *Derived*, *Synthesis*, *Conjecture*) are what let the reviewer score a
  research-program claim at full weight on dim 3 without an overclaiming
  deduction. Keep them through any revision; a later reviser tempted to
  "tighten" §1 by dropping the labels would be removing the paper's evidence
  that it knows which of its parts are which.
- **nit**: §1's *Conjecture* item names the null result that would confine the
  claim to cache warming. That sentence is doing more work than its length
  suggests and should survive compression passes.

## §2 Related Work

- **minor**: the co-change paragraph states plainly that all three measures
  are taken unchanged, then states what the paper adds — that the mined output
  is fresh and accurate enough to drive an online decision. This is the
  component-novelty calibration `commands/paper-litsearch.md` asks for; no
  change requested. Noted here because the sibling fixture's corresponding
  paragraph stops at the first half and loses two points on dim 4 for it.

## §5 Discussion

- **minor**: "What the claim rests on, and where it stops" bounds the
  demonstrated claim to one organization, three repositories, one build tool,
  and eight weeks. The bold framing does not weaken this paragraph, and the
  paragraph does not weaken the framing — this is the target state the rubric
  describes as hype-free but not timid.

## Tables

- **minor**: Table 2's caption states where the latency numbers come from but
  not what the comparison shows. A caption that told its own story would read
  the non-redundancy off the table. Dim 6. This is the one deduction the two
  fixtures share, because they carry the same tables.

## What is not wrong

- No AI-tell vocabulary was found: no instance of a self-flattering
  virtue-signalling adjective and no instance of a structural-importance
  announcement in the body.
- No unlabelled conjecture, no novelty assertion without a named search, no
  promotional adjective standing in for evidence. The claim is large and the
  labelling is exact, which is the combination `rubric.md` §"Ambition is not
  novelty inflation" exists to protect.
