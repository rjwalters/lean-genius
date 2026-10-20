# Comments — build-cache-miss-study.1

Line-level comments keyed to `main.tex` sections.

## Underclaiming / buried-lede

- **blocker**: `underclaiming_buried_lede` — the paper's organizing idea
  (version-control history as a build-scheduling signal, per the thread
  brief's §"Strongest claim") appears only in §5's "A possible reading"
  paragraph, and is disowned there. Every ingredient the claim needs is
  already in the paper: the concentration measurement, the AUC gap against
  the recency baseline, and an ablation showing the two history signals are
  non-redundant. Promote the claim to the title, the abstract's first
  sentence, and the head of the contribution list; keep the ablation exactly
  where it is as its evidence. Dims 3 and 9.
- **major**: abstract — the closing sentence withholds twice ("descriptive",
  "preliminary", "we do not claim") for a study with a randomized
  deployment and a clean ablation. Hedging should mark the boundary of the
  claim, not occupy its centre. State the claim, then state the boundary.
  Dim 9.
- **major**: §1 — the contribution list is organized by artifact (a trace, a
  characterization, a prototype) rather than by assertion. Re-cast each item
  as something the authors believe is true, and label it demonstrated /
  derived / synthesis / conjecture. Dim 3.
- **major**: title — "An Empirical Characterization of Remote Cache Miss
  Behavior in Distributed Build Systems" survives noun substitution into
  fifty adjacent papers. The genericness is a symptom, not the defect. Dim 3.

## §2 Related Work

- **major**: the paragraph on co-change mining ends by claiming no novelty in
  the predictor. That is accurate and should stay — but the section then
  never states what *is* new, so a reviewer skimming §2 concludes the paper
  has inherited everything. Position at the composition's scope: history read
  online by the scheduler rather than offline by humans. See
  `commands/paper-litsearch.md` §"Component-novelty calibration". Dim 4.
- **minor**: the test-selection paragraph dismisses `bhattacharya2022testsel`
  as out of scope in one sentence. It is the closest prior instance of
  history driving an online decision and deserves engagement on that basis.
  Dim 4.

## §5 Discussion

- **major**: "A possible reading" is the paper. Moving it to §1 costs nothing
  in rigor and is the single change that would move dims 3 and 9 most. The
  hedge "one might read these measurements as suggesting" attributes the
  paper's own claim to a hypothetical third party. Dim 3, dim 9.
- **nit**: the cost paragraph is well judged and should survive the revision
  unchanged.

## Tables

- **minor**: Table 2's caption states where the latency numbers come from but
  not what the comparison shows. A caption that told its own story would read
  the non-redundancy off the table. Dim 6.

## What is not wrong

- No AI-tell vocabulary was found: no instance of a self-flattering
  virtue-signalling adjective and no instance of a structural-importance
  announcement in the body.
- No citation defect, no numerical inconsistency, no ignored close prior work.
  The revision must not trade any of this for boldness.
