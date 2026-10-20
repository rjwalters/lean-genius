---
title: "Scaling Laws for Sparse Mixture-of-Experts on a $11B-Token Corpus"
author: "Author Name(s) Withheld"
abstract: >
  We study compute-optimal scaling of sparse MoE models and report a 5x
  throughput improvement over the dense baseline at matched quality.
---

# Introduction

Recent work has established compute-optimal scaling for dense transformers.
We extend the analysis to sparse mixture-of-experts (MoE) architectures and
fit a power law of the form $L(C) = a \, C^{-\alpha} + L_\infty$ to the loss
$L$ as a function of compute $C$.

# Results

Figure 1 shows the fitted scaling curve. Table 1 reports per-method results
across the six benchmark suites, including the wide confidence-interval
columns for each task.

![Loss vs. compute, log-log, with the fitted power law overlaid.](figures/fig-scaling.pdf)

| Method | ARC | HellaSwag | MMLU | GSM8K | HumanEval | Best-F1 (95% CI) |
|--------|-----|-----------|------|-------|-----------|-------------------|
| Dense baseline | 41.2 | 58.9 | 44.1 | 19.3 | 22.0 | 0.611 (0.598-0.624) |
| MoE (ours) | 47.8 | 63.1 | 49.7 | 27.6 | 31.4 | 0.689 (0.677-0.701) |

Our best configuration reaches a corpus value of $11B tokens at a $40k
training cost, a 5x speedup over the dense baseline.

<!--
Smoke fixture for paper-vision (#46).

This Markdown paper reproduces the four paper-relevant rendered-only defect
families that the vision critic must catch. None of these are visible in the
source — they only manifest in the compiled PDF:

1. mathtext_artifacts (HIGHEST stakes for a paper): the title and the results
   sentence contain "$11B" and "$40k". When rendered, the "$" opens a math
   span and the figures render as italic math with no dollar sign — a
   correctness defect because LaTeX is source-of-truth. A vision critic SHOULD
   score `mathtext_artifacts` 0-1 and SHOULD raise the
   `mathtext_artifact_breaks_meaning` critical flag.

2. label_cropping / table overflow: Table 1 has 7 columns including a wide
   "Best-F1 (95% CI)" column. Rendered at paper width the right-most column
   crosses the page's right margin and is clipped — the best-result column
   (the load-bearing number) drops off the page. A vision critic SHOULD score
   `label_cropping` low and SHOULD raise `rendered_overflow_unrecoverable`.

3. axis_legibility: fig-scaling.pdf is a log-log plot whose axis tick labels
   are rendered too small to read at print size. A vision critic SHOULD score
   `axis_legibility` low and surface a major finding.

4. palette_adherence: the plot uses the raw matplotlib default color cycle
   rather than a print-safe palette, and the two series differ only by color
   (fails in grayscale). A vision critic SHOULD score `palette_adherence` low
   and surface a minor finding.
-->
