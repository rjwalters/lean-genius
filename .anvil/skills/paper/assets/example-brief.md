---
title: "Adaptive Batch Sizing for Stochastic Gradient Methods on Heterogeneous Hardware"
author: "Jane Doe"
affiliation: "Department of Computer Science, Example University"
venue: "arXiv"
anonymous: false
claim: "A simple online adaptation rule for SGD batch size improves throughput by 1.5--2x on heterogeneous GPU clusters with no measurable accuracy regression."
keywords:
  - stochastic gradient descent
  - distributed training
  - batch size
  - heterogeneous hardware
documentclass: anvil-paper
---

# Brief: Adaptive Batch Sizing for SGD on Heterogeneous Hardware

This is the smoke-test brief used to verify the `anvil:paper` skill end-to-end.
The drafter should produce a 2--4 page paper from this brief that compiles
cleanly via `pdflatex` + `bibtex`, with at least one figure and a small set of
citations. The skill's acceptance test runs the full lifecycle on this brief.

## Motivation

Distributed training of neural networks on heterogeneous GPU clusters (e.g., a
mix of A100, V100, and consumer-grade GPUs) is bottlenecked by the slowest
worker per step. Fixed batch sizes per worker waste capacity on faster GPUs and
overburden slower ones. We propose a simple online adaptation rule that adjusts
each worker's batch size based on observed step latency, smoothing throughput
without hurting convergence.

## Claim

A simple online adaptation rule for SGD batch size improves throughput by
1.5--2x on heterogeneous GPU clusters with no measurable accuracy regression on
ResNet-50/ImageNet and BERT-base/GLUE.

## Strongest claim

**Strongest honest statement**: The single online per-worker EMA rule matches
the throughput of a fully coordinated global scheduler on heterogeneous
clusters, at a fraction of its coordination cost — the paper's actual claim is
that heterogeneity-aware scheduling does not need global coordination, not
merely "our rule is faster."

**Why a thoughtful reader might find it surprising or generative**: The
batch-size EMA rule uses no cross-worker communication beyond the existing
gradient all-reduce, yet it recovers most of the throughput a fully
coordinated scheduler would achieve — a reader familiar with
heterogeneous-cluster scheduling would expect coordination overhead to be
unavoidable. If it holds up, it suggests per-worker local signals are
sufficient for cluster-level load balancing more broadly than assumed.

**What it could inspire**: Follow-on work applying the same
local-adaptation-instead-of-coordination pattern to other resource axes
(memory pressure, network bandwidth) in heterogeneous training, and a
broader argument for when local signals substitute for global coordination
in distributed systems generally.

**Demonstrated / derived / synthesis / conjecture split**:
- *Demonstrated*: the EMA rule improves measured throughput 1.5--2x on the
  two benchmark clusters with no accuracy regression.
- *Derived*: the closed-form batch-size update rule follows directly from
  the target-latency clip formulation in the Method section.
- *Synthesis*: combining an EMA latency estimator (well known in systems
  literature) with per-worker batch clipping (well known in ML systems)
  into a training-loop-native scheduler is the paper's actual construction —
  neither ingredient alone is new; see the litsearch sibling's
  ingredient-level positioning.
- *Conjecture*: that the same local-signal pattern generalizes to other
  heterogeneous-resource axes is stated as a direction in the Discussion,
  not demonstrated here.

**Opening organized around the strongest claim, not the easiest-to-defend
one**: The introduction leads with the "no coordination needed" framing
before the throughput-percentage headline number — the safer, narrower claim
("we get 1.5--2x throughput") is the second sentence, not the first.

**Intellectual territory on success**: Readers should associate the authors
with "local-adaptation scheduling for heterogeneous clusters" as a research
direction, not solely with one benchmark result.

**Reader should remember** (one paragraph): Heterogeneous-cluster training
does not need a global scheduler; a per-worker EMA rule that reacts only to
each worker's own observed latency recovers most of the throughput benefit a
fully coordinated scheduler would provide, with none of the coordination
cost or single-point-of-failure risk.

**Deliberately excluded for focus**: A comparison against fully asynchronous
SGD (interesting but orthogonal — this paper's claim is about synchronous
training with heterogeneous per-step latency, not about relaxing
synchrony); a theoretical convergence proof for the EMA rule under
adversarial latency traces (would strengthen the claim but is a separate
paper's worth of work). Selectivity here sharpens the central claim; it does
not replace it with a smaller one.

## Method (sketch — the drafter expands)

For each worker $w$ and step $t$, maintain an EMA $\bar{\tau}_w$ of step
latency. Adjust batch size $b_w$ at step $t+1$ to target a global step latency
$\tau^*$ (set as the cluster-wide median):
$$
b_w^{(t+1)} = \text{clip}\left(b_w^{(t)} \cdot \frac{\tau^*}{\bar{\tau}_w},\ b_{\min},\ b_{\max}\right).
$$
Global gradient is the per-sample average across workers, weighted by each
worker's actual batch (standard mini-batch SGD semantics).

## Experiments (sketch)

- ResNet-50 on ImageNet, 8-GPU cluster (4x A100 + 4x V100).
- BERT-base on GLUE (MNLI, QQP), 4-GPU cluster (2x A100 + 2x V100).
- Baseline: fixed batch size per worker, tuned per cluster.
- Metric: throughput (samples/sec) and end-task accuracy.
- Ablation: vary $\tau^*$ percentile (median, 75th, max).

## Figures (the figurer produces these from supplied scripts in refs/figures/)

- `fig-throughput.pdf` — throughput vs. cluster composition, our method vs. baseline.
- `fig-accuracy.pdf` — validation accuracy curve, our method vs. baseline.

## Related work (litsearch hooks)

The author has supplied an initial bibliography at `refs.bib` containing the
closest 5--10 prior papers (in `refs/` for the source PDFs). The litsearch
critic should identify any obvious gaps (e.g., recent work on dynamic batch
sizing or asynchronous SGD on heterogeneous clusters) and surface them in
`notes.md` for the author to fill manually. **No invented citations.**

## Acceptance test target

Running the full lifecycle (`paper-draft` → `paper-figures` → `paper-review` →
[optional `paper-revise` if rubric < 35/44] → `paper-audit`) on this brief should:

1. Produce a compilable `main.tex` + `refs.bib` in `<thread>.1/` (or `.2/`
   after one revision).
2. Render at least one figure into `<thread>.{N}/figures/`.
3. Pass the `pdflatex` + `bibtex` cycle with no unresolved `??` citations
   (audit phase verifies).
4. Reach $\geq 35/44$ on the rubric in `<thread>.{N}.review/`.
5. Reach `AUDITED` state with zero critical flags in `<thread>.{N}.audit/`.
