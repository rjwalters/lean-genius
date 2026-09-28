---
venue: arxiv
claim: >
  Remote-cache misses in distributed build systems concentrate in a small,
  history-predictable minority of source files, and a scheduler that acts on
  that prediction cuts median build latency 22.4% at a 5.8% CPU cost.
title: An Empirical Characterization of Remote Cache Miss Behavior in Distributed Build Systems
author: Author Names Withheld
anonymous: true
keywords:
  - build systems
  - caching
  - mining software repositories
---

# Brief — build-cache-miss-study (Fixture A)

The measurement study and the deployment behind this thread are the same work
described in `../../bold-synthesis-labeled/build-latency-history-problem/BRIEF.md`.
The `## Strongest claim` section below is **byte-identical** to that sibling's
— both threads were briefed on the same organizing idea. Only the drafted
paper differs.

**What Fixture A demonstrates**: the draft in `build-cache-miss-study.1/`
answers question 5 of the inventory in the negative. Its title, abstract, and
contribution list are organized around the easiest claim to defend (a
measurement and a prototype), and the strongest honest statement recorded
below appears exactly once, hedged, in the last paragraph of the Discussion
("More speculatively, one might read these measurements as suggesting..."). A
reviewer running the cold-reader check in `commands/paper-review.md` compares
the draft's extractable idea against this section and records the named
`underclaiming_buried_lede` finding.

## Motivation

Build latency is the most frequently cited developer-productivity complaint in
the organization's internal surveys. The remote cache already runs at a high
aggregate hit rate, so the usual capacity and eviction levers are exhausted;
what remains unexamined is which work the scheduler chooses to start.

## Claim

Remote-cache misses concentrate in a small, history-predictable minority of
source files, and a scheduler that pre-warms their downstream targets cuts
median build latency 22.4% for a 5.8% cluster-CPU cost.

## Strongest claim

**Strongest honest statement**: Version-control history is a build-scheduling
signal, not merely input to offline code analysis — the dependency graph says
what could change, history says what will, and history is accurate enough
(AUC 0.87 a day ahead) and fresh enough to drive an online scheduling
decision.

**Why a thoughtful reader might find it surprising or generative**: Build
schedulers are built almost exclusively from the dependency graph, and the
mining-software-repositories literature that reads history has treated it as
an offline, advisory product for humans. That the two have not been joined is
an accident of which conference each lives in, not a technical necessity; the
measured 16-point AUC gap over the recency proxy in production use says the
unused signal is large.

**What it could inspire**: Follow-on work putting the same history signal into
other scheduling decisions over the same change distribution —
regression-test selection, CI-runner placement, cache-eviction ordering — and
a broader argument about which system decisions should read the repository's
own history as a live input.

**Demonstrated / derived / synthesis / conjecture split**:
- *Demonstrated*: miss concentration (8.3% of files, 71.4% of misses across
  2.1M invocations); next-day predictability at AUC 0.87 against a 0.71
  recency baseline; a randomized eight-week deployment cutting median latency
  22.4% and p90 31.1% at 5.8% CPU.
- *Derived*: the ranking rule (rank by predicted miss probability, admit until
  the CPU budget binds) follows from the concentration measurement plus the
  standard speculative-work cost model; it is not tuned.
- *Synthesis*: co-change mining and speculative build warming are both mature
  and neither is ours; the composition — history as a live scheduler input —
  is, and the ablation showing the two history signals are non-redundant
  (9.1% + 7.4% separately, 22.4% together) is what tests it.
- *Conjecture*: that the same signal governs test selection and runner
  placement. Not tested here; stated with a falsifiable prediction so a null
  result confines the claim to cache warming.

**Opening organized around the strongest claim, not the easiest-to-defend
one**: The title and the first sentence must state the scheduling claim. The
measurement (8.3%/71.4%) and the deployment number (22.4%) are the *evidence*
for it and belong second, not first — a paper that opens on the measurement
has described what was built without explaining why it changes how a reader
might think.

**Intellectual territory on success**: Readers should associate the authors
with "repository history as a scheduling input," a direction, rather than
with one cache-warming benchmark.

**Reader should remember** (one paragraph): A build cluster's scheduler is
deciding what to compute next from the dependency graph alone, while the
repository's own history sits unread and predicts, a day in advance and with
AUC 0.87, which files will actually miss. Wiring that history into the
scheduler is worth roughly a fifth of median build latency, and the same
signal is probably sitting unread in front of several other scheduling
decisions.

**Deliberately excluded for focus**: A cache-eviction policy driven by the
same predictor (adjacent and likely to work, but it would split the paper's
claim across two mechanisms); a comparison against build-graph-partitioning
schedulers (a different lever on the same metric, and treating it fairly
needs its own deployment). Excluding them sharpens the scheduling claim; it
does not replace it with a smaller one.

## Method (sketch)

Fourteen-week action-level trace across three repositories; fractional
attribution of each miss to the changed source files; a four-feature logistic
regression (30-day churn count, 90-day co-change eigenvector centrality,
reverse-dependency fan-out, mean diff size) predicting next-day top-decile
miss-set membership; a pre-warmer that speculatively builds the downstream
targets of the top-ranked files under a 6% CPU budget controller.

## Experiments

Miss-concentration table across R1/R2/R3 and pooled; AUC against the
recency-only baseline on the same folds; a four-row feature ablation; an
eight-week engineer-randomized deployment (1,412 engineers, 612k builds)
reporting median and p90 latency, CPU cost, and a 1% correctness-audit
sample.

## Related work

Four clusters: build caching / remote execution; prefetching in CI; co-change
mining; history-aware test selection. The co-change and centrality measures
are inherited unchanged — positioning must say so without collapsing the
paper's synthesis claim to that least-novel ingredient
(`commands/paper-litsearch.md` §"Component-novelty calibration").
