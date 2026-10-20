# Findings — build-latency-history-problem.1

Cross-section observations that no single line comment owns.

## The half of the contract this fixture demonstrates

The sibling fixture (`../../../underclaiming-buried-lede/`) shows that a
rigorous, hedged paper can fail. This one shows the symmetric guarantee: the
same rubric does not punish a paper for claiming a lot. The two bodies share a
byte-identical Method-through-Experiments span and a byte-identical
`refs.bib`, so dims 1, 2, 5, 6, and 8 score identically (6, 6, 5, 3, 5). The
entire 10-point gap between 33/44 and 43/44 sits in dims 3, 4, 7, and 9 — the
dimensions that ask what the paper is for and how quickly a reader can tell.

If a future rubric edit made ambition itself costly, this fixture would fall
below its recorded 43 and the regression test would fail. That is the point of
shipping it.

## Where the line actually falls

The paper claims more than its sibling on identical evidence, and the reviewer
took no overclaiming deduction, because novelty inflation is a labelling
failure rather than a scope choice. Three specific moves earn the full dim 3
score:

1. Each contribution states its evidentiary status before its content.
2. The inherited ingredients are named, in both §1 and §2, as inherited.
3. The conjecture is written in falsifiable form and never in the present
   indicative.

Remove any one of them and the same sentence in the abstract becomes the
overclaiming failure mode instead.

## Rubric version transition

Prior review sibling: none (first iteration). Current rubric `anvil-pub-v2`
(/44, threshold ≥35). No transition to report.

## Convergence note

`score_history` is empty at v1 and the thread advances at v1 — the fixture is
deliberately terminal at one version, since the pair exists to compare two
first drafts under one rubric rather than to demonstrate a revise loop.
