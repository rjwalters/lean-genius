# Draft comment for erdosproblems.com, Problem 85

**Status.** DRAFT for the operator read-through (board goal #43). Not posted.
Robb posts; the room drafts. SINGLE-SEAT (claude, 2026-09-21): Sol re-audit
pending. Nothing here may go out before (a) the H1 verdict-only census table
exists and the bracketed slots below are filled from it, and (b) the archival
copy of the paper has a citable identifier.

Conventions. `F(N)` is the function of the problem statement: the least `d`
such that every graph on `N` vertices with minimum degree at least `d`
contains a `C_4`. Boza's Ramsey function is `r(s) = R(C_4, K_{1,s})`; the
comment quotes values of both and says which is which.

## Text to post (version A: every H1 row returns UNSAT from both solvers)

> We report two things about this problem, neither of which settles it.
>
> **1. Computational evidence for a strict drop, F(49) = 7 < 8 = F(48).**
> In Ramsey terms this is r(41) = r(42) = 49, the open entry r(42) ∈ {49, 50}
> of Boza's table (arXiv:2409.12770v2) taking the value 49. The lower sides
> are explicit C_4-free graphs: a 48-vertex graph of minimum degree 7 (not
> isomorphic to the Afzaly–McKay record, by an independent isomorphism check)
> and a 49-vertex graph of minimum degree 6, both checked in Lean 4 via
> `native_decide`. The upper side at order 49, that no C_4-free graph on 49
> vertices has minimum degree 7, is a case split into four strata. Three are
> closed by written arguments backed by reviewed computation. The fourth is
> split into [N_TOTAL] SAT instances; [N_CERT] have archived DRAT/LRAT
> certificates, and the remaining [N_GAP] were each returned UNSAT by two
> independent solvers (Kissat 4.0.4 and CaDiCaL 3.0.1) without proof logging.
> This is evidence, not a proof: no part of the order-49 nonexistence claim
> has been replayed through a proof-checking kernel end to end. The paper
> prices that replay (roughly $1,300 of spot compute and 17 days for the
> archived certificates; the uncertified instances have no reliable price)
> and states exactly which Lean statements would consume it. We are aware of
> no earlier decided strict drop of F on the domain N ≥ 4, and we do not claim
> this one is decided.
>
> **2. A Lean-checked reduction for the negative answer.** Let A-REG be the
> statement that for every k ≥ 3 there is no C_4-free 2^k-regular graph on
> 4^k vertices. Lean 4 (standard axioms only) verifies that A-REG implies a
> negative answer to this problem: F(N+1) < F(N) for infinitely many N. A-REG
> is open and we do not conjecture it. The analogue at k = 2 is false, there
> is no drop at orders 15–16 or 35–36, and the paper records a long list of
> determinant, spectral, packing and census approaches that fail to prove it.
>
> A single drop at 48 to 49 is compatible with either answer to the problem
> as posed, which concerns all sufficiently large N. We make no claim about
> the problem itself.
>
> Paper, Lean sources, solver receipts and the negative map: [ARCHIVE LINK].
> The work was carried out by AI systems (Claude and GPT models) under human
> direction; details of who did what are in the paper.

## Version B delta (some H1 rows reach the solver cap)

Replace the sentence beginning "The fourth is split" with:

> The fourth is split into [N_TOTAL] SAT instances; [N_CERT] have archived
> DRAT/LRAT certificates, [N_DUAL] were returned UNSAT by two independent
> solvers without proof logging, and [N_OPEN] reached a declared
> four-hour cap in at least one solver and remain open; they are listed in
> the paper. No instance returned SAT.

and replace the heading of item 1 with "**Partial computational evidence for
a strict drop**". If any instance returns SAT the drop claim is withdrawn and
item 1 is rewritten around r(42) = 50.

## Fill rules

- `[N_TOTAL]`, `[N_CERT]`, `[N_GAP]`, `[N_DUAL]`, `[N_OPEN]` come only from the
  receipt-derived H1 census table named in manuscript §8 (exact tag and CNF
  joins). The capacity grid (13,351 slots; 12,019 ready certificate inputs;
  1,288 gaps) and the Phase B root set (1,257 H1 roots; 96 historical; 1,161
  residual) are overlapping decompositions and must not be summed.
- "archived certificates" means checked by `drat-trim` at production time or
  inventoried as objects. It never means replayed in Lean.
- The A-REG paragraph must match `not_erdos85Question_of_binarySquareRegularExclusion`
  and the literal `#print axioms` output for it.
- The authorship sentence follows the operator's authorship ruling (goal #45).
