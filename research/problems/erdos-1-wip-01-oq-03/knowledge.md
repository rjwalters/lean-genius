# Knowledge Base: erdos-1-wip-01-oq-03

**Problem**: Erdős #1 — Conway–Guy construction / optimality (WIP Extension OQ03)
**Open question**: Is the Conway–Guy sequence optimal for large n? Known for n ≤ 10
(OEIS A005318), open for n ≥ 11. Is there algebraic structure enabling a Lean
formalization of its construction?

---

## Session 2026-07-03 (Session 1) — Decidable DSS criterion + Conway–Guy witnesses

**Mode**: FRESH
**Outcome**: progress (new verified entry)

### What I Did

1. Surveyed the Erdős #1 family. Existing infra (`Erdos1Wip01.lean`) proves the
   powers-of-two upper bound `f(n) ≤ 2^(n-1)` via a superincreasing extension
   lemma, but nothing certified the **Conway–Guy** improvement that beats it.
2. Identified the tractable, honestly-scoped deliverable: the *optimality*
   question is open (n ≥ 11), and even the general `< 2^(n-1)` gap needs the
   Conway–Guy recurrence `a(n+1)=2a(n)−a(n−r)`, `r=round(√(2n))`, whose
   subset-sum-distinctness has no known elementary induction (prior session on
   `erdos-1-wip-01` flagged the recurrence as "unclear"). So I certified the
   phenomenon on explicit cases and built reusable decidability infrastructure.
3. Created `proofs/Proofs/Erdos1Wip01OQ03.lean` (0 sorries, 0 axioms):
   - `hasDistinctSubsetSums_iff_image_card`: the bare DSS definition quantifies
     over all `Finset ℕ` (not decidable); reduced it to injectivity of the
     subset-sum map on `A.powerset`, i.e. `(A.powerset.image (·.sum id)).card =
     A.powerset.card`. Decidable ⇒ concrete instances by `decide`.
   - `hasDistinctSubsetSums_iff_card_pow`: same with explicit `2^|A|`.
   - Explicit Conway–Guy witnesses `cg4…cg8` = difference sets of
     `0,1,2,4,7,13,24,44,84`: `{3,5,6,7}`, `{6,9,11,12,13}`,
     `{11,17,20,22,23,24}`, `{20,31,37,40,42,43,44}`,
     `{40,60,71,77,80,82,83,84}`. Each certified DSS + card + all elements
     `< 2^(n-1)` by kernel `decide` (NO native_decide, so axiom-free).
   - `conwayGuy_beats_powers_of_two`: for n ∈ {4,…,8} there is an n-element DSS
     set with every element `< 2^(n-1)` — powers-of-two is not optimal.

### Key Findings

- **DSS is decidable via powerset-image cardinality.** `Finset.card_image_iff`
  turns "distinct subset sums" into an `InjOn` check on the powerset, which
  `decide` evaluates in O(2^n) rather than the naive O(4^n) pair scan.
- **Conway–Guy difference sets verified numerically** (Python) for n=4..9: all
  DSS, all with max element < 2^(n-1) (7<8, 13<16, 24<32, 44<64, 84<128,
  161<256). Chose n≤8 for kernel-`decide` feasibility (axiom-free). n=7,8 need
  `set_option maxRecDepth 10000`.
- **Optimality stays open.** A005318 optimality is only computationally known
  for n ≤ 10; no algebraic proof for large n. Not attempted (genuinely open).

### Files Modified

- `proofs/Proofs/Erdos1Wip01OQ03.lean` (new)
- `src/data/proofs/erdos-1-wip-01-oq-03/meta.json` (new gallery entry)

### Next Steps

- Formalize the Conway–Guy recurrence `a(n+1)=2a(n)−a(n−round(√(2n)))` as a Lean
  `def` and attempt an inductive DSS proof for the general family (HARD/OPEN —
  candidate for Aristotle on the concrete recurrence lemmas).
- Push the decidable criterion into `Erdos1Wip01.lean` for reuse across OQ01–04.
- Larger explicit witnesses (n=9,10) would need `native_decide` (adds
  `Lean.ofReduceBool`) — only if an axiomatized variant is wanted.
