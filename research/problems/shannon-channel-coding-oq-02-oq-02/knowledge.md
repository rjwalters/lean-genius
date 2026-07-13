# Shannon channel coding — OQ-02 / OQ-02: formalize the joint typicality lemma

**Problem.** Formalize the joint typicality lemma used in the random-coding achievability proof of
the channel coding theorem.

## Session 1 (researcher-2, 2026-06-27) — phase OBSERVE → ACT

### Background
The joint typicality lemma (Cover & Thomas, Thm 7.6.1) has three properties of the jointly
ε-typical set `A_ε^{(n)} ⊆ 𝒳ⁿ × 𝒴ⁿ`:
1. `P((Xⁿ,Yⁿ) ∈ A_ε) → 1`  — **AEP / weak law of large numbers** (analytic, hard).
2. `|A_ε| ≤ 2^{n(H(X,Y)+ε)}` — size bound (combinatorial).
3. `P((X̃ⁿ,Ỹⁿ) ∈ A_ε) ≤ 2^{-n(I−3ε)}` for independent sequences — independence bound (combinatorial).

### Strategy chosen
Full lemma (esp. Property 1) needs the i.i.d.-product LLN — that is a >1000-line undertaking on
its own and the analytic heart. Rather than axiomatize it (which would be scaffolding), I isolated
the **combinatorial core (Properties 2 & 3)**, which is fully provable WITHOUT any probabilistic
limit by taking the per-sequence probability bounds that *define* typicality as hypotheses (they are
definitional, not the hard part).

### What was proved (`proofs/Proofs/ShannonChannelCodingOQ02OQ02.lean`, namespace
`InformationTheory.ChannelCoding.JointTypicality`, 0 axioms / 0 sorries, 4 theorems)
- `typicalSet_card_le` — abstract: under a sub-pmf `p`, a set whose elements each carry mass ≥ δ>0
  has ≤ 1/δ elements (`card·δ ≤ ∑_A p ≤ ∑ p ≤ 1`).
- `prob_le_card_mul` — abstract: `∑_{A} q ≤ |A|·(max mass)`.
- `jointlyTypicalSet_card_le` — Property (2): `|A_ε| ≤ 2^{n(H(X,Y)+ε)}` (uses `Real.rpow_neg`).
- `joint_typicality_independence_bound` — Property (3): product-law mass `≤ 2^{-n((HX+HY−HXY)−3ε)}
  = 2^{-n(I−3ε)}` (combine (2) with `prob_le_card_mul`, `Real.rpow_add`, exponent `ring`).

The file is standalone (`import Mathlib`, no dependency on the possibly-stale Shannon Lean files),
so it builds independently. Registered in `proofs/Proofs.lean`.

### Honesty boundary
Property (1) (the AEP convergence) is **not** formalized and **not** axiomatized — the axiom count
stays 0. It is the genuinely analytic next target (Chebyshev/L² on the empirical information
density), buildable on Mathlib's `ProbabilityTheory` LLN.

### Verification status: UNVERIFIED
Both channels down this session:
- Docker host: containerd `meta.db: input/output error`; `docker images` empty (cached
  `lean4-arm64:v4.26.0` gone). Operator restart needed (NOT ENOSPC).
- Aristotle MCP: `404` on `/api/v1/project`.
Manually reviewed lemma-by-lemma; all lemma names (`le_div_iff₀`, `Real.rpow_add`,
`Real.rpow_neg`, `Finset.sum_const`, `nsmul_eq_mul`, `Finset.sum_le_sum_of_subset_of_nonneg`)
confirmed present by grepping existing compiling proofs in the repo.

### Next steps
- Rebuild `Proofs.ShannonChannelCodingOQ02OQ02` when the host recovers; if green, add gallery
  `src/data/proofs/shannon-channel-coding-oq-02-oq-02/{meta.json,annotations.json}`.
- Follow-up (depth 2, allowed): formalize Property (1) via i.i.d. product + WLLN, completing the
  full lemma; then wire (1)+(3) into the random-coding error bound.
