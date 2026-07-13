# Erdős #1162 OQ-04 — Analogous asymptotic for the alternating group A_n

## Question

Erdős #1162 asks for the asymptotic of f(n) = #{subgroups of S_n}
(answered by Roney–Dougal–Tracey 2025: log f(n) = (1/16 + o(1))n²).
**OQ-04:** what is the analogous result for A_n? Write g(n) = #{subgroups of A_n}.

## Answer (this project's decomposition)

**log g(n) = (1/16 + o(1)) n² — the SAME constant as S_n.**

The result splits cleanly into a *free* upper half and a *deep* lower half:

| Half | Statement | Cost |
|------|-----------|------|
| Reduction | g(n) ≤ f(n) unconditionally | **0 axioms** (theorem) |
| Upper | limsup log g(n)/n² ≤ 1/16 | **0 new axioms** (from parent RDT) |
| Lower | liminf log g(n)/n² ≥ 1/16 | **1 new axiom** (A_n analogue of RDT lower bound) |

So the entire *upper* asymptotic transfers from the already-axiomatized S_n
result for free. Only the lower bound is genuinely new — and even that keeps the
constant 1/16 unchanged.

## Key insights

1. **Reduction g(n) ≤ f(n) is unconditional.** The inclusion A_n ↪ S_n is an
   injective group homomorphism, so `Subgroup.map` along `(alternatingGroup
   (Fin n)).subtype` injects the subgroup lattice of A_n into that of S_n.
   `Nat.card` is monotone under injections into the finite type `Subgroup(S_n)`.

2. **Upper half is FREE.** Composing g ≤ f with the parent asymptotic
   log f(n)/n² → 1/16 gives, with no new axiom, `∀ε>0, eventually log g/n² < 1/16+ε`.
   Formally: `An_ratio_eventually_lt`.

3. **Same constant 1/16 for A_n.** The dominant contribution to the subgroup
   count comes from elementary abelian 2-subgroups on ≈ n/4 points; (1/4)² = 1/16.
   A_n still contains these: even-weight products of disjoint transpositions form
   an elementary abelian 2-group of rank ⌊n/2⌋ − 1, ample for the 2^{cn²} lower
   bound. Hence the lower half also has constant 1/16.

4. **Contrast at small n.** |A_2| = 1, so g(2) = 1, whereas f(2) = 2. Also
   g(1)=1, g(3)=2 (A_3 ≅ Z/3 prime cyclic), g(4)=10 (A_4 of order 12).

## Candidate formalization

`Erdos1162OQ04.lean` (in this directory — **kept out of `proofs/Proofs/`** so the
lakefile glob does not try to compile an unverified file). Contents:

- `numSubgroupsAn n := Nat.card (Subgroup (alternatingGroup (Fin n)))`
- `numSubgroupsAn_pos`, `numSubgroupsAn_le` (the reduction, 0 axioms)
- `log_numSubgroupsAn_le`, `An_ratio_le` (log/ratio transfer)
- `An_ratio_eventually_lt` (upper half, 0 new axioms — from parent RDT)
- `axiom An_lower_bound` (the ONE new axiom)
- `alternating_asymptotic`, `pyber_alternating` (assembled results)

The file imports `Proofs.Erdos1162Problem` and reuses
`Erdos1162.roney_dougal_tracey`, so the S_n axiom is NOT double-counted.

## Status of tooling (this session)

- **Docker build BLOCKED**: containerd blob (`lean4-arm64:v4.26.0`) EIO —
  `docker run` fails with `input/output error` on the content-store blob.
- **Aristotle OFFLINE**: `prove` returns `{"status":"error","message":
  "Resource not found."}` (404).
- **No local Mathlib source** in `.lake` to grep for API names.

Consequently the candidate is **UNVERIFIED**. The parts mirroring the verified
parent proof (`rdt_implies_pyber` machinery: `Metric.tendsto_nhds`, `abs_lt`,
`lt_div_iff`, …) are high-confidence; the genuinely new API surface to confirm is:
`Subgroup.map_injective`, `Nat.card_le_card_of_injective`, the
`Finite (Subgroup (Perm (Fin n)))` instance, `Real.log_le_log` arg order, and the
`(A_n).subtype` injectivity route. See the checklist at the bottom of the .lean file.

## Next steps

1. When Docker/Aristotle recover: move `Erdos1162OQ04.lean` into `proofs/Proofs/`,
   build (`./proofs/scripts/docker-build.sh Proofs.Erdos1162OQ04`), fix the ≤5 API
   names on the checklist.
2. On success, create gallery entry `src/data/proofs/erdos-1162-oq-04/`
   (status `axiomatized`, axiomCount 1, badge `axiom`) mirroring parent erdos-1162.
3. Optional: prove the small cases g1,g2,g3 (structurally / native_decide) — note
   native_decide would add `Lean.ofReduceBool`.

## References

- [RoTr25] Roney-Dougal, Tracey, "The number of subgroups of the symmetric
  group" (2025).
- [Py93] Pyber, "Enumerating finite groups of given order" (1993).
- Parent: `proofs/Proofs/Erdos1162Problem.lean`, `research/problems/erdos-1162/`.

---

### Session 2026-07-04 (researcher-6) — ORIENT increment

- Phase NEW → ORIENT. Established the free-upper / deep-lower decomposition and
  wrote the candidate `Erdos1162OQ04.lean` implementing it (reduction as a
  0-axiom theorem, exactly one new axiom `An_lower_bound`).
- Reconstructed the reduction proof that a prior iteration described but never
  committed. Kept the file outside the `proofs/` glob to avoid breaking CI while
  UNVERIFIED.
- Dual-tool blackout (Docker containerd EIO + Aristotle 404) persists; build not
  verified. Produced an API-name checklist for when tooling recovers.
