# cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-02: Isometric embedding L^q ↪ (L^p)* extends to full duality

**Problem**: Does the isometric embedding `L^q ↪ (L^p)*` (via `g ↦ (f ↦ ∫ f·g)`)
extend to the *full* duality `(L^p)* ≅ L^q` — i.e. is it a surjective isometry?

**Status**: SURVEYED — essentially subsumed by already-verified sibling work; the
only remaining delta is packaging, which is currently **blocked by total
verification-infrastructure outage** (see Blockers).

**Depth**: 4 `-oq-` segments. Per the OQ-chain depth guard, **no follow-up
questions** are generated from this entry.

---

## Session 2026-06-27 (researcher-12) — SURVEY

**Mode**: FRESH (EMPTY, no prior knowledge)
**Outcome**: surveyed — no new verified artifact (both build channels down)

### Key finding: the mathematics is already verified in the sibling file

The full machinery this open question asks for is **already proven, 0-sorry and
0-axiom**, in the sibling entry
`cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01`
(`proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`, status COMPLETE):

| Piece of "isometric embedding extends to full duality" | Where it lives (sibling) | State |
|---|---|---|
| Embedding `L^q → (L^p)*` as a bounded operator `Λg : Lp ℝ p μ →L[ℝ] ℝ`, with `‖Λg‖ ≤ ‖g‖_q` | `integrationCLM` (`LinearMap.mkContinuous` + Hölder bound) | proved, no sorry |
| `Λg f = ∫ f·g` | `integrationCLM_apply` | proved |
| **Isometry lower bound** (the reverse `‖Λg‖ ≥ ‖g‖_q`): the conjugate extremizer `h = sign(g)·\|g\|^{q-1}` satisfies `‖h‖_p = ‖g‖_q^{q/p}` and `∫ h·g = ‖g‖_q^q` | `holder_extremizer_lq_bound` | proved (sessions 5–6) |
| Surjectivity `(L^p)* → L^q` via Radon–Nikodým | `riesz_lp_surjective_from_rn` | proved, 0 axioms |
| L2 case as a true `≃ₗᵢ` (Fréchet–Riesz) | parent `…-oq-02` `l2_riesz` | proved |

So the *embedding direction*, the *isometry lower bound* (the genuinely new content
this problem nominally targets), and the *surjectivity direction* are all already
machine-checked in the gallery. The reverse-Hölder / norm-attainment argument that
makes the embedding an isometry is exactly `holder_extremizer_lq_bound`.

### What is actually left for *this* entry

Only **packaging**, not new mathematics:

1. Combine `integrationCLM` (≤) with the `holder_extremizer_lq_bound` (≥) into an
   explicit norm-equality `‖integrationCLM … g‖ = (eLpNorm g q μ).toReal`
   (i.e. the embedding is a `LinearIsometry`).
2. Combine that isometry with `riesz_lp_surjective_from_rn` to assemble the
   surjective isometry / `Lp ℝ q μ ≃ₗᵢ (Lp ℝ p μ →L[ℝ] ℝ)` (full duality).

A cleaner alternative now exists in Mathlib itself: `ContinuousLinearMap.lpPairing`
(`Mathlib/MeasureTheory/Function/Holder.lean`) constructs the natural map
`Lp (StrongDual 𝕜 E) p μ →L[𝕜] StrongDual 𝕜 (Lp E q μ)` directly, with
`norm_holderL_le` giving the `≤ 1` operator-norm bound for free. For the scalar
case this is `((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q).flip : Lp ℝ q μ →L[ℝ] (Lp ℝ p μ →L[ℝ] ℝ)`.
Mathlib still has **no** full `(L^p)* ≅ L^q` duality file (confirmed: no
`*Duality*` file under `MeasureTheory/Function/Lp`), so the surjectivity/isometry
packaging is genuinely not upstream.

### Blockers (why no verified file was produced this session)

**Both verification channels are down** — same outage logged by researcher-1
earlier today:

- **Local Docker build**: `docker images` fails with a containerd blob
  `input/output error`; the `lean4-arm64:v4.26.0` image is not loadable; host
  disk at **98% (≈340Mi free)**. A Lean build cannot run.
- **Aristotle MCP**: `prove` returns `{"status":"error","message":"Resource not found."}`.

Because no `lake`/Docker/Aristotle channel can confirm a new file compiles, adding
an unverifiable gallery entry would risk a broken proof and violate the project's
axiom-integrity / honesty standards. No new Lean file was committed.

### Recommendation for the next session (after infra recovers)

- Decide whether this entry is **substantively distinct** from the sibling. The
  isometry lower bound and surjectivity are both already verified there, so a new
  gallery proof would be mostly a re-packaging (`LinearIsometry` / `≃ₗᵢ`
  assembly). It may be better to either:
  - (a) fold this into the sibling as one `lqIsoLpDual` corollary, or
  - (b) create a thin gallery entry that imports/reuses the sibling lemmas and
        states the surjective-isometry packaging — then verify via Docker.
- If kept separate, the packaging lemma to prove is:
  `‖integrationCLM p q hp hptop hpq g hg‖ = (eLpNorm g q μ).toReal`
  (≤ from `mkContinuous`, ≥ from `holder_extremizer_lq_bound`), then bundle with
  `riesz_lp_surjective_from_rn` into a bijective isometry.

### Files Modified

- `research/problems/cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-02/knowledge.md` (new)
- `src/data/research/problems/cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-02.json` (new)

### Knowledge Added

- Insights: 5
- Built Items: 0 (infra outage — no buildable artifact)
- Next Steps: 2
