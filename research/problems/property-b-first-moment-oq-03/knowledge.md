# Knowledge Base: property-b-first-moment-oq-03

Open question: sharpen the Property B lower bound to the **Radhakrishnan–Srinivasan**
`m(k) = Ω(2^k·√(k/log k))` (RS 2000) via the asymmetric/recoloring refinement of the
first moment argument. Parent `property-b-first-moment` (file `PropertyBFirstMoment.lean`)
proves Erdős' 1963 uniform bound `m(k) ≥ 2^(k-1)`.

---

## State of the parent / siblings (as of 2026-06-28)

- Parent `PropertyBFirstMoment.lean` (`ProbMethod.PropertyB`): Erdős 1963 uniform
  first-moment bound. Key reusable API: `Mono e c`, `card_mono` (exactly `2·2^(n-|e|)`
  colorings are monochromatic on a nonempty edge `e`), `exists_zero_of_sum_lt_card`
  (integer first moment principle), `card_const_on`. 0 sorries / 0 axioms.
- Sibling oq-01 → `PropertyBUpperBound.lean`: explicit non-2-colorable hypergraphs
  bracketing `m(k)` (upper bounds).
- Sibling oq-02 → `PropertyBFirstMomentRamsey.lean`: Erdős' 1947 Ramsey bound via the
  same template (edges of `K_n` as the 2-colored ground set).

## Session (2026-06-28, researcher-1): non-uniform first-moment sharpening

New file `PropertyBFirstMomentOQ03.lean` (122 lines, 3 theorems, **0 sorries / 0 axioms**,
`#print axioms` = propext/Classical.choice/Quot.sound only; the worked example uses
`decide`, NOT `native_decide`, so no `Lean.ofReduceBool`). Gallery entry
`src/data/proofs/property-b-first-moment-oq-03/` (meta.json + annotations.json) added.

Delivered the **sharp single-round first-moment criterion** — the honest, tractable part
of oq-03:

* `property_b_of_weighted_first_moment` — a finite family `E` of nonempty edges of
  *arbitrary sizes* is 2-colorable as soon as `2·∑_{e∈E} 2^(n-|e|) < 2^n`, equivalently
  the genuine Erdős criterion `∑_e 2^(1-|e|) < 1`. Proof = parent's first moment with
  `card_mono` summed over heterogeneous edge sizes (`card_filter` + `sum_comm` +
  `mul_sum` + `exists_zero_of_sum_lt_card`). Dropping uniformity is free because
  `card_mono` is already per-edge.
* `property_b_two_colorable_of_uniform` — recovers the parent's uniform theorem
  (`|e|=k`, `<2^(k-1)` edges) as a corollary; the weighted sum collapses to `|E|·2^(n-k)`.
  Confirms the refinement strictly extends the parent.
* `mixed_example_two_colorable` — `{{0,1},{0,1,2}}` over `Fin 3`: weighted sum `2+1=3`,
  `2·3=6<8`, certified 2-colorable though the uniform theorem can't be applied (mixed
  sizes). Hypotheses by `decide`.

### Why this is NOT the full oq-03 (honest scoping)

The single-round first moment is **sharp at `∑ 2^(1-|e|) < 1`** and provably cannot reach
RS `Ω(2^k·√(k/log k))`. The RS improvement needs a **random recoloring (alteration)**:
after the first uniform 2-coloring, independently recolor the vertices lying in surviving
monochromatic edges (in a fixed random vertex order, recolor with small probability `p`),
and bound `P[some edge still monochromatic]` by `m·2^(1-k)·(stuff) + m·k·p·(1-p)^(...)`,
optimized at `p ≈ (log k)/k` to give the `√(k/log k)` gain. This is a genuinely different
(two-round, order-dependent) probability model — NOT expressible by summing `card_mono`
over a single product sample space `V → Bool`.

### Roadmap / tractability verdict for RS (oq-03 remainder)

RS formalization is a **moonshot** in Lean 4.26.0:
- Needs a real-valued (or rational) probability model with a *recoloring* second stage
  and a vertex ordering — the current file's integer first-moment counting does not
  scale to it.
- Needs concentration / union-bound estimates with the `p ≈ log k / k` optimization and
  `√(k/log k)` asymptotics — heavy real-analysis bookkeeping.
- Recommended decomposition if pursued: (1) a rational two-stage "recolor-with-prob-`p`"
  expectation lemma for a single edge; (2) the union bound over `m` edges; (3) the
  `p = log k / k` optimization as a separate analytic lemma. Each is a multi-session
  effort. Until (1)–(3) exist, further single-round first-moment work adds nothing new
  beyond the criterion proved this session.

## Verification
`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/PropertyBFirstMomentOQ03.lean`
exits 0 (~45s, host toolchain, single-file against prebuilt Mathlib oleans). `#print axioms`
checked by appending the print lines, `env lean`, then reverting.
